(*  Title:       The Chop Operation on Lambda-Free Higher-Order Terms
    Author:      Alexander Bentkamp <a.bentkamp at vu.nl>, 2018
    Maintainer:  Alexander Bentkamp <a.bentkamp at vu.nl>
*)

section \<open>The Chop Operation on Lambda-Free Higher-Order Terms\<close>

theory Chop
imports Embeddings
begin

definition chop :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm" where
  "chop t = apps (hd (args t)) (tl (args t))"

subsection \<open>Basic properties\<close>

lemma chop_App_Hd: "is_Hd s \<Longrightarrow> chop (App s t) = t" 
  unfolding chop_def args.simps 
  using args_Nil_iff_is_Hd by force

lemma chop_apps: "is_App t \<Longrightarrow> chop (apps t ts) = apps (chop t) ts" 
  unfolding chop_def by (simp add: args_Nil_iff_is_Hd)

lemma vars_chop: "is_App t \<Longrightarrow> vars (chop t) \<union> vars_hd (head t) = vars t" 
  by (induct rule:tm_induct_apps; metis (no_types, lifting) chop_def UN_insert Un_commute list.exhaust_sel list.simps(15)
      args_Nil_iff_is_Hd tm.simps(17) tm_exhaust_apps_sel vars_apps)

lemma ground_chop: "is_App t \<Longrightarrow> ground t \<Longrightarrow> ground (chop t)" 
  using vars_chop by auto

(* TODO: move? *)
lemma size_apps: "size (apps t ts) = size t + sum_list (map size ts) + length ts"
  by (induct ts arbitrary:t; simp)

(* TODO: move? *)
lemma size_args_plus_num_args: "1 + sum_list (map size (args t)) + num_args t = size t"
  by (metis One_nat_def size_apps tm.size(3) tm_collapse_apps)

lemma size_chop: "is_App t \<Longrightarrow> Suc (Suc (size (chop t))) = size t"
  unfolding size_args_plus_num_args[of t, symmetric] chop_def size_apps
  by (metis Nitpick.size_list_simp(1) ab_semigroup_add_class.add_ac(1) args_Nil_iff_is_Hd plus_1_eq_Suc size_list_conv_sum_list)

lemma size_chop_lt: "is_App t \<Longrightarrow> size (chop t) < size t"
  by (simp add: Suc_le_lessD less_or_eq_imp_le size_chop)

lemma chop_fun:
  assumes "is_App t" "is_App (fun t)" 
  shows "App (chop (fun t)) (arg t) = chop t"  
proof -
  have "args (fun t) \<noteq> []"
    using assms(2) args_Nil_iff_is_Hd by blast
  then show ?thesis 
    unfolding chop_def
    using assms(1) by (metis (no_types) App_apps args.simps(2) hd_append2 tl_append2 tm.collapse(2))
qed

subsection \<open>Chop and the Embedding Relation\<close>

lemma emb_step_chop: "is_App t \<Longrightarrow> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop t" 
proof (induct "num_args t - 1" arbitrary:t)
  case 0
  have nil: "num_args t = 0 \<Longrightarrow> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop t" unfolding chop_def using 0 args_Nil_iff_is_Hd by force
  have single: "\<And>a. args t = [a] \<Longrightarrow> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop t" unfolding chop_def 
    by (metis "0.prems" apps.simps(1) args.elims args_Nil_iff_is_Hd emb_step_arg last.simps last_snoc list.sel(1) list.sel(3) tm.sel(6))
  then show ?case using nil single
    by (metis "0.hyps" length_0_conv length_tl list.exhaust_sel)
next
  case (Suc x)
  have 1:"apps (Hd (head t)) (butlast (args t)) \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop (apps (Hd (head t)) (butlast (args t)))"
    using Suc(1)[of "apps (Hd (head t)) (butlast (args t))"]
    by (metis Suc.hyps(2) Suc_eq_plus1 add_diff_cancel_right' args_Nil_iff_is_Hd length_butlast list.size(3) nat.distinct(1) tm_exhaust_apps_sel tm_inject_apps)
  have 2:"App (apps (Hd (head t)) (butlast (args t))) (last (args t)) = t"
    by (simp add: App_apps Suc.prems args_Nil_iff_is_Hd)
  have 3:"App (chop (apps (Hd (head t)) (butlast (args t)))) (last (args t)) = chop t"
  proof -
    have f1: "hd (args t) = hd (butlast (args t))"
      by (metis Suc.hyps(2) Suc.prems append_butlast_last_id args_Nil_iff_is_Hd hd_append2 length_0_conv length_butlast nat.simps(3))
    have "tl (args t) = tl (butlast (args t)) @ [last (args t)]"
      by (metis (no_types) Suc.hyps(2) Suc.prems append_butlast_last_id args_Nil_iff_is_Hd length_0_conv length_butlast nat.simps(3) tl_append2)
    then show ?thesis
      using f1 chop_def 
      by (metis App_apps append_Nil args.simps(1) args_apps)
  qed
  then show ?case using 1 2 3 by (metis context_left)
qed 

lemma chop_emb_step_at:
  assumes "is_App t"
  shows "chop t = emb_step_at (replicate (num_args (fun t)) Left) Right t"
using assms proof (induct "num_args (fun t)" arbitrary: t)
  case 0
  then have rep_Nil:"replicate (num_args (fun t)) dir.Left = []" 
    by simp 
  then show ?case unfolding rep_Nil 
    by (metis "0.hyps" "0.prems" emb_step_at_right append_Nil apps.simps(1) args.simps(2) chop_def length_0_conv list.sel(1) list.sel(3) tm.collapse(2)) 
next
  case (Suc n)
  then show ?case using Suc.hyps(1)[of "fun t"]
    using emb_step_at_left_context args.elims args_Nil_iff_is_Hd chop_fun butlast_snoc diff_Suc_1 length_0_conv length_butlast nat.distinct(1) replicate_Suc tm.collapse(2) tm.sel(4)
    by metis
qed

lemma emb_step_at_chop:
  assumes emb_step_at: "emb_step_at p Right t = s"
    and pos:"position_of t (p @ [Right])"
    and all_Left: "list_all (\<lambda>x. x = Left) p"
  shows "chop t = s \<or> chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s"
proof -
  have "is_App t" 
    by (metis emb_step_at_if_position emb_step_at_is_App emb_step_equiv pos)
  have p_replicate: "replicate (length p) Left = p" using replicate_length_same[of p Left]
    by (simp add: Ball_set all_Left)
  show ?thesis
  proof (cases "Suc (length p) = num_args t")
    case True
    then have "p = replicate (num_args (fun t)) Left" using p_replicate 
      by (metis Suc_inject \<open>is_App t\<close> args.elims args_Nil_iff_is_Hd length_append_singleton tm.sel(4))
    then have "chop t = s" unfolding chop_emb_step_at[OF \<open>is_App t\<close>] 
      using pos emb_step_at by blast
    then show ?thesis by blast
  next
    case False
    then have "Suc (length p) < num_args t"
      using pos emb_step_at \<open>is_App t\<close> \<open>list_all (\<lambda>x. x = dir.Left) p\<close>
    proof (induct p arbitrary:t s)
      case Nil
      then show ?case 
        by (metis Suc_lessI args_Nil_iff_is_Hd length_greater_0_conv list.size(3))
    next
      case (Cons a p)
      have "a = Left" 
        using Cons.prems(5) by auto
      have 1:"Suc (length p) \<noteq> num_args (fun t)"  
        by (metis (no_types, lifting) Cons.prems(1) Cons.prems(4) args.elims args_Nil_iff_is_Hd length_Cons length_append_singleton tm.sel(4))
      have 2:"position_of (fun t) (p @ [Right])"   using \<open>position_of t ((a # p) @ [Right])\<close> \<open>is_App t\<close> 
        by (metis (full_types) Cons.prems(5) position_of_left append_Cons list_all_simps(1) tm.collapse(2))
      have 3: "emb_step_at p dir.Right (fun t) = emb_step_at p dir.Right (fun t)" 
        using emb_step_at_left_context[of p Right "fun t" "arg t"] by blast
      have "Suc (length p) < num_args (fun t)" using Cons.hyps[OF 1 2 3] 
        by (metis "2" Cons.prems(5) Nil_is_append_conv list_all_simps(1) not_Cons_self2 position_of.elims(2) tm.discI(2))
      then show ?case 
        by (metis Cons.prems(4) Suc_less_eq2 args.simps(2) length_Cons length_append_singleton tm.collapse(2))
    qed      
    define q where "q = replicate (num_args (fun t) - Suc (length p)) dir.Left"
    have "chop t = emb_step_at (p @ [Left] @ q) dir.Right t"
    proof -
      have "length p + (num_args (fun t) - length p) = num_args (fun t)" 
        using \<open>Suc (length p) < num_args t\<close>
        by (metis Suc_less_eq2 \<open>is_App t\<close> args.simps(2) diff_Suc_1 leD length_butlast nat_le_linear 
            ordered_cancel_comm_monoid_diff_class.add_diff_inverse snoc_eq_iff_butlast tm.collapse(2))
      then have 1:"replicate (num_args (fun t)) dir.Left = p @ replicate (num_args (fun t) - length p) dir.Left" 
        by (metis p_replicate replicate_add)
      have "0 < num_args (fun t) - length p"
        by (metis (no_types) False \<open>is_App t\<close> \<open>length p + (num_args (fun t) - length p) = num_args (fun t)\<close> args.simps(2) length_append_singleton less_Suc_eq less_add_Suc1 tm.collapse(2) zero_less_diff)
      then have "replicate (num_args (fun t) - length p) dir.Left = [Left] @ q" unfolding q_def
        by (metis (no_types) Cons_replicate_eq Nat.diff_cancel Suc_eq_plus1 \<open>length p + (num_args (fun t) - length p) = num_args (fun t)\<close> append_Cons self_append_conv2)
      then show ?thesis using chop_emb_step_at
        using \<open>is_App t\<close> 1
        by (simp add: chop_emb_step_at)
    qed
    then have "chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s"
      using pos merge_emb_step_at[of p Right q Right t] 
      by (metis emb_step_at_if_position opp_simps(1) emb_step_at pos_emb_step_at_opp)
    then show ?thesis by blast
  qed
qed

lemma emb_step_at_remove_arg:
  assumes emb_step_at: "emb_step_at p Left t = s"
    and pos:"position_of t (p @ [Left])"
    and all_Left: "list_all (\<lambda>x. x = Left) p"
  shows "let i = num_args t - Suc (length p) in 
  head t = head s \<and> i < num_args t \<and> args s = take i (args t) @ drop (Suc i) (args t)"
proof -
  have "is_App t" 
    by (metis emb_step_at_if_position emb_step_at_is_App emb_step_equiv pos)
  have C1: "head t = head s" 
    using all_Left emb_step_at pos proof (induct p arbitrary:s t)
    case Nil
    then have "s = emb_step_at [] dir.Left (App (fun t) (arg t))"
      by (metis position_of.elims(2) snoc_eq_iff_butlast tm.collapse(2) tm.discI(2))
    then have "s = fun t" by simp
    then show ?case by simp
  next
    case (Cons a p)
    then have "a = Left" by simp
    then have "head (emb_step_at p Left (fun t)) = head t" 
      by (metis Cons.hyps Cons.prems(1) head_fun list.pred_inject(2) position_if_emb_step_at)
    then show ?case using emb_step_at_left_context[of p a "fun t" "arg t"]
      by (metis Cons.prems(2) \<open>a = Left\<close> emb_step_at_is_App head_App tm.collapse(2)) 
  qed

  let ?i = "num_args t - Suc (length p)"

  have C2:"?i < num_args t" 
    by (simp add: \<open>is_App t\<close> args_Nil_iff_is_Hd)

  have C3:"args s = take ?i (args t) @ drop (Suc ?i) (args t)"
    using all_Left pos emb_step_at \<open>is_App t\<close> proof (induct p arbitrary:s t)
    case Nil
    then show ?case using emb_step_at_left[of "fun t" "arg t"]
      by (simp, metis One_nat_def args.simps(2) butlast_conv_take butlast_snoc tm.collapse(2))
  next
    case (Cons a p)
    have "position_of (fun t) (p @ [Left])"
      by (metis (full_types) Cons.prems(1) Cons.prems(2) Cons.prems(4) position_of_left 
          append_Cons list.pred_inject(2) tm.collapse(2))
    then have 0:"args (emb_step_at p Left (fun t))
                   = take (num_args (fun t) - Suc (length p)) (args (fun t)) 
                   @ drop (Suc (num_args (fun t) - Suc (length p))) (args (fun t))"
      using Cons.hyps[of "fun t"] by (metis Cons.prems(1) append_Nil args_Nil_iff_is_Hd drop_Nil 
          emb_step_at_is_App list.size(3) list_all_simps(1) take_0 zero_diff)
    have 1:"s = App (emb_step_at p Left (fun t)) (arg t)" using emb_step_at_left_context[of p Left "fun t" "arg t"] 
      using Cons.prems by auto
    define k where k_def:"k = (num_args (fun t) - Suc (length p))"
    have 2:"take k (args (fun t)) = take (num_args t - Suc (length (a # p))) (args t)"
      by (smt k_def Cons.prems(4) args.elims args_Nil_iff_is_Hd butlast_snoc diff_Suc_eq_diff_pred 
          diff_Suc_less length_Cons length_butlast length_greater_0_conv take_butlast tm.sel(4))
    have k_def': "k = num_args t - Suc (Suc (length p))" using k_def
      by (metis args.simps(2) diff_Suc_Suc length_append_singleton local.Cons(5) tm.collapse(2))
    have 3:"args (fun t) @ [arg t] = args t"
      by (metis Cons.prems(4) args.simps(2) tm.collapse(2))
    have "num_args t > 1" using \<open>position_of t ((a # p) @ [Left])\<close> 
      by (metis "3" \<open>position_of (fun t) (p @ [dir.Left])\<close> args_Nil_iff_is_Hd butlast_snoc emb_step.simps emb_step_at_if_position length_butlast length_greater_0_conv tm.discI(2) zero_less_diff)
    then have "Suc k<num_args t" unfolding k_def'
      using \<open>1 < num_args t\<close> by linarith
    have "\<forall>k< num_args t. drop k (args (fun t)) @ [arg t] = drop k (args t)"
      by (metis (no_types, lifting) \<open>args (fun t) @ [arg t] = args t\<close> drop_butlast drop_eq_Nil last_drop leD snoc_eq_iff_butlast)
    then show ?case using 0 1 2 3 k_def'
      using \<open>Suc k < num_args t\<close> k_def by auto
  qed
  show ?thesis using C1 C2 C3 by simp
qed

lemma emb_step_cases [consumes 1, case_names chop extended_chop remove_arg under_arg]:
  assumes emb:"t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s"
    and chop:"chop t = s \<Longrightarrow> P"
    and extended_chop:"chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> P"
    and remove_arg:"\<And>i. head t = head s \<Longrightarrow> i<num_args t \<Longrightarrow> args s = take i (args t) @ drop (Suc i) (args t) \<Longrightarrow> P"
    and under_arg:"\<And>i. head t = head s \<Longrightarrow> num_args t = num_args s \<Longrightarrow> args t ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b args s ! i \<Longrightarrow>
         (\<And>j. j<num_args t \<Longrightarrow> i \<noteq> j \<Longrightarrow> args t ! j = args s ! j) \<Longrightarrow> P"
  shows P
proof -
  obtain p d where pd_def:"emb_step_at p d t = s" "position_of t (p @ [d])"
    using emb emb_step_equiv' position_if_emb_step_at by metis
  have "is_App t"
    by (metis emb emb_step_at_is_App emb_step_equiv)
  show ?thesis 
  proof (cases "list_all (\<lambda>x. x = Left) p")
    case True
    show ?thesis 
    proof (cases d)
      case Left
      then show P using emb_step_at_remove_arg 
        by (metis True pd_def(1) pd_def(2) remove_arg)
    next
      case Right
      then show P 
        using True chop emb_step_at_chop extended_chop pd_def(1) pd_def(2) by blast
    qed
  next
    case False
    have 1:"num_args t = num_args s" using emb_step_under_args_num_args
      by (metis False pd_def(1))
    have 2:"head t = head s" using emb_step_under_args_head
      by (metis False pd_def(1))
    show ?thesis using 1 2 under_arg emb_step_under_args_emb_step
      by (metis False pd_def(1) pd_def(2))
  qed
qed

lemma chop_position_of:
  assumes "is_App s"
  shows "position_of s (replicate (num_args (fun s)) dir.Left @ [Right])"
  by (metis Suc_n_not_le_n assms chop_emb_step_at lessI less_imp_le_nat position_if_emb_step_at size_chop)

subsection \<open>Chop and Substitutions\<close>

(* TODO: move *)
lemma Suc_num_args: "is_App t \<Longrightarrow> Suc (num_args (fun t)) = num_args t" 
  by (metis args.simps(2) length_append_singleton tm.collapse(2))

(* TODO: move *)
lemma fun_subst: "is_App s \<Longrightarrow> subst \<rho> (fun s) = fun (subst \<rho> s)"
  by (metis subst.simps(2) tm.collapse(2) tm.sel(4))

(* TODO: move *)
lemma args_subst_Hd:
  assumes "is_Hd (subst \<rho> (Hd (head s)))"
  shows  "args (subst \<rho> s) = map (subst \<rho>) (args s)"
  using assms 
  by (metis append_Nil args_Nil_iff_is_Hd args_apps subst_apps tm_exhaust_apps_sel)

lemma chop_subst_emb0:
  assumes "is_App s"
  assumes "chop (subst \<rho> s) \<noteq> subst \<rho> (chop s)"
  shows "emb_step_at (replicate (num_args (fun s)) Left) Right (chop (subst \<rho> s)) = subst \<rho> (chop s)"
proof -
  have "is_App (subst \<rho> s)"
    by (metis assms(1) subst.simps(2) tm.collapse(2) tm.disc(2))
  have 1:"subst \<rho> (chop s) = emb_step_at (replicate (num_args (fun s)) dir.Left) dir.Right (subst \<rho>  s)"
    using chop_emb_step_at[OF assms(1)] using emb_step_at_subst chop_position_of[OF \<open>is_App s\<close>] 
    by (metis)
  have "num_args (fun s) \<le> num_args (fun (subst \<rho> s))" 
    using fun_subst[OF \<open>is_App s\<close>] 
    by (metis args_subst leI length_append length_map not_add_less2)
  then have "num_args (fun s) < num_args (fun (subst \<rho> s))" 
    using assms(2) "1" \<open>is_App (subst \<rho> s)\<close> chop_emb_step_at le_imp_less_or_eq 
    by fastforce
  then have "num_args s \<le> num_args (fun (subst \<rho> s))" 
    using Suc_num_args[OF \<open>is_App s\<close>] by linarith
  then have  "replicate (num_args (fun s)) dir.Left @
        [opp dir.Right] @ replicate (num_args (fun (subst \<rho> s)) - num_args s) dir.Left =
        replicate (num_args (fun (subst \<rho> s))) dir.Left" 
    unfolding append.simps opp_simps replicate_Suc[symmetric] replicate_add[symmetric]
    using Suc_num_args[OF \<open>is_App s\<close>]
    by (metis add_Suc_shift ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  then show ?thesis unfolding 1
    unfolding  chop_emb_step_at[OF \<open>is_App (subst \<rho> s)\<close>]
    by (metis merge_emb_step_at)
qed

lemma chop_subst_emb:
  assumes "is_App s"
  shows "chop (subst \<rho> s) \<unrhd>\<^sub>e\<^sub>m\<^sub>b subst \<rho> (chop s)"
  using chop_subst_emb0
  by (metis assms emb.refl emb_step_equiv emb_step_is_emb)

lemma chop_subst_Hd:
  assumes "is_App s"
  assumes "is_Hd (subst \<rho> (Hd (head s)))"
  shows "chop (subst \<rho> s) = subst \<rho> (chop s)" 
proof -
  have "is_App (subst \<rho> s)"
    by (metis assms(1) subst.simps(2) tm.collapse(2) tm.disc(2))
  have "num_args (fun s) = num_args (fun (subst \<rho> s))" unfolding fun_subst[OF \<open>is_App s\<close>,symmetric]
    using args_subst_Hd using assms(2) by auto
  then show ?thesis
    unfolding chop_emb_step_at[OF assms(1)] chop_emb_step_at[OF \<open>is_App (subst \<rho> s)\<close>]
    using emb_step_at_subst[OF chop_position_of[OF \<open>is_App s\<close>]]
    by simp
qed

lemma chop_subst_Sym:
  assumes "is_App s"
  assumes "is_Sym (head s)"
  shows "chop (subst \<rho> s) = subst \<rho> (chop s)" 
  by (metis assms(1) assms(2) chop_subst_Hd ground_imp_subst_iden hd.collapse(2) hd.simps(18) tm.disc(1) tm.simps(17))

end