(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Executable Translation from Mojmir to Rabin Automata\<close>

theory Mojmir_Rabin_Impl
  imports Main "../Mojmir_Rabin"
begin

\<comment> \<open>Ranking functions are stored as lists sorted ascending by the state rank\<close>

fun init :: "'a \<Rightarrow> 'a list"
where
  "init q\<^sub>0 = [q\<^sub>0]"

fun nxt :: "'b set \<Rightarrow> ('a, 'b) DTS \<Rightarrow> 'a \<Rightarrow> ('a list, 'b) DTS"
where
  "nxt \<Sigma> \<delta> q\<^sub>0 = (\<lambda>qs \<nu>. remdups_fwd ((filter (\<lambda>q. \<not>semi_mojmir_def.sink \<Sigma> \<delta> q\<^sub>0 q) (map (\<lambda>q. \<delta> q \<nu>) qs)) @ [q\<^sub>0]))" 

\<comment> \<open>Recompute the rank from the list\<close>

fun rk :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option"
where
  "rk qs q = (let i = index qs q in if i \<noteq> length qs then Some i else None)"

\<comment> \<open>Instead of computing the whole sets for fail, merge, and succeed, we define filters (a.k.a. characteristic functions)\<close> 

fun fail_filt :: "'b set \<Rightarrow> ('a, 'b) DTS \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a list, 'b) transition \<Rightarrow> bool"
where
  "fail_filt \<Sigma> \<delta> q\<^sub>0 F (r, \<nu>, _) = (\<exists>q \<in> set r. let q' = \<delta> q \<nu> in (\<not>F q') \<and> semi_mojmir_def.sink \<Sigma> \<delta> q\<^sub>0 q')"

fun merge_filt :: "('a, 'b) DTS \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('a list, 'b) transition \<Rightarrow> bool"
where
  "merge_filt \<delta> q\<^sub>0 F i (r, \<nu>, _) = (\<exists>q \<in> set r. let q' = \<delta> q \<nu> in the (rk r q) < i \<and> \<not>F q' \<and> ((\<exists>q'' \<in> set r. q'' \<noteq> q \<and> \<delta> q'' \<nu> = q') \<or> q' = q\<^sub>0))"

fun succeed_filt :: "('a, 'b) DTS \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('a list, 'b) transition \<Rightarrow> bool"
where
  "succeed_filt \<delta> q\<^sub>0 F i (r, \<nu>, _) = (\<exists>q \<in> set r. let q' = \<delta> q \<nu> in rk r q = Some i  \<and> (\<not>F q \<or> q = q\<^sub>0) \<and> F q')" 

subsubsection \<open>nxt Properties\<close>

lemma nxt_run_distinct:
  "distinct (run (nxt \<Sigma> \<Delta> q\<^sub>0) (init q\<^sub>0) w n)"
  by (cases n; simp del: remdups_fwd.simps; metis (no_types) remdups_fwd_distinct)

lemma nxt_run_reverse_step:
  fixes \<Sigma> \<delta> q\<^sub>0 w
  defines "r \<equiv> run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w" 
  assumes "q \<in> set (r (Suc n))"
  assumes "q \<noteq> q\<^sub>0"
  shows "\<exists>q' \<in> set (r n). \<delta> q' (w n) = q"
  using assms(2-3) unfolding r_def run.simps nxt.simps remdups_fwd_set by auto

lemma nxt_run_sink_free:
  "q \<in> set (run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w n) \<Longrightarrow> \<not>semi_mojmir_def.sink \<Sigma> \<delta> q\<^sub>0 q"
  by (induction n) (simp_all add: semi_mojmir_def.sink_def del: remdups_fwd.simps, blast)

subsubsection \<open>rk Properties\<close>

lemma rk_bounded:
  "rk xs x = Some i \<Longrightarrow> i < length xs"
  by (simp add: Let_def) (metis index_conv_size_if_notin index_less_size_conv option.distinct(1) option.inject)

lemma rk_facts:
  "x \<in> set xs \<longleftrightarrow> rk xs x \<noteq> None"
  "x \<in> set xs \<longleftrightarrow> (\<exists>i. rk xs x = Some i)"
  using rk_bounded by (simp add: index_size_conv)+

lemma rk_split:
  "y \<notin> set xs \<Longrightarrow> rk (xs @ y # zs) y = Some (length xs)"
  by (induction xs) auto

lemma rk_split_card:
  "y \<notin> set xs \<Longrightarrow> distinct xs \<Longrightarrow> rk (xs @ y # zs) y = Some (card (set xs))"
  using rk_split by (metis length_remdups_card_conv remdups_id_iff_distinct)

lemma rk_split_card_takeWhile:
  assumes "x \<in> set xs"
  assumes "distinct xs"
  shows "rk xs x = Some (card (set (takeWhile (\<lambda>y. y \<noteq> x) xs)))"
proof -
  obtain ys zs where "xs = ys @ x # zs" and "x \<notin> set ys"
    using assms by (blast dest: split_list_first)
  moreover
  hence "distinct ys" and "ys = takeWhile (\<lambda>y. y \<noteq> x) xs"
    using takeWhile_foo assms by (simp, fast)
  ultimately
  show ?thesis
    using rk_split_card by metis
qed

lemma take_rk:
  assumes "distinct xs"
  shows "set (take i xs) = {q. \<exists>j < i. rk xs q = Some j}" 
  (is "?rhs = ?lhs")
  using assms
proof (induction i arbitrary: xs)
  case (Suc i)
    thus ?case
    proof (induction xs)
      case (Cons x xs)
        have "set (take (Suc i) (x # xs)) = {x} \<union> set (take i xs)"
          by simp
        also
        have "\<dots> = {x} \<union> {q. \<exists>j < i. rk xs q = Some j}"
          using Cons by simp
        finally
        show ?case 
          by force
    qed simp
qed simp

lemma drop_rk:
  assumes "distinct xs"
  shows "set (drop i xs) = {q. \<exists>j \<ge> i. rk xs q = Some j}" 
proof -
  have "set xs = {q. \<exists>j. rk xs q = Some j}" (is "_ = ?U")
    using rk_facts(2)[of _ xs] by blast
  moreover
  have "?U = {q. \<exists>j \<ge> i. rk xs q = Some j} \<union> {q. \<exists>j < i. rk xs q = Some j}"
    and "{} = {q. \<exists>j \<ge> i. rk xs q = Some j} \<inter> {q. \<exists>j < i. rk xs q = Some j}"
    by auto
  moreover
  have "set xs = set (drop i xs) \<union> set (take i xs)"
    and "{} = set (drop i xs) \<inter> set (take i xs)" 
    by (metis assms append_take_drop_id inf_sup_aci(1,5) distinct_append set_append)+
  ultimately
  show ?thesis
    using take_rk[OF assms] by blast
qed

subsubsection \<open>Relation to (Semi) Mojmir Automata\<close>

lemma (in semi_mojmir) nxt_run_configuration:
  defines "r \<equiv> run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w"
  shows "q \<in> set (r n) \<longleftrightarrow> \<not>sink q \<and> configuration q n \<noteq> {}"
proof (induction n arbitrary: q)
  case (Suc n)
    thus ?case
    proof (cases "q \<noteq> q\<^sub>0")
      case True
        {
          assume "q \<in> set (r (Suc n))"
          hence "\<not> sink q"
            using r_def nxt_run_sink_free by metis
          moreover
          obtain q' where "q' \<in> set (r n)" and "\<delta> q' (w n) = q"
            using \<open>q \<in> set (r (Suc n))\<close> nxt_run_reverse_step[OF _ \<open>q \<noteq> q\<^sub>0\<close>] unfolding r_def by blast
          hence "configuration q (Suc n) \<noteq> {}" and "\<not> sink q"
            unfolding configuration_step_eq[OF True] Suc using True \<open>\<not> sink q\<close> by auto
        }
        moreover
        {
          assume "\<not>sink q" and "configuration q (Suc n) \<noteq> {}"
          then obtain q' where "configuration q' n \<noteq> {}" and "\<delta> q' (w n) = q"
            unfolding configuration_step_eq[OF True] by blast
          moreover 
          hence "\<not>sink q'"
            using \<open>\<not>sink q\<close> sink_rev_step assms by blast
          ultimately
          have "q' \<in> set (r n)"
            unfolding Suc by blast
          hence "q \<in> set (r (Suc n))"
            using \<open>\<delta> q' (w n) = q\<close> \<open>\<not>sink q\<close> 
            unfolding r_def run.simps set_filter comp_def remdups_fwd_set set_map set_append image_def
            unfolding r_def[symmetric] by auto
        }
        ultimately
        show ?thesis
          by blast
    qed (insert assms, auto simp add: r_def sink_def)
qed (insert assms, auto simp add: r_def sink_def)

lemma (in semi_mojmir) nxt_run_sorted:
  defines "r \<equiv> run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w" 
  shows "sorted (map (\<lambda>q. the (oldest_token q n)) (r n))"
proof (induction n)
  case (Suc n)
    let ?f_n = "\<lambda>q. the (oldest_token q n)"
    let ?f_Suc_n = "\<lambda>q. the (oldest_token q (Suc n))"
    let ?step = "filter (\<lambda>q. \<not>sink q) ((map (\<lambda>q. \<delta> q (w n)) (r n)) @ [q\<^sub>0])"

    have "\<And>q p qs ps. remdups_fwd ?step = qs @ q # p # ps \<Longrightarrow> ?f_Suc_n q \<le> ?f_Suc_n p"
    proof -
      fix q qs p ps
      assume "remdups_fwd ?step = qs @ q # p # ps"
      then obtain zs zs' zs'' where step_def: "?step = zs @ q # zs' @ p # zs''"
        and "remdups_fwd zs = qs" 
        and "remdups_fwd_acc (set qs \<union> {q}) zs' = []" 
        and "remdups_fwd_acc (set qs \<union> {q, p}) zs'' = ps" 
        and "q \<notin> set zs" 
        and "p \<notin> set zs \<union> {q}"
        unfolding remdups_fwd.simps remdups_fwd_split_exact_iff remdups_fwd_split_exact_iff[where ?ys = "[]", simplified] insert_commute
        by auto
      hence  "p \<notin> set zs \<union> set zs' \<union> {q}"
        and "q \<noteq> p" unfolding remdups_fwd_acc_empty[symmetric] by auto
      hence  "p \<notin> set zs \<union> set zs' \<union> set [q]"
        by simp
      hence "{q, p} \<subseteq> set ?step"
        using step_def by simp
      hence "\<not> sink q" and "\<not> sink p"
        unfolding set_map set_filter by blast+

      show "?f_Suc_n q \<le> ?f_Suc_n p"
      proof (cases "zs'' = []")
        case True
          hence "p = q\<^sub>0" and q_def: "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) (r n)) = zs @ [q] @ zs'"
            using step_def unfolding sink_def by simp+
          hence "q\<^sub>0 \<notin> set (filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) (r n)))"
            using \<open>p \<notin> set zs \<union> set zs' \<union> {q}\<close>  unfolding \<open>p = q\<^sub>0\<close> sink_def by simp
          hence "q\<^sub>0 \<notin> (\<lambda>q. \<delta> q (w n)) ` {q'. configuration q' n \<noteq> {}}"
            using nxt_run_configuration bounded_w unfolding set_map set_filter r_def sink_def init.simps by blast
          hence "configuration p (Suc n) = {Suc n}" using assms
            unfolding \<open>p = q\<^sub>0\<close> using configuration_step_eq_q\<^sub>0 by blast
          hence "?f_Suc_n p = Suc n"
           using assms  by force
          moreover
          have "q \<in> (\<lambda>q. \<delta> q (w n)) ` set (r n)"
            using  \<open>p \<notin> set zs \<union> set zs' \<union> {q}\<close> image_set unfolding filter_map_split_iff[of "(\<lambda>q. \<not> sink q)" "\<lambda>q. \<delta> q (w n)"] 
            by (metis (no_types, lifting) Un_insert_right \<open>p = q\<^sub>0\<close>  \<open>{q, p} \<subseteq> set [q\<leftarrow>map (\<lambda>q. \<delta> q (w n)) (r n) @ [q\<^sub>0] . \<not> sink q]\<close> append_Nil2 insert_iff insert_subset list.simps(15) mem_Collect_eq set_append set_filter)  
          hence "q \<in> (\<lambda>q. \<delta> q (w n)) ` {q'. configuration q' n \<noteq> {}}"
            using nxt_run_configuration unfolding r_def by auto
          hence "configuration q (Suc n) \<noteq> {}"
            using configuration_step assms by blast
          hence "?f_Suc_n q \<le> Suc n"
            using assms oldest_token_bounded[of q "Suc n"] 
            by (simp del: configuration.simps) 
          ultimately
          show "?f_Suc_n q \<le> ?f_Suc_n p"
            by presburger
      next
        case False
          hence X: "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) (r n)) = zs @ [q] @ zs' @ [p] @ butlast zs''"
            using step_def unfolding map_append filter_append sink_def apply simp 
            by (metis (no_types, lifting) butlast.simps(2) list.distinct(1) butlast_append append_is_Nil_conv butlast_snoc) (* Slow *)
          obtain qs' sq' sp' ps' ps'' where r_def': "r n = qs' @ sq' @ ps' @ sp' @ ps''"
            and 1: "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) qs') = zs"
            and 2: "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) sq') = [q]"
            and 3: "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) ps') = zs'"
            and "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) sp') = [p]"
            and "filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) ps'') = butlast zs''"
            using X  unfolding filter_map_split_iff by (blast)
          hence 21: "Set.filter (\<lambda>q. \<not>sink q) ((\<lambda>q. \<delta> q (w n)) ` set sq') = {q}"
            and 41: "Set.filter (\<lambda>q. \<not>sink q) ((\<lambda>q. \<delta> q (w n)) ` set sp') = {p}"
            by (metis filter_set image_set list.set(1) list.simps(15))+
          from 21 obtain q' where "q' \<in> set sq'" and "\<not> sink q'" and "q = \<delta> q' (w n)"
            using sink_rev_step(2)[OF \<open>\<not> sink q\<close>, of _ n] by fastforce
          from 41 obtain p' where "p' \<in> set sp'" and "\<not> sink p'" and "p = \<delta> p' (w n)"
            using sink_rev_step(2)[OF \<open>\<not> sink p\<close>, of _ n] by fastforce
          from Suc have "?f_n q' \<le> ?f_n p'"
            unfolding r_def' map_append sorted_append set_append set_map using \<open>q' \<in> set sq'\<close> \<open>p' \<in> set sp'\<close> by auto
          moreover
          {
            have "oldest_token q' n \<noteq> None"     
              using nxt_run_configuration option.distinct(1) r_def r_def'  \<open>q' \<in> set sq'\<close> \<open>p' \<in> set sp'\<close> set_append
              unfolding init.simps oldest_token.simps by (metis UnCI)
            moreover
            hence "oldest_token q (Suc n) \<noteq> None"
              using \<open>q = \<delta> q' (w n)\<close> by (metis oldest_token.simps option.distinct(1) configuration_step_non_empty)
            ultimately 
            obtain x y where x_def: "oldest_token q' n = Some x"  
              and y_def: "oldest_token q (Suc n) = Some y" 
              by blast
            moreover
            hence "x \<le> n" and "token_run x n = q'"
              using oldest_token_bounded push_down_oldest_token_token_run assms by blast+
            moreover
            hence "token_run x (Suc n) = q"
              using \<open>q = \<delta> q' (w n)\<close> by (rule token_run_step)
            ultimately
            have "x \<ge> y" 
              using oldest_token_monotonic_Suc assms by blast
            moreover
            {
              have "\<And>q''. q = \<delta> q'' (w n) \<Longrightarrow> q'' \<notin> set qs'"
                 using \<open>q \<notin> set zs\<close> unfolding \<open>filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) qs') = zs\<close>[symmetric] set_map set_filter apply simp using \<open>\<not> sink q\<close> by blast 
              moreover
              {
                obtain us vs where 1: "map (\<lambda>q. \<delta> q (w n)) sq' = us @ [q] @ vs" and "\<forall>u\<in>set us. sink u" and "[] = [q\<leftarrow>vs . \<not> sink q]"
                   using \<open>filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) sq') = [q]\<close>   unfolding filter_eq_Cons_iff by auto
                moreover
                hence "\<And>q''. q'' \<in> (set us) \<union> (set vs) \<Longrightarrow> sink q''"
                  by (metis UnE filter_empty_conv) 
                hence "q \<notin> (set us) \<union> (set vs)"
                  using \<open>\<not> sink q\<close> by blast
                ultimately
                have "\<And>q''. q'' \<in> (set sq' - {q'}) \<Longrightarrow> \<delta> q'' (w n) \<noteq> q"
                  using 1 \<open>q = \<delta> q' (w n)\<close> \<open>q' \<in> set sq'\<close> by (fastforce dest: split_list elim: map_splitE)
              }
              ultimately
              have "\<And>q''. q = \<delta> q'' (w n) \<Longrightarrow> configuration q'' n \<noteq> {} \<Longrightarrow> q'' \<in> set (ps' @ sp' @ ps'') \<or> q'' = q'"
                using nxt_run_configuration[of _ n] \<open>\<not> sink q\<close> sink_rev_step 
                unfolding r_def'[unfolded r_def] set_append 
                by blast
              moreover
              have "\<And>q''. q'' \<in> set (ps' @ sp' @ ps'') \<Longrightarrow> x \<le> ?f_n q''"
                using x_def using Suc unfolding r_def' map_append sorted_append set_append set_map  using \<open>q' \<in> set sq'\<close> \<open>p' \<in> set sp'\<close>
                apply (simp del: oldest_token.simps) by fastforce 
              moreover
              have "\<And>q''. q'' = q' \<Longrightarrow> x \<le> ?f_n q''"
                using x_def by simp
              moreover
              have "\<And>q'' x. x \<in> configuration q'' n \<Longrightarrow> the (oldest_token q'' n) \<le> x"
               using assms by auto
              ultimately
              have "\<And>z. z \<in> \<Union>{configuration q' n |q'. q = \<delta> q' (w n)} \<Longrightarrow> x \<le> z"
                by fastforce
            }
            hence "\<And>z. z \<in> configuration q (Suc n) \<Longrightarrow> x \<le> z"
              unfolding configuration_step_eq_unified using \<open>x \<le> n\<close> 
              by (cases "q = q\<^sub>0"; auto)
            hence "x \<le> y"
              using y_def Min.boundedI configuration_finite using push_down_oldest_token_configuration by presburger 
            ultimately
            have "?f_n q' = ?f_Suc_n q"
              using x_def y_def by fastforce
          }
          moreover
          {
            have "oldest_token p' n \<noteq> None"     
              using nxt_run_configuration oldest_token.simps option.distinct(1) r_def r_def'  \<open>q' \<in> set sq'\<close> \<open>p' \<in> set sp'\<close> set_append
              unfolding init.simps by (metis UnCI)
            moreover
            hence "oldest_token p (Suc n) \<noteq> None"
              using \<open>p = \<delta> p' (w n)\<close> by (metis oldest_token.simps option.distinct(1) configuration_step_non_empty)
            ultimately 
            obtain x y where x_def: "oldest_token p' n = Some x"  
              and y_def: "oldest_token p (Suc n) = Some y" 
              by blast
            moreover
            hence "x \<le> n" and "token_run x n = p'"
              using oldest_token_bounded push_down_oldest_token_token_run assms by blast+
            moreover
            hence "token_run x (Suc n) = p"
              using \<open>p = \<delta> p' (w n)\<close> assms token_run_step by simp
            ultimately
            have "x \<ge> y" 
              using oldest_token_monotonic_Suc assms by blast
            moreover
            {     
              have "\<And>q''. p = \<delta> q'' (w n) \<Longrightarrow> q'' \<notin> set qs' \<union> set sq' \<union> set ps'"
                 using \<open>p \<notin> set zs \<union> set zs' \<union> set [q]\<close> \<open>\<not> sink p\<close> unfolding 1[symmetric] 2[symmetric] 3[symmetric] set_map set_filter by blast 
              moreover
              {
                obtain us vs where 1: "map (\<lambda>q. \<delta> q (w n)) sp' = us @ [p] @ vs" and "\<forall>u\<in>set us. sink u" and "[] = [q\<leftarrow>vs . \<not> sink q]"
                   using \<open>filter (\<lambda>q. \<not>sink q) (map (\<lambda>q. \<delta> q (w n)) sp') = [p]\<close> unfolding filter_eq_Cons_iff by auto
                moreover
                hence "\<And>q''. q'' \<in> (set us) \<union> (set vs) \<Longrightarrow> sink q''"
                  by (metis UnE filter_empty_conv) 
                hence "p \<notin> (set us) \<union> (set vs)"
                  using \<open>\<not> sink p\<close> by blast
                ultimately
                have "\<And>q''. q'' \<in> (set sp' - {p'}) \<Longrightarrow> \<delta> q'' (w n) \<noteq> p"
                  using 1 \<open>p = \<delta> p' (w n)\<close> \<open>p' \<in> set sp'\<close> by (fastforce dest: split_list elim: map_splitE)
              }
              ultimately
              have "\<And>q''. p = \<delta> q'' (w n) \<Longrightarrow> configuration q'' n \<noteq> {} \<Longrightarrow> q'' \<in> set ps'' \<or> q'' = p'"
                using nxt_run_configuration[of _ n]  \<open>\<not> sink p\<close>[THEN sink_rev_step(2)] unfolding r_def'[unfolded r_def] set_append 
                by blast 
              moreover
              have "\<And>q''. q'' \<in> set ps'' \<Longrightarrow> x \<le> ?f_n q''"
                using x_def using Suc unfolding r_def' map_append sorted_append set_append set_map  using \<open>q' \<in> set sq'\<close> \<open>p' \<in> set sp'\<close>
                apply (simp del: oldest_token.simps)  by fastforce 
              moreover
              have "\<And>q''. q'' = p' \<Longrightarrow> x \<le> ?f_n q''"
                using x_def by simp
              moreover
              have "\<And>q'' x. x \<in> configuration q'' n \<Longrightarrow> the (oldest_token q'' n) \<le> x"
                using assms  by auto
              ultimately
              have "\<And>z. z \<in> \<Union>{configuration p' n |p'. p = \<delta> p' (w n)} \<Longrightarrow> x \<le> z"
                by fastforce
            }
            hence "\<And>z. z \<in> configuration p (Suc n) \<Longrightarrow> x \<le> z"
              unfolding configuration_step_eq_unified using \<open>x \<le> n\<close> 
              by (cases "p = q\<^sub>0"; auto)
            hence "x \<le> y"
              using y_def Min.boundedI configuration_finite using push_down_oldest_token_configuration  by presburger 
            ultimately
            have "?f_n p' = ?f_Suc_n p"
              using x_def y_def by fastforce
          }
          ultimately
          show ?thesis
            by presburger
       qed
    qed 
    hence "\<And>x y xs ys. map ?f_Suc_n (remdups_fwd ?step) = xs @ [x, y] @ ys \<Longrightarrow> x \<le> y"
      by (auto elim: map_splitE simp del: remdups_fwd.simps)
    hence "sorted (map ?f_Suc_n (remdups_fwd (?step)))"
      using sorted_pre by metis
    thus ?case
      by (simp add: r_def sink_def)
qed (simp add: r_def)

lemma (in semi_mojmir) nxt_run_senior_states: 
  defines "r \<equiv> run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w" 
  assumes "\<not>sink q"
  assumes "configuration q n \<noteq> {}" 
  shows "senior_states q n = set (takeWhile (\<lambda>q'. q' \<noteq> q) (r n))" 
  (is "?lhs = ?rhs")
proof (rule set_eqI, rule)
  fix q' assume q'_def: "q' \<in> senior_states q n"
  then obtain x y where "oldest_token q' n = Some y" and "oldest_token q n = Some x" and "y < x"
    using senior_states.simps using assms by blast
  hence "the (oldest_token q' n) < the (oldest_token q n)"
    by fastforce  
  moreover
  hence "\<not>sink q'" and "configuration q' n \<noteq> {}"
    using q'_def option.distinct(1) \<open>oldest_token q' n = Some y\<close> 
     oldest_token.simps using assms by (force, metis)
  hence "q' \<in> set (r n)" and "q \<in> set (r n)"
    using nxt_run_configuration assms by blast+
  moreover
  have "distinct (r n)"
    unfolding r_def using nxt_run_distinct by fast
  ultimately
  obtain r' r'' r''' where r_alt_def: "r n = r' @ q' # r'' @ q # r'''"
    using sorted_list[OF _ _ nxt_run_sorted] assms unfolding r_def by presburger
  hence "q' \<in> set (r' @ q' # r'')"
    by simp
  thus "q' \<in> set (takeWhile (\<lambda>q'. q' \<noteq> q) (r n))"
    using \<open>distinct (r n)\<close> takeWhile_distinct[of "r' @ q' # r''" q r''' q'] unfolding r_alt_def by simp
next
  fix q' assume q'_def: "q' \<in> set (takeWhile (\<lambda>q'. q' \<noteq> q) (r n))"
  moreover
  hence "q' \<in> set (r n)"
    by (blast dest: set_takeWhileD)+
  hence 5: "\<not> sink q'"
    using nxt_run_configuration assms by simp
  have "q \<in> set (r n)"
    using nxt_run_configuration assms by blast+
  ultimately
  obtain  r' r'' r''' where r_alt_def: "r n = r' @ q' # r'' @ q # r'''"
    using takeWhile_split by metis
  have "distinct (r n)"
     unfolding r_def using nxt_run_distinct by fast
  have 1: "the (oldest_token q' n) \<le> the (oldest_token q n)"
    using nxt_run_sorted[of n, unfolded r_def[symmetric]] assms
    unfolding r_alt_def map_append list.map
    unfolding sorted_append by (simp del: oldest_token.simps)
  have "q \<noteq> q'"
    using \<open>distinct (r n)\<close> r_alt_def by auto 
  moreover
  have 2: "oldest_token q' n \<noteq> None" and 3: "oldest_token q n \<noteq> None"
    using assms \<open>q' \<in> set (r n)\<close> nxt_run_configuration by force+
  ultimately
  have 4: "the (oldest_token q' n) \<noteq> the (oldest_token q n)"
    by (metis oldest_token_equal option.collapse)
  
  show "q' \<in> senior_states q n"
    using 1 2 3 4 5 assms by fastforce
qed

lemma (in semi_mojmir) nxt_run_state_rank:
  "state_rank q n = rk (run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w n) q"
  by (cases "\<not>sink q \<and> configuration q n \<noteq> {}", unfold state_rank.simps) 
     (metis nxt_run_senior_states rk_split_card_takeWhile nxt_run_distinct nxt_run_configuration, metis nxt_run_configuration rk_facts(1))

lemma (in semi_mojmir) nxt_foldl_state_rank:
  "state_rank q n = rk (foldl (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) (map w [0..<n])) q"
  unfolding nxt_run_state_rank run_foldl ..

lemma (in semi_mojmir) nxt_run_step_run:
  "run step initial w = rk o (run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w)"
  using nxt_run_state_rank state_rank_step_foldl[unfolded run_foldl[symmetric]] unfolding comp_def by presburger  

definition (in semi_mojmir_def) Q\<^sub>E
where
  "Q\<^sub>E \<equiv> reach \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0)"

lemma (in semi_mojmir) finite_Q:
  "finite Q\<^sub>E"
proof -
  {
    fix i fix w :: "nat \<Rightarrow> 'a" 
    assume "range w \<subseteq> \<Sigma>"
    then interpret \<HH>: semi_mojmir \<Sigma> \<delta> q\<^sub>0 w
      using finite_reach finite_\<Sigma> by (unfold_locales, blast)  
    have "set (run (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w i) \<subseteq> {\<HH>.token_run j i | j. j \<le> i}" (is "?S1 \<subseteq> _")
      using \<HH>.nxt_run_configuration by auto
    also 
    have "\<dots> \<subseteq> reach \<Sigma> \<delta> q\<^sub>0" (is "_ \<subseteq> ?S2")
      unfolding reach_def token_run.simps using \<open>range w \<subseteq> \<Sigma>\<close> by fastforce
    finally
    have "?S1 \<subseteq> ?S2" .
  }
  hence "set ` Q\<^sub>E \<subseteq> Pow (reach \<Sigma> \<delta> q\<^sub>0)"
    unfolding Q\<^sub>E_def reach_def by blast
  hence "finite (set ` Q\<^sub>E)"
    using finite_reach by (blast dest: finite_subset)
  moreover
  have "\<And>xs. xs \<in> Q\<^sub>E \<Longrightarrow> distinct xs"
    unfolding Q\<^sub>E_def reach_def using nxt_run_distinct by fastforce
  ultimately
  show "finite Q\<^sub>E"
    using set_list by auto
qed

lemma (in mojmir_to_rabin_def) filt_equiv:
  "(rk x, \<nu>, y) \<in> fail\<^sub>R \<longleftrightarrow> fail_filt \<Sigma> \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) (x, \<nu>, y')"
  "(rk x, \<nu>, y) \<in> succeed\<^sub>R i \<longleftrightarrow> succeed_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i (x, \<nu>, y')"
  "(rk x, \<nu>, y) \<in> merge\<^sub>R i \<longleftrightarrow> merge_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i (x, \<nu>, y')"
  by (simp add: fail\<^sub>R_def succeed\<^sub>R_def merge\<^sub>R_def del: rk.simps; metis (no_types, lifting) option.sel rk_facts(2))+

lemma fail_filt_eq: 
  "fail_filt \<Sigma> \<delta> q\<^sub>0 P (x, \<nu>, y) \<longleftrightarrow> (rk x, \<nu>, y') \<in> mojmir_to_rabin_def.fail\<^sub>R \<Sigma> \<delta> q\<^sub>0 {x. P x}"
  unfolding mojmir_to_rabin_def.filt_equiv(1)[where y' = y] by simp

lemma merge_filt_eq: 
  "merge_filt \<delta> q\<^sub>0 P i (x, \<nu>, y) \<longleftrightarrow> (rk x, \<nu>, y') \<in> mojmir_to_rabin_def.merge\<^sub>R \<delta> q\<^sub>0 {x. P x} i"
  unfolding mojmir_to_rabin_def.filt_equiv(3)[where y' = y] by simp

lemma succeed_filt_eq: 
  "succeed_filt \<delta> q\<^sub>0 P i (x, \<nu>, y) \<longleftrightarrow> (rk x, \<nu>, y') \<in> mojmir_to_rabin_def.succeed\<^sub>R \<delta> q\<^sub>0 {x. P x} i"
  unfolding mojmir_to_rabin_def.filt_equiv(2)[where y' = y] by simp

theorem (in mojmir_to_rabin) rabin_accept_iff_rabin_list_accept_rank:
  "accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> i) w \<longleftrightarrow> accepting_pair\<^sub>R (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) ({t. fail_filt \<Sigma> \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) t} \<union> {t. merge_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i t}, {t. succeed_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i t}) w"
  (is "accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (?F, ?I) w \<longleftrightarrow> accepting_pair\<^sub>R (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) (?F', ?I') w")
proof -
  have "finite (reach\<^sub>t \<Sigma> \<delta>\<^sub>\<R> q\<^sub>\<R>)"
    using wellformed_\<R> finite_\<Sigma> finite_reach\<^sub>t by fast
  moreover
  have "finite (reach\<^sub>t \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0))"
    using finite_Q finite_\<Sigma> finite_reach\<^sub>t by (auto simp add: Q\<^sub>E_def) 
  moreover
  have "run\<^sub>t step initial w = (\<lambda>(x, \<nu>, y). (rk x, \<nu>, rk y)) o (run\<^sub>t (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0) w)"
    using nxt_run_step_run by auto
  moreover
  note bounded_w filt_equiv 
  ultimately
  show ?thesis
    by (intro accepting_pair\<^sub>R_abstract) auto
qed

subsection \<open>Compute Rabin Automata List Representation\<close>

fun mojmir_to_rabin_exec
where
  "mojmir_to_rabin_exec \<Sigma> \<delta> q\<^sub>0 F = (
    let 
      q\<^sub>0' = init q\<^sub>0;
      \<delta>' = \<delta>\<^sub>L \<Sigma> (nxt (set \<Sigma>) \<delta> q\<^sub>0) q\<^sub>0';
      max_rank = card (Set.filter (Not o semi_mojmir_def.sink (set \<Sigma>) \<delta> q\<^sub>0) (Q\<^sub>L \<Sigma> \<delta> q\<^sub>0));
      fail = Set.filter (fail_filt (set \<Sigma>) \<delta> q\<^sub>0 F) \<delta>';
      merge = (\<lambda>i. Set.filter (merge_filt \<delta> q\<^sub>0 F i) \<delta>');
      succeed = (\<lambda>i. Set.filter (succeed_filt \<delta> q\<^sub>0 F i) \<delta>')
    in
      (\<delta>', q\<^sub>0', (\<lambda>i. (fail \<union> (merge i), succeed i)) ` {0..<max_rank}))"

subsection \<open>Code Generation\<close>

\<comment> \<open>Setup missing equations for code generator\<close>
declare semi_mojmir_def.sink_def [code]

\<comment> \<open>Drop computation of length by different code equation\<close>
fun index_option ::  "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat option"
where
  "index_option n [] y = None"
| "index_option n (x # xs) y = (if x = y then Some n else index_option (Suc n) xs y)"

declare rk.simps [code del]

lemma rk_eq_index_option [code]:
  "rk xs x = index_option 0 xs x"
proof -
  have A: "\<And>n. x \<in> set xs \<Longrightarrow> index xs x + n = the (index_option n xs x)"
   and B: "\<And>n. x \<notin> set xs \<longleftrightarrow> index_option n xs x = None"
   by (induction xs) (auto, metis add_Suc_right)
  thus ?thesis
  proof (cases "x \<in> set xs")
    case True
      moreover
      hence "index xs x = the (index_option 0 xs x)"
        using A[OF True, of 0] by simp
      ultimately
      show ?thesis
        unfolding rk.simps by (metis (mono_tags, lifting) B True index_less_size_conv less_irrefl option.collapse)
  qed simp
qed

\<comment> \<open>Check Code Export\<close> 
export_code init nxt fail_filt succeed_filt merge_filt mojmir_to_rabin_exec checking

lemma (in mojmir) max_rank_card:
  assumes "\<Sigma> = set \<Sigma>'"
  shows "max_rank = card (Set.filter (Not o semi_mojmir_def.sink (set \<Sigma>') \<delta> q\<^sub>0) (Q\<^sub>L \<Sigma>' \<delta> q\<^sub>0))"
  unfolding max_rank_def Q\<^sub>L_reach[OF finite_reach[unfolded \<open>\<Sigma> = set \<Sigma>'\<close>]] 
  by (simp add: Set.filter_def set_diff_eq assms(1))
 
theorem (in mojmir_to_rabin) exec_correct:
  assumes "\<Sigma> = set \<Sigma>'"
  shows "accept \<longleftrightarrow> accept\<^sub>R_LTS (mojmir_to_rabin_exec \<Sigma>' \<delta> q\<^sub>0 (\<lambda>x. x \<in> F)) w" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
 have F1: "finite (reach \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0))"
    using finite_Q by (simp add: Q\<^sub>E_def)
  hence F2: "finite (reach\<^sub>t \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0))"
    using finite_\<Sigma> by (rule finite_reach\<^sub>t)

  let ?\<delta>' = "\<delta>\<^sub>L \<Sigma>' (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0)"
  have \<delta>'_Def: "?\<delta>' = reach\<^sub>t \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0)"
    using \<delta>\<^sub>L_reach[OF F2[unfolded assms]] unfolding  assms  by simp
 
  have 3: "snd (snd ((mojmir_to_rabin_exec \<Sigma>' \<delta> q\<^sub>0 (\<lambda>x. x \<in> F)))) 
    = {(({t. fail_filt \<Sigma> \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) t} \<union> {t. merge_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i t}) \<inter> reach\<^sub>t \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0), 
        {t. succeed_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i t}  \<inter> reach\<^sub>t \<Sigma> (nxt \<Sigma> \<delta> q\<^sub>0) (init q\<^sub>0)) | i. i < max_rank}"
    unfolding assms mojmir_to_rabin_exec.simps Let_def fst_conv snd_conv set_map \<delta>'_Def[unfolded assms] max_rank_card[OF assms, symmetric] 
    unfolding assms[symmetric] Set.filter_def by auto
  
  have "?lhs \<longleftrightarrow> accept\<^sub>R (\<delta>\<^sub>\<R>, q\<^sub>\<R>, {(Acc\<^sub>\<R> i) | i. i < max_rank}) w"
    using mojmir_accept_iff_rabin_accept by blast

  moreover

  have "\<dots> \<longleftrightarrow> accept\<^sub>R (nxt \<Sigma> \<delta> q\<^sub>0, init q\<^sub>0, {({t. fail_filt \<Sigma> \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) t} \<union> {t. merge_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i t}, {t. succeed_filt \<delta> q\<^sub>0 (\<lambda>x. x \<in> F) i t}) | i. i < max_rank}) w"
    unfolding accept\<^sub>R_def fst_conv snd_conv using rabin_accept_iff_rabin_list_accept_rank by blast 
 
  moreover 

  have "\<dots> \<longleftrightarrow> ?rhs"
    apply (subst accept\<^sub>R_restrict[OF bounded_w])
    unfolding 3[unfolded mojmir_to_rabin_exec.simps Let_def snd_conv, symmetric] assms[symmetric] mojmir_to_rabin_exec.simps Let_def unfolding assms \<delta>'_Def[unfolded assms]
    unfolding accept\<^sub>R_LTS[OF bounded_w[unfolded assms], symmetric, unfolded assms] by simp
  
  ultimately
 
  show ?thesis
    by blast
qed

end
