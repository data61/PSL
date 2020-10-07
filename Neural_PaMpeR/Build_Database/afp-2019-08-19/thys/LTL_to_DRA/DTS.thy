(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Deterministic Transition Systems\<close>

theory DTS
  imports Main "HOL-Library.Omega_Words_Fun" "Auxiliary/Mapping2" KBPs.DFS
begin

\<comment> \<open>DTS are realised by functions\<close>

type_synonym ('a, 'b) DTS = "'a \<Rightarrow> 'b \<Rightarrow> 'a"
type_synonym ('a, 'b) transition = "('a \<times> 'b \<times> 'a)"

subsection \<open>Infinite Runs\<close>

fun run :: "('q,'a) DTS \<Rightarrow> 'q \<Rightarrow> 'a word \<Rightarrow> 'q word"
where
  "run \<delta> q\<^sub>0 w 0 = q\<^sub>0"
| "run \<delta> q\<^sub>0 w (Suc i) = \<delta> (run \<delta> q\<^sub>0 w i) (w i)"

fun run\<^sub>t :: "('q,'a) DTS \<Rightarrow> 'q \<Rightarrow> 'a word \<Rightarrow> ('q * 'a * 'q) word"
where
  "run\<^sub>t \<delta> q\<^sub>0 w i = (run \<delta> q\<^sub>0 w i, w i, run \<delta> q\<^sub>0 w (Suc i))"

lemma run_foldl:
  "run \<Delta> q\<^sub>0 w i = foldl \<Delta> q\<^sub>0 (map w [0..<i])"
  by (induction i; simp)

lemma run\<^sub>t_foldl:
  "run\<^sub>t \<Delta> q\<^sub>0 w i = (foldl \<Delta> q\<^sub>0 (map w [0..<i]), w i, foldl \<Delta> q\<^sub>0 (map w [0..<Suc i]))"
  unfolding run\<^sub>t.simps run_foldl ..

subsection \<open>Reachable States and Transitions\<close>

definition reach :: "'a set \<Rightarrow> ('b, 'a) DTS \<Rightarrow> 'b \<Rightarrow> 'b set"
where
  "reach \<Sigma> \<delta> q\<^sub>0 = {run \<delta> q\<^sub>0 w n | w n. range w \<subseteq> \<Sigma>}"

definition reach\<^sub>t :: "'a set \<Rightarrow> ('b, 'a) DTS \<Rightarrow> 'b \<Rightarrow> ('b, 'a) transition set"
where
  "reach\<^sub>t \<Sigma> \<delta> q\<^sub>0 = {run\<^sub>t \<delta> q\<^sub>0 w n | w n. range w \<subseteq> \<Sigma>}"

lemma reach_foldl_def:
  assumes "\<Sigma> \<noteq> {}"
  shows "reach \<Sigma> \<delta> q\<^sub>0 = {foldl \<delta> q\<^sub>0 w | w. set w \<subseteq> \<Sigma>}"
proof -
  {
    fix w assume "set w \<subseteq> \<Sigma>"
    moreover
    obtain a where "a \<in> \<Sigma>"
      using \<open>\<Sigma> \<noteq> {}\<close> by blast
    ultimately
    have "foldl \<delta> q\<^sub>0 w = foldl \<delta> q\<^sub>0 (prefix (length w) (w \<frown> (iter [a])))" 
      and "range (w \<frown> (iter [a])) \<subseteq> \<Sigma>"
      by (unfold prefix_conc_length, auto simp add: iter_def conc_def) 
    hence "\<exists>w' n. foldl \<delta> q\<^sub>0 w = run \<delta> q\<^sub>0 w' n \<and> range w' \<subseteq> \<Sigma>"
      unfolding run_foldl subsequence_def by blast
  }
  thus ?thesis
    by (fastforce simp add: reach_def run_foldl)
qed

lemma reach\<^sub>t_foldl_def:
  "reach\<^sub>t \<Sigma> \<delta> q\<^sub>0 = {(foldl \<delta> q\<^sub>0 w, \<nu>, foldl \<delta> q\<^sub>0 (w@[\<nu>])) | w \<nu>. set w \<subseteq> \<Sigma> \<and> \<nu> \<in> \<Sigma>}" (is "?lhs = ?rhs")
proof (cases "\<Sigma> \<noteq> {}")
  case True
    show ?thesis
    proof
      {
        fix w \<nu> assume "set w \<subseteq> \<Sigma>" "\<nu> \<in> \<Sigma>"
        moreover
        obtain a where "a \<in> \<Sigma>"
          using \<open>\<Sigma> \<noteq> {}\<close> by blast
        moreover
        have "w = map (\<lambda>n. if n < length w then w ! n else if n - length w = 0 then [\<nu>] ! (n - length w) else a) [0..<length w]"
          by (simp add: nth_equalityI)  
        ultimately
        have "foldl \<delta> q\<^sub>0 w = foldl \<delta> q\<^sub>0 (prefix (length w) ((w @ [\<nu>]) \<frown> (iter [a])))" 
          and"foldl \<delta> q\<^sub>0 (w @ [\<nu>]) = foldl \<delta> q\<^sub>0 (prefix (length (w @ [\<nu>])) ((w @ [\<nu>]) \<frown> (iter [a])))" 
          and "range ((w @ [\<nu>]) \<frown> (iter [a])) \<subseteq> \<Sigma>"
          by (simp_all only: prefix_conc_length conc_conc[symmetric] iter_def)
             (auto simp add: subsequence_def conc_def upt_Suc_append[OF le0])
        moreover
        have "((w @ [\<nu>]) \<frown> (iter [a])) (length w) = \<nu>"
          by (simp add: conc_def)
        ultimately
        have "\<exists>w' n. (foldl \<delta> q\<^sub>0 w, \<nu>, foldl \<delta> q\<^sub>0 (w @ [\<nu>])) = run\<^sub>t \<delta> q\<^sub>0 w' n \<and> range w' \<subseteq> \<Sigma>"
          by (metis run\<^sub>t_foldl length_append_singleton subsequence_def)
      }
      thus "?lhs \<supseteq> ?rhs"
        unfolding reach\<^sub>t_def run\<^sub>t.simps by blast
    qed (unfold reach\<^sub>t_def run\<^sub>t_foldl, fastforce simp add: upt_Suc_append)
qed (simp add: reach\<^sub>t_def)

lemma reach_card_0:
  assumes "\<Sigma> \<noteq> {}"
  shows "infinite (reach \<Sigma> \<delta> q\<^sub>0) \<longleftrightarrow> card (reach \<Sigma> \<delta> q\<^sub>0) = 0"
proof -
  have "{run \<delta> q\<^sub>0 w n | w n. range w \<subseteq> \<Sigma>} \<noteq> {}"
    using assms by fast
  thus ?thesis
    unfolding reach_def card_eq_0_iff by auto
qed

lemma reach\<^sub>t_card_0:
  assumes "\<Sigma> \<noteq> {}"
  shows "infinite (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) \<longleftrightarrow> card (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) = 0"
proof -
  have "{run\<^sub>t \<delta> q\<^sub>0 w n | w n. range w \<subseteq> \<Sigma>} \<noteq> {}"
    using assms by fast
  thus ?thesis
    unfolding reach\<^sub>t_def card_eq_0_iff by blast
qed

subsubsection \<open>Relation to runs\<close>

lemma run_subseteq_reach:
  assumes "range w \<subseteq> \<Sigma>"
  shows "range (run \<delta> q\<^sub>0 w) \<subseteq> reach \<Sigma> \<delta> q\<^sub>0" 
    and "range (run\<^sub>t \<delta> q\<^sub>0 w) \<subseteq> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0"
  using assms unfolding reach_def reach\<^sub>t_def by blast+

lemma limit_subseteq_reach:
  assumes "range w \<subseteq> \<Sigma>"
  shows "limit (run \<delta> q\<^sub>0 w) \<subseteq> reach \<Sigma> \<delta> q\<^sub>0"
    and "limit (run\<^sub>t \<delta> q\<^sub>0 w) \<subseteq> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0"
  using run_subseteq_reach[OF assms] limit_in_range by fast+

lemma run\<^sub>t_finite:
  assumes "finite (reach \<Sigma> \<delta> q\<^sub>0)"
  assumes "finite \<Sigma>"
  assumes "range w \<subseteq> \<Sigma>"
  defines "r \<equiv> run\<^sub>t \<delta> q\<^sub>0 w"
  shows "finite (range r)"
proof -
  let ?S = "(reach \<Sigma> \<delta> q\<^sub>0) \<times> \<Sigma> \<times> (reach \<Sigma> \<delta> q\<^sub>0)"
  have "\<And>i. w i \<in> \<Sigma>" and "\<And>i. set (map w [0..<i]) \<subseteq> \<Sigma>" and "\<Sigma> \<noteq> {}"
    using \<open>range w \<subseteq> \<Sigma>\<close> by auto 
  hence "\<And>n. r n \<in> ?S"
    unfolding run\<^sub>t.simps run_foldl reach_foldl_def[OF \<open>\<Sigma> \<noteq> {}\<close>] r_def by blast
  hence "range r \<subseteq> ?S" and "finite ?S"
    using assms by blast+
  thus "finite (range r)"
    by (blast dest: finite_subset)
qed

subsubsection \<open>Compute reach Using DFS\<close>

definition Q\<^sub>L :: "'a list \<Rightarrow> ('b, 'a) DTS \<Rightarrow> 'b \<Rightarrow> 'b set"
where
  "Q\<^sub>L \<Sigma> \<delta> q\<^sub>0 = (if \<Sigma> \<noteq> [] then gen_dfs (\<lambda>q. map (\<delta> q) \<Sigma>) Set.insert (\<in>) {} [q\<^sub>0] else {})"

definition list_dfs :: "(('a, 'b) transition \<Rightarrow> ('a, 'b) transition list) \<Rightarrow> ('a, 'b) transition list => ('a, 'b) transition list => ('a, 'b) transition list"
where
  "list_dfs succ S start \<equiv> gen_dfs succ List.insert (\<lambda>x xs. x \<in> set xs) S start"

definition \<delta>\<^sub>L :: "'a list \<Rightarrow> ('b, 'a) DTS \<Rightarrow> 'b \<Rightarrow> ('b, 'a) transition set"
where
  "\<delta>\<^sub>L \<Sigma> \<delta> q\<^sub>0 = set ( 
    let 
      start = map (\<lambda>\<nu>. (q\<^sub>0, \<nu>, \<delta> q\<^sub>0 \<nu>)) \<Sigma>; 
      succ = \<lambda>(_, _, q). (map (\<lambda>\<nu>. (q, \<nu>, \<delta> q \<nu>)) \<Sigma>)
    in 
      (list_dfs succ [] start))"

lemma Q\<^sub>L_reach:
  assumes "finite (reach (set \<Sigma>) \<delta> q\<^sub>0)"
  shows "Q\<^sub>L \<Sigma> \<delta> q\<^sub>0 = reach (set \<Sigma>) \<delta> q\<^sub>0"
proof (cases "\<Sigma> \<noteq> []")
  case True
    hence reach_redef: "reach (set \<Sigma>) \<delta> q\<^sub>0 = {foldl \<delta> q\<^sub>0 w | w. set w \<subseteq> set \<Sigma>}"
      using reach_foldl_def[of "set \<Sigma>"] unfolding set_empty[of \<Sigma>, symmetric] by force
  
    {
      fix x w y
      assume "set w \<subseteq> set \<Sigma>" "x = foldl \<delta> q\<^sub>0 w" "y \<in> set (map (\<delta> x) \<Sigma>)"
      moreover
      then obtain \<nu> where "y = \<delta> x \<nu>" and "\<nu> \<in> set \<Sigma>"
        by auto
      ultimately
      have "y = foldl \<delta> q\<^sub>0 (w@[\<nu>])" and "set (w@[\<nu>]) \<subseteq> set \<Sigma>"
        by simp+
      hence "\<exists>w'. set w' \<subseteq> set \<Sigma> \<and> y = foldl  \<delta> q\<^sub>0 w'"
        by blast
    }
    note extend_run = this
    
    interpret DFS "\<lambda>q. map (\<delta> q) \<Sigma>" "\<lambda>q. q \<in> reach (set \<Sigma>) \<delta> q\<^sub>0" "\<lambda>S. S \<subseteq> reach (set \<Sigma>) \<delta> q\<^sub>0" Set.insert "(\<in>)" "{}" id
      apply (unfold_locales; auto simp add: member_rec reach_redef list_all_iff elim: extend_run)
      apply (metis extend_run image_eqI set_map)
      apply (metis assms[unfolded reach_redef])
      done

    have Nil1: "set [] \<subseteq> set \<Sigma>" and Nil2: "q\<^sub>0 = foldl \<delta> q\<^sub>0 []"
      by simp+
    have list_all_init: "list_all (\<lambda>q. q \<in> reach (set \<Sigma>) \<delta> q\<^sub>0) [q\<^sub>0]"
      unfolding list_all_iff list.set reach_redef using Nil1 Nil2 by blast

    have "reach (set \<Sigma>) \<delta> q\<^sub>0 \<subseteq> reachable {q\<^sub>0}"
    proof rule
      fix x 
      assume "x \<in> reach (set \<Sigma>) \<delta> q\<^sub>0"
      then obtain w where x_def: "x = foldl \<delta> q\<^sub>0 w" and "set w \<subseteq> set \<Sigma>"
        unfolding reach_redef by blast
      hence "foldl \<delta> q\<^sub>0 w \<in> reachable {q\<^sub>0}"
      proof (induction w arbitrary: x rule: rev_induct)
        case (snoc \<nu> w)
          hence "foldl \<delta> q\<^sub>0 w \<in> reachable {q\<^sub>0}" and "\<delta> (foldl \<delta> q\<^sub>0 w) \<nu> \<in> set (map (\<delta> (foldl \<delta> q\<^sub>0 w)) \<Sigma>)"
            by simp+
          thus ?case
            by (simp add: rtrancl.rtrancl_into_rtrancl reachable_def)
      qed (simp add: reachable_def)
      thus "x \<in> reachable {q\<^sub>0}"
        by (simp add: x_def)
    qed
    moreover
    have "reachable {q\<^sub>0} \<subseteq> reach (set \<Sigma>) \<delta> q\<^sub>0"
    proof rule
      fix x 
      assume "x \<in> reachable {q\<^sub>0}"
      hence "(q\<^sub>0, x) \<in> {(x, y). y \<in> set (map (\<delta> x) \<Sigma>)}\<^sup>*"
        unfolding reachable_def by blast
      thus "x \<in> reach (set \<Sigma>) \<delta> q\<^sub>0"
        apply (induction)
        apply (insert reach_redef Nil1 Nil2; blast)
        apply (metis r_into_rtrancl succsr_def succsr_isNode) 
        done
    qed
    ultimately
    have reachable_redef: "reachable {q\<^sub>0} = reach (set \<Sigma>) \<delta> q\<^sub>0"
      by blast

    moreover

    have "reachable {q\<^sub>0} \<subseteq> Q\<^sub>L \<Sigma> \<delta> q\<^sub>0"
      using reachable_imp_dfs[OF _ list_all_init] unfolding list.set reachable_redef
      unfolding  reach_redef Q\<^sub>L_def using \<open>\<Sigma> \<noteq> []\<close> by auto

    moreover

    have "Q\<^sub>L \<Sigma> \<delta> q\<^sub>0 \<subseteq> reach (set \<Sigma>) \<delta> q\<^sub>0"
      using dfs_invariant[of "{}", OF _ list_all_init] 
      by (auto simp add: reach_redef Q\<^sub>L_def)

    ultimately
    show ?thesis
      using \<open>\<Sigma> \<noteq> []\<close> dfs_invariant[of "{}", OF _ list_all_init] by simp+
qed (simp add: reach_def Q\<^sub>L_def)

lemma \<delta>\<^sub>L_reach: 
  assumes "finite (reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0)"
  shows "\<delta>\<^sub>L \<Sigma> \<delta> q\<^sub>0 = reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0"
proof -
  {
    fix x w y
    assume "set w \<subseteq> set \<Sigma>" "x = foldl \<delta> q\<^sub>0 w" "y \<in> set (map (\<delta> x) \<Sigma>)"
    moreover
    then obtain \<nu> where "y = \<delta> x \<nu>" and "\<nu> \<in> set \<Sigma>"
      by auto
    ultimately
    have "y = foldl \<delta> q\<^sub>0 (w@[\<nu>])" and "set (w@[\<nu>]) \<subseteq> set \<Sigma>"
      by simp+
    hence "\<exists>w'. set w' \<subseteq> set \<Sigma> \<and> y = foldl  \<delta> q\<^sub>0 w'"
      by blast
  }
  note extend_run = this

  let ?succs = "\<lambda>(_, _, q). (map (\<lambda>\<nu>. (q, \<nu>, \<delta> q \<nu>)) \<Sigma>)"

  interpret DFS "\<lambda>(_, _, q). (map (\<lambda>\<nu>. (q, \<nu>, \<delta> q \<nu>)) \<Sigma>)" "\<lambda>t. t \<in> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0" "\<lambda>S. set S \<subseteq> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0" List.insert "\<lambda>x xs. x \<in> set xs" "[]" id
    apply (unfold_locales; auto simp add: member_rec reach\<^sub>t_foldl_def list_all_iff elim: extend_run)
    apply (metis extend_run image_eqI set_map)
    using  assms unfolding reach\<^sub>t_foldl_def by simp

  have Nil1: "set [] \<subseteq> set \<Sigma>" and Nil2: "q\<^sub>0 = foldl \<delta> q\<^sub>0 []"
    by simp+
  have list_all_init: "list_all (\<lambda>q. q \<in> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0) (map (\<lambda>\<nu>. (q\<^sub>0, \<nu>, \<delta> q\<^sub>0 \<nu>)) \<Sigma>)"
    unfolding list_all_iff reach\<^sub>t_foldl_def set_map image_def using Nil2 by fastforce
  
  let ?q\<^sub>0 = "set (map (\<lambda>\<nu>. (q\<^sub>0, \<nu>, \<delta> q\<^sub>0 \<nu>)) \<Sigma>)"

  {
    fix q \<nu> q'  
    assume "(q, \<nu>, q') \<in> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0"
    then obtain w where q_def: "q = foldl \<delta> q\<^sub>0 w" and q'_def: "q' = foldl \<delta> q\<^sub>0 (w@[\<nu>])" 
      and "set w \<subseteq> set \<Sigma>" and "\<nu> \<in> set \<Sigma>"
      unfolding reach\<^sub>t_foldl_def by blast
    hence "(foldl \<delta> q\<^sub>0 w, \<nu>, foldl \<delta> q\<^sub>0 (w@[\<nu>])) \<in> reachable ?q\<^sub>0"
    proof (induction w arbitrary: q q' \<nu> rule: rev_induct)
      case (snoc \<nu>' w)
        hence "(foldl \<delta> q\<^sub>0 w, \<nu>', foldl \<delta> q\<^sub>0 (w@[\<nu>'])) \<in> reachable ?q\<^sub>0" (is "(?q, \<nu>', ?q') \<in> _")
          and "\<And>q. \<delta> q \<nu> \<in> set (map (\<delta> q) \<Sigma>)"
          and "\<nu> \<in> set \<Sigma>"
          by simp+
        then obtain x\<^sub>0 where 1: "(x\<^sub>0, (?q, \<nu>', ?q')) \<in> {(x, y). y \<in> set (?succs x)}\<^sup>*" and 2: "x\<^sub>0 \<in> ?q\<^sub>0"
          unfolding reachable_def by auto
        moreover
        have 3: "((?q, \<nu>', ?q'), (?q', \<nu>, \<delta> ?q' \<nu>)) \<in> {(x, y). y \<in> set (?succs x)}"
          using snoc \<open>\<And>q. \<delta> q \<nu> \<in> set (map (\<delta> q) \<Sigma>)\<close> by simp
        ultimately
        show ?case
          using rtrancl.rtrancl_into_rtrancl[OF 1 3] 2 unfolding reachable_def foldl_append foldl.simps  by auto
    qed (auto simp add: reachable_def)
    hence "(q, \<nu>, q') \<in> reachable ?q\<^sub>0"
      by (simp add: q_def q'_def)
  }
  hence "reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0 \<subseteq> reachable ?q\<^sub>0"
    by auto
  moreover
  {
    fix y  
    assume "y \<in> reachable ?q\<^sub>0" 
    then obtain x where "(x, y) \<in> {(x, y). y \<in> set (case x of (_, _, q) \<Rightarrow> map (\<lambda>\<nu>. (q, \<nu>, \<delta> q \<nu>)) \<Sigma>)}\<^sup>*"
      and "x \<in> ?q\<^sub>0"
      unfolding reachable_def by auto
    hence "y \<in> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0"
    proof induction
      case base
        have "\<forall>p ps. list_all p ps = (\<forall>pa. pa \<in> set ps \<longrightarrow> p pa)"
          by (meson list_all_iff)
        hence "x \<in> {(foldl \<delta> (foldl \<delta> q\<^sub>0 []) bs, b, foldl \<delta> (foldl \<delta> q\<^sub>0 []) (bs @ [b])) | bs b. set bs \<subseteq> set \<Sigma> \<and> b \<in> set \<Sigma>}"
          using base by (metis (no_types) Nil2 list_all_init reach\<^sub>t_foldl_def)
        thus ?case
          unfolding reach\<^sub>t_foldl_def by auto
    next
      case (step x' y')
        thus ?case using succsr_def succsr_isNode by blast
    qed
  }
  hence "reachable ?q\<^sub>0 \<subseteq> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0"
     by blast
  ultimately
  have reachable_redef: "reachable ?q\<^sub>0 = reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0"
    by blast

  moreover

  have "reachable ?q\<^sub>0 \<subseteq> (\<delta>\<^sub>L \<Sigma> \<delta> q\<^sub>0)"
    using reachable_imp_dfs[OF _ list_all_init] unfolding \<delta>\<^sub>L_def reachable_redef list_dfs_def
    by (simp; blast)

  moreover

  have "\<delta>\<^sub>L \<Sigma> \<delta> q\<^sub>0 \<subseteq> reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0"
    using dfs_invariant[of "[]", OF _ list_all_init] 
    by (auto simp add: reach\<^sub>t_foldl_def \<delta>\<^sub>L_def list_dfs_def)

  ultimately
  show ?thesis 
    by simp
qed

lemma reach_reach\<^sub>t_fst:
  "reach \<Sigma> \<delta> q\<^sub>0 = fst ` reach\<^sub>t \<Sigma> \<delta> q\<^sub>0"
  unfolding reach\<^sub>t_def reach_def image_def by fastforce

lemma finite_reach:
  "finite (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) \<Longrightarrow> finite (reach \<Sigma> \<delta> q\<^sub>0)"
  by (simp add: reach_reach\<^sub>t_fst)

lemma finite_reach\<^sub>t:
  assumes "finite (reach \<Sigma> \<delta> q\<^sub>0)"
  assumes "finite \<Sigma>"
  shows "finite (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0)"
proof -
  have "reach\<^sub>t \<Sigma> \<delta> q\<^sub>0 \<subseteq> reach \<Sigma> \<delta> q\<^sub>0 \<times> \<Sigma> \<times> reach \<Sigma> \<delta> q\<^sub>0"
    unfolding reach\<^sub>t_def reach_def run\<^sub>t.simps by blast
  thus ?thesis
    using assms finite_subset by blast
qed

lemma Q\<^sub>L_eq_\<delta>\<^sub>L:
  assumes "finite (reach\<^sub>t (set \<Sigma>) \<delta> q\<^sub>0)"
  shows "Q\<^sub>L \<Sigma> \<delta> q\<^sub>0 = fst ` (\<delta>\<^sub>L \<Sigma> \<delta> q\<^sub>0)"
  unfolding set_map \<delta>\<^sub>L_reach[OF assms] Q\<^sub>L_reach[OF finite_reach[OF assms]] reach_reach\<^sub>t_fst ..

subsection \<open>Product of DTS\<close> 

fun simple_product :: "('a, 'c) DTS \<Rightarrow> ('b, 'c) DTS \<Rightarrow> ('a \<times> 'b, 'c) DTS" ("_ \<times> _")
where
  "\<delta>\<^sub>1 \<times> \<delta>\<^sub>2 = (\<lambda>(q\<^sub>1, q\<^sub>2) \<nu>. (\<delta>\<^sub>1 q\<^sub>1 \<nu>, \<delta>\<^sub>2 q\<^sub>2 \<nu>))"  

lemma simple_product_run:
  fixes \<delta>\<^sub>1 \<delta>\<^sub>2 w q\<^sub>1 q\<^sub>2
  defines "\<rho> \<equiv> run (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) w"
  defines "\<rho>\<^sub>1 \<equiv> run \<delta>\<^sub>1 q\<^sub>1 w"
  defines "\<rho>\<^sub>2 \<equiv> run \<delta>\<^sub>2 q\<^sub>2 w"
  shows "\<rho> i = (\<rho>\<^sub>1 i, \<rho>\<^sub>2 i)"
  by (induction i) (insert assms, auto)

theorem finite_reach_simple_product:
  assumes "finite (reach \<Sigma> \<delta>\<^sub>1 q\<^sub>1)"
  assumes "finite (reach \<Sigma> \<delta>\<^sub>2 q\<^sub>2)"
  shows "finite (reach \<Sigma> (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2))"
proof -
  have "reach \<Sigma> (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) \<subseteq> reach \<Sigma> \<delta>\<^sub>1 q\<^sub>1 \<times> reach \<Sigma> \<delta>\<^sub>2 q\<^sub>2"
    unfolding reach_def simple_product_run by blast
  thus ?thesis
    using assms finite_subset by blast
qed

subsection \<open>(Generalised) Product of DTS\<close>

fun product :: "('a \<Rightarrow> ('b, 'c) DTS) \<Rightarrow> ('a \<rightharpoonup> 'b, 'c) DTS" ("\<Delta>\<^sub>\<times>")
where
  "\<Delta>\<^sub>\<times> \<delta>\<^sub>m = (\<lambda>q \<nu>. (\<lambda>x. case q x of None \<Rightarrow> None | Some y \<Rightarrow> Some (\<delta>\<^sub>m x y \<nu>)))"  

lemma product_run_None:
  fixes \<iota>\<^sub>m \<delta>\<^sub>m w
  defines "\<rho> \<equiv> run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w"
  assumes "\<iota>\<^sub>m k = None"
  shows "\<rho> i k = None"
  by (induction i) (insert assms, auto)

lemma product_run_Some:
  fixes \<iota>\<^sub>m \<delta>\<^sub>m w q\<^sub>0 k
  defines "\<rho> \<equiv> run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w"
  defines "\<rho>' \<equiv> run (\<delta>\<^sub>m k) q\<^sub>0 w"
  assumes "\<iota>\<^sub>m k = Some q\<^sub>0"
  shows "\<rho> i k = Some (\<rho>' i)"
  by (induction i) (insert assms, auto)

theorem finite_reach_product:
  assumes "finite (dom \<iota>\<^sub>m)"
  assumes "\<And>x. x \<in> dom \<iota>\<^sub>m \<Longrightarrow> finite (reach \<Sigma> (\<delta>\<^sub>m x) (the (\<iota>\<^sub>m x)))"
  shows "finite (reach \<Sigma> (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m)"
  using assms(1,2) 
proof (induction "dom \<iota>\<^sub>m" arbitrary: \<iota>\<^sub>m) 
  case empty
    hence "\<iota>\<^sub>m = Map.empty"
      by auto
    hence "\<And>w i. run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w i = (\<lambda>x. None)"
      using product_run_None by fast
    thus ?case
      unfolding reach_def by simp
next 
  case (insert k K)
    define f where "f = (\<lambda>(q :: 'b, m :: 'a \<rightharpoonup> 'b). m(k := Some q))"
    define Reach where "Reach = (reach \<Sigma> (\<delta>\<^sub>m k) (the (\<iota>\<^sub>m k))) \<times> ((reach \<Sigma> (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) (\<iota>\<^sub>m(k := None))))"

    have "(reach \<Sigma> (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m) \<subseteq> f ` Reach"
    proof
      fix x
      assume "x \<in> reach \<Sigma> (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m"
      then obtain w n where x_def: "x = run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w n" and "range w \<subseteq> \<Sigma>"
        unfolding reach_def by blast
      {
        fix k'
        have "k' \<notin> dom \<iota>\<^sub>m \<Longrightarrow> x k' = run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) (\<iota>\<^sub>m(k := None)) w n k'"
          unfolding x_def dom_def using product_run_None[of _ _ \<delta>\<^sub>m] by simp
        moreover
        have "k' \<in> dom \<iota>\<^sub>m - {k} \<Longrightarrow> x k' = run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) (\<iota>\<^sub>m(k := None)) w n k'"
          unfolding x_def dom_def using product_run_Some[of _ _ _ \<delta>\<^sub>m] by auto
        ultimately
        have "k' \<noteq> k \<Longrightarrow> x k' = run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) (\<iota>\<^sub>m(k := None)) w n k'"
          by blast
      }
      hence "x(k := None) = run (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) (\<iota>\<^sub>m(k := None)) w n"
        using product_run_None[of _ _ \<delta>\<^sub>m] by auto
      moreover
      have "x k = Some (run (\<delta>\<^sub>m k) (the (\<iota>\<^sub>m k)) w n)"
        unfolding x_def using product_run_Some[of \<iota>\<^sub>m k _ \<delta>\<^sub>m] insert.hyps(4) by force 
      ultimately
      have "(the (x k), x(k := None)) \<in> Reach"
        unfolding Reach_def reach_def using \<open>range w \<subseteq> \<Sigma>\<close> by auto
      moreover
      have "x = f (the (x k), x(k := None))"
        unfolding f_def using \<open>x k = Some (run (\<delta>\<^sub>m k) (the (\<iota>\<^sub>m k)) w n)\<close> by auto 
      ultimately
      show "x \<in> f ` Reach"
         by simp
    qed
    moreover
    have "finite (reach \<Sigma> (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) (\<iota>\<^sub>m (k := None)))"
      using insert insert(3)[of "\<iota>\<^sub>m (k:=None)"] by auto 
    hence "finite Reach"
      using insert Reach_def by blast
    hence "finite (f ` Reach)"
      .. 
    ultimately
    show ?case
      by (rule finite_subset)
qed

subsection \<open>Simple Product Construction Helper Functions and Lemmas\<close>

fun embed_transition_fst :: "('a, 'c) transition \<Rightarrow> ('a \<times> 'b, 'c) transition set"
where
  "embed_transition_fst (q, \<nu>, q') = {((q, x), \<nu>, (q', y)) | x y. True}"

fun embed_transition_snd :: "('b, 'c) transition \<Rightarrow> ('a \<times> 'b, 'c) transition set"
where
  "embed_transition_snd (q, \<nu>, q') = {((x, q), \<nu>, (y, q')) | x y. True}"

lemma embed_transition_snd_unfold:
  "embed_transition_snd t = {((x, fst t), fst (snd t), (y, snd (snd t))) | x y. True}"
  unfolding embed_transition_snd.simps[symmetric] by simp

fun project_transition_fst :: "('a \<times> 'b, 'c) transition \<Rightarrow> ('a, 'c) transition" 
where
  "project_transition_fst (x, \<nu>, y) = (fst x, \<nu>, fst y)"

fun project_transition_snd :: "('a \<times> 'b, 'c) transition \<Rightarrow> ('b, 'c) transition" 
where
  "project_transition_snd (x, \<nu>, y) = (snd x, \<nu>, snd y)"

lemma
  fixes \<delta>\<^sub>1 \<delta>\<^sub>2 w q\<^sub>1 q\<^sub>2
  defines "\<rho> \<equiv> run\<^sub>t (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) w"
  defines "\<rho>\<^sub>1 \<equiv> run\<^sub>t \<delta>\<^sub>1 q\<^sub>1 w"
  defines "\<rho>\<^sub>2 \<equiv> run\<^sub>t \<delta>\<^sub>2 q\<^sub>2 w"
  shows product_run_project_fst: "project_transition_fst (\<rho> i) = \<rho>\<^sub>1 i" 
    and product_run_project_snd: "project_transition_snd (\<rho> i) = \<rho>\<^sub>2 i"
    and product_run_embed_fst: "\<rho> i \<in> embed_transition_fst (\<rho>\<^sub>1 i)"
    and product_run_embed_snd: "\<rho> i \<in> embed_transition_snd (\<rho>\<^sub>2 i)"
  unfolding assms run\<^sub>t.simps simple_product_run by simp_all

lemma 
  fixes \<delta>\<^sub>1 \<delta>\<^sub>2 w q\<^sub>1 q\<^sub>2
  defines "\<rho> \<equiv> run\<^sub>t (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) w"
  defines "\<rho>\<^sub>1 \<equiv> run\<^sub>t \<delta>\<^sub>1 q\<^sub>1 w"
  defines "\<rho>\<^sub>2 \<equiv> run\<^sub>t \<delta>\<^sub>2 q\<^sub>2 w"
  assumes "finite (range \<rho>)"
  shows product_run_finite_fst: "finite (range \<rho>\<^sub>1)"
    and product_run_finite_snd: "finite (range \<rho>\<^sub>2)"
proof -
  have "\<And>k. project_transition_fst (\<rho> k) = \<rho>\<^sub>1 k"
    and "\<And>k. project_transition_snd (\<rho> k) = \<rho>\<^sub>2 k"
    unfolding assms product_run_project_fst product_run_project_snd by simp+
  hence "project_transition_fst ` range \<rho> = range \<rho>\<^sub>1"
    and "project_transition_snd ` range \<rho> = range \<rho>\<^sub>2"
    using range_composition[symmetric, of project_transition_fst \<rho>]
    using range_composition[symmetric, of project_transition_snd \<rho>] by presburger+
  thus "finite (range \<rho>\<^sub>1)" and "finite (range \<rho>\<^sub>2)"
    using assms finite_imageI by metis+
qed

lemma 
  fixes \<delta>\<^sub>1 \<delta>\<^sub>2 w q\<^sub>1 q\<^sub>2
  defines "\<rho> \<equiv> run\<^sub>t (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) w"
  defines "\<rho>\<^sub>1 \<equiv> run\<^sub>t \<delta>\<^sub>1 q\<^sub>1 w"
  assumes "finite (range \<rho>)"
  shows product_run_project_limit_fst: "project_transition_fst ` limit \<rho> = limit \<rho>\<^sub>1"
    and product_run_embed_limit_fst: "limit \<rho> \<subseteq> \<Union> (embed_transition_fst ` (limit \<rho>\<^sub>1))"
proof -
  have "finite (range \<rho>\<^sub>1)"
    using assms product_run_finite_fst by metis

  then obtain i where "limit \<rho> = range (suffix i \<rho>)" and "limit \<rho>\<^sub>1 = range (suffix i \<rho>\<^sub>1)"
    using common_range_limit assms by metis
  moreover
  have "\<And>k. project_transition_fst (suffix i \<rho> k) = (suffix i \<rho>\<^sub>1 k)"
    by (simp only: assms run\<^sub>t.simps) (metis \<rho>\<^sub>1_def product_run_project_fst suffix_nth) 
  hence "project_transition_fst ` range (suffix i \<rho>) = (range (suffix i \<rho>\<^sub>1))"
    using range_composition[symmetric, of "project_transition_fst" "suffix i \<rho>"] by presburger
  moreover
  have "\<And>k. (suffix i \<rho> k) \<in> embed_transition_fst (suffix i \<rho>\<^sub>1 k)"
    using assms product_run_embed_fst by simp
  ultimately
  show "project_transition_fst ` limit \<rho> = limit \<rho>\<^sub>1" 
    and "limit \<rho> \<subseteq> \<Union> (embed_transition_fst ` (limit \<rho>\<^sub>1))"
    by auto
qed 

lemma 
  fixes \<delta>\<^sub>1 \<delta>\<^sub>2 w q\<^sub>1 q\<^sub>2
  defines "\<rho> \<equiv> run\<^sub>t (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) w"
  defines "\<rho>\<^sub>2 \<equiv> run\<^sub>t \<delta>\<^sub>2 q\<^sub>2 w"
  assumes "finite (range \<rho>)"
  shows product_run_project_limit_snd: "project_transition_snd ` limit \<rho> = limit \<rho>\<^sub>2"
    and product_run_embed_limit_snd: "limit \<rho> \<subseteq> \<Union> (embed_transition_snd ` (limit \<rho>\<^sub>2))"
proof -
  have "finite (range \<rho>\<^sub>2)"
    using assms product_run_finite_snd by metis

  then obtain i where "limit \<rho> = range (suffix i \<rho>)" and "limit \<rho>\<^sub>2 = range (suffix i \<rho>\<^sub>2)"
    using common_range_limit assms by metis
  moreover
  have "\<And>k. project_transition_snd (suffix i \<rho> k) = (suffix i \<rho>\<^sub>2 k)"
    by (simp only: assms run\<^sub>t.simps) (metis \<rho>\<^sub>2_def product_run_project_snd suffix_nth) 
  hence "project_transition_snd ` range ((suffix i \<rho>)) = (range (suffix i \<rho>\<^sub>2))"
    using range_composition[symmetric, of "project_transition_snd" "(suffix i \<rho>)"] by presburger
  moreover
  have "\<And>k. (suffix i \<rho> k) \<in> embed_transition_snd (suffix i \<rho>\<^sub>2 k)"
    using assms product_run_embed_snd by simp
  ultimately
  show "project_transition_snd ` limit \<rho> = limit \<rho>\<^sub>2" 
    and "limit \<rho> \<subseteq> \<Union> (embed_transition_snd ` (limit \<rho>\<^sub>2))"
    by auto
qed 

lemma 
  fixes \<delta>\<^sub>1 \<delta>\<^sub>2 w q\<^sub>1 q\<^sub>2
  defines "\<rho> \<equiv> run\<^sub>t (\<delta>\<^sub>1 \<times> \<delta>\<^sub>2) (q\<^sub>1, q\<^sub>2) w"
  defines "\<rho>\<^sub>1 \<equiv> run\<^sub>t \<delta>\<^sub>1 q\<^sub>1 w"
  defines "\<rho>\<^sub>2 \<equiv> run\<^sub>t \<delta>\<^sub>2 q\<^sub>2 w"
  assumes "finite (range \<rho>)"
  shows product_run_embed_limit_finiteness_fst: "limit \<rho> \<inter> (\<Union> (embed_transition_fst ` S)) = {} \<longleftrightarrow> limit \<rho>\<^sub>1 \<inter> S = {}" (is "?thesis1")
    and product_run_embed_limit_finiteness_snd: "limit \<rho> \<inter> (\<Union> (embed_transition_snd ` S')) = {} \<longleftrightarrow> limit \<rho>\<^sub>2 \<inter> S' = {}" (is "?thesis2")
proof -
  show ?thesis1
    using assms product_run_project_limit_fst by fastforce
  show ?thesis2
    using assms product_run_project_limit_snd by fastforce
qed

subsection \<open>Product Construction Helper Functions and Lemmas\<close>

fun embed_transition :: "'a \<Rightarrow> ('b, 'c) transition \<Rightarrow> ('a \<rightharpoonup> 'b, 'c) transition set" ("\<upharpoonleft>\<^sub>_")
where
  "\<upharpoonleft>\<^sub>x (q, \<nu>, q') = {(m, \<nu>, m') | m m'. m x = Some q \<and> m' x = Some q'}"

fun project_transition :: "'a \<Rightarrow> ('a \<rightharpoonup> 'b, 'c) transition \<Rightarrow> ('b, 'c) transition" ("\<downharpoonleft>\<^sub>_")
where
  "\<downharpoonleft>\<^sub>x (m, \<nu>, m') = (the (m x), \<nu>, the (m' x))"

fun embed_pair :: "'a \<Rightarrow> (('b, 'c) transition set \<times> ('b, 'c) transition set) \<Rightarrow> (('a \<rightharpoonup> 'b, 'c) transition set \<times> ('a \<rightharpoonup> 'b, 'c) transition set)" ("\<^bold>\<upharpoonleft>\<^sub>_")
where
  "\<^bold>\<upharpoonleft>\<^sub>x (S, S') = (\<Union>(\<upharpoonleft>\<^sub>x ` S), \<Union>(\<upharpoonleft>\<^sub>x ` S'))" 

fun project_pair :: "'a \<Rightarrow> (('a \<rightharpoonup> 'b, 'c) transition set \<times> ('a \<rightharpoonup> 'b, 'c) transition set) \<Rightarrow> (('b, 'c) transition set \<times> ('b, 'c) transition set)" ("\<^bold>\<downharpoonleft>\<^sub>_")
where
  "\<^bold>\<downharpoonleft>\<^sub>x (S, S') = (\<downharpoonleft>\<^sub>x ` S, \<downharpoonleft>\<^sub>x ` S')" 

lemma embed_transition_unfold:
  "embed_transition x t = {(m, fst (snd t), m') | m m'. m x = Some (fst t) \<and> m' x = Some (snd (snd t))}"
  unfolding embed_transition.simps[symmetric] by simp

lemma
  fixes \<iota>\<^sub>m \<delta>\<^sub>m w q\<^sub>0 
  fixes x :: "'a"
  defines "\<rho> \<equiv> run\<^sub>t (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w"
  defines "\<rho>' \<equiv> run\<^sub>t (\<delta>\<^sub>m x) q\<^sub>0 w"
  assumes "\<iota>\<^sub>m x = Some q\<^sub>0"
  shows product_run_project: "\<downharpoonleft>\<^sub>x (\<rho> i) = \<rho>' i" 
    and product_run_embed: "\<rho> i \<in> \<upharpoonleft>\<^sub>x (\<rho>' i)"
  using assms product_run_Some[of _ _ _ \<delta>\<^sub>m] by simp+

lemma 
  fixes \<iota>\<^sub>m \<delta>\<^sub>m w q\<^sub>0 x
  defines "\<rho> \<equiv> run\<^sub>t (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w"
  defines "\<rho>' \<equiv> run\<^sub>t (\<delta>\<^sub>m x) q\<^sub>0 w"
  assumes "\<iota>\<^sub>m x = Some q\<^sub>0"
  assumes "finite (range \<rho>)"
  shows product_run_project_limit: "\<downharpoonleft>\<^sub>x ` limit \<rho> = limit \<rho>'" 
    and product_run_embed_limit: "limit \<rho> \<subseteq> \<Union> (\<upharpoonleft>\<^sub>x ` (limit \<rho>'))"
proof -
  have "\<And>k. \<downharpoonleft>\<^sub>x (\<rho> k) = \<rho>' k"
    using assms product_run_embed[of _ _ _ \<delta>\<^sub>m] by simp
  hence "\<downharpoonleft>\<^sub>x ` range \<rho> = range \<rho>'"
    using range_composition[symmetric, of "\<downharpoonleft>\<^sub>x" \<rho>] by presburger
  hence "finite (range \<rho>')"
    using assms finite_imageI by metis

  then obtain i where "limit \<rho> = range (suffix i \<rho>)" and "limit \<rho>' = range (suffix i \<rho>')"
    using common_range_limit assms by metis
  moreover  
  have "\<And>k. \<downharpoonleft>\<^sub>x (suffix i \<rho> k) = (suffix i \<rho>' k)"
    using assms product_run_embed[of _ _ _ \<delta>\<^sub>m] by simp
  hence "\<downharpoonleft>\<^sub>x ` range ((suffix i \<rho>)) = (range (suffix i \<rho>'))"
    using range_composition[symmetric, of "\<downharpoonleft>\<^sub>x" "(suffix i  \<rho>)"] by presburger
  moreover
  have "\<And>k. (suffix i \<rho> k) \<in> \<upharpoonleft>\<^sub>x (suffix i \<rho>' k)"
    using assms product_run_embed[of _ _ _ \<delta>\<^sub>m] by simp
  ultimately
  show "\<downharpoonleft>\<^sub>x ` limit \<rho> = limit \<rho>'" and "limit \<rho> \<subseteq> \<Union> (\<upharpoonleft>\<^sub>x ` (limit \<rho>'))"
    by auto
qed

lemma product_run_embed_limit_finiteness:
  fixes \<iota>\<^sub>m \<delta>\<^sub>m w q\<^sub>0 k
  defines "\<rho> \<equiv> run\<^sub>t (\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w"
  defines "\<rho>' \<equiv> run\<^sub>t (\<delta>\<^sub>m k) q\<^sub>0 w"
  assumes "\<iota>\<^sub>m k = Some q\<^sub>0"
  assumes "finite (range \<rho>)"
  shows "limit \<rho> \<inter> (\<Union> (\<upharpoonleft>\<^sub>k ` S)) = {} \<longleftrightarrow> limit \<rho>' \<inter> S = {}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "\<downharpoonleft>\<^sub>k ` limit \<rho> \<inter> S \<noteq> {} \<longrightarrow> limit \<rho> \<inter> (\<Union> (\<upharpoonleft>\<^sub>k ` S)) \<noteq> {}"
  proof
    assume "\<downharpoonleft>\<^sub>k ` limit \<rho> \<inter> S \<noteq> {}"
    then obtain q \<nu> q' where "(q, \<nu>, q') \<in> \<downharpoonleft>\<^sub>k ` limit \<rho>" and "(q, \<nu>, q') \<in> S"
      by auto
    moreover
    have "\<And>m \<nu> m' i. (m, \<nu>, m') = \<rho> i \<Longrightarrow> \<exists>p p'. m k = Some p \<and> m' k = Some p'" 
      using assms product_run_Some[of \<iota>\<^sub>m , OF assms(3)] by auto
    hence "\<And>m \<nu> m'. (m, \<nu>, m') \<in> limit \<rho> \<Longrightarrow> \<exists>p p'. m k = Some p \<and> m' k = Some p'" 
      using limit_in_range by fast
    ultimately
    obtain m m' where "m k = Some q" and "m' k = Some q'" and "(m, \<nu>, m') \<in> limit \<rho>"
      by auto
    moreover
    hence "(m, \<nu>, m') \<in> \<Union> (\<upharpoonleft>\<^sub>k ` S)"
      using \<open>(q, \<nu>, q') \<in> S\<close> by force
    ultimately
    show "limit \<rho> \<inter> (\<Union> (\<upharpoonleft>\<^sub>k ` S)) \<noteq> {}"
      by blast
  qed
  hence "?lhs \<longleftrightarrow> \<downharpoonleft>\<^sub>k ` limit \<rho> \<inter> S = {}"
    by auto
  also
  have "\<dots> \<longleftrightarrow> ?rhs"
    using assms product_run_project_limit[of _ _ _ \<delta>\<^sub>m] by simp
  finally
  show ?thesis
    by simp
qed

subsection \<open>Transfer Rules\<close>

context includes lifting_syntax
begin

lemma product_parametric [transfer_rule]:
  "((A ===> B ===> C ===> B) ===> (A ===> rel_option B) ===> C ===> A ===> rel_option B) product product"
  by (auto simp add: rel_fun_def rel_option_iff split: option.split)

lemma run_parametric [transfer_rule]:
  "((A ===> B ===> A) ===> A ===> ((=) ===> B) ===> (=) ===> A) run run"
proof -
  {
    fix \<delta> \<delta>' q q' n w 
    fix w' :: "nat \<Rightarrow> 'd" 
    assume "(A ===> B ===> A) \<delta> \<delta>'" "A q q'" "((=) ===> B) w w'" 
    hence "A (run \<delta> q w n) (run \<delta>' q' w' n)"
      by (induction n) (simp_all add: rel_fun_def)
  }
  thus ?thesis
    by blast
qed

lemma reach_parametric [transfer_rule]:
  assumes "bi_total B"
  assumes "bi_unique B"
  shows "(rel_set B ===> (A ===> B ===> A) ===> A ===> rel_set A) reach reach"
proof standard+
  fix \<Sigma> \<Sigma>' \<delta> \<delta>' q q'
  assume "rel_set B \<Sigma> \<Sigma>'" "(A ===> B ===> A) \<delta> \<delta>'" "A q q'"

  {
    fix z 
    assume "z \<in> reach \<Sigma> \<delta> q"
    then obtain w n where "z = run \<delta> q w n" and "range w \<subseteq> \<Sigma>"
      unfolding reach_def by auto
    
    define w' where "w' n = (SOME x. B (w n) x)" for n
    
    have "\<And>n. w n \<in> \<Sigma>"
      using \<open>range w \<subseteq> \<Sigma>\<close> by blast
    hence "\<And>n. w' n \<in> \<Sigma>'"
      using assms \<open>rel_set B \<Sigma> \<Sigma>'\<close> by (simp add: w'_def bi_unique_def rel_set_def; metis someI) 
    hence "run \<delta>' q' w' n \<in> reach \<Sigma>' \<delta>' q'"
      unfolding reach_def by auto
     
    moreover

    have "A z (run \<delta>' q' w' n)"
      apply (unfold \<open>z = run \<delta> q w n\<close>)
      apply (insert \<open>A q q'\<close> \<open>(A ===> B ===> A) \<delta> \<delta>'\<close> assms(1))  
      apply (induction n) 
      apply (simp_all add: rel_fun_def bi_total_def w'_def) 
      by (metis tfl_some)  

    ultimately

    have "\<exists>z' \<in> reach \<Sigma>' \<delta>' q'. A z z'"
      by blast
  }

  moreover
  
  {
    fix z 
    assume "z \<in> reach \<Sigma>' \<delta>' q'"
    then obtain w n where "z = run \<delta>' q' w n" and "range w \<subseteq> \<Sigma>'"
      unfolding reach_def by auto
    
    define w' where "w' n = (SOME x. B x (w n))" for n
    
    have "\<And>n. w n \<in> \<Sigma>'"
      using \<open>range w \<subseteq> \<Sigma>'\<close> by blast
    hence "\<And>n. w' n \<in> \<Sigma>"
      using assms \<open>rel_set B \<Sigma> \<Sigma>'\<close> by (simp add: w'_def bi_unique_def rel_set_def; metis someI)
    hence "run \<delta> q w' n \<in> reach \<Sigma> \<delta> q"
      unfolding reach_def by auto
     
    moreover

    have "A (run \<delta> q w' n) z"
      apply (unfold \<open>z = run \<delta>' q' w n\<close>)
      apply (insert \<open>A q q'\<close> \<open>(A ===> B ===> A) \<delta> \<delta>'\<close> assms(1))  
      apply (induction n) 
      apply (simp_all add: rel_fun_def bi_total_def w'_def) 
      by (metis tfl_some)  

    ultimately

    have "\<exists>z' \<in> reach \<Sigma> \<delta> q. A z' z"
      by blast
  }
  ultimately
  show "rel_set A (reach \<Sigma> \<delta> q) (reach \<Sigma>' \<delta>' q')"
    unfolding rel_set_def by blast
qed

end

subsection \<open>Lift to Mapping\<close>

lift_definition product_abs :: "('a \<Rightarrow> ('b, 'c) DTS) \<Rightarrow> (('a, 'b) mapping, 'c) DTS" ("\<up>\<Delta>\<^sub>\<times>") is product 
  parametric product_parametric .

lemma product_abs_run_None:
  "Mapping.lookup \<iota>\<^sub>m k = None \<Longrightarrow> Mapping.lookup (run (\<up>\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w i) k = None"
  by (transfer; insert product_run_None)

lemma product_abs_run_Some:
  "Mapping.lookup \<iota>\<^sub>m k = Some q\<^sub>0 \<Longrightarrow> Mapping.lookup (run (\<up>\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m w i) k = Some (run (\<delta>\<^sub>m k) q\<^sub>0 w i)"
  by (transfer; insert product_run_Some)

theorem finite_reach_product_abs:
  assumes "finite (Mapping.keys \<iota>\<^sub>m)"
  assumes "\<And>x. x \<in> (Mapping.keys \<iota>\<^sub>m) \<Longrightarrow> finite (reach \<Sigma> (\<delta>\<^sub>m x) (the (Mapping.lookup \<iota>\<^sub>m x)))"
  shows "finite (reach \<Sigma> (\<up>\<Delta>\<^sub>\<times> \<delta>\<^sub>m) \<iota>\<^sub>m)"
  using assms by (transfer; blast intro: finite_reach_product)

end
