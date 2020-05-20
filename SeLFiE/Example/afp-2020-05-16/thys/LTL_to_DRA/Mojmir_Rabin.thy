(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Translation to Deterministic Transition-Based Rabin Automata\<close>

theory Mojmir_Rabin
  imports Main Mojmir Rabin "Auxiliary/List2"
begin

locale mojmir_to_rabin_def = mojmir_def 
begin
  
definition fail\<^sub>R :: "('b \<Rightarrow> nat option, 'a) transition set"
where
  "fail\<^sub>R = {(r, \<nu>, s) | r \<nu> s q q'. r q \<noteq> None \<and> q' = \<delta> q \<nu> \<and> q' \<notin> F \<and> sink q'}"

definition succeed\<^sub>R :: "nat \<Rightarrow> ('b \<Rightarrow> nat option, 'a) transition set"
where
  "succeed\<^sub>R i = {(r, \<nu>, s) | r \<nu> s q. r q = Some i \<and> q \<notin> F - {q\<^sub>0} \<and> (\<delta> q \<nu>) \<in> F}"

definition merge\<^sub>R :: "nat \<Rightarrow> ('b \<Rightarrow> nat option, 'a) transition set"
where
  "merge\<^sub>R i = {(r, \<nu>, s) | r \<nu> s q q' j. r q = Some j \<and> j < i \<and> q' = \<delta> q \<nu> \<and>
        ((\<exists>q''. q' = \<delta> q'' \<nu> \<and> r q'' \<noteq> None \<and> q'' \<noteq> q) \<or> q' = q\<^sub>0) \<and> q' \<notin> F}"

abbreviation Q\<^sub>R
where
  "Q\<^sub>R \<equiv> reach \<Sigma> step initial"

abbreviation q\<^sub>\<R>
where
  "q\<^sub>\<R> \<equiv> initial"

abbreviation \<delta>\<^sub>\<R>
where
  "\<delta>\<^sub>\<R> \<equiv> step"

abbreviation Acc\<^sub>\<R>
where
  "Acc\<^sub>\<R> j \<equiv> (fail\<^sub>R \<union> merge\<^sub>R j, succeed\<^sub>R j)"

abbreviation \<R>
where
  "\<R> \<equiv> (\<delta>\<^sub>\<R>, q\<^sub>\<R>, {Acc\<^sub>\<R> j | j. j < max_rank})"

end



subsection \<open>Well-formedness\<close>

lemma function_set_finite:
  assumes "finite R"
  assumes "finite A"
  shows "finite {f. (\<forall>x. x \<notin> R \<longrightarrow> f x = c) \<and> (\<forall>x. x \<in> R \<longrightarrow> f x \<in> A)}" (is "finite ?F")
  using assms(1)
proof (induction R rule: finite_induct)
  case empty
    have "{f. (\<forall>x. x \<in> {} \<longrightarrow> f x \<in> A) \<and> (\<forall>x. x \<notin> {} \<longrightarrow> f x = c)} \<subseteq> {\<lambda>x. c}"
      by auto
    thus ?case
      using finite_subset by auto
next
  case (insert r R)
    let ?F = "{f. (\<forall>x. x \<notin> R \<union> {r} \<longrightarrow> f x = c) \<and> (\<forall>x. x \<in> R \<union> {r} \<longrightarrow> f x \<in> A)}"
    let ?F' = "{f. (\<forall>x. x \<notin> R \<longrightarrow> f x = c) \<and> (\<forall>x. x \<in> R \<longrightarrow> f x \<in> A)}"
 
    have "?F \<subseteq> {f(r := a) | f a. f \<in> ?F' \<and> a \<in> A}" (is "_ \<subseteq> ?X")
    proof 
      fix f
      assume "f \<in> ?F"
      hence "f(r := c) \<in> ?F'" and "f r \<in> A"
        using insert(2) by (simp, blast)
      hence "f(r := c, r := (f r)) \<in> ?X"
        by blast
      thus "f \<in> ?X"
        by simp
    qed
    moreover
    have "finite (?F' \<times> A)"
      using assms(2) insert(3) by simp  
    have "(\<lambda>(f,a). f(r:=a)) ` (?F' \<times> A) = ?X"
      by auto
    hence "finite ?X"
      using finite_imageI[OF \<open>finite (?F' \<times> A)\<close>, of "(\<lambda>(f,a). f(r:=a))"] by presburger
    ultimately
    have "finite ?F"
      by (blast intro: finite_subset)
    thus ?case
      unfolding insert_def by simp
qed

lemma (in semi_mojmir) wellformed_\<R>:
  shows "finite (reach \<Sigma> step initial)"
proof (rule finite_subset)
  let ?R = "{f. (\<forall>x. x \<notin> reach \<Sigma> \<delta> q\<^sub>0 \<longrightarrow> f x = None) \<and> 
    (\<forall>x. x \<in> reach \<Sigma> \<delta> q\<^sub>0 \<longrightarrow> f x \<in> {None} \<union> Some ` {0..<max_rank})}"

  show "reach \<Sigma> step initial \<subseteq> ?R"
  proof
    fix x 
    assume "x \<in> reach \<Sigma> step initial"
    then obtain w where x_def: "x = foldl step initial w" and "set w \<subseteq> \<Sigma>"
      unfolding reach_foldl_def[OF nonempty_\<Sigma>] by blast
    obtain a where "a \<in> \<Sigma>"
      using nonempty_\<Sigma> by blast
    have "range (w \<frown> (\<lambda>i. a)) \<subseteq> \<Sigma>"
      using \<open>set w \<subseteq> \<Sigma>\<close> \<open>a \<in> \<Sigma>\<close> unfolding conc_def by auto
    then interpret \<HH>: semi_mojmir \<Sigma> \<delta> q\<^sub>0 "(w \<frown> (\<lambda>i. a))"
      using finite_reach finite_\<Sigma> by (unfold_locales; simp_all)
    have "x = (\<lambda>q. \<HH>.state_rank q (length w))" 
      unfolding \<HH>.state_rank_step_foldl x_def using prefix_conc_length subsequence_def by metis
    thus "x \<in> ?R"
      using \<HH>.state_rank_in_function_set by meson
  qed

  have "finite ({None} \<union> Some ` {0..<max_rank})"
    by blast
  thus "finite ?R"
    using finite_reach by (blast intro: function_set_finite)
qed

locale mojmir_to_rabin = mojmir + mojmir_to_rabin_def begin

subsection \<open>Correctness\<close>

lemma imp_and_not_imp_eq:
  assumes "P \<Longrightarrow> Q"
  assumes "\<not>P \<Longrightarrow> \<not>Q"
  shows "P = Q"
  using assms by blast  

lemma finite_limit_intersection:
  assumes "finite (range f)"
  assumes "\<And>x::nat. x \<in> A \<longleftrightarrow> (f x) \<in> B"
  shows "finite A \<longleftrightarrow> limit f \<inter> B = {}"
proof (rule imp_and_not_imp_eq)
  assume "finite A"
  {
    fix x
    assume "x > Max (A \<union> {0})"
    moreover
    have "finite (A \<union> {0})"
      using \<open>finite A\<close> by simp
    ultimately
    have "x \<notin> A"
      using Max.coboundedI 
      by (metis insert_iff insert_is_Un not_le sup.commute)
    hence "f x \<notin> B"
      using assms(2) by simp
  }
  hence "f ` {Suc (Max (A \<union> {0}))..} \<inter> B = {}"
    by auto
  thus "limit f \<inter> B = {}"
    using limit_subset[of f] by blast
next
  assume "infinite A"
  have "f ` A \<subseteq> B"
    unfolding image_def using assms by auto 
  moreover
  have "finite (range f)"
    using assms(1) unfolding limit_def Inf_many_def by simp  
  hence "finite (f ` A)"
    by (metis infinite_iff_countable_subset subset_UNIV subset_image_iff)
  then obtain y where "y \<in> f ` A" and "\<exists>\<^sub>\<infinity>n. f n = y"
    unfolding Inf_many_def using pigeonhole_infinite[OF \<open>infinite A\<close>] by fast
  ultimately
  show "limit f \<inter> B \<noteq> {}"
    using limit_iff_frequent by fast
qed

lemma finite_range_run:
  defines "r \<equiv> run\<^sub>t \<delta>\<^sub>\<R> q\<^sub>\<R> w"
  shows "finite (range r)"
proof -
  {
    fix n
    have "\<And>n. w n \<in> \<Sigma>" and "set (map w [0..<n]) \<subseteq> \<Sigma>" and "set ( map w [0..<Suc n]) \<subseteq> \<Sigma>"
      using bounded_w by auto 
    hence "r n \<in> Q\<^sub>R \<times> \<Sigma> \<times> Q\<^sub>R"
      unfolding run\<^sub>t.simps run_foldl reach_foldl_def[OF nonempty_\<Sigma>] r_def 
      unfolding fst_conv comp_def snd_conv by blast
  }
  hence "range r \<subseteq> Q\<^sub>R \<times> \<Sigma> \<times> Q\<^sub>R"
    by blast
  thus "finite (range r)"
    using finite_\<Sigma> wellformed_\<R> 
    by (blast dest: finite_subset)
qed

theorem mojmir_accept_iff_rabin_accept_rank:
  shows "(finite (fail) \<and> finite (merge i) \<and> infinite (succeed  i))
    \<longleftrightarrow> accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> i) w"
  (is "?lhs = ?rhs")
proof
  define r where "r = run\<^sub>t \<delta>\<^sub>\<R> q\<^sub>\<R> w" 
  have r_alt_def: "\<And>i. r i = (\<lambda>q. state_rank q i, w i, \<lambda>q. state_rank q (Suc i))"
    using r_def state_rank_step_foldl run_foldl by fastforce

  have F: "\<And>x. x \<in> fail_t \<longleftrightarrow> (r x) \<in> fail\<^sub>R"
    unfolding fail_t_def fail\<^sub>R_def r_alt_def by blast
  have B: "\<And>x i. x \<in> merge_t i \<longleftrightarrow> (r x) \<in> merge\<^sub>R i"
    unfolding merge_t_def merge\<^sub>R_def r_alt_def by blast
  have S: "\<And>x i. x \<in> succeed_t i \<longleftrightarrow> (r x) \<in> succeed\<^sub>R i"
    unfolding succeed_t_def succeed\<^sub>R_def r_alt_def by blast

  have "finite (range r)"
    using finite_range_run r_def by simp
  note finite_limit_rule = finite_limit_intersection[OF \<open>finite (range r)\<close>]
 
  {
    assume "?lhs"
    hence "finite fail_t" and "finite (merge_t i)" and "infinite (succeed_t i)"
      unfolding finite_fail_t finite_merge_t finite_succeed_t by blast+

    have "limit r \<inter> fail\<^sub>R = {}"
      by (metis finite_limit_rule F \<open>finite (fail_t)\<close>)
    moreover
    have "limit r \<inter> merge\<^sub>R i = {}"
      by (metis finite_limit_rule B \<open>finite (merge_t i)\<close>)
    ultimately
    have "limit r \<inter> fst (Acc\<^sub>\<R> i) = {}"
      by auto
    moreover
    have "limit r \<inter> succeed\<^sub>R i \<noteq> {}"
      by (metis finite_limit_rule S \<open>infinite (succeed_t i)\<close>)
    hence "limit r \<inter> snd (Acc\<^sub>\<R> i) \<noteq> {}"
      by auto
    ultimately
    show ?rhs
      unfolding r_def by simp
  }

  {
    assume ?rhs
    hence "limit r \<inter> fail\<^sub>R = {}" and "limit r \<inter> merge\<^sub>R i = {}" and "limit r \<inter> (succeed\<^sub>R i) \<noteq> {}"
      unfolding r_def by auto 

    have "finite fail_t"
      by (metis finite_limit_rule F \<open>limit r \<inter> fail\<^sub>R = {}\<close>)
    moreover
    have "finite (merge_t i)"
      by (metis finite_limit_rule B \<open>limit r \<inter> merge\<^sub>R i = {}\<close>)
    moreover
    have "infinite (succeed_t i)"
      by (metis finite_limit_rule S \<open>limit r \<inter> (succeed\<^sub>R i) \<noteq> {}\<close>)
    ultimately
    show ?lhs
      unfolding finite_fail_t finite_merge_t finite_succeed_t by blast
  }
qed

theorem mojmir_accept_iff_rabin_accept:
  "accept \<longleftrightarrow> accept\<^sub>R \<R> w"
  unfolding mojmir_accept_iff_token_set_accept mojmir_accept_iff_rabin_accept_rank by auto

definition smallest_accepting_rank\<^sub>\<R> :: "nat option"
where 
  "smallest_accepting_rank\<^sub>\<R> \<equiv> (if accept\<^sub>R \<R> w then 
    Some (LEAST i. accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> i) w) else None)"

theorem Mojmir_rabin_smallest_accepting_rank:
  "smallest_accepting_rank = smallest_accepting_rank\<^sub>\<R>"
  by (simp only: smallest_accepting_rank_def smallest_accepting_rank\<^sub>\<R>_def 
    mojmir_accept_iff_rabin_accept mojmir_accept_iff_rabin_accept_rank)

lemma smallest_accepting_rank\<^sub>\<R>_properties:
  "smallest_accepting_rank\<^sub>\<R> = Some i \<Longrightarrow> accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> i) w"
  by (unfold Mojmir_rabin_smallest_accepting_rank[symmetric] mojmir_accept_iff_rabin_accept_rank[symmetric];
      blast dest: smallest_accepting_rank_properties)

end

end
