(*
  File: Connectivity.thy
  Author: Bohua Zhan
*)

section \<open>Connectedness for a set of undirected edges.\<close>

theory Connectivity
  imports Union_Find
begin

text \<open>A simple application of union-find for graph connectivity.\<close>

fun is_path :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> nat list \<Rightarrow> bool" where
  "is_path n S [] = False"
| "is_path n S (x # xs) =
   (if xs = [] then x < n else ((x, hd xs) \<in> S \<or> (hd xs, x) \<in> S) \<and> is_path n S xs)"
setup \<open>fold add_rewrite_rule @{thms is_path.simps}\<close>

definition has_path :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "has_path n S i j \<longleftrightarrow> (\<exists>p. is_path n S p \<and> hd p = i \<and> last p = j)"

lemma is_path_nonempty [forward]: "is_path n S p \<Longrightarrow> p \<noteq> []" by auto2
lemma nonempty_is_not_path [resolve]: "\<not>is_path n S []" by auto2

lemma is_path_extend [forward]:
  "is_path n S p \<Longrightarrow> S \<subseteq> T \<Longrightarrow> is_path n T p"
@proof @induct p @qed

lemma has_path_extend [forward]:
  "has_path n S i j \<Longrightarrow> S \<subseteq> T \<Longrightarrow> has_path n T i j" by auto2

definition joinable :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "joinable p q \<longleftrightarrow> (last p = hd q)"

definition path_join :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where [rewrite]:
  "path_join p q = p @ tl q"
setup \<open>register_wellform_data ("path_join p q", ["joinable p q"])\<close>
setup \<open>add_prfstep_check_req ("path_join p q", "joinable p q")\<close>

lemma path_join_hd [rewrite]: "p \<noteq> [] \<Longrightarrow> hd (path_join p q) = hd p" by auto2

lemma path_join_last [rewrite]: "joinable p q \<Longrightarrow> q \<noteq> [] \<Longrightarrow> last (path_join p q) = last q"
@proof @have "q = hd q # tl q" @case "tl q = []" @qed

lemma path_join_is_path [backward]:
  "joinable p q \<Longrightarrow> is_path n S p \<Longrightarrow> is_path n S q \<Longrightarrow> is_path n S (path_join p q)"
@proof @induct p @qed

lemma has_path_trans [forward]:
  "has_path n S i j \<Longrightarrow> has_path n S j k \<Longrightarrow> has_path n S i k"
@proof
  @obtain p where "is_path n S p" "hd p = i" "last p = j"
  @obtain q where "is_path n S q" "hd q = j" "last q = k"
  @have "is_path n S (path_join p q)"
@qed

definition is_valid_graph :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool" where [rewrite]:
  "is_valid_graph n S \<longleftrightarrow> (\<forall>p\<in>S. fst p < n \<and> snd p < n)"

lemma has_path_single1 [backward1]:
  "is_valid_graph n S \<Longrightarrow> (a, b) \<in> S \<Longrightarrow> has_path n S a b"
@proof @have "is_path n S [a, b]" @qed

lemma has_path_single2 [backward1]:
  "is_valid_graph n S \<Longrightarrow> (a, b) \<in> S \<Longrightarrow> has_path n S b a"
@proof @have "is_path n S [b, a]" @qed

lemma has_path_refl [backward2]:
  "is_valid_graph n S \<Longrightarrow> a < n \<Longrightarrow> has_path n S a a"
@proof @have "is_path n S [a]" @qed

definition connected_rel :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set" where
  "connected_rel n S = {(a,b). has_path n S a b}"

lemma connected_rel_iff [rewrite]:
  "(a, b) \<in> connected_rel n S \<longleftrightarrow> has_path n S a b" using connected_rel_def by simp

lemma connected_rel_trans [forward]:
  "trans (connected_rel n S)" by auto2

lemma connected_rel_refl [backward2]:
  "is_valid_graph n S \<Longrightarrow> a < n \<Longrightarrow> (a, a) \<in> connected_rel n S" by auto2

lemma is_path_per_union [rewrite]:
  "is_valid_graph n (S \<union> {(a, b)}) \<Longrightarrow>
   has_path n (S \<union> {(a, b)}) i j \<longleftrightarrow> (i, j) \<in> per_union (connected_rel n S) a b"
@proof
  @let "R = connected_rel n S"
  @let "S' = S \<union> {(a, b)}" @have "S \<subseteq> S'"
  @case "(i, j) \<in> per_union R a b" @with
    @case "(i, a) \<in> R \<and> (b, j) \<in> R" @with
      @have "has_path n S' i a" @have "has_path n S' a b" @have "has_path n S' b j"
    @end
    @case "(i, b) \<in> R \<and> (a, j) \<in> R" @with
      @have "has_path n S' i b" @have "has_path n S' b a" @have "has_path n S' a j"
    @end
  @end
  @case "has_path n S' i j" @with
    @have (@rule) "\<forall>p. is_path n S' p \<longrightarrow> (hd p, last p) \<in> per_union R a b" @with
      @induct p @with
      @subgoal "p = x # xs" @case "xs = []"
        @have "(x, hd xs) \<in> per_union R a b" @with
          @have "is_valid_graph n S"
          @case "(x, hd xs) \<in> S'" @with @case "(x, hd xs) \<in> S" @end
          @case "(hd xs, x) \<in> S'" @with @case "(hd xs, x) \<in> S" @end
        @end
      @endgoal @end
    @end
    @obtain p where "is_path n S' p" "hd p = i" "last p = j"
  @end
@qed

lemma connected_rel_union [rewrite]:
  "is_valid_graph n (S \<union> {(a, b)}) \<Longrightarrow>
   connected_rel n (S \<union> {(a, b)}) = per_union (connected_rel n S) a b" by auto2

lemma connected_rel_init [rewrite]:
  "connected_rel n {} = uf_init_rel n"
@proof
  @have "is_valid_graph n {}"
  @have "\<forall>i j. has_path n {} i j \<longleftrightarrow> (i, j) \<in> uf_init_rel n" @with
    @case "has_path n {} i j" @with
      @obtain p where "is_path n {} p" "hd p = i" "last p = j"
      @have "p = hd p # tl p"
    @end
  @end
@qed

fun connected_rel_ind :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "connected_rel_ind n es 0 = uf_init_rel n"
| "connected_rel_ind n es (Suc k) =
   (let R = connected_rel_ind n es k; p = es ! k in
      per_union R (fst p) (snd p))"
setup \<open>fold add_rewrite_rule @{thms connected_rel_ind.simps}\<close>

lemma connected_rel_ind_rule [rewrite]:
  "is_valid_graph n (set es) \<Longrightarrow> k \<le> length es \<Longrightarrow>
   connected_rel_ind n es k = connected_rel n (set (take k es))"
@proof @induct k @with
  @subgoal "k = Suc m"
    @have "is_valid_graph n (set (take (Suc m) es))"
  @endgoal @end
@qed

text \<open>Correctness of the functional algorithm.\<close>
theorem connected_rel_ind_compute [rewrite]:
  "is_valid_graph n (set es) \<Longrightarrow>
   connected_rel_ind n es (length es) = connected_rel n (set es)" by auto2

end
