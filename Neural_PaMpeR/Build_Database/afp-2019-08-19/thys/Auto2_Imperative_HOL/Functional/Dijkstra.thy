(*
  File: Dijkstra.thy
  Author: Bohua Zhan
*)

section \<open>Dijkstra's algorithm for shortest paths\<close>

theory Dijkstra
  imports Mapping_Str Arrays_Ex
begin

text \<open>
  Verification of Dijkstra's algorithm: function part.

  The algorithm is also verified by Nordhoff and Lammich in
  \cite{Dijkstra_Shortest_Path-AFP}.
\<close>

subsection \<open>Graphs\<close>

datatype graph = Graph "nat list list"

fun size :: "graph \<Rightarrow> nat" where
  "size (Graph G) = length G"

fun weight :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "weight (Graph G) m n = (G ! m) ! n"

fun valid_graph :: "graph \<Rightarrow> bool" where
  "valid_graph (Graph G) \<longleftrightarrow> (\<forall>i<length G. length (G ! i) = length G)"
setup \<open>add_rewrite_rule @{thm valid_graph.simps}\<close>

subsection \<open>Paths on graphs\<close>

text \<open>The set of vertices less than n.\<close>
definition verts :: "graph \<Rightarrow> nat set" where
  "verts G = {i. i < size G}"

lemma verts_mem [rewrite]: "i \<in> verts G \<longleftrightarrow> i < size G" by (simp add: verts_def)
lemma card_verts [rewrite]: "card (verts G) = size G" using verts_def by auto
lemma finite_verts [forward]: "finite (verts G)" using verts_def by auto

definition is_path :: "graph \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "is_path G p \<longleftrightarrow> p \<noteq> [] \<and> set p \<subseteq> verts G"

lemma is_path_to_in_verts [forward]: "is_path G p \<Longrightarrow> hd p \<in> verts G \<and> last p \<in> verts G"
@proof @have "last p \<in> set p" @qed

definition joinable :: "graph \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "joinable G p q \<longleftrightarrow> (is_path G p \<and> is_path G q \<and> last p = hd q)"

definition path_join :: "graph \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where [rewrite]:
  "path_join G p q = p @ tl q"
setup \<open>register_wellform_data ("path_join G p q", ["joinable G p q"])\<close>
setup \<open>add_prfstep_check_req ("path_join G p q", "joinable G p q")\<close>

lemma path_join_is_path:
  "joinable G p q \<Longrightarrow> is_path G (path_join G p q)"
@proof @have "q = hd q # tl q" @qed
setup \<open>add_forward_prfstep_cond @{thm path_join_is_path} [with_term "path_join ?G ?p ?q"]\<close>

fun path_weight :: "graph \<Rightarrow> nat list \<Rightarrow> nat" where
  "path_weight G [] = 0"
| "path_weight G (x # xs) = (if xs = [] then 0 else weight G x (hd xs) + path_weight G xs)"
setup \<open>fold add_rewrite_rule @{thms path_weight.simps}\<close>

lemma path_weight_singleton [rewrite]: "path_weight G [x] = 0" by auto2
lemma path_weight_doubleton [rewrite]: "path_weight G [m, n] = weight G m n" by auto2

lemma path_weight_sum [rewrite]:
  "joinable G p q \<Longrightarrow> path_weight G (path_join G p q) = path_weight G p + path_weight G q"
@proof @induct p @qed

fun path_set :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "path_set G m n = {p. is_path G p \<and> hd p = m \<and> last p = n}"

lemma path_set_mem [rewrite]:
  "p \<in> path_set G m n \<longleftrightarrow> is_path G p \<and> hd p = m \<and> last p = n" by simp

lemma path_join_set: "joinable G p q \<Longrightarrow> path_join G p q \<in> path_set G (hd p) (last q)"
@proof @have "q = hd q # tl q" @case "tl q = []" @qed
setup \<open>add_forward_prfstep_cond @{thm path_join_set} [with_term "path_join ?G ?p ?q"]\<close>

subsection \<open>Shortest paths\<close>

definition is_shortest_path :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "is_shortest_path G m n p \<longleftrightarrow>
     (p \<in> path_set G m n \<and> (\<forall>p'\<in>path_set G m n. path_weight G p' \<ge> path_weight G p))"

lemma is_shortest_pathD1 [forward]:
  "is_shortest_path G m n p \<Longrightarrow> p \<in> path_set G m n" by auto2

lemma is_shortest_pathD2 [forward]:
  "is_shortest_path G m n p \<Longrightarrow> p' \<in> path_set G m n \<Longrightarrow> path_weight G p' \<ge> path_weight G p" by auto2
setup \<open>del_prfstep_thm_eqforward @{thm is_shortest_path_def}\<close>

definition has_dist :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "has_dist G m n \<longleftrightarrow> (\<exists>p. is_shortest_path G m n p)"

lemma has_distI [forward]: "is_shortest_path G m n p \<Longrightarrow> has_dist G m n" by auto2
lemma has_distD [resolve]: "has_dist G m n \<Longrightarrow> \<exists>p. is_shortest_path G m n p" by auto2
lemma has_dist_to_in_verts [forward]: "has_dist G u v \<Longrightarrow> u \<in> verts G \<and> v \<in> verts G" by auto2
setup \<open>del_prfstep_thm @{thm has_dist_def}\<close>

definition dist :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where [rewrite]:
  "dist G m n = path_weight G (SOME p. is_shortest_path G m n p)"
setup \<open>register_wellform_data ("dist G m n", ["has_dist G m n"])\<close>

lemma dist_eq [rewrite]:
  "is_shortest_path G m n p \<Longrightarrow> dist G m n = path_weight G p" by auto2

lemma distD [forward]:
  "has_dist G m n \<Longrightarrow> p \<in> path_set G m n \<Longrightarrow> path_weight G p \<ge> dist G m n" by auto2
setup \<open>del_prfstep_thm @{thm dist_def}\<close>

lemma shortest_init [resolve]: "n \<in> verts G \<Longrightarrow> is_shortest_path G n n [n]" by auto2

subsection \<open>Interior points\<close>

text \<open>List of interior points\<close>
definition int_pts :: "nat list \<Rightarrow> nat set" where [rewrite]:
  "int_pts p = set (butlast p)"

lemma int_pts_singleton [rewrite]: "int_pts [x] = {}" by auto2
lemma int_pts_doubleton [rewrite]: "int_pts [x, y] = {x}" by auto2

definition path_set_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat list set" where
  "path_set_on G m n V = {p. p \<in> path_set G m n \<and> int_pts p \<subseteq> V}"

lemma path_set_on_mem [rewrite]:
  "p \<in> path_set_on G m n V \<longleftrightarrow> p \<in> path_set G m n \<and> int_pts p \<subseteq> V" by (simp add: path_set_on_def)

text \<open>Version of shortest path on a set of points\<close>
definition is_shortest_path_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> bool" where [rewrite]:
  "is_shortest_path_on G m n p V \<longleftrightarrow>
    (p \<in> path_set_on G m n V \<and> (\<forall>p'\<in>path_set_on G m n V. path_weight G p' \<ge> path_weight G p))"

lemma is_shortest_path_onD1 [forward]:
  "is_shortest_path_on G m n p V \<Longrightarrow> p \<in> path_set_on G m n V" by auto2

lemma is_shortest_path_onD2 [forward]:
  "is_shortest_path_on G m n p V \<Longrightarrow> p' \<in> path_set_on G m n V \<Longrightarrow> path_weight G p' \<ge> path_weight G p" by auto2
setup \<open>del_prfstep_thm_eqforward @{thm is_shortest_path_on_def}\<close>

definition has_dist_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool" where [rewrite]:
  "has_dist_on G m n V \<longleftrightarrow> (\<exists>p. is_shortest_path_on G m n p V)"

lemma has_dist_onI [forward]: "is_shortest_path_on G m n p V \<Longrightarrow> has_dist_on G m n V" by auto2
lemma has_dist_onD [resolve]: "has_dist_on G m n V \<Longrightarrow> \<exists>p. is_shortest_path_on G m n p V" by auto2
setup \<open>del_prfstep_thm @{thm has_dist_on_def}\<close>

definition dist_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat" where [rewrite]:
  "dist_on G m n V = path_weight G (SOME p. is_shortest_path_on G m n p V)"
setup \<open>register_wellform_data ("dist_on G m n V", ["has_dist_on G m n V"])\<close>

lemma dist_on_eq [rewrite]:
  "is_shortest_path_on G m n p V \<Longrightarrow> dist_on G m n V = path_weight G p" by auto2

lemma dist_onD [forward]:
  "has_dist_on G m n V \<Longrightarrow> p \<in> path_set_on G m n V \<Longrightarrow> path_weight G p \<ge> dist_on G m n V" by auto2
setup \<open>del_prfstep_thm @{thm dist_on_def}\<close>

subsection \<open>Two splitting lemmas\<close>

lemma path_split1 [backward]: "is_path G p \<Longrightarrow> hd p \<in> V \<Longrightarrow> last p \<notin> V \<Longrightarrow>
  \<exists>p1 p2. joinable G p1 p2 \<and> p = path_join G p1 p2 \<and> int_pts p1 \<subseteq> V \<and> hd p2 \<notin> V"
@proof @induct p @with
  @subgoal "p = a # p'"
    @let "p = a # p'"
    @case "p' = []"
    @case "hd p' \<notin> V" @with @have "p = path_join G [a, hd p'] p'" @end
    @obtain p1 p2 where "joinable G p1 p2" "p' = path_join G p1 p2" "int_pts p1 \<subseteq> V" "hd p2 \<notin> V"
    @have "p = path_join G (a # p1) p2"
  @endgoal @end
@qed

lemma path_split2 [backward]: "is_path G p \<Longrightarrow> hd p \<noteq> last p \<Longrightarrow>
  \<exists>q n. joinable G q [n, last p] \<and> p = path_join G q [n, last p]"
@proof
  @have "p = butlast p @ [last p]"
  @have "butlast p \<noteq> []"
  @let "n = last (butlast p)"
  @have "p = path_join G (butlast p) [n, last p]"
@qed

subsection \<open>Deriving has\_dist and has\_dist\_on\<close>

definition known_dists :: "graph \<Rightarrow> nat set \<Rightarrow> bool" where [rewrite]:
  "known_dists G V \<longleftrightarrow> (V \<subseteq> verts G \<and> 0 \<in> V \<and>
      (\<forall>i\<in>verts G. has_dist_on G 0 i V) \<and>
      (\<forall>i\<in>V. has_dist G 0 i \<and> dist G 0 i = dist_on G 0 i V))"

lemma derive_dist [backward2]:
  "known_dists G V \<Longrightarrow>
   m \<in> verts G - V \<Longrightarrow>
   \<forall>i\<in>verts G - V. dist_on G 0 i V \<ge> dist_on G 0 m V \<Longrightarrow>
   has_dist G 0 m \<and> dist G 0 m = dist_on G 0 m V"
@proof
  @obtain p where "is_shortest_path_on G 0 m p V"
  @have "is_shortest_path G 0 m p" @with
    @have "p \<in> path_set G 0 m"
    @have "\<forall>p'\<in>path_set G 0 m. path_weight G p' \<ge> path_weight G p" @with
      @obtain p1 p2 where "joinable G p1 p2" "p' = path_join G p1 p2"
                          "int_pts p1 \<subseteq> V" "hd p2 \<notin> V"
      @let "x = last p1"
      @have "dist_on G 0 x V \<ge> dist_on G 0 m V"
      @have "p1 \<in> path_set_on G 0 x V"
      @have "path_weight G p1 \<ge> dist_on G 0 x V"
      @have "path_weight G p' \<ge> dist_on G 0 m V + path_weight G p2"
    @end
  @end
@qed

lemma join_def' [resolve]: "joinable G p q \<Longrightarrow> path_join G p q = butlast p @ q"
@proof
  @have "p = butlast p @ [last p]"
  @have "path_join G p q = butlast p @ [last p] @ tl q"
@qed

lemma int_pts_join [rewrite]:
  "joinable G p q \<Longrightarrow> int_pts (path_join G p q) = int_pts p \<union> int_pts q"
@proof @have "path_join G p q = butlast p @ q" @qed

lemma dist_on_triangle_ineq [backward]:
  "has_dist_on G k m V \<Longrightarrow> has_dist_on G k n V \<Longrightarrow> V \<subseteq> verts G \<Longrightarrow> n \<in> verts G \<Longrightarrow> m \<in> V \<Longrightarrow>
   dist_on G k m V + weight G m n \<ge> dist_on G k n V"
@proof
  @obtain p where "is_shortest_path_on G k m p V"
  @let "pq = path_join G p [m, n]"
  @have "V \<union> {m} = V"
  @have "pq \<in> path_set_on G k n V"
@qed

lemma derive_dist_on [backward2]:
  "known_dists G V \<Longrightarrow>
   m \<in> verts G - V \<Longrightarrow>
   \<forall>i\<in>verts G - V. dist_on G 0 i V \<ge> dist_on G 0 m V \<Longrightarrow>
   V' = V \<union> {m} \<Longrightarrow>
   n \<in> verts G - V' \<Longrightarrow>
   has_dist_on G 0 n V' \<and> dist_on G 0 n V' = min (dist_on G 0 n V) (dist_on G 0 m V + weight G m n)"
@proof
  @have "has_dist G 0 m \<and> dist G 0 m = dist_on G 0 m V"
  @let "M = min (dist_on G 0 n V) (dist_on G 0 m V + weight G m n)"
  @have "\<forall>p\<in>path_set_on G 0 n V'. path_weight G p \<ge> M" @with
    @obtain q n' where "joinable G q [n', n]" "p = path_join G q [n', n]"
    @have "q \<in> path_set G 0 n'"
    @have "n' \<in> V'"
    @case "n' \<in> V" @with
      @have "dist_on G 0 n' V = dist G 0 n'"
      @have "path_weight G q \<ge> dist_on G 0 n' V"
      @have "path_weight G p \<ge> dist_on G 0 n' V + weight G n' n"
      @have "dist_on G 0 n' V + weight G n' n \<ge> dist_on G 0 n V"
    @end
    @have "n' = m"
    @have "path_weight G q \<ge> dist G 0 m"
    @have "path_weight G p \<ge> dist G 0 m + weight G m n"
  @end
  @case "dist_on G 0 m V + weight G m n \<ge> dist_on G 0 n V" @with
    @obtain p where "is_shortest_path_on G 0 n p V"
    @have "is_shortest_path_on G 0 n p V'" @with
      @have "p \<in> path_set_on G 0 n V'" @with @have "V \<subseteq> V'" @end
    @end
  @end
  @have "M = dist_on G 0 m V + weight G m n"
  @obtain pm where "is_shortest_path_on G 0 m pm V"
  @have "path_weight G pm = dist G 0 m"
  @let "p = path_join G pm [m, n]"
  @have "joinable G pm [m, n]"
  @have "path_weight G p = path_weight G pm + weight G m n"
  @have "is_shortest_path_on G 0 n p V'"
@qed

subsection \<open>Invariant for the Dijkstra's algorithm\<close>

text \<open>The state consists of an array maintaining the best estimates,
  and a heap containing estimates for the unknown vertices.\<close>
datatype state = State (est: "nat list") (heap: "(nat, nat) map")
setup \<open>add_simple_datatype "state"\<close>

definition unknown_set :: "state \<Rightarrow> nat set" where [rewrite]:
  "unknown_set S = keys_of (heap S)"

definition known_set :: "state \<Rightarrow> nat set" where [rewrite]:
  "known_set S = {..<length (est S)} - unknown_set S"

text \<open>Invariant: for every vertex, the estimate is at least the shortest distance.
  Furthermore, for the known vertices the estimate is exact.\<close>
definition inv :: "graph \<Rightarrow> state \<Rightarrow> bool" where [rewrite]:
  "inv G S \<longleftrightarrow> (let V = known_set S; W = unknown_set S; M = heap S in
      (length (est S) = size G \<and> known_dists G V \<and>
      keys_of M \<subseteq> verts G \<and>
      (\<forall>i\<in>W. M\<langle>i\<rangle> = Some (est S ! i)) \<and>
      (\<forall>i\<in>V. est S ! i = dist G 0 i) \<and>
      (\<forall>i\<in>verts G. est S ! i = dist_on G 0 i V)))"

lemma invE1 [forward]: "inv G S \<Longrightarrow> length (est S) = size G \<and> known_dists G (known_set S) \<and> unknown_set S \<subseteq> verts G" by auto2
lemma invE2 [forward]: "inv G S \<Longrightarrow> i \<in> known_set S \<Longrightarrow> est S ! i = dist G 0 i" by auto2
lemma invE3 [forward]: "inv G S \<Longrightarrow> i \<in> verts G \<Longrightarrow> est S ! i = dist_on G 0 i (known_set S)" by auto2
lemma invE4 [rewrite]: "inv G S \<Longrightarrow> i \<in> unknown_set S \<Longrightarrow> (heap S)\<langle>i\<rangle> = Some (est S ! i)" by auto2
setup \<open>del_prfstep_thm_str "@eqforward" @{thm inv_def}\<close>

lemma inv_unknown_set [rewrite]:
  "inv G S \<Longrightarrow> unknown_set S = verts G - known_set S" by auto2

lemma dijkstra_end_inv [forward]:
  "inv G S \<Longrightarrow> unknown_set S = {} \<Longrightarrow> \<forall>i\<in>verts G. has_dist G 0 i \<and> est S ! i = dist G 0 i" by auto2

subsection \<open>Starting state\<close>

definition dijkstra_start_state :: "graph \<Rightarrow> state" where [rewrite]:
  "dijkstra_start_state G =
     State (list (\<lambda>i. if i = 0 then 0 else weight G 0 i) (size G))
           (map_constr (\<lambda>i. i > 0) (\<lambda>i. weight G 0 i) (size G))"
setup \<open>register_wellform_data ("dijkstra_start_state G", ["size G > 0"])\<close>

lemma dijkstra_start_known_set [rewrite]:
  "size G > 0 \<Longrightarrow> known_set (dijkstra_start_state G) = {0}" by auto2
    
lemma dijkstra_start_unknown_set [rewrite]:
  "size G > 0 \<Longrightarrow> unknown_set (dijkstra_start_state G) = verts G - {0}" by auto2

lemma card_start_state [rewrite]:
  "size G > 0 \<Longrightarrow> card (unknown_set (dijkstra_start_state G)) = size G - 1"
@proof @have "0 \<in> verts G" @qed

text \<open>Starting start of Dijkstra's algorithm satisfies the invariant.\<close>
theorem dijkstra_start_inv [backward]:
  "size G > 0 \<Longrightarrow> inv G (dijkstra_start_state G)"
@proof
  @let "V = {0::nat}"
  @have "has_dist G 0 0 \<and> dist G 0 0 = 0" @with
    @have "is_shortest_path G 0 0 [0]" @end
  @have "has_dist_on G 0 0 V \<and> dist_on G 0 0 V = 0" @with
    @have "is_shortest_path_on G 0 0 [0] V" @end
  @have "V \<subseteq> verts G \<and> 0 \<in> V"
  @have (@rule) "\<forall>i\<in>verts G. i \<noteq> 0 \<longrightarrow> has_dist_on G 0 i V \<and> dist_on G 0 i V = weight G 0 i" @with
    @let "p = [0, i]"
    @have "is_shortest_path_on G 0 i p V" @with
      @have "p \<in> path_set_on G 0 i V"
      @have "\<forall>p'\<in>path_set_on G 0 i V. path_weight G p' \<ge> weight G 0 i" @with
        @obtain q n where "joinable G q [n, last p']" "p' = path_join G q [n, last p']"
        @have "n \<in> V" @have "n = 0"
        @have "path_weight G p' = path_weight G q + weight G 0 i"
      @end
    @end
  @end
@qed

subsection \<open>Step of Dijkstra's algorithm\<close>

fun dijkstra_step :: "graph \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "dijkstra_step G m (State e M) =
    (let M' = delete_map m M;
         e' = list_update_set (\<lambda>i. i \<in> keys_of M') (\<lambda>i. min (e ! m + weight G m i) (e ! i)) e;
         M'' = map_update_all (\<lambda>i. e' ! i) M'
     in State e' M'')"
setup \<open>add_rewrite_rule @{thm dijkstra_step.simps}\<close>
setup \<open>register_wellform_data ("dijkstra_step G m S", ["inv G S", "m \<in> unknown_set S"])\<close>

lemma has_dist_on_larger [backward1]:
  "has_dist G m n \<Longrightarrow> has_dist_on G m n V \<Longrightarrow> dist_on G m n V = dist G m n \<Longrightarrow>
   has_dist_on G m n (V \<union> {x}) \<and> dist_on G m n (V \<union> {x}) = dist G m n"
@proof
  @obtain p where "is_shortest_path_on G m n p V"
  @let "V' = V \<union> {x}"
  @have "p \<in> path_set_on G m n V'" @with @have "V \<subseteq> V'" @end
  @have "is_shortest_path_on G m n p V'"
@qed

lemma dijkstra_step_unknown_set [rewrite]:
  "inv G S \<Longrightarrow> m \<in> unknown_set S \<Longrightarrow> unknown_set (dijkstra_step G m S) = unknown_set S - {m}" by auto2

lemma dijkstra_step_known_set [rewrite]:
  "inv G S \<Longrightarrow> m \<in> unknown_set S \<Longrightarrow> known_set (dijkstra_step G m S) = known_set S \<union> {m}" by auto2

text \<open>One step of Dijkstra's algorithm preserves the invariant.\<close>
theorem dijkstra_step_preserves_inv [backward]:
  "inv G S \<Longrightarrow> is_heap_min m (heap S) \<Longrightarrow> inv G (dijkstra_step G m S)"
@proof
  @let "V = known_set S" "V' = V \<union> {m}"
  @have (@rule) "\<forall>i\<in>V. has_dist G 0 i \<and> has_dist_on G 0 i V' \<and> dist_on G 0 i V' = dist G 0 i"
  @have "has_dist G 0 m \<and> dist G 0 m = dist_on G 0 m V"
  @have "has_dist_on G 0 m V' \<and> dist_on G 0 m V' = dist G 0 m"
  @have (@rule) "\<forall>i\<in>verts G - V'. has_dist_on G 0 i V' \<and> dist_on G 0 i V' = min (dist_on G 0 i V) (dist_on G 0 m V + weight G m i)"
  @let "S' = dijkstra_step G m S"
  @have "known_dists G V'"
  @have "\<forall>i\<in>V'. est S' ! i = dist G 0 i"
  @have "\<forall>i\<in>verts G. est S' ! i = dist_on G 0 i V'" @with @case "i \<in> V'" @end
@qed

definition is_dijkstra_step :: "graph \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where [rewrite]:
  "is_dijkstra_step G S S' \<longleftrightarrow> (\<exists>m. is_heap_min m (heap S) \<and> S' = dijkstra_step G m S)"

lemma is_dijkstra_stepI [backward2]:
  "is_heap_min m (heap S) \<Longrightarrow> dijkstra_step G m S = S' \<Longrightarrow> is_dijkstra_step G S S'" by auto2

lemma is_dijkstra_stepD1 [forward]:
  "inv G S \<Longrightarrow> is_dijkstra_step G S S' \<Longrightarrow> inv G S'" by auto2

lemma is_dijkstra_stepD2 [forward]:
  "inv G S \<Longrightarrow> is_dijkstra_step G S S' \<Longrightarrow> card (unknown_set S') = card (unknown_set S) - 1" by auto2
setup \<open>del_prfstep_thm @{thm is_dijkstra_step_def}\<close>

end
