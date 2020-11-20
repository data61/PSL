section \<open>Directed Graphs\<close>
(* Author: Peter Lammich *)
theory Digraph
  imports 
  CAVA_Base.CAVA_Base
  Digraph_Basic
begin

subsection "Directed Graphs with Explicit Node Set and Set of Initial Nodes"

record 'v graph_rec = 
  g_V :: "'v set"
  g_E :: "'v digraph"  
  g_V0 :: "'v set"

definition graph_restrict :: "('v, 'more) graph_rec_scheme \<Rightarrow> 'v set \<Rightarrow> ('v, 'more) graph_rec_scheme"
  where "graph_restrict G R \<equiv>
  \<lparr>
    g_V = g_V G,
    g_E = rel_restrict (g_E G) R,
    g_V0 = g_V0 G - R,
    \<dots> = graph_rec.more G
  \<rparr>"

lemma graph_restrict_simps[simp]:
  "g_V (graph_restrict G R) = g_V G"
  "g_E (graph_restrict G R) = rel_restrict (g_E G) R"
  "g_V0 (graph_restrict G R) = g_V0 G - R"
  "graph_rec.more (graph_restrict G R) = graph_rec.more G"
  unfolding graph_restrict_def by auto

lemma graph_restrict_trivial[simp]: "graph_restrict G {} = G" by simp

locale graph_defs =
  fixes G :: "('v, 'more) graph_rec_scheme"
begin

  abbreviation "V \<equiv> g_V G"
  abbreviation "E \<equiv> g_E G"
  abbreviation "V0 \<equiv> g_V0 G"

  abbreviation "reachable \<equiv> E\<^sup>* `` V0"
  abbreviation "succ v \<equiv> E `` {v}"

  lemma finite_V0: "finite reachable \<Longrightarrow> finite V0" by (auto intro: finite_subset)

  definition is_run
    \<comment> \<open>Infinite run, i.e., a rooted infinite path\<close>
    where "is_run r \<equiv> r 0 \<in> V0 \<and> ipath E r"

  lemma run_ipath: "is_run r \<Longrightarrow> ipath E r" unfolding is_run_def by auto
  lemma run_V0: "is_run r \<Longrightarrow> r 0 \<in> V0" unfolding is_run_def by auto

  lemma run_reachable: "is_run r \<Longrightarrow> range r \<subseteq> reachable"
    unfolding is_run_def using ipath_to_rtrancl by blast

end

locale graph =
  graph_defs G
  for G :: "('v, 'more) graph_rec_scheme"
  +
  assumes V0_ss: "V0 \<subseteq> V"
  assumes E_ss: "E \<subseteq> V \<times> V"
begin

  lemma reachable_V: "reachable \<subseteq> V" using V0_ss E_ss by (auto elim: rtrancl_induct)

  lemma finite_E: "finite V \<Longrightarrow> finite E" using finite_subset E_ss by auto

end

(* TODO: finite reachability is handled using loose assumptions, while finitely branching
  graphs are captured using a locale. it may be advantageous to unify this. *)
locale fb_graph =
  graph G
  for G :: "('v, 'more) graph_rec_scheme"
  +
  assumes finite_V0[simp, intro!]: "finite V0"
  assumes finitely_branching[simp, intro]: "v \<in> reachable \<Longrightarrow> finite (succ v)"
begin

  lemma fb_graph_subset:
    assumes "g_V G' = V"
    assumes "g_E G' \<subseteq> E"
    assumes "finite (g_V0 G')"
    assumes "g_V0 G' \<subseteq> reachable"
    shows "fb_graph G'"
  proof
    show "g_V0 G' \<subseteq> g_V G'" using reachable_V assms(1, 4) by simp
    show "g_E G' \<subseteq> g_V G' \<times> g_V G'" using E_ss assms(1, 2) by simp
    show "finite (g_V0 G')" using assms(3) by this
  next
    fix v
    assume 1: "v \<in> (g_E G')\<^sup>* `` g_V0 G'"
    obtain u where 2: "u \<in> g_V0 G'" "(u, v) \<in> (g_E G')\<^sup>*" using 1 by rule
    have 3: "u \<in> reachable" "(u, v) \<in> E\<^sup>*" using rtrancl_mono assms(2, 4) 2 by auto
    have 4: "v \<in> reachable" using rtrancl_image_advance_rtrancl 3 by metis
    have 5: "finite (E `` {v})" using 4 by rule
    have 6: "g_E G' `` {v} \<subseteq> E `` {v}" using assms(2) by auto
    show "finite (g_E G' `` {v})" using finite_subset 5 6 by auto
  qed

  lemma fb_graph_restrict: "fb_graph (graph_restrict G R)"
    by (rule fb_graph_subset, auto simp: rel_restrict_sub)

end

lemma (in graph) fb_graphI_fr:
  assumes "finite reachable"
  shows "fb_graph G"
proof
  from assms show "finite V0" by (rule finite_subset[rotated]) auto
  fix v
  assume "v \<in> reachable"
  hence "succ v \<subseteq> reachable" by (metis Image_singleton_iff rtrancl_image_advance subsetI)
  thus "finite (succ v)" using assms by (rule finite_subset)
qed

abbreviation "rename_E f E \<equiv> (\<lambda>(u,v). (f u, f v))`E"

definition "fr_rename_ext ecnv f G \<equiv> \<lparr> 
    g_V = f`(g_V G),
    g_E = rename_E f (g_E G),   
    g_V0 = (f`g_V0 G),
    \<dots> = ecnv G
  \<rparr>"

locale g_rename_precond =
  graph G
  for G :: "('u,'more) graph_rec_scheme"
  +
  fixes f :: "'u \<Rightarrow> 'v"
  fixes ecnv :: "('u, 'more) graph_rec_scheme \<Rightarrow> 'more'"
  assumes INJ: "inj_on f V"
begin

  abbreviation "G' \<equiv> fr_rename_ext ecnv f G"

  lemma G'_fields:
    "g_V G' = f`V"
    "g_V0 G' = f`V0"
    "g_E G' = rename_E f E"
    unfolding fr_rename_ext_def by simp_all

  definition "fi \<equiv> the_inv_into V f"

  lemma 
    fi_f: "x\<in>V \<Longrightarrow> fi (f x) = x" and
    f_fi: "y\<in>f`V \<Longrightarrow> f (fi y) = y" and
    fi_f_eq: "\<lbrakk>f x = y; x\<in>V\<rbrakk> \<Longrightarrow> fi y = x"
    unfolding fi_def
    by (auto 
      simp: the_inv_into_f_f f_the_inv_into_f the_inv_into_f_eq INJ)

  lemma E'_to_E: "(u,v) \<in> g_E G' \<Longrightarrow> (fi u, fi v)\<in>E"
    using E_ss
    by (auto simp: fi_f G'_fields)

  lemma V0'_to_V0: "v\<in>g_V0 G' \<Longrightarrow> fi v \<in> V0"
    using V0_ss
    by (auto simp: fi_f G'_fields)


  lemma rtrancl_E'_sim:
    assumes "(f u,v')\<in>(g_E G')\<^sup>*"
    assumes "u\<in>V"
    shows "\<exists>v. v' = f v \<and> v\<in>V \<and> (u,v)\<in>E\<^sup>*"
    using assms
  proof (induction "f u" v' arbitrary: u)
    case (rtrancl_into_rtrancl v' w' u)
    then obtain v w where "v' = f v" "w' = f w" "(v,w)\<in>E"
      by (auto simp: G'_fields)
    hence "v\<in>V" "w\<in>V" using E_ss by auto
    from rtrancl_into_rtrancl obtain vv where "v' = f vv" "vv\<in>V" "(u,vv)\<in>E\<^sup>*"
      by blast
    from \<open>v' = f v\<close> \<open>v\<in>V\<close> \<open>v' = f vv\<close> \<open>vv\<in>V\<close> have [simp]: "vv = v"
      using INJ by (metis inj_on_contraD)

    note \<open>(u,vv)\<in>E\<^sup>*\<close>[simplified]
    also note \<open>(v,w)\<in>E\<close>
    finally show ?case using \<open>w' = f w\<close> \<open>w\<in>V\<close> by blast
  qed auto
    
  lemma rtrancl_E'_to_E: assumes "(u,v)\<in>(g_E G')\<^sup>*" shows "(fi u, fi v)\<in>E\<^sup>*"
    using assms apply induction
    by (fastforce intro: E'_to_E rtrancl_into_rtrancl)+

  lemma G'_invar: "graph G'"
    apply unfold_locales
  proof -
    show "g_V0 G' \<subseteq> g_V G'"
      using V0_ss by (auto simp: G'_fields) []

    show "g_E G' \<subseteq> g_V G' \<times> g_V G'"
      using E_ss by (auto simp: G'_fields) []
  qed

  sublocale G': graph G' using G'_invar .

  lemma G'_finite_reachable:
    assumes "finite ((g_E G)\<^sup>* `` g_V0 G)"
    shows "finite ((g_E G')\<^sup>* `` g_V0 G')"
  proof -
    have "(g_E G')\<^sup>* `` g_V0 G' \<subseteq> f ` (E\<^sup>*``V0)"
      apply (clarsimp_all simp: G'_fields(2))
      apply (drule rtrancl_E'_sim)
      using V0_ss apply auto []
      apply auto
      done
    thus ?thesis using finite_subset assms by blast
  qed

  lemma V'_to_V: "v \<in> G'.V \<Longrightarrow> fi v \<in> V"
    by (auto simp: fi_f G'_fields)

  lemma ipath_sim1: "ipath E r \<Longrightarrow> ipath G'.E (f o r)"
    unfolding ipath_def by (auto simp: G'_fields)

  lemma ipath_sim2: "ipath G'.E r \<Longrightarrow> ipath E (fi o r)"
    unfolding ipath_def 
    apply (clarsimp simp: G'_fields)
    apply (drule_tac x=i in spec)
    using E_ss
    by (auto simp: fi_f)

  lemma run_sim1: "is_run r \<Longrightarrow> G'.is_run (f o r)"
    unfolding is_run_def G'.is_run_def
    apply (intro conjI)
    apply (auto simp: G'_fields) []
    apply (auto simp: ipath_sim1)
    done

  lemma run_sim2: "G'.is_run r \<Longrightarrow> is_run (fi o r)"
    unfolding is_run_def G'.is_run_def
    by (auto simp: ipath_sim2 V0'_to_V0)

end


end
