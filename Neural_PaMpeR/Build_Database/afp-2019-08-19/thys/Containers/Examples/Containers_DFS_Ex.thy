(* Title:      Containers/Examples/Containers_DFS_Ex.thy
   Author:     Andreas Lochbihler, ETH Zurich *)

section \<open>Formalisation of depth-first search using Containers\<close>

theory Containers_DFS_Ex imports
  "../Containers"
  "HOL-Library.Transitive_Closure_Table"
begin

subsection \<open>Auxiliary stuff\<close>

definition restrict :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set" (infixl "\<upharpoonleft>" 60)
where "R \<upharpoonleft> A = {(a, b) \<in> R. b \<in> A}"

lemma in_restrict [iff]: "(a, b) \<in> R \<upharpoonleft> A \<longleftrightarrow> (a, b) \<in> R \<and> b \<in> A"
by(simp add: restrict_def)

lemma restrict_UNIV [simp]: "R \<upharpoonleft> UNIV = R"
by auto

lemma restrict_restrict [simp]: "R \<upharpoonleft> A \<upharpoonleft> B = R \<upharpoonleft> (A \<inter> B)"
by auto

lemma rtrancl_restrict_reachable:
  assumes x: "(x, y) \<in> R\<^sup>*"
  and z: "(z, y) \<notin> R\<^sup>*"
  shows "(x, y) \<in> (R \<upharpoonleft> - R\<^sup>* `` {z})\<^sup>*"
using x
proof(induction rule: converse_rtrancl_induct)
  case (step x x')
  from \<open>(x, x') \<in> R\<close> z \<open>(x', y) \<in> R\<^sup>*\<close>
  have "(x, x') \<in> R \<upharpoonleft> - R\<^sup>* `` {z}" by(auto intro: rtrancl_trans converse_rtrancl_into_rtrancl)
  thus ?case using step.IH by(rule converse_rtrancl_into_rtrancl)
qed simp

lemma rtrancl_restrict_start:
  assumes "(x, y) \<in> R\<^sup>*"
  shows "(x, y) \<in> (R \<upharpoonleft> - {x})\<^sup>*"
proof -
  let ?R = "\<lambda>x y. (x, y) \<in> R"
  define z where "z \<equiv> x"
  with assms obtain xs where "rtrancl_path ?R x xs y" "z \<notin> set xs"
    by(auto simp add: rtrancl_def rtranclp_eq_rtrancl_path elim: rtrancl_path_distinct)
  thus "(x, y) \<in> (R \<upharpoonleft> - {z})\<^sup>*"
    by induction(auto intro: converse_rtrancl_into_rtrancl)
qed

lemma (in comp_fun_commute) fold_set_union_disj: (* Move to distribution *)
  assumes "finite A" "finite B" "A \<inter> B = {}"
  shows "Finite_Set.fold f z (A \<union> B) = Finite_Set.fold f (Finite_Set.fold f z A) B"
using assms(2,1,3) by induction simp_all

lemma Image_insert [simp]:
  fixes A :: "'a set"
  assumes "NO_MATCH ({} :: 'a set) A"
  shows "R `` insert x A = R `` {x} \<union> (R `` A)"
by(auto)

subsection \<open>Declarative definition\<close>

datatype 'a dfs_result = is_Reachable: Reachable | Visited "'a set"

context fixes E :: "('a \<times> 'a) set" begin

definition reachable :: "'a => 'a => bool"
where "reachable src tgt \<longleftrightarrow> (src, tgt) \<in> E\<^sup>*"

text \<open>
  We avoid the non-determinism of visited nodes in depth-first search by only returning
  the set of visited nodes when the search fails, because in that case it contains all reachable
  nodes and therefore is deterministic again.
\<close>

definition dfs :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a dfs_result"
where 
  "dfs src tgt visited =
  (if tgt \<in> (E \<upharpoonleft> - visited)\<^sup>* `` {src} then Reachable else Visited (visited \<union> (E \<upharpoonleft> - visited)\<^sup>* `` {src}))"

subsection \<open>Derivation of the recursion equation\<close>

context
  fixes tgt :: 'a and loop
  defines "loop \<equiv> \<lambda>x r. case r of Reachable \<Rightarrow> Reachable | Visited \<V> \<Rightarrow> 
    if x \<in> \<V> then Visited \<V> else dfs x tgt \<V>"
begin

private lemma loop_simps:
  "loop x Reachable = Reachable"
  "loop x (Visited \<V>) = (if x \<in> \<V> then Visited \<V> else dfs x tgt \<V>)"
by(simp_all add: loop_def)

context notes [simp] = loop_simps begin

lemma comp_fun_commute_dfs_body: "comp_fun_commute loop"
by(unfold_locales)(auto simp add: loop_def dfs_def fun_eq_iff intro: rtrancl_mono[THEN subsetD, rotated] rtrancl_trans dest: rtrancl_restrict_reachable split: dfs_result.split)

interpretation f: comp_fun_commute loop
by(rule comp_fun_commute_dfs_body)

lemma fold_dfs_Reachable [simp]:
  "Finite_Set.fold loop Reachable A = Reachable"
proof(cases "finite A")
  case True thus ?thesis by(induction) auto
qed simp

lemma dfs_blocked:
  assumes "finite A"
  and "E `` A \<subseteq> visited" "tgt \<notin> A"
  shows "Finite_Set.fold loop (Visited visited) A = Visited (A \<union> visited)"
using assms by induction(auto elim: converse_rtranclE simp add: dfs_def)

lemma dfs_visited:
  assumes "finite A"
  and "A \<subseteq> visited"
  shows "Finite_Set.fold loop (Visited visited) A = Visited visited"
using assms by induction(auto)

lemma dfs_rec:
  "dfs src tgt visited =
  (if src = tgt then Reachable
   else let succs = E `` {src} in if finite succs then Finite_Set.fold loop (Visited (insert src visited)) succs
   else Code.abort (STR ''infinite successor relation'') (\<lambda>_. dfs src tgt visited))"
proof(cases "src \<noteq> tgt \<and> finite (E `` {src})")
  case False
  thus ?thesis by(auto simp add: dfs_def)
next
  case True
  hence [simp]: "src \<noteq> tgt" "tgt \<noteq> src"
    and fin: "finite (E `` {src})" by auto

  show ?thesis
  proof(cases "(src, tgt) \<in> (E \<upharpoonleft> - visited)\<^sup>*")
    case True
    let ?g = "\<lambda>x y. (x, y) \<in> E \<upharpoonleft> - visited"
    have "Finite_Set.fold loop (Visited (insert src visited)) (E `` {src}) = 
      Finite_Set.fold loop (Finite_Set.fold loop (Visited (insert src visited)) (E `` {src} - insert src visited)) (E `` {src} \<inter> insert src visited)"
      using fin by(subst f.fold_set_union_disj[symmetric])(auto intro: arg_cong2[where f="Finite_Set.fold loop"])
    also from True obtain xs where "rtrancl_path ?g src xs tgt" "distinct (src # xs)"
      by(auto simp add: rtrancl_def rtranclp_eq_rtrancl_path elim: rtrancl_path_distinct)
    hence "Finite_Set.fold loop (Visited (insert src visited)) (E `` {src} - insert src visited) = Reachable"
      using \<open>src \<noteq> tgt\<close> fin
    proof(induction src xs z\<equiv>tgt)
      case (step x y xs)
      let ?succs = "E `` {x} - visited - {y,x}"
    
      have "Finite_Set.fold loop (Visited (insert x visited)) (insert y ?succs) =
            Finite_Set.fold loop (loop y (Visited (insert x visited))) ?succs"
        by(rule f.fold_insert2)(simp_all add: \<open>finite (E `` {x})\<close>)
      also
      from \<open>distinct (x # y # xs)\<close> have "x \<notin> set (y # xs)" by simp
      with \<open>rtrancl_path ?g y xs tgt\<close>
      have "(y, tgt) \<in> (E \<upharpoonleft> - insert x visited)\<^sup>*"
        by induction(auto intro: converse_rtrancl_into_rtrancl)
      with \<open>(x, y) \<in> E \<upharpoonleft> - visited\<close> have "loop y (Visited (insert x visited)) = Reachable" 
        using \<open>x \<notin> set (y # xs)\<close> by(auto simp add: dfs_def)
      also from \<open>(x, y) \<in> E \<upharpoonleft> - visited\<close>
      have "insert y ?succs = E `` {x} - insert x visited"
        using \<open>distinct (x # y # xs)\<close> by auto
      finally show ?case by simp
    qed simp
    finally show ?thesis using True by(simp add: dfs_def Let_def)
  next
    case False
    have "Finite_Set.fold loop (Visited (insert src visited)) (E `` {src}) = 
      Finite_Set.fold loop (Finite_Set.fold loop (Visited (insert src visited)) (E `` {src} - insert src visited)) (E `` {src} \<inter> insert src visited)"
      using fin by(subst f.fold_set_union_disj[symmetric])(auto intro: arg_cong2[where f="Finite_Set.fold loop"])
    also from fin have "finite (E `` {src} - visited)" by simp
    then have "Finite_Set.fold loop (Visited (insert src visited)) (E `` {src} - insert src visited) = Visited (visited \<union> (E \<upharpoonleft> - visited)\<^sup>* `` {src})"
      using False
    proof(induct A\<equiv>"E `` {src} - visited" arbitrary: visited rule: finite_psubset_induct)
      case psubset
      note fin = \<open>finite (E `` {src})\<close>
      note src_tgt = \<open>(src, tgt) \<notin> (E \<upharpoonleft> - visited)\<^sup>*\<close>
      show ?case
      proof (cases "E `` {src} - insert src visited = {}")
        case True
        { let ?g = "\<lambda>x y. (x, y) \<in> E \<upharpoonleft> - visited"
          fix x
          assume "(src, x) \<in> (E \<upharpoonleft> - visited)\<^sup>*"
          then obtain xs where "rtrancl_path ?g src xs x" "distinct (src # xs)"
            by(auto simp add: rtrancl_def rtranclp_eq_rtrancl_path elim: rtrancl_path_distinct)
          hence "src = x" using True by induction auto }
        then show ?thesis unfolding True using True
          by(auto elim: converse_rtranclE)
      next
        case False
        then obtain y where y: "y \<in> E `` {src}" "y \<notin> visited" "y \<noteq> src" by auto
        let ?succs = "E `` {src} - insert src visited - {y}"
        let ?visited = "insert src visited"
        let ?visited' = "?visited \<union> (E \<upharpoonleft> - insert src visited)\<^sup>* `` {y}"
        have "Finite_Set.fold loop (Visited ?visited) (insert y ?succs) =
              Finite_Set.fold loop (loop y (Visited ?visited)) ?succs"
          by(rule f.fold_insert2)(simp_all add: fin)
        also have y_tgt: "(y, tgt) \<notin> (E \<upharpoonleft> - ?visited)\<^sup>*" using y src_tgt
          by(auto intro: converse_rtrancl_into_rtrancl rtrancl_mono[THEN subsetD, rotated])
        hence "loop y (Visited (insert src visited)) = Visited ?visited'"
          using y by(auto simp add: dfs_def)
        also define A where "A \<equiv> ?succs \<inter> (E \<upharpoonleft> - insert src visited)\<^sup>* `` {y}"
        have "?succs = A \<union> (E `` {src} - insert src ?visited')" unfolding A_def using y by auto
        hence "Finite_Set.fold loop (Visited ?visited') ?succs =
               Finite_Set.fold loop (Visited ?visited') \<dots>" by simp
        also have "\<dots> = Finite_Set.fold loop (Finite_Set.fold loop (Visited ?visited') A) (E `` {src} - insert src ?visited')"
          by(rule f.fold_set_union_disj)(auto simp add: A_def intro: finite_subset[OF _ fin])
        also {
          from fin have "finite A" unfolding A_def
            by(rule finite_subset[rotated]) auto
          moreover have "E `` A \<subseteq> ?visited'" using y unfolding A_def
            by(auto intro: rtrancl_into_rtrancl)
          moreover have "tgt \<notin> A" unfolding A_def using y_tgt by auto
          ultimately have "Finite_Set.fold loop (Visited ?visited') A = (Visited (A \<union> ?visited'))"
            by(rule dfs_blocked) }
        also have "A \<union> ?visited' = insert src ?visited'" unfolding A_def by auto
        also { 
          have "E `` {src} - ?visited' \<subset> E `` {src} - visited" using y by fastforce
          moreover have "(src, tgt) \<notin> (E \<upharpoonleft> - ?visited')\<^sup>*" using \<open>(src, tgt) \<notin> (E \<upharpoonleft> - visited)\<^sup>*\<close>
            by(auto intro: rtrancl_mono[THEN subsetD, rotated])
          ultimately
          have "Finite_Set.fold loop (Visited (insert src ?visited')) (E `` {src} - insert src ?visited') =
                Visited (?visited' \<union> (E \<upharpoonleft> - ?visited')\<^sup>* `` {src})"
            by(rule psubset.hyps) }
        also {
          fix x
          assume src_x: "(src, x) \<in> (E \<upharpoonleft> - visited)\<^sup>*"
            and y_x: "(y, x) \<notin> (E \<upharpoonleft> - insert src visited)\<^sup>*"
          from src_x have "(src, x) \<in> (E \<upharpoonleft> - ?visited)\<^sup>*"
            by (metis rtrancl_restrict_start Compl_insert Containers_DFS_Ex.restrict_restrict Diff_Compl double_complement)
          from rtrancl_restrict_reachable[OF this y_x]
          have "(src, x) \<in> (E \<upharpoonleft> - ?visited')\<^sup>*" by simp (metis Un_insert_left compl_sup) }
        then have "?visited' \<union> (E \<upharpoonleft> - ?visited')\<^sup>* `` {src} = visited \<union> (E \<upharpoonleft> - visited)\<^sup>* `` {src}"
          using y by(auto intro: converse_rtrancl_into_rtrancl rtrancl_mono[THEN subsetD, rotated])
        also have "insert y ?succs = E `` {src} - insert src visited" using y by auto
        finally show ?thesis .
      qed
    qed
    finally
    show ?thesis using False fin
      by(simp add: dfs_def Let_def)(subst dfs_visited; auto)
  qed
qed

end

end

lift_definition dfs_body :: "'a \<Rightarrow> ('a, 'a dfs_result) comp_fun_commute"
is "\<lambda>tgt x r. case r of Reachable \<Rightarrow> Reachable | Visited \<V> \<Rightarrow> if x \<in> \<V> then Visited \<V> else dfs x tgt \<V>"
 by(rule comp_fun_commute_dfs_body)

lemma dfs_code [code]:
  "dfs src tgt visited =
  (if src = tgt then Reachable
   else let S = E `` {src} in 
   if finite S then set_fold_cfc (dfs_body tgt) (Visited (insert src visited)) S
   else Code.abort (STR ''infinite successor relation'') (\<lambda>_. dfs src tgt visited))"
by transfer(subst dfs_rec, simp add: Let_def)

lemma reachable_dfs [code]:
  "reachable src tgt = is_Reachable (dfs src tgt {})"
by(simp add: dfs_def reachable_def)

end

subsection \<open>Refinement to executable code\<close>

typedef 'a graph = "UNIV :: ('a \<times> 'a) set set" morphisms edges Graph ..
setup_lifting type_definition_graph

text \<open>Implement graphs with successor function\<close>

definition graph_of_succs :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<times> 'a) set"
where "graph_of_succs succs = {(v, w). w \<in> succs v}"
declare graph_of_succs_def[containers_post, symmetric, containers_pre]

lift_definition Succ :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a graph" is "graph_of_succs" .
code_datatype Succ

text \<open>Identify operations on graph\<close>

definition successors :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set" where "successors E x = E `` {x}"
declare successors_def[containers_post, symmetric, containers_pre]

lift_definition succs :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a set" is successors .
lemma succs_code [code]: "succs (Succ s) = s" by transfer(simp add: successors_def fun_eq_iff graph_of_succs_def)

text \<open>Transfer algorithms to abstract graph type\<close>

lift_definition reachable_impl :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" is reachable .
lift_definition dfs_impl :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a dfs_result" is dfs .
lift_definition dfs_body_impl :: "'a graph \<Rightarrow> 'a \<Rightarrow> ('a, 'a dfs_result) comp_fun_commute" is dfs_body .

lemmas [containers_identify, code] = reachable_dfs dfs_code dfs_body.rep_eq

subsection \<open>Tests\<close>

definition test_graph :: "nat graph"
where "test_graph = Succ ((\<lambda>_. {})(0 := {1,3}, 1 := {2,4}, 2 := {1}, 3 := {1, 5}, 4 := {5}))"

definition test_dfs where "test_dfs = map (reachable_impl test_graph 0) [0..<7]"

ML_val \<open>
  val [true, true, true, true, true, true, false] = @{code test_dfs};
\<close>

end
