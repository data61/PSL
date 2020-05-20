(*  Title:       Executable Transitive Closures of Finite Relations
    Author:      Christian Sternagel <c.sternagel@gmail.com>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

section \<open>Closure Computation via Red Black Trees\<close>

theory Transitive_Closure_RBT_Impl
imports
  Transitive_Closure_Impl
  RBT_Map_Set_Extension
begin

text \<open>
  We provide two algorithms to compute the reflexive transitive closure which internally work on red
  black trees. Therefore, the carrier has to be linear ordered. The first one (@{term
  rtrancl_rbt_impl}) computes the closure on demand for a given set of initial states. The second
  one (@{term memo_rbt_rtrancl}) precomputes the closure for each individual state, stores the
  results, and then only does a look-up.
  
  For the transitive closure there are the corresponding algorithms @{term trancl_rbt_impl} and
  @{term memo_rbt_trancl}
\<close>

subsection \<open>Computing Closures from Sets On-The-Fly\<close> 

text \<open>
  The algorithms are based on the generic algorithms @{const rtrancl_impl} and @{const trancl_impl}
  using red black trees. To compute the successors efficiently, all successors of a state are
  collected and stored in a red black tree map by using @{const elem_list_to_rm}. Then, to lift the
  successor relation for single states to lists of states, all results are united using @{const
  rs_Union}. The rest is standard.
\<close>

interpretation set_access "\<lambda> as bs. rs.union bs (rs.from_list as)" rs.\<alpha> rs.memb "rs.empty ()"
  by (unfold_locales, auto simp: rs.correct)

abbreviation rm_succ :: "('a :: linorder \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "rm_succ \<equiv> (\<lambda> r. let rm = elem_list_to_rm fst r in
    (\<lambda> as. rs.to_list (rs_Union (map (\<lambda> a. rs.from_list (map snd (rm_set_lookup rm a))) as))))"

definition rtrancl_rbt_impl :: "('a :: linorder \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a rs"
where
  "rtrancl_rbt_impl = rtrancl_impl rm_succ
    (\<lambda> as bs. rs.union bs (rs.from_list as)) rs.memb (rs.empty ())" 

definition trancl_rbt_impl :: "('a :: linorder \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a rs"
where
  "trancl_rbt_impl = trancl_impl rm_succ
    (\<lambda> as bs. rs.union bs (rs.from_list as)) rs.memb (rs.empty ())" 

lemma rtrancl_rbt_impl:
  "rs.\<alpha> (rtrancl_rbt_impl r as) = {b. \<exists> a \<in> set as. (a,b) \<in> (set r)\<^sup>*}"
  unfolding rtrancl_rbt_impl_def
  by (rule set_access_gen.rtrancl_impl, unfold_locales, unfold Let_def, simp add: rs.correct elem_list_to_rm.rm_set_lookup, force)

lemma trancl_rbt_impl:
  "rs.\<alpha> (trancl_rbt_impl r as) = {b. \<exists> a \<in> set as. (a,b) \<in> (set r)\<^sup>+}"
  unfolding trancl_rbt_impl_def
  by (rule set_access_gen.trancl_impl, unfold_locales, unfold Let_def, simp add: rs.correct elem_list_to_rm.rm_set_lookup, force)

subsection \<open>Precomputing Closures for Single States\<close>

text \<open>
  Storing all relevant entries is done by mapping all left-hand sides of the relation to their
  closure. Since we assume a linear order on the carrier, for the lookup we can use maps that are
  implemented as red black trees.
\<close>

definition memo_rbt_rtrancl :: "('a :: linorder \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a rs)"
where
  "memo_rbt_rtrancl r =
    (let 
      tr = rtrancl_rbt_impl r;
      rm = rm.to_map (map (\<lambda> a. (a, tr [a])) ((rs.to_list \<circ> rs.from_list \<circ> map fst) r))
    in
      (\<lambda>a. case rm.lookup a rm of 
        None \<Rightarrow> rs.from_list [a] 
      | Some as \<Rightarrow> as))"

lemma memo_rbt_rtrancl:
  "rs.\<alpha> (memo_rbt_rtrancl r a) = {b. (a, b) \<in> (set r)\<^sup>*}" (is "?l = ?r")
proof -
  let ?rm = "rm.to_map
    (map (\<lambda>a. (a, rtrancl_rbt_impl r [a])) ((rs.to_list \<circ> rs.from_list \<circ> map fst) r))"
  show ?thesis
  proof (cases "rm.lookup a ?rm")
    case None
    have one: "?l = {a}"
      unfolding memo_rbt_rtrancl_def Let_def None
      by (simp add: rs.correct)
    from None [unfolded rm.lookup_correct [OF rm.invar], simplified rm.correct map_of_eq_None_iff]
    have a: "a \<notin> fst ` set r" by (simp add: rs.correct, force)
    {
      fix b
      assume "b \<in> ?r"
      from this [unfolded rtrancl_power relpow_fun_conv] obtain n f where 
        ab: "f 0 = a \<and> f n = b" and steps: "\<And> i. i < n \<Longrightarrow> (f i, f (Suc i)) \<in> set r" by auto
      from ab steps [of 0] a have "b = a" 
        by (cases n, force+)
    }
    then have "?r = {a}" by auto
    then show ?thesis unfolding one by simp
  next
    case (Some as) 
    have as: "rs.\<alpha> as = {b. (a,b) \<in> (set r)\<^sup>*}"
      using map_of_SomeD [OF Some [unfolded rm.lookup_correct [OF rm.invar], simplified rm.correct]]
        rtrancl_rbt_impl [of r "[a]"] by force
    then show ?thesis unfolding memo_rbt_rtrancl_def Let_def Some by simp
  qed
qed

definition memo_rbt_trancl :: "('a :: linorder \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a rs)" 
where
  "memo_rbt_trancl r =
    (let
      tr = trancl_rbt_impl r;
      rm = rm.to_map (map (\<lambda> a. (a, tr [a])) ((rs.to_list \<circ> rs.from_list \<circ> map fst) r))
    in (\<lambda> a.
      (case rm.lookup a rm of
        None \<Rightarrow> rs.empty ()
      | Some as \<Rightarrow> as)))"

lemma memo_rbt_trancl:
  "rs.\<alpha> (memo_rbt_trancl r a) = {b. (a, b) \<in> (set r)\<^sup>+}" (is "?l = ?r")
proof -
  let ?rm = "rm.to_map
    (map (\<lambda> a. (a, trancl_rbt_impl r [a])) ((rs.to_list \<circ> rs.from_list \<circ> map fst) r))"
  show ?thesis
  proof (cases "rm.lookup a ?rm")
    case None
    have one: "?l = {}"
      unfolding memo_rbt_trancl_def Let_def None
      by (simp add: rs.correct)
    from None [unfolded rm.lookup_correct [OF rm.invar], simplified rm.correct map_of_eq_None_iff]
    have a: "a \<notin> fst ` set r" by (simp add: rs.correct, force)
    {
      fix b
      assume "b \<in> ?r"
      from this [unfolded trancl_unfold_left] a have False by force
    }
    then have "?r = {}" by auto
    then show ?thesis unfolding one by simp
  next
    case (Some as) 
    have as: "rs.\<alpha> as = {b. (a,b) \<in> (set r)\<^sup>+}"
      using map_of_SomeD [OF Some [unfolded rm.lookup_correct [OF rm.invar], simplified rm.correct]]
        trancl_rbt_impl [of r "[a]"] by force
    then show ?thesis unfolding memo_rbt_trancl_def Let_def Some by simp
  qed
qed

end
