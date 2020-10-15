(*  Title:       Executable Transitive Closures of Finite Relations
    Author:      Christian Sternagel <c.sternagel@gmail.com>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

section \<open>Closure Computation using Lists\<close>

theory Transitive_Closure_List_Impl
imports Transitive_Closure_Impl
begin

text \<open>
  We provide two algorithms for the computation of the reflexive transitive closure which internally
  work on lists. The first one (@{term rtrancl_list_impl}) computes the closure on demand for a
  given set of initial states. The second one (@{term memo_list_rtrancl}) precomputes the closure
  for each individual state, stores the result, and then only does a look-up.
  
  For the transitive closure there are the corresponding algorithms @{term trancl_list_impl} and
  @{term memo_list_trancl}.
\<close>

subsection \<open>Computing Closures from Sets On-The-Fly\<close>

text \<open>
  The algorithms are based on the generic algorithms @{const rtrancl_impl} and @{const trancl_impl}
  instantiated by list operations. Here, after computing the successors in a straightforward way,
  we use @{const remdups} to not have duplicates in the results. Moreover, also in the union
  operation we filter to those elements that have not yet been seen. The use of @{const filter} in
  the union operation is preferred over @{const remdups} since by construction the latter set will
  not contain duplicates.
\<close>

definition rtrancl_list_impl :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "rtrancl_list_impl = rtrancl_impl
    (\<lambda> r as. remdups (map snd (filter (\<lambda> (a, b). a \<in> set as) r)))
    (\<lambda> xs ys. (filter (\<lambda> x. x \<notin> set ys) xs) @ ys)
    (\<lambda> x xs. x \<in> set xs)
    []"

definition trancl_list_impl :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "trancl_list_impl = trancl_impl
    (\<lambda> r as. remdups (map snd (filter (\<lambda> (a, b). a \<in> set as) r)))
    (\<lambda> xs ys. (filter (\<lambda> x. x \<notin> set ys) xs) @ ys)
    (\<lambda> x xs. x \<in> set xs)
    []"

lemma rtrancl_list_impl:
  "set (rtrancl_list_impl r as) = {b. \<exists> a \<in> set as. (a, b) \<in> (set r)\<^sup>*}"
  unfolding rtrancl_list_impl_def
  by (rule set_access_gen.rtrancl_impl, unfold_locales, force+)

lemma trancl_list_impl:
  "set (trancl_list_impl r as) = {b. \<exists> a \<in> set as. (a, b) \<in> (set r)\<^sup>+}"
  unfolding trancl_list_impl_def
  by (rule set_access_gen.trancl_impl, unfold_locales, force+)


subsection \<open>Precomputing Closures for Single States\<close>

text \<open>
  Storing all relevant entries is done by mapping all left-hand sides of the relation to their
  closure. To avoid redundant entries, @{const remdups} is used.
\<close>

definition memo_list_rtrancl :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a list)"
where
  "memo_list_rtrancl r =
    (let
      tr = rtrancl_list_impl r;
      rm = map (\<lambda>a. (a, tr [a])) ((remdups \<circ> map fst) r)
    in
      (\<lambda>a. case map_of rm a of
        None \<Rightarrow> [a]
      | Some as \<Rightarrow> as))"

lemma memo_list_rtrancl:
  "set (memo_list_rtrancl r a) = {b. (a, b) \<in> (set r)\<^sup>*}" (is "?l = ?r")
proof -
  let ?rm = "map (\<lambda> a. (a, rtrancl_list_impl r [a])) ((remdups \<circ> map fst) r)"
  show ?thesis
  proof (cases "map_of ?rm a")
    case None
    have one: "?l = {a}"
      unfolding memo_list_rtrancl_def Let_def None
      by auto
    from None [unfolded map_of_eq_None_iff]
    have a: "a \<notin> fst ` set r" by force
    {
      fix b
      assume "b \<in> ?r"
      from this [unfolded rtrancl_power relpow_fun_conv] obtain n f where 
        ab: "f 0 = a \<and> f n = b" and steps: "\<And> i. i < n \<Longrightarrow> (f i, f (Suc i)) \<in> set r" by auto
      from ab steps [of 0] a have "a = b" 
        by (cases n, force+)
    }
    then have "?r = {a}" by auto
    then show ?thesis unfolding one by simp
  next
    case (Some as) 
    have as: "set as = {b. (a, b) \<in> (set r)^*}"
      using map_of_SomeD [OF Some]
        rtrancl_list_impl [of r "[a]"] by force
    then show ?thesis unfolding memo_list_rtrancl_def Let_def Some by simp
  qed
qed

definition memo_list_trancl :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a list)"
where
  "memo_list_trancl r =
    (let
      tr = trancl_list_impl r;
      rm = map (\<lambda>a. (a, tr [a])) ((remdups \<circ> map fst) r)
    in
      (\<lambda>a. case map_of rm a of
        None \<Rightarrow> []
      | Some as \<Rightarrow> as))"

lemma memo_list_trancl:
  "set (memo_list_trancl r a) = {b. (a, b) \<in> (set r)\<^sup>+}" (is "?l = ?r")
proof -
  let ?rm = "map (\<lambda> a. (a, trancl_list_impl r [a])) ((remdups \<circ> map fst) r)"
  show ?thesis
  proof (cases "map_of ?rm a")
    case None
    have one: "?l = {}"
      unfolding memo_list_trancl_def Let_def None
      by auto
    from None [unfolded map_of_eq_None_iff]
      have a: "a \<notin> fst ` set r" by force
    {
      fix b
      assume "b \<in> ?r"
      from this [unfolded trancl_unfold_left] a have False by force
    }
    then have "?r = {}" by auto
    then show ?thesis unfolding one by simp
  next
    case (Some as) 
    have as: "set as = {b. (a, b) \<in> (set r)\<^sup>+}"
      using map_of_SomeD [OF Some]
        trancl_list_impl[of r "[a]"] by force
    then show ?thesis unfolding memo_list_trancl_def Let_def Some by simp
  qed
qed

end
