(*  Title:       Executable Transitive Closures of Finite Relations
    Author:      Christian Sternagel <c.sternagel@gmail.com>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

section \<open>Accessing Values via Keys\<close>

theory RBT_Map_Set_Extension
imports
  Collections.RBTMapImpl 
  Collections.RBTSetImpl
  Matrix.Utility
begin

text \<open>
  We provide two extensions of the red black tree implementation.

  The first extension provides two convenience methods on sets which are represented by red black
  trees: a check on subsets and the big union operator. 

  The second extension is to provide two operations @{term elem_list_to_rm} and @{term
  rm_set_lookup} which can be used to index a set of values via keys. More precisely, given a list
  of values of type @{typ "'v"} and a key function of type @{typ "'v => 'k"}, @{term
  elem_list_to_rm} will generate a map of type @{typ "'k => 'v set"}. Then with @{term
  rs_set_lookup} we can efficiently access all values which match a given key.
\<close>

subsection \<open>Subset and Union\<close>

text \<open>
  For the subset operation @{term "r \<subseteq> s"} we provide two implementations. The first one (@{term
  rs_subset}) traverses over @{term r} and then performs membership tests \<open>\<in> s\<close>. Its
  complexity is ${\cal O}(|r| \cdot log (|s|))$. The second one (@{term rs_subset_list}) generates
  sorted lists for both @{term r} and @{term s} and then linearly checks the subset condition. Its
  complexity is ${\cal O}(|r| + |s|)$.
\<close>

text \<open>
  As union operator we use the standard fold function. Note that the order of the union is important
  so that new sets are added to the big union.
\<close>

(* perhaps there is a smarter way to use two iterates at the same time, however,
  when writing this theory this feature was not detected in the RBTSetImpl theory *)
definition rs_subset :: "('a :: linorder) rs \<Rightarrow> 'a rs \<Rightarrow> 'a option"
where
  "rs_subset as bs = rs.iteratei
    as
    (\<lambda> maybe. case maybe of None \<Rightarrow> True | Some _ \<Rightarrow> False)
    (\<lambda> a _. if rs.memb a bs then None else Some a)
    None"

lemma rs_subset [simp]:
  "rs_subset as bs = None \<longleftrightarrow> rs.\<alpha> as \<subseteq> rs.\<alpha> bs"
proof -
  let ?abort = "\<lambda> maybe. case maybe of None \<Rightarrow> True | Some _ \<Rightarrow> False"
  let ?I = "\<lambda> aas maybe. maybe = None \<longleftrightarrow> (\<forall> a. a \<in> rs.\<alpha> as - aas \<longrightarrow> a \<in> rs.\<alpha> bs)"
  let ?it = "rs_subset as bs"
  have "?I {} ?it \<or> (\<exists> it \<subseteq> rs.\<alpha> as. it \<noteq> {} \<and> \<not> ?abort ?it \<and> ?I it ?it)"
    unfolding rs_subset_def
    by (rule rs.iteratei_rule_P [where I="?I"]) (auto simp: rs.correct)
  then show ?thesis by auto
qed
    
definition rs_subset_list :: "('a :: linorder) rs \<Rightarrow> 'a rs \<Rightarrow> 'a option"
where
  "rs_subset_list as bs = sorted_list_subset (rs.to_sorted_list as) (rs.to_sorted_list bs)"

lemma rs_subset_list [simp]:
  "rs_subset_list as bs = None \<longleftrightarrow> rs.\<alpha> as \<subseteq> rs.\<alpha> bs"
  unfolding rs_subset_list_def
    sorted_list_subset[OF rs.to_sorted_list_correct(3)[OF rs.invar, of as]
    rs.to_sorted_list_correct(3)[OF rs.invar, of bs]]
  by (simp add: rs.to_sorted_list_correct)

definition rs_Union :: "('q :: linorder) rs list \<Rightarrow> 'q rs"
where
  "rs_Union = foldl rs.union (rs.empty ())"

lemma rs_Union [simp]:
  "rs.\<alpha> (rs_Union qs) = \<Union> (rs.\<alpha> ` set qs)"
proof -
  { 
    fix start
    have "rs.\<alpha> (foldl rs.union start qs) = rs.\<alpha> start \<union> \<Union> (rs.\<alpha> ` set qs)"
      by (induct qs arbitrary: start, auto simp: rs.correct)
  } from this[of "rs.empty ()"]
  show ?thesis unfolding rs_Union_def
    by (auto simp: rs.correct)
qed

subsection \<open>Grouping Values via Keys\<close>
 
text \<open>
  The functions to produce the index (@{term elem_list_to_rm}) and the lookup function (@{term
  rm_set_lookup}) are straight-forward, however it requires some tedious reasoning that they perform
  as they should.
\<close>
fun elem_list_to_rm :: "('d \<Rightarrow> 'k :: linorder) \<Rightarrow> 'd list \<Rightarrow> ('k, 'd list) rm"
where
  "elem_list_to_rm key [] = rm.empty ()" |
  "elem_list_to_rm key (d # ds) =
    (let
      rm = elem_list_to_rm key ds;
      k = key d
    in
      (case rm.\<alpha> rm k of
        None \<Rightarrow> rm.update_dj k [d] rm
      | Some data \<Rightarrow> rm.update k (d # data) rm))"

definition "rm_set_lookup rm = (\<lambda> a. (case rm.\<alpha> rm a of None \<Rightarrow> [] | Some rules \<Rightarrow> rules))"

lemma rm_to_list_empty [simp]:
  "rm.to_list (rm.empty ()) = []" 
proof -
  have "map_of (rm.to_list (rm.empty ())) = Map.empty" 
    by (simp add: rm.correct)
  moreover have map_of_empty_iff: "\<And>l. map_of l = Map.empty \<longleftrightarrow> l = []"
    by (case_tac l) auto
  ultimately show ?thesis by metis
qed

locale rm_set = 
  fixes rm :: "('k :: linorder, 'd list) rm"
    and key :: "'d \<Rightarrow> 'k"
    and data :: "'d set"
  assumes rm_set_lookup: "\<And> k. set (rm_set_lookup rm k) = {d \<in> data. key d = k}"
begin

lemma data_lookup:
  "data = \<Union> {set (rm_set_lookup rm k) | k. True}" (is "_ = ?R")
proof -
  { 
    fix d
    assume d: "d \<in> data"
    then have d: "d \<in> {d' \<in> data. key d' = key d}" by auto
    have "d \<in> ?R"
      by (rule UnionI[OF _ d], rule CollectI, rule exI[of _ "key d"], unfold rm_set_lookup[of "key d"], simp)
  }
  moreover
  {
    fix d
    assume "d \<in> ?R"
    from this[unfolded rm_set_lookup]
    have "d \<in> data" by auto
  }
  ultimately show ?thesis by blast
qed

lemma finite_data:
  "finite data"
  unfolding data_lookup
proof
  show "finite {set (rm_set_lookup rm k) | k. True}" (is "finite ?L")
  proof - 
    let ?rmset = "rm.\<alpha> rm"
    let ?M = "?rmset ` Map.dom ?rmset"
    let ?N = "((\<lambda> e. set (case e of None \<Rightarrow> [] | Some ds \<Rightarrow> ds)) ` ?M)"
    let ?K = "?N \<union> {{}}"
    from rm.finite[of rm] have fin: "finite ?K" by auto 
    show ?thesis 
    proof (rule finite_subset[OF _ fin], rule)
      fix ds
      assume "ds \<in> ?L"
      from this[unfolded rm_set_lookup_def]
      obtain fn where ds: "ds = set (case rm.\<alpha> rm fn of None \<Rightarrow> []
          | Some ds \<Rightarrow> ds)" by auto
      show "ds \<in> ?K" 
      proof (cases "rm.\<alpha> rm fn")
        case None
        then show ?thesis unfolding ds by auto
      next
        case (Some rules)
        from Some have fn: "fn \<in> Map.dom ?rmset" by auto
        have "ds \<in> ?N"
          unfolding ds
          by (rule, rule refl, rule, rule refl, rule fn)
        then show ?thesis by auto
      qed
    qed
  qed
qed (force simp: rm_set_lookup_def)

end

interpretation elem_list_to_rm: rm_set "elem_list_to_rm key ds" key "set ds"
proof
  fix k
  show "set (rm_set_lookup (elem_list_to_rm key ds) k) = {d \<in> set ds. key d = k}"
  proof (induct ds arbitrary: k)
    case Nil
    then show ?case unfolding rm_set_lookup_def 
      by (simp add: rm.correct)
  next
    case (Cons d ds k)
    let ?el = "elem_list_to_rm key"
    let ?l = "\<lambda>k ds. set (rm_set_lookup (?el ds) k)"
    let ?r = "\<lambda>k ds. {d \<in> set ds. key d = k}"
    from Cons have ind:
      "\<And> k. ?l k ds = ?r k ds" by auto
    show "?l k (d # ds) = ?r k (d # ds)"
    proof (cases "rm.\<alpha> (?el ds) (key d)")
      case None
      from None ind[of "key d"] have r: "{da \<in> set ds. key da = key d} = {}"
        unfolding rm_set_lookup_def by auto
      from None have el: "?el (d # ds) = rm.update_dj (key d) [d] (?el ds)"
        by simp
      from None have ndom: "key d \<notin> Map.dom (rm.\<alpha> (?el ds))" by auto
      have r: "?r k (d # ds) = ?r k ds \<inter> {da. key da \<noteq> key d} \<union> {da . key da = k \<and> da = d}" (is "_ = ?r1 \<union> ?r2") using r by auto
      from ndom have l: "?l k (d # ds) = 
        set (case (rm.\<alpha> (elem_list_to_rm key ds)(key d \<mapsto> [d])) k of None \<Rightarrow> []
        | Some rules \<Rightarrow> rules)" (is "_ = ?l") unfolding el rm_set_lookup_def 
        by (simp add: rm.correct)
      {
        fix da
        assume "da \<in> ?r1 \<union> ?r2"
        then have "da \<in> ?l"
        proof
          assume "da \<in> ?r2"
          then have da: "da = d" and k: "key d = k" by auto
          show ?thesis unfolding da k by auto
        next
          assume "da \<in> ?r1"
          from this[unfolded ind[symmetric] rm_set_lookup_def]
          obtain das where rm: "rm.\<alpha> (?el ds) k = Some das" and da: "da \<in> set das" and k: "key da \<noteq> key d" by (cases "rm.\<alpha> (?el ds) k", auto)
          from ind[of k, unfolded rm_set_lookup_def] rm da k have k: "key d \<noteq> k" by auto
          have rm: "(rm.\<alpha> (elem_list_to_rm key ds)(key d \<mapsto> [d])) k = Some das"
            unfolding rm[symmetric] using k by auto
          show ?thesis unfolding rm using da by auto
        qed
      } 
      moreover 
      {
        fix da
        assume l: "da \<in> ?l"
        let ?rm = "((rm.\<alpha> (elem_list_to_rm key ds))(key d \<mapsto> [d])) k"
        from l obtain das where rm: "?rm = Some das" and da: "da \<in> set das"
          by (cases ?rm, auto)
        have "da \<in> ?r1 \<union> ?r2" 
        proof (cases "k = key d")
          case True
          with rm da have da: "da = d" by auto
          then show ?thesis using True by auto
        next
          case False
          with rm have "rm.\<alpha> (?el ds) k = Some das" by auto
          from ind[of k, unfolded rm_set_lookup_def this] da False
          show ?thesis by auto
        qed
      }
      ultimately have "?l = ?r1 \<union> ?r2" by blast
      then show ?thesis unfolding l r .
    next
      case (Some das)
      from Some ind[of "key d"] have das: "{da \<in> set ds. key da = key d} = set das"
        unfolding rm_set_lookup_def by auto
      from Some have el: "?el (d # ds) = rm.update (key d) (d # das) (?el ds)"
        by simp
      from Some have dom: "key d \<in> Map.dom (rm.\<alpha> (?el ds))" by auto
      from dom have l: "?l k (d # ds) = 
        set (case (rm.\<alpha> (elem_list_to_rm key ds)(key d \<mapsto> (d # das))) k of None \<Rightarrow> []
        | Some rules \<Rightarrow> rules)" (is "_ = ?l") unfolding el rm_set_lookup_def 
        by (simp add: rm.correct)
      have r: "?r k (d # ds) = ?r k ds \<union> {da. key da = k \<and> da = d}" (is "_ = ?r1 \<union> ?r2")  by auto
      {
        fix da
        assume "da \<in> ?r1 \<union> ?r2"
        then have "da \<in> ?l"
        proof
          assume "da \<in> ?r2"
          then have da: "da = d" and k: "key d = k" by auto
          show ?thesis unfolding da k by auto
        next
          assume "da \<in> ?r1"
          from this[unfolded ind[symmetric] rm_set_lookup_def]
          obtain das' where rm: "rm.\<alpha> (?el ds) k = Some das'" and da: "da \<in> set das'" by (cases "rm.\<alpha> (?el ds) k", auto)
          from ind[of k, unfolded rm_set_lookup_def rm] have das': "set das' = {d \<in> set ds. key d = k}" by auto
          show ?thesis 
          proof (cases "k = key d")
            case True
            show ?thesis using das' das da unfolding True by simp
          next
            case False
            then show ?thesis using das' da rm by auto
          qed
        qed
      } 
      moreover 
      {
        fix da
        assume l: "da \<in> ?l"
        let ?rm = "((rm.\<alpha> (elem_list_to_rm key ds))(key d \<mapsto> d # das)) k"
        from l obtain das' where rm: "?rm = Some das'" and da: "da \<in> set das'"
          by (cases ?rm, auto)
        have "da \<in> ?r1 \<union> ?r2" 
        proof (cases "k = key d")
          case True
          with rm da das have da: "da \<in> set (d # das)" by auto
          then have "da = d \<or> da \<in> set das" by auto
          then have k: "key da = k" 
          proof
            assume "da = d"
            then show ?thesis using True by simp
          next
            assume "da \<in> set das"
            with das True show ?thesis by auto
          qed
          from da k show ?thesis using das by auto
        next
          case False
          with rm have "rm.\<alpha> (?el ds) k = Some das'" by auto
          from ind[of k, unfolded rm_set_lookup_def this] da False
          show ?thesis by auto
        qed
      }
      ultimately have "?l = ?r1 \<union> ?r2" by blast
      then show ?thesis unfolding l r .
    qed
  qed
qed

end
