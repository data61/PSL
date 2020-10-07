section \<open>Graph rewriting and saturation\<close>
text \<open>Here we describe graph rewriting, again without connecting it to semantics.\<close>
theory GraphRewriting
  imports RulesAndChains 
    "HOL-Library.Infinite_Set"
begin

(* Algorithm 1 on page 16 *)
text \<open>To describe Algorithm 1, we give a single step instead of the recursive call.
This allows us to reason about its effect without dealing with non-termination.
We define a worklist, saying what work can be done.
A valid selection needs to be made in order to ensure fairness.
To do a step, we define the function extend, and use it in @{term make_step}.
A function that always makes a valid selection is used in this step. \<close>

abbreviation graph_of where
  "graph_of \<equiv> \<lambda> X. LG (snd X) {0..<fst X}"

definition nextMax :: "nat set \<Rightarrow> nat"
  where
  "nextMax x \<equiv> if x = {} then 0 else Suc (Max x)"

lemma nextMax_max[intro]:
  assumes "finite x" "v \<in> x"
  shows "v < nextMax x" "v \<le> nextMax x"
  using Max.coboundedI[OF assms] assms(2) unfolding nextMax_def by auto

definition worklist :: "nat \<times> ('a \<times> nat \<times> nat) set
           \<Rightarrow> (('a, 'b) labeled_graph \<times> ('a, 'b) labeled_graph) set
              \<Rightarrow> (nat \<times> ('a, 'b) Graph_PreRule \<times> ('b \<times> nat) set) set" where
"worklist G Rs \<equiv> let G = graph_of G
  in {(N,R,f). R\<in> Rs \<and> graph_homomorphism (fst R) G f \<and> N = nextMax (Range f)
                 \<and> \<not> extensible R G f }"

definition valid_selection where
"valid_selection Rs G R f \<equiv>
  let wl = worklist G Rs in
    (nextMax (Range f), R,f) \<in> wl \<and>
    (\<forall> (N,_) \<in> wl. N \<ge> nextMax (Range f)) \<and>
    graph_rule R"

lemma valid_selection_exists:
  assumes "worklist G Rs \<noteq> {}"
          "set_of_graph_rules Rs"
  shows "\<exists>L R f. valid_selection Rs G R f"
proof -
  define wl where "wl = worklist G Rs" hence wl_ne:"wl \<noteq> {}" using assms(1) by auto
  let ?N = "LEAST N. N \<in> Domain wl"
  from wl_ne have "\<exists> N. N \<in> Domain wl" by auto
  with LeastI2 have "?N \<in> Domain wl" by metis
  then obtain L R f where NLRf:"(?N,(L,R),f)\<in>wl" by auto
  hence N_def:"?N = nextMax (Range f)"
    and in_Rs: "(L,R) \<in> Rs" unfolding wl_def worklist_def Let_def by auto
  from Least_le wl_ne Domain.intros case_prodI2 
  have min:"(\<forall> (N',_) \<in> wl. N' \<ge> ?N)" by (metis (no_types, lifting))
  from in_Rs have "finite_graph R" "subgraph L R"
    using assms(2)[unfolded set_of_graph_rules_def] by auto
  with min NLRf N_def show ?thesis unfolding wl_def[symmetric] valid_selection_def by auto
qed

definition valid_selector where
"valid_selector Rs selector \<equiv> \<forall> G.
   (worklist G Rs \<noteq> {} \<longrightarrow> (\<exists> (R,f)\<in>UNIV. selector G = Some (R,f)
                               \<and> valid_selection Rs G R f)) \<and>
   (worklist G Rs = {} \<longrightarrow> selector G = None)"

lemma valid_selectorD[dest]:
  assumes "valid_selector Rs selector"
  shows "worklist G Rs = {} \<longleftrightarrow> selector G = None"
        "selector G = Some (R,f) \<Longrightarrow> valid_selection Rs G R f"
  using assms[unfolded valid_selector_def,rule_format,of G]
  by (cases "worklist G Rs = {}",auto)

text \<open>The following gives a valid selector.
      This selector is not useful as concrete implementation, because it used the choice operation.\<close>
definition non_constructive_selector where
"non_constructive_selector Rs G \<equiv> let wl = worklist G Rs in
   if wl = {} then None else Some (SOME (R,f). valid_selection Rs G R f) "

lemma non_constructive_selector:
  assumes "set_of_graph_rules Rs"
  shows "valid_selector Rs (non_constructive_selector Rs)"
  unfolding valid_selector_def proof((clarify,standard;clarify),goal_cases)
  case (1 n E)
  let ?x = "(SOME (R, f). valid_selection Rs (n, E) R f)"
  from valid_selection_exists[OF 1 assms]
  have "\<exists> R f. valid_selection Rs (n, E) R f" by auto
  hence "\<exists> x. valid_selection Rs (n, E) (fst x) (snd x)"
    by auto
  from this prod.case_eq_if tfl_some
  have "\<not> valid_selection Rs (n, E) (fst ?x) (snd ?x) \<Longrightarrow> False"
    by (metis (mono_tags, lifting))
  thus ?case unfolding non_constructive_selector_def Let_def using 1 by (auto simp:prod_eq_iff)
qed (auto simp:non_constructive_selector_def)


text \<open>The following is used to make a weak pushout step.
      In the paper, we aren't too specific on how this should be done. Here we are.
      We work on natural numbers in order to be able to pick fresh elements easily. \<close>
definition extend ::
    "nat \<Rightarrow> ('b, 'a::linorder) Graph_PreRule  \<Rightarrow> ('a \<times> nat) set \<Rightarrow> ('a \<times> nat) set" where
"extend n R f \<equiv> f \<union> 
   (let V_new = sorted_list_of_set (vertices (snd R) - vertices (fst R))
    in set (zip V_new [n..<(n+length V_new)]))"

lemma nextMax_set[simp]:
  assumes "sorted xs"
  shows "nextMax (set xs) = (if xs = Nil then 0 else Suc (last xs))"
  using assms
proof(induct xs)
  case Nil show ?case unfolding nextMax_def by auto
next
  case (Cons a list)
  hence "list \<noteq> [] \<Longrightarrow> fold max list a = last list"
    using list_sorted_max by (metis last.simps)
  thus ?case unfolding nextMax_def Max.set_eq_fold by auto
qed

lemma nextMax_Un_eq[simp]:
"finite x \<Longrightarrow> finite y \<Longrightarrow> nextMax (x \<union> y) = max (nextMax x) (nextMax y)"
  unfolding nextMax_def using Max_Un by auto

lemma extend: (* extensible into the new graph *)
  assumes "graph_homomorphism (fst R) (LG E {0..<n}) f" "graph_rule R"
  defines "g \<equiv> extend n R f"
  defines "G' \<equiv> LG ((on_triple g `` (edges (snd R))) \<union> E) {0..<max n (nextMax (Range g))}"
  shows "graph_homomorphism (snd R) G' g" "agree_on (fst R) f g" "f \<subseteq> g"
        "subgraph (LG E {0..<n}) G'"
        "weak_universal (t:: 'x itself) R (LG E {0..<n}) G' f g"
proof -
  have ln:"length x = length [n..<n + length x]" for x::"'b list" by auto
  let ?R_L = "vertices (snd R) - vertices (fst R)"
  from assms
  have "graph_rule (fst R,snd R)" and fin_R:"finite (vertices (snd R))"
    and subsLR:"vertices (fst R) \<subseteq> vertices (snd R)" and gr_R:"graph (snd R)"
    unfolding subgraph_def graph_union_iff
    by auto
  hence fin_R_L[simp]:"finite ?R_L"
     and fin_L:"finite (vertices (fst R))"
     using finite_subset by auto
  from assms have f_dom:"Domain f = vertices (fst R)"
    and f_uni:"univalent f" unfolding graph_homomorphism_def by auto
  from assms[unfolded graph_homomorphism_def]
  have "f `` vertices (fst R) \<subseteq> vertices (LG E {0..<n})" by blast
  hence f_ran:"Range f \<subseteq> {0..<n}" using f_dom by auto
  let ?g = "(let V_new = sorted_list_of_set ?R_L
              in set (zip V_new [n..<n + length V_new]))" (* new part of g *)
  have fin_g':"finite ?g" "finite (Range ?g)" unfolding Let_def by auto
  have "finite (Domain f)" "univalent f" using assms(1) fin_L
    unfolding graph_homomorphism_def by auto
  hence fin_f:"finite (Range f)" unfolding Range_snd by auto
  hence fin_g:"finite (Range g)" unfolding extend_def g_def Let_def Range_Un_eq by auto
  have nextMax_f:"nextMax (Range f) \<le> n"
    using f_ran Max_in[OF fin_f] by (simp add:nextMax_def Suc_leI subset_eq)
  
  have "x \<in> Domain ?g \<Longrightarrow> x \<notin> Domain f" for x unfolding f_dom Let_def by auto
  hence g_not_f:"(x,y) \<in> ?g \<Longrightarrow> (x,z) \<notin> f" for x y z by auto
  have uni_g':"univalent ?g" "univalent (converse ?g)" unfolding Let_def by auto
  with f_uni have uni_g:"univalent g" by (auto simp:g_def extend_def g_not_f)
  from fin_g have "(a,b) \<in> g \<Longrightarrow> b < Suc (Max (Range g))" for a b
    unfolding less_Suc_eq_le by (rule Max.coboundedI) force
  hence "(a,b) \<in> g \<Longrightarrow> b < nextMax (Range g)" for a b
    unfolding nextMax_def by (cases "Range g = {}",auto)
  hence in_g:"(a,b) \<in> g \<Longrightarrow> b < max n (nextMax (Range g))" for a b by fastforce
  let ?G = "LG E {0..<n}"
  have gr_G:"graph ?G" using assms(1) unfolding graph_homomorphism_def by blast
  hence "(a, aa, b) \<in> E \<Longrightarrow> b < max n c" "(a, aa, b) \<in> E \<Longrightarrow> aa < max n c"
    for a aa b c by fastforce+
  hence gr_G':"graph G'" unfolding G'_def restrict_def using in_g by auto
  show "subgraph (LG E {0..<n}) G'"
    unfolding subgraph_def2[OF gr_G gr_G'] unfolding G'_def by auto
  have g_dom:"vertices (snd R) = Domain g" using subsLR
    unfolding g_def extend_def Domain_Un_eq f_dom by (auto simp:Let_def)
  show "graph_homomorphism (snd R) G' g"
    by (intro graph_homomorphismI[OF g_dom _ uni_g _ gr_R gr_G'])
       (auto simp:G'_def intro:in_g)
  show "f \<subseteq> g" by (auto simp:g_def extend_def)
  thus "agree_on (fst R) f g" using f_dom uni_g agree_on_subset equalityE by metis
  show "weak_universal t R ?G G' f g" proof fix a:: "('b \<times> 'x) set" fix b G
    assume a:"graph_homomorphism (snd R) G a"
             "graph_homomorphism ?G G b" "f O b \<subseteq> a"
    hence univ_b:"univalent b" and univ_a:"univalent a"
      and rng_b:"Range b \<subseteq> vertices G" and rng_a:"Range a \<subseteq> vertices G"
      and ep_b:"edge_preserving b (edges (LG E {0..<n})) (edges G)"
      and ep_a:"edge_preserving a (edges (snd R)) (edges G)"
      unfolding graph_homomorphism_def prod.sel labeled_graph.sel by blast+
    from a have dom_b:"Domain b = {0..<n}"
      and dom_a:"Domain a = vertices (snd R)" and v6: "graph G"
      unfolding graph_homomorphism_def prod.sel labeled_graph.sel by auto

    have help_dom_b:"(y, z) \<in> b \<Longrightarrow> n \<le> y \<Longrightarrow> False" for y z using dom_b
      by (metis Domain.DomainI atLeastLessThan_iff not_less)
    have disj_doms:"Domain b \<inter> Domain (?g\<inverse> O a) = {}" using help_dom_b
      unfolding Let_def by (auto dest!:set_zip_leftD)

    have "max n (nextMax (Range ?g)) = n + length (sorted_list_of_set ?R_L)" (is "_ = ?len")
      unfolding Let_def Range_snd set_map[symmetric] map_snd_zip[OF ln] nextMax_set[OF sorted_upt]
      by fastforce
    hence n_eq:"?len = max n (nextMax (Range g))"
      unfolding Range_snd[symmetric] g_def extend_def Range_Un_eq
                nextMax_Un_eq[OF fin_f fin_g'(2)] max.assoc[symmetric] max_absorb1[OF nextMax_f]
      by auto

    let ?h = "b \<union> ?g\<inverse> O a"

    have dg:"Domain (?g\<inverse>) = {n..<max n (nextMax (Range g))}"
      unfolding Let_def Domain_converse Range_set_zip[OF ln] atLeastLessThan_upt
      unfolding Range_snd n_eq ..
    have "?g `` Domain a = ?g `` (?R_L \<union> vertices (fst R))"
      using dom_a subsLR by auto
    also have "\<dots> = ?g `` ?R_L \<union> ?g `` vertices (fst R)" by auto
    also have "?g `` vertices (fst R) = {}" apply(rule Image_outside_Domain)
      unfolding Let_def Domain_set_zip[OF ln] by auto
    also have "?g `` ?R_L = Range ?g" apply(rule Image_Domain)
      unfolding Let_def Domain_set_zip[OF ln] by auto
    finally have dg2:"?g `` Domain a = {n..<max n (nextMax (Range g))}"
      unfolding Let_def Range_set_zip[OF ln] set_sorted_list_of_set[OF fin_R_L] 
      unfolding n_eq set_upt by auto
    have "Domain (?g\<inverse> O a) = {n..<max n (nextMax (Range g))}"
      unfolding Domain_id_on converse_converse dg dg2 by auto
    hence v1: "vertices G' = Domain ?h" unfolding G'_def Domain_Un_eq dom_b by auto
    have "b `` vertices G' \<subseteq> vertices G" "(?g\<inverse> O a) `` vertices G' \<subseteq> vertices G"
      using rng_a rng_b by auto
    hence v2: "?h `` vertices G' \<subseteq> vertices G" by blast
    have v3: "univalent ?h"
      using disj_doms univalent_union[OF univ_b univalent_composes[OF uni_g'(2) univ_a]] by blast
    (* showing edge preservation *)
    { fix l x y x' y' assume a2:"(l,x,y) \<in> edges G'" "(x,x') \<in> ?h" "(y,y') \<in> ?h"
      have "(l,x',y') \<in> edges G" proof(cases "(l,x,y) \<in> edges ?G")
        case True
        with gr_G[THEN restrictD]
        have "x \<in> Domain b" "y \<in> Domain b" unfolding dom_b by auto
        hence "x \<notin> Domain (converse ?g O a)" "y \<notin> Domain (converse ?g O a)"
          using disj_doms by blast+
        hence "(x,x') \<in> b" "(y,y') \<in> b" using a2 by auto
        with ep_b True show ?thesis unfolding edge_preserving by auto
      next
        have "g O ?h = f O b \<union> ?g O b \<union> ((f O ?g\<inverse>) O a \<union> (?g O ?g\<inverse>) O a)"
          unfolding g_def extend_def by blast
        also have "(?g O ?g\<inverse>) = Id_on ?R_L"
          unfolding univalent_O_converse[OF uni_g'(2)] unfolding Let_def by auto
        also have "(f O ?g\<inverse>) = {}" using f_ran unfolding Let_def by (auto dest!:set_zip_leftD)
        also have "?g O b = {}" using help_dom_b unfolding Let_def by (auto dest!:set_zip_rightD)
        finally have gOh:"g O ?h \<subseteq> a" using a(3) by blast
        case False
        hence "(l,x,y) \<in> on_triple g `` edges (snd R)" using a2(1) unfolding G'_def by auto
        then obtain r_x r_y
          where r:"(l,r_x,r_y) \<in> edges (snd R)" "(r_x,x) \<in> g" "(r_y,y) \<in> g" by auto
        hence "(r_x,x') \<in> a" "(r_y,y') \<in> a" using gOh a2(2,3) by auto
        hence "(l,x',y') \<in> on_triple a `` edges (snd R)" using r(1) unfolding on_triple_def by auto
        thus ?thesis using ep_a unfolding edge_preserving by auto
      qed
    }
    hence v4: "edge_preserving ?h (edges G') (edges G)" by auto
    have "graph_homomorphism G' G ?h" by(fact graph_homomorphismI[OF v1 v2 v3 v4 gr_G' v6])
    thus "\<exists>h. graph_homomorphism G' G h \<and> b \<subseteq> h" by auto
  qed
qed

text \<open>Showing that the extend function indeed creates a valid pushout.\<close>
lemma selector_pushout:
  assumes "valid_selector Rs selector" "selector G'' = Some (R,f)"
  defines "G \<equiv> graph_of G''"
  assumes "graph G"
  defines "g \<equiv> extend (fst G'') R f"
  defines "G' \<equiv> LG (on_triple g `` edges (snd R) \<union> (snd G'')) {0..<max (fst G'') (nextMax (Range g))}"
  shows "pushout_step (t:: 'x itself) R G G'"
proof -
  have "valid_selection Rs G'' R f" using assms by(cases "selector G''",auto)
  hence igh:"graph_homomorphism (fst R) G f" "graph_rule R"
    unfolding valid_selection_def worklist_def G_def Let_def by auto
  have "subgraph G G'"
       "graph_homomorphism (fst R) G f"
       "graph_homomorphism (snd R) G' g"
       "f \<subseteq> g"
       "weak_universal t R G G' f g"
    using extend[OF igh[unfolded G_def],folded g_def,folded G'_def,folded G_def] igh(1)
    by auto
  thus ?thesis unfolding pushout_step_def by auto
qed

text \<open>Making a single step in Algorithm 1.
  A prerequisite is that its first argument is a @{term valid_selector}.\<close>

definition make_step where
"make_step selector S \<equiv>
   case selector S of
     None \<Rightarrow> S |
     Some (R,f) \<Rightarrow> (let g = extend (fst S) R f in
         (max (fst S) (nextMax (Range g)), (on_triple g `` (edges (snd R))) \<union> (snd S)))"

lemma WPC_through_make_step:
  assumes "set_of_graph_rules Rs" "graph (graph_of (X 0))"
     and makestep: "\<forall> i. X (Suc i) = make_step selector (X i)"
     and selector: "valid_selector Rs selector"
  shows "Simple_WPC t Rs (\<lambda> i. graph_of (X i))" "chain (\<lambda> i. graph_of (X i))"
proof
  note ms = makestep[unfolded make_step_def,rule_format]
  have gr:"graph (graph_of (X i))" for i proof(induct i)
    case (Suc i)
    then show ?case proof(cases "selector (X i)")
      case None
      then show ?thesis using ms Suc by auto
    next
      case (Some a)
      then obtain R f where Some:"selector (X i) = Some (R,f)" by fastforce
      then show ?thesis using ms[of i,unfolded Some Let_def]
        selector_pushout[OF selector Some Suc,of t
                        ,unfolded pushout_step_def subgraph_def]
        by auto
    qed
  qed (fact assms)
  show "chain (\<lambda> i. graph_of (X i))" unfolding chain_def
  proof(clarify) fix i
    show "subgraph (graph_of (X i)) (graph_of (X (i + 1)))"
    proof(cases "selector (X i)")
      case None
      then show ?thesis using ms gr by (auto intro!:graph_homomorphismI)
    next
      case Some
      then obtain R f where Some:"selector (X i) = Some (R,f)" by fastforce
      then show ?thesis using ms selector_pushout[OF selector Some gr,of t]
      unfolding pushout_step_def Let_def by simp
    qed
  qed
  show "graph_of (X i) = graph_of (X (Suc i)) \<or>
         (\<exists>R\<in>Rs. pushout_step t R (graph_of (X i)) (graph_of (X (Suc i))))" for i
  proof(cases "selector (X i)")
    case None thus ?thesis using ms by auto
  next
    case Some
    then obtain R f where Some:"selector (X i) = Some (R,f)" by fastforce
    hence "R \<in> Rs" 
      using valid_selectorD(2)[OF selector,unfolded valid_selection_def worklist_def Let_def]
      by(cases R,blast)
    then show ?thesis using ms[of i,unfolded Some Let_def] selector_pushout[OF selector Some gr]
      unfolding make_step_def by auto
  qed
qed (fact assms)+

lemma N_occurs_finitely_often:
  assumes "finite Rs" "set_of_graph_rules Rs" "graph (graph_of (X 0))"
      and makestep: "\<And> i. X (Suc i) = make_step selector (X i)"
      and selector: "valid_selector Rs selector"
    shows "finite {(R,f). \<exists> i. R\<in> Rs \<and> graph_homomorphism (fst R) (graph_of (X i)) f
                        \<and> nextMax (Range f) \<le> N}" (is "finite {(R,f).?P R f}")
proof -
  have prod_eq : "(\<forall> x \<in> {(x, y). A x y}. B x) \<longleftrightarrow> (\<forall> x. A (fst x) (snd x) \<longrightarrow> B x)"
     "(x \<in> {(x, y). A x y}) \<longleftrightarrow> (A (fst x) (snd x))"
    for A B x by auto
  let ?S = "{(R,f).?P R f}"
  let "?Q R f" = "Domain f = vertices (fst (R::('a, 'b) Graph_PreRule)) \<and> univalent f \<and> nextMax (Range f) \<le> N"
  have seteq:"(\<Union>R\<in>Rs. {(R', f). R' = R \<and> ?Q R f}) = {(R,f). R \<in> Rs \<and> ?Q R f}" by auto
  have "\<forall> R \<in> Rs. finite {(R',f). R' = R \<and> ?Q R f}"
  proof fix R assume "R \<in> Rs"
    hence fin:"finite (vertices (fst R))" using assms by auto
    hence fin2:"finite (Pow (vertices (fst R) \<times> {0..N}))" by auto
    have fin:"Domain x = vertices (fst R) \<Longrightarrow> univalent x \<Longrightarrow> finite (snd ` x)"
      for x:: "('b \<times> nat) set" using fin univalent_finite[of x] by simp
    hence "Domain f = vertices (fst R) \<Longrightarrow>
      univalent f \<Longrightarrow> (a,b) \<in> f \<Longrightarrow> nextMax (Range f) \<le> N \<Longrightarrow> b \<le> N" for f a b
      unfolding Range_snd using image_eqI nextMax_max(2) snd_conv order.trans by metis
    hence sub:"{f. ?Q R f} \<subseteq> Pow (vertices (fst R) \<times> {0..N})"
      using nextMax_max[OF fin] by (auto simp:Range_snd image_def)
    from finite_subset[OF sub fin2] show "finite {(R',f). R' = R \<and> ?Q R f}" by auto
  qed
  from this[folded finite_UN[OF assms(1)],unfolded seteq]
  have fin:"finite {(R,f). R \<in> Rs \<and> ?Q R f}".
  have "?P R f \<Longrightarrow> R \<in> Rs \<and> ?Q R f" for R f
    unfolding graph_homomorphism_def by auto
  hence "?S \<subseteq> {(R,f). R \<in> Rs \<and> ?Q R f}" unfolding subset_eq prod_eq by blast
  from finite_subset[OF this fin] show ?thesis by auto
qed

lemma inj_on_infinite:
  assumes "infinite A" "inj_on f A" "range f \<subseteq> B"
  shows "infinite B"
proof -
  from assms[unfolded infinite_iff_countable_subset] obtain g::"nat \<Rightarrow> 'a" where
    g:"inj g \<and> range g \<subseteq> A" by blast
  hence i:"inj (f o g)" using assms(2) using comp_inj_on inj_on_subset by blast
  have "range (f o g) \<subseteq> B" using assms(3) by auto
  with i show ?thesis
    unfolding infinite_iff_countable_subset by blast
qed

lemma makestep_makes_selector_inj:
  assumes "selector (X y) = Some (R,f)"
          "selector (X x) = Some (R,f)"
          "valid_selector Rs selector"
    and step: "\<forall> i. X (Suc i) = make_step selector (X i)"
    and chain:"chain (\<lambda> i. graph_of (X i))"
  shows "x = y"
proof(rule ccontr)
  assume a:"x \<noteq> y"
  define x' y' where "x' \<equiv> min x y" "y' \<equiv> max x y"
  hence xy:"selector (X x') = Some (R, f)" "selector (X y') = Some (R, f)" "x' < y'"
    using assms(1,2) a unfolding min_def max_def by auto
  with valid_selectorD assms
  have "valid_selection Rs (X x') R f" "valid_selection Rs (X y') R f" by auto
  hence not_ex:"\<not> extensible R (graph_of (X y')) f"
    and hom:"graph_homomorphism (fst R) (graph_of (X x')) f" "graph_rule R"
    unfolding valid_selection_def Let_def worklist_def by auto
  have X:"X (Suc x') = (max (fst (X x')) (nextMax (Range (extend (fst (X x')) R f))),
          on_triple (extend (fst (X x')) R f) `` edges (snd R) \<union> snd (X x'))"
    unfolding step[unfolded make_step_def Let_def,rule_format] xy by auto
  let ?ex = "extend (fst (X x')) R f"
  have hom:"graph_homomorphism (snd R) (graph_of (X (Suc x'))) ?ex"
       and agr:"agree_on (fst R) f ?ex" using extend(1,2)[OF hom] unfolding X by auto
  from xy have "Suc x' \<le> y'" by auto
  with chain[unfolded chain_def2] have "subgraph (graph_of (X (Suc x'))) (graph_of (X y'))" by auto
  from subgraph_preserves_hom[OF this hom]
  have hom:"graph_homomorphism (snd R) (graph_of (X y')) ?ex".
  with agr have "extensible R (graph_of (X y')) f" unfolding extensible_def by auto
  thus False using not_ex by auto
qed

lemma fair_through_make_step:
  assumes "finite Rs" "set_of_graph_rules Rs" "graph (graph_of (X 0))"
     (* It should suffice to take infinitely many make_steps, 
        rather than having every step be a make_step,
        but we focus on the algorithm as in the paper here *)
     and makestep: "\<forall> i. X (Suc i) = make_step selector (X i)"
     and selector: "valid_selector Rs selector"
  shows "fair_chain Rs (\<lambda> i. graph_of (X i))"
proof
  show chn:"chain (\<lambda>i. graph_of (X i))" using WPC_through_make_step assms by blast
  fix R f i
  assume Rs:"R \<in> Rs" and h:"graph_homomorphism (fst R) (graph_of (X i)) f"
  hence R:"finite (vertices (snd R))" "subgraph (fst R) (snd R)"  "finite (vertices (fst R))"
    using assms by auto
  hence f:"finite f" "finite (Range f)" "finite (Domain f)" "univalent f" 
    using h unfolding graph_homomorphism_def Range_snd by auto
  define N where "N \<equiv> nextMax (Range f)"
  fix S
  let "?Q X' j" = " fst X' \<in> Rs
                  \<and> graph_homomorphism (fst (fst X')) (graph_of (X (j+i))) (snd X')
                  \<and> nextMax (Range (snd X')) \<le> N"
  let ?S = "{(R,f). \<exists>j. ?Q (R,f) j}"
  from assms(4) have "\<And>ia. X (Suc ia + i) = make_step selector (X (ia + i))" by auto
  note r = assms(1,2) chain_then_restrict[OF chn] this assms(5)
  from N_occurs_finitely_often[of Rs "\<lambda> j. X (j + i)",OF r]
  have fin_S:"finite ?S" by auto
  { assume a:"\<forall>j. \<not> extensible R (graph_of (X j)) f"
    let "?P X' j" = "?Q X' j \<and> Some X' = selector (X (j+i))"
    { fix j let ?j = "j+i" have "?j \<ge> i" by auto
      from subgraph_preserves_hom[OF chain[OF chn this] h]
      have h:"graph_homomorphism (fst R) (graph_of (X ?j)) f".
      have "\<not> extensible R (graph_of (X ?j)) f" using a by blast 
      with h Rs have wl:"(nextMax (Range f),R,f) \<in> worklist (X ?j) Rs" 
        unfolding worklist_def Let_def set_eq_iff by auto
      hence "worklist (X ?j) Rs \<noteq> {}" by auto
      with valid_selectorD[OF selector]
      obtain R' f'
        where sel:"Some (R',f') = selector (X ?j)"
                  "valid_selection Rs (X ?j) R' f'" by auto
      hence max:"(nextMax (Range f'), R', f') \<in> worklist (X ?j) Rs"
                "(\<forall>(N, _)\<in>worklist (X ?j) Rs. nextMax (Range f') \<le> N)"
        unfolding valid_selection_def Let_def by auto
      with wl have "nextMax (Range f') \<le> N" unfolding N_def by auto
      with max(1)[unfolded worklist_def Let_def mem_Collect_eq prod.case] sel(1)
      have "\<exists> X'. ?P X' j" by (metis fst_conv snd_conv)
    }
    then obtain ch where ch:"\<And> j. ?P (ch j) j" by metis (* uses 'choice' internally *)
    have inj:"inj ch" proof fix x y assume "ch x = ch y"
      with ch[of x] ch[of y]
      have "selector (X (x + i)) = Some (ch x)" "selector (X (y + i)) = Some (ch x)" by auto
      with makestep_makes_selector_inj[OF _ _ selector makestep chn] have "x + i = y + i"
        by (cases "ch x",metis (full_types))
      thus "x = y" by auto
    qed
    have "ch x \<in> ?S" for x using ch[of x] unfolding mem_Collect_eq by(intro case_prodI2) metis
    hence "range ch \<subseteq> ?S" unfolding UNIV_def by(rule image_Collect_subsetI)
    with infinite_iff_countable_subset inj have "infinite ?S" by blast
    with fin_S have "False" by auto
  }
  thus "\<exists>j. extensible R (graph_of (X j)) f" by auto
qed

fun mk_chain where
  "mk_chain sel Rs init 0 = init" |
  "mk_chain sel Rs init (Suc n) = mk_chain sel Rs (make_step sel init) n"

lemma mk_chain:
  "\<forall> i. mk_chain sel Rs init (Suc i) = make_step sel (mk_chain sel Rs init i)"
proof
  fix i
  show "mk_chain sel Rs init (Suc i) = make_step sel (mk_chain sel Rs init i)"
    by (induct i arbitrary:init,auto)
qed

text \<open>Algorithm 1, abstractly.\<close>
abbreviation the_lcg where
"the_lcg sel Rs init \<equiv> chain_sup (\<lambda>i. graph_of (mk_chain sel Rs init i))"

lemma mk_chain_edges:
  assumes "valid_selector Rules sel"
          "UNION Rules (edges \<circ> snd) \<subseteq> L \<times> UNIV"
          "edges (graph_of G) \<subseteq> L \<times> UNIV"
  shows "edges (graph_of (mk_chain sel Rules G i)) \<subseteq> L \<times> UNIV"
using assms(3) proof(induct i arbitrary:G)
  case 0
  then show ?case using assms(2) by auto
next
  case (Suc i G)
  hence "edges (graph_of (make_step sel G)) \<subseteq> L \<times> UNIV"
  proof(cases "sel G")
    case None show ?thesis unfolding None make_step_def using Suc by auto
  next
    case (Some a)
    then obtain R f where Some:"sel G = Some (R, f)" by fastforce
    hence "(a, x, y) \<in> edges (snd R) \<Longrightarrow> a \<in> L" for a x y
      using assms(2) valid_selectorD(2)[OF assms(1) Some]
      unfolding valid_selection_def Let_def worklist_def by auto
    then show ?thesis unfolding Some make_step_def Let_def using Suc by auto
  qed
  thus ?case unfolding mk_chain.simps by(rule Suc)
qed

lemma the_lcg_edges:
  assumes "valid_selector Rules sel"
          "fst ` UNION Rules (edges \<circ> snd) \<subseteq> L" (is "fst `?fR \<subseteq> _")
          "fst ` snd G \<subseteq> L"
  shows "fst ` edges (the_lcg sel Rules G) \<subseteq> L"
proof -
  from assms have "fst `?fR \<times> UNIV \<subseteq> L \<times> UNIV" "fst `(edges (graph_of G)) \<times> UNIV \<subseteq> L \<times> UNIV"
    by auto
  hence "UNION Rules (edges \<circ> snd) \<subseteq> L \<times> UNIV" "edges (graph_of G) \<subseteq> L \<times> UNIV"
    using fst_UNIV[of ?fR] fst_UNIV[of "(edges (graph_of G))"] by blast+
  note assms = assms(1) this
  have "edges (graph_of (mk_chain sel Rules G i)) \<subseteq> L \<times> UNIV" for i
    using mk_chain_edges[OF assms,unfolded Times_subset_cancel2[OF UNIV_I]].
  hence "edges (the_lcg sel Rules G) \<subseteq> L \<times> UNIV" unfolding chain_sup_def by auto
  thus ?thesis by auto
qed

text \<open>Lemma 9.\<close>
lemma lcg_through_make_step:
assumes "finite Rs" "set_of_graph_rules Rs" "graph (graph_of init)"
        "valid_selector Rs sel"
  shows "least_consequence_graph t Rs (graph_of init) (the_lcg sel Rs init)"
proof -
  from assms have gr:"graph (graph_of (mk_chain sel Rs init 0))" by auto
  note assms = assms(1,2) this mk_chain assms(4)
  from set_of_graph_rulesD[OF assms(2)]
  have "(\<And>R. R \<in> Rs \<Longrightarrow> subgraph (fst R) (snd R) \<and> finite_graph (fst R))" by auto
  from fair_chain_impl_consequence_graph[OF fair_through_make_step[OF assms] this]
       wpc_simpl[OF WPC_through_make_step(1)[OF assms(2-)],THEN wpc_least] 
  show ?thesis unfolding least_consequence_graph_def by auto
qed

end
