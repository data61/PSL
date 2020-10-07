section \<open>Rules, and the chains we can make with them\<close>
text \<open>This describes graph rules, and the reasoning is fully on graphs here (no semantics).
      The formalisation builds up to Lemma 4 in the paper.\<close>
theory RulesAndChains
imports LabeledGraphs
begin

type_synonym ('l,'v) graph_seq = "(nat \<Rightarrow> ('l, 'v) labeled_graph)"

text \<open>Definition 8.\<close>
definition chain :: "('l, 'v) graph_seq \<Rightarrow> bool" where
  "chain S \<equiv> \<forall> i. subgraph (S i) (S (i + 1))"

lemma chain_then_restrict:
  assumes "chain S" shows "S i = restrict (S i)"
  using assms[unfolded chain_def graph_homomorphism_def] by auto

lemma chain:
  assumes "chain S"
  shows "j \<ge> i \<Longrightarrow> subgraph (S i) (S j)"
proof(induct "j-i" arbitrary:i j)
  case 0
  then show ?case using chain_then_restrict[OF assms] assms[unfolded chain_def] by auto
next
  case (Suc x)
  hence j:"i + x + 1 = j" by auto
  thus ?case
    using subgraph_trans[OF Suc(1) assms[unfolded chain_def,rule_format,of "i+x"],of i,unfolded j]
    using Suc by auto
qed

lemma chain_def2:
  "chain S = (\<forall> i j. j \<ge> i \<longrightarrow> subgraph (S i) (S j))"
proof
  show "chain S \<Longrightarrow> \<forall>i j. i \<le> j \<longrightarrow> subgraph (S i) (S j)" using chain by auto
  show "\<forall>i j. i \<le> j \<longrightarrow> subgraph (S i) (S j) \<Longrightarrow> chain S" unfolding chain_def by simp
qed

text \<open>Second part of definition 8.\<close>
definition chain_sup :: "('l, 'v) graph_seq \<Rightarrow> ('l, 'v) labeled_graph" where
  "chain_sup S \<equiv> LG (\<Union> i. edges (S i)) (\<Union> i. vertices (S i))"

lemma chain_sup_const[simp]:
  "chain_sup (\<lambda> x. S) = S"
  unfolding chain_sup_def by auto

lemma chain_sup_subgraph[intro]:
  assumes "chain S"
  shows "subgraph (S j) (chain_sup S)"
proof -
  have c1: "S j = restrict (S j)" for j
    using assms[unfolded chain_def,rule_format,of j] graph_homomorphism_def by auto
  hence c2: "chain_sup S = restrict (chain_sup S)"
    unfolding chain_sup_def by fastforce
  have c3: "graph_union (S j) (chain_sup S) = chain_sup S"
    unfolding chain_sup_def graph_union_def by auto
  show ?thesis unfolding subgraph_def using c1 c2 c3 by auto
qed

lemma chain_sup_graph[intro]:
  assumes "chain S"
  shows "graph (chain_sup S)"
  using chain_sup_subgraph[OF assms]
  unfolding subgraph_def by auto

lemma map_graph_chain_sup:
"map_graph g (chain_sup S) = chain_sup (map_graph g o S)"
  unfolding map_graph_def chain_sup_def by auto

lemma graph_union_chain_sup[intro]:
  assumes "\<And> i. graph_union (S i) C = C"
  shows "graph_union (chain_sup S) C = C"
proof
  from assms have e:"edges (S i) \<subseteq> edges C" and v:"vertices (S i) \<subseteq> vertices C" for i
    by (auto simp:graph_union_iff)
  show "edges (chain_sup S) \<subseteq> edges C" using e unfolding chain_sup_def by auto
  show "vertices (chain_sup S) \<subseteq> vertices C" using v unfolding chain_sup_def by auto
qed


type_synonym ('l,'v) Graph_PreRule = "('l, 'v) labeled_graph \<times> ('l, 'v) labeled_graph"
text \<open>Definition 9.\<close>
abbreviation graph_rule :: "('l,'v) Graph_PreRule \<Rightarrow> bool" where
"graph_rule R \<equiv> subgraph (fst R) (snd R) \<and> finite_graph (snd R)"

definition set_of_graph_rules :: "('l,'v) Graph_PreRule set \<Rightarrow> bool" where
"set_of_graph_rules Rs \<equiv> \<forall> R\<in>Rs. graph_rule R"

lemma set_of_graph_rulesD[dest]:
  assumes "set_of_graph_rules Rs" "R \<in> Rs"
  shows "finite_graph (fst R)" "finite_graph (snd R)" "subgraph (fst R) (snd R)"
  using assms(1)[unfolded set_of_graph_rules_def] assms(2)
        rev_finite_subset[of "vertices (snd R)"]
        rev_finite_subset[of "edges (snd R)"]
  unfolding subgraph_def graph_union_iff by auto

text \<open>We define @{term agree_on} as an equivalence.\<close>
definition agree_on where
"agree_on G f\<^sub>1 f\<^sub>2 \<equiv> (\<forall> v \<in> vertices G. f\<^sub>1 `` {v} = f\<^sub>2 `` {v})"

lemma agree_on_empty[intro,simp]: "agree_on (LG {} {}) f g" unfolding agree_on_def by auto

lemma agree_on_comm[intro]: "agree_on X f g = agree_on X g f" unfolding agree_on_def by auto
lemma agree_on_refl[intro]:
  "agree_on R f f" unfolding agree_on_def by auto
lemma agree_on_trans:
  assumes "agree_on X f g" "agree_on X g h"
  shows "agree_on X f h" using assms unfolding agree_on_def by auto

lemma agree_on_equivp:
  shows "equivp (agree_on G)"
  by (auto intro:agree_on_trans intro!:equivpI simp:reflp_def symp_def transp_def agree_on_comm)

lemma agree_on_subset:
  assumes "f \<subseteq> g" "vertices G \<subseteq> Domain f" "univalent g"
  shows "agree_on G f g"
  using assms unfolding agree_on_def by auto

lemma agree_iff_subset[simp]:
  assumes "graph_homomorphism G X f" "univalent g"
  shows "agree_on G f g \<longleftrightarrow> f \<subseteq> g"
  using assms unfolding agree_on_def graph_homomorphism_def by auto

lemma agree_on_ext:
  assumes "agree_on G f\<^sub>1 f\<^sub>2"
  shows "agree_on G (f\<^sub>1 O g) (f\<^sub>2 O g)"
  using assms unfolding agree_on_def by auto

lemma agree_on_then_eq:
  assumes "agree_on G f\<^sub>1 f\<^sub>2" "Domain f\<^sub>1 = vertices G" "Domain f\<^sub>2 = vertices G"
  shows "f\<^sub>1 = f\<^sub>2"
proof -
  from assms have agr:"\<And> v. v\<in>Domain f\<^sub>1 \<Longrightarrow> f\<^sub>1 `` {v} = f\<^sub>2 `` {v}" unfolding agree_on_def by auto
  have agr2:"\<And> v. v\<notin>Domain f\<^sub>1 \<Longrightarrow> f\<^sub>1 `` {v} = {}"
            "\<And> v. v\<notin>Domain f\<^sub>2 \<Longrightarrow> f\<^sub>2 `` {v} = {}" by auto
  with agr agr2 assms have "\<And> v. f\<^sub>1 `` {v} = f\<^sub>2 `` {v}" by blast
  thus ?thesis by auto
qed

lemma agree_on_subg_compose:
  assumes "agree_on R g h" "agree_on F f g" "subgraph F R"
  shows "agree_on F f h"
  using assms unfolding agree_on_def subgraph_def graph_union_iff by auto

definition extensible :: "('l,'x) Graph_PreRule \<Rightarrow> ('l,'v) labeled_graph \<Rightarrow> ('x \<times> 'v) set \<Rightarrow> bool"
  where
"extensible R G f \<equiv> (\<exists> g. graph_homomorphism (snd R) G g \<and> agree_on (fst R) f g)"

lemma extensibleI[intro]: (* not nice as a standard rule, since obtained variables cannot be used *)
  assumes "graph_homomorphism R2 G g" "agree_on R1 f g"
  shows "extensible (R1,R2) G f"
  using assms unfolding extensible_def by auto

lemma extensibleD[elim]:
  assumes "extensible R G f"
          "\<And> g. graph_homomorphism (snd R) G g \<Longrightarrow> agree_on (fst R) f g \<Longrightarrow> thesis"
  shows thesis using assms extensible_def by blast

lemma extensible_refl_concr[simp]:
  assumes "graph_homomorphism (LG e\<^sub>1 v) G f"
  shows "extensible (LG e\<^sub>1 v, LG e\<^sub>2 v) G f \<longleftrightarrow> graph_homomorphism (LG e\<^sub>2 v) G f"
proof
  assume "extensible (LG e\<^sub>1 v, LG e\<^sub>2 v) G f"
  then obtain g where g: "graph_homomorphism (LG e\<^sub>2 v) G g" "agree_on (LG e\<^sub>1 v) f g"
    unfolding extensible_def by auto
  hence d:"Domain f = Domain g" "univalent f" "univalent g" using assms
    unfolding graph_homomorphism_def by auto
  from g have subs:"f \<subseteq> g"
    by(subst agree_iff_subset[symmetric,OF assms],auto simp:graph_homomorphism_def)
  with d have "f = g" by auto
  thus "graph_homomorphism (LG e\<^sub>2 v) G f" using g by auto
qed (auto simp: assms extensible_def)

lemma   extensible_chain_sup[intro]:
assumes "chain S" "extensible R (S j) f"
shows "extensible R (chain_sup S) f"
proof -
  from assms obtain g where g:"graph_homomorphism (snd R) (S j) g \<and> agree_on (fst R) f g"
    unfolding extensible_def by auto
  have [simp]:"g O Id_on (vertices (S j)) = g" using g[unfolded graph_homomorphism_def] by auto
  from g assms(1)
  have "graph_homomorphism (snd R) (S j) g" "subgraph (S j) (chain_sup S)" by auto
  from graph_homomorphism_composes[OF this]
  have "graph_homomorphism (snd R) (chain_sup S) g" by auto
  thus ?thesis using g unfolding extensible_def by blast
qed

text \<open>Definition 11.\<close>
definition maintained :: "('l,'x) Graph_PreRule \<Rightarrow> ('l,'v) labeled_graph \<Rightarrow> bool"
  where "maintained R G \<equiv> \<forall> f. graph_homomorphism (fst R) G f \<longrightarrow> extensible R G f"

abbreviation maintainedA
  :: "('l,'x) Graph_PreRule set \<Rightarrow> ('l, 'v) labeled_graph \<Rightarrow> bool"
  where "maintainedA Rs G \<equiv> \<forall> R\<in>Rs. maintained R G"

lemma maintainedI[intro]:
  assumes "\<And> f. graph_homomorphism A G f \<Longrightarrow> extensible (A,B) G f"
  shows "maintained (A,B) G"
  using assms unfolding maintained_def by auto
lemma maintainedD[dest]:
  assumes "maintained (A,B) G" "graph_homomorphism A G f"
  shows "extensible (A,B) G f"
  using assms unfolding maintained_def by auto

lemma maintainedD2[dest]:
  assumes "maintained (A,B) G" "graph_homomorphism A G f"
          "\<And> g. graph_homomorphism B G g \<Longrightarrow> f \<subseteq> g \<Longrightarrow> thesis"
        shows thesis
  using maintainedD[OF assms(1,2),unfolded extensible_def]
proof
  fix g
  assume "graph_homomorphism (snd (A, B)) G g \<and> agree_on (fst (A, B)) f g"
  hence "graph_homomorphism B G g" "f \<subseteq> g"
    using assms(2) unfolding graph_homomorphism_def2 agree_on_def by auto
  from assms(3)[OF this] show thesis.
qed

lemma extensible_refl[intro]:
  "graph_homomorphism R G f \<Longrightarrow> extensible (R,R) G f"
  unfolding extensible_def by auto

lemma maintained_refl[intro]:
  "maintained (R,R) G" by auto

text \<open>Alternate version of definition 8.\<close>
definition fin_maintained :: "('l,'x) Graph_PreRule \<Rightarrow> ('l,'v) labeled_graph \<Rightarrow> bool"
  where
"fin_maintained R G \<equiv> \<forall> F f. finite_graph F
                         \<longrightarrow> subgraph F (fst R)
                         \<longrightarrow> extensible (F,fst R) G f
                         \<longrightarrow> graph_homomorphism F G f
                         \<longrightarrow> extensible (F,snd R) G f"

lemma fin_maintainedI [intro]:
  assumes "\<And> F f. finite_graph F
           \<Longrightarrow> subgraph F (fst R)
           \<Longrightarrow> extensible (F,fst R) G f
           \<Longrightarrow> graph_homomorphism F G f
           \<Longrightarrow> extensible (F,snd R) G f"
  shows "fin_maintained R G" using assms unfolding fin_maintained_def by auto

lemma maintained_then_fin_maintained[simp]:
  assumes maintained:"maintained R G"
  shows "fin_maintained R G"
proof
  fix F f
  assume subg:"subgraph F (fst R)"
     and ext:"extensible (F, fst R) G f" and igh:"graph_homomorphism F G f"
  from ext[unfolded extensible_def prod.sel] obtain g where
     g:"graph_homomorphism (fst R) G g" "agree_on F f g" by blast
  from maintained[unfolded maintained_def,rule_format,OF g(1)] g(2) subg
       agree_on_subg_compose
  show "extensible (F, snd R) G f" unfolding extensible_def prod.sel by blast
qed

lemma fin_maintained_maintained:
  assumes "finite_graph (fst R)"
  shows "fin_maintained R G \<longleftrightarrow> maintained R G" (is "?lhs = ?rhs")
proof
  from assms rev_finite_subset
  have fin:"finite (vertices (fst R))"
           "finite (edges (fst R))"
           "subgraph (fst R) (fst R)"
    unfolding subgraph_def graph_union_iff by auto
  assume ?lhs
  with fin have "extensible (fst R, fst R) G f \<Longrightarrow> graph_homomorphism (fst R) G f
         \<Longrightarrow> extensible R G f" for f unfolding fin_maintained_def by auto 
  thus ?rhs by (simp add: extensible_refl maintained_def)
qed simp

lemma extend_for_chain:
assumes "g 0 = f"
    and "\<And> i. graph_homomorphism (S i) C (g i)"
    and "\<And> i. agree_on (S i) (g i) (g (i + 1))"
    and "chain S"
  shows "extensible (S 0, chain_sup S) C f"
proof
  let ?g = "\<Union>i. g i"
  from assms(4)[unfolded chain_def subgraph_def graph_union_iff]
  have v:"vertices (S i) \<subseteq> vertices (S (i + 1))"
    and e:"edges (S i) \<subseteq> edges (S (i + 1))" for i by auto
  { fix a b i
    assume a:"(a, b) \<in> g i"
    hence "a \<in> vertices (S i)" using assms(2)[of i]
      unfolding graph_homomorphism_def2 by auto
    from assms(3)[unfolded agree_on_def,rule_format,OF this] a
    have "(a, b) \<in> g (Suc i)" by auto
  }
  hence gi:"g i \<subseteq> g (Suc i)" for i by auto
  have gij:"i \<le> j \<Longrightarrow> g i \<subseteq> g j" for i j proof(induct j)
    case (Suc j) with gi[of j] show ?case by (cases "i = Suc j",auto)
  qed auto
  from assms(1) have f_subset:"f \<subseteq> ?g" by auto
  from assms(2)[of 0,unfolded assms(1)] have domf:"Domain f = vertices (S 0)"
    and grC:"graph C" and v_dom:"vertices (S i) = Domain (g i)" for i using assms(2)
    unfolding graph_homomorphism_def by auto
  { fix x y z i j assume "(x, y) \<in> g i" "(x, z) \<in> g j"
    with gij[of i "max i j"] gij[of j "max i j"]
    have "(x,y) \<in> g (max i j)" "(x,z) \<in> g (max i j)" by auto
    with assms(2)[unfolded graph_homomorphism_def]
    have "y = z" by auto
  } note univ_strong = this
  hence univ:"univalent ?g" unfolding univalent_def by auto
  { fix xa x i
    assume "(xa, x) \<in> g i"
    hence "x \<in> vertices (map_graph (g i) (S i))"
      using assms(2) unfolding graph_homomorphism_def by auto
    hence "x \<in> vertices C"
      using assms(2) unfolding graph_homomorphism_def2 graph_union_iff by blast
  } note eq_v = this
  { fix l x y x' y' j i
    assume "(l,x,y) \<in> edges (S j)" "(x, x') \<in> g i" "(y, y') \<in> g i"
    with gij[of i "max i j"] gij[of j "max i j"]
         chain[OF assms(4),unfolded subgraph_def graph_union_iff, of i "max i j"]
         chain[OF assms(4),unfolded subgraph_def graph_union_iff, of j "max i j"]
    have "(x,x') \<in> g (max i j)" "(y,y') \<in> g (max i j)"
         "(l,x,y) \<in> edges (S (max i j))" by auto
    hence "(l, x', y') \<in> edges C"
      using assms(2)[unfolded graph_homomorphism_def2 graph_union_iff] by auto
  } note eq_e = this
  have "graph_union (map_graph (g i) (chain_sup S)) C = C" for i
    unfolding graph_union_iff using eq_e eq_v
    unfolding graph_homomorphism_def2 chain_sup_def by auto
  hence subg:"graph_union (map_graph ?g (chain_sup S)) C = C"
    apply (rule graph_map_union) using gij by auto
  have "(\<Union>i. vertices (S i)) = (\<Union>i. Domain (g i))" using v_dom by auto
  hence vd:"vertices (chain_sup S) = Domain ?g"
    unfolding chain_sup_def by auto
  show "graph_homomorphism (chain_sup S) C ?g"
    unfolding graph_homomorphism_def2
    using univ chain_sup_graph[OF assms(4)] grC vd subg by auto
  show "agree_on (S 0) f ?g" using agree_on_subset[OF f_subset _ univ] domf by auto
qed

text \<open>Definition 8, second part.\<close>
definition consequence_graph
  where "consequence_graph Rs G \<equiv> graph G \<and> (\<forall> R \<in> Rs. subgraph (fst R) (snd R) \<and> maintained R G)"

lemma consequence_graphI[intro]:
  assumes "\<And> R. R\<in> Rs \<Longrightarrow> maintained R G"
          "\<And> R. R\<in> Rs \<Longrightarrow> subgraph (fst R) (snd R)"
          "graph G"
  shows "consequence_graph Rs G"
  unfolding consequence_graph_def fin_maintained_def using assms by auto

lemma consequence_graphD[dest]:
  assumes "consequence_graph Rs G"
  shows "\<And> R. R\<in> Rs \<Longrightarrow> maintained R G"
        "\<And> R. R\<in> Rs \<Longrightarrow> subgraph (fst R) (snd R)"
        "graph G"
  using assms unfolding consequence_graph_def fin_maintained_def by auto

text \<open>Definition 8 states: If furthermore S is a subgraph of G,
    and (S, G) is maintained in each consequence graph maintaining Rs,
    then G is a least consequence graph of S maintaining Rs.
    Note that the type of 'each consequence graph' isn't given here.
   Taken literally, this should mean 'for every possible type'.
   We avoid quantifying on types by making the type an argument.
   Consequently, when proving 'least', the first argument should be free.\<close>
definition least
  :: "'x itself \<Rightarrow> (('l, 'v) Graph_PreRule) set \<Rightarrow> ('l, 'c) labeled_graph \<Rightarrow> ('l, 'c) labeled_graph \<Rightarrow> bool"
  where "least _ Rs S G \<equiv> subgraph S G \<and> 
            (\<forall> C :: ('l, 'x) labeled_graph. consequence_graph Rs C \<longrightarrow> maintained (S,G) C)"

lemma leastI[intro]:
assumes "subgraph S (G:: ('l, 'c) labeled_graph)"
        "\<And> C :: ('l, 'x) labeled_graph. consequence_graph Rs C \<Longrightarrow> maintained (S,G) C"
      shows "least (t:: 'x itself) Rs S G"
  using assms unfolding least_def by auto

definition least_consequence_graph
  :: "'x itself \<Rightarrow> (('l, 'v) Graph_PreRule) set
     \<Rightarrow> ('l, 'c) labeled_graph \<Rightarrow> ('l, 'c) labeled_graph \<Rightarrow> bool"
  where "least_consequence_graph t Rs S G \<equiv> consequence_graph Rs G \<and> least t Rs S G"

lemma least_consequence_graphI[intro]:
assumes "consequence_graph Rs (G:: ('l, 'c) labeled_graph)"
        "subgraph S G"
        "\<And> C :: ('l, 'x) labeled_graph. consequence_graph Rs C \<Longrightarrow> maintained (S,G) C"
      shows "least_consequence_graph (t:: 'x itself) Rs S G"
  using assms unfolding least_consequence_graph_def least_def by auto

text \<open>Definition 12.\<close>
definition fair_chain where
  "fair_chain Rs S \<equiv> chain S \<and> 
    (\<forall> R f i. (R \<in> Rs \<and> graph_homomorphism (fst R) (S i) f) \<longrightarrow> (\<exists> j. extensible R (S j) f))"

lemma fair_chainI[intro]:
  assumes "chain S"
    "\<And> R f i. R \<in> Rs \<Longrightarrow> graph_homomorphism (fst R) (S i) f \<Longrightarrow> \<exists> j. extensible R (S j) f"
  shows "fair_chain Rs S"
  using assms unfolding fair_chain_def by blast

lemma fair_chainD:
  assumes "fair_chain Rs S"
  shows "chain S"
        "R \<in> Rs \<Longrightarrow> graph_homomorphism (fst R) (S i) f \<Longrightarrow> \<exists> j. extensible R (S j) f"
  using assms unfolding fair_chain_def by blast+

lemma find_graph_occurence_vertices:
  assumes "chain S" "finite V" "univalent f" "f `` V \<subseteq> vertices (chain_sup S)"
  shows "\<exists> i. f `` V \<subseteq> vertices (S i)"
  using assms(2,4)
proof(induct V)
  case empty thus ?case by auto
next
  case (insert v V)
  from insert.prems have V:"f `` V \<subseteq> vertices (chain_sup S)"
    and v:"f `` {v} \<subseteq> vertices (chain_sup S)" by auto
  from insert.hyps(3)[OF V] obtain i where i:"f `` V \<subseteq> vertices (S i)" by auto
  have "\<exists> j. f `` {v} \<subseteq> vertices (S j)"
  proof(cases "(f `` {v}) = {}")
    case False
    then obtain v' where f:"(v,v') \<in> f" by auto
    hence "v' \<in> vertices (chain_sup S)" using v by auto
    then show ?thesis using assms(3) f unfolding chain_sup_def by auto
  qed auto
  then obtain j where j:"f `` {v} \<subseteq> vertices (S j)" by blast
  have sg:"subgraph (S i) (S (max i j))" "subgraph (S j) (S (max i j))"
    by(rule chain[OF assms(1)],force)+
  have V:"(f \<inter> V \<times> UNIV) `` V \<subseteq> vertices (S (max i j))"
    using i subgraph_subset[OF sg(1)] by auto
  have v:"f `` {v} \<subseteq> vertices (S (max i j))" using j subgraph_subset[OF sg(2)] by auto
  have "f `` insert v V \<subseteq> vertices (S (max i j))" using v V by auto
  thus ?case by blast
qed

lemma find_graph_occurence_edges:
  assumes "chain S" "finite E" "univalent f"
        "on_triple f `` E \<subseteq> edges (chain_sup S)"
      shows "\<exists> i. on_triple f `` E \<subseteq> edges (S i)"
  using assms(2,4)
proof(induct E)
  case empty thus ?case unfolding graph_homomorphism_def by auto
next
  case (insert e E)
  have univ:"univalent (on_triple f)" using assms(3) by auto
  have [simp]:"restrict (S i) = S i" for i
    using chain[OF assms(1),unfolded subgraph_def,of i i] by auto
  from insert.prems have E:"on_triple f `` E \<subseteq> edges (chain_sup S)"
    and e:"on_triple f `` {e} \<subseteq> edges (chain_sup S)" by auto
  with insert.hyps obtain i where i:"on_triple f `` E \<subseteq> edges (S i)" by auto
  have "\<exists> j. on_triple f `` {e} \<subseteq> edges (S j)"
  proof(cases "on_triple f `` {e} = {}")
    case False
    then obtain e' where f:"(e,e') \<in> on_triple f" by auto
    hence "e' \<in> edges (chain_sup S)" using e by auto
    then show ?thesis using univ f unfolding chain_sup_def by auto
  qed auto
  then obtain j where j:"on_triple f `` {e} \<subseteq> edges (S j)" by blast
  have sg:"subgraph (S i) (S (max i j))" "subgraph (S j) (S (max i j))"
    by(rule chain[OF assms(1)],force)+
  have E:"on_triple f `` E \<subseteq> edges (S (max i j))"
    using i subgraph_subset[OF sg(1)] by auto
  have e:"on_triple f `` {e} \<subseteq> edges (S (max i j))" using j subgraph_subset[OF sg(2)] by auto
  have "on_triple f `` insert e E \<subseteq> edges (S (max i j))" using e E by auto
  thus ?case by blast
qed

lemma find_graph_occurence:
  assumes "chain S" "finite E" "finite V" "graph_homomorphism (LG E V) (chain_sup S) f"
  shows "\<exists> i. graph_homomorphism (LG E V) (S i) f"
proof -
  have [simp]:"restrict (S i) = S i" for i
    using chain[OF assms(1),unfolded subgraph_def,of i i] by auto
  from assms[unfolded graph_homomorphism_def edge_preserving labeled_graph.sel]
  have u:"univalent f" 
   and e:"on_triple f `` E \<subseteq> edges (chain_sup S)"
   and v:"f `` V \<subseteq> vertices (chain_sup S)"
    by blast+
  from find_graph_occurence_edges[OF assms(1,2) u e]
  obtain i where i:"on_triple f `` E \<subseteq> edges (S i)" by blast
  from find_graph_occurence_vertices[OF assms(1,3) u v]
  obtain j where j:"f `` V \<subseteq> vertices (S j)" by blast
  have sg:"subgraph (S i) (S (max i j))" "subgraph (S j) (S (max i j))"
    by(rule chain[OF assms(1)],force)+
  have e:"on_triple f `` E \<subseteq> edges (S (max i j))"
   and v:"f `` V \<subseteq> vertices (S (max i j))"
    using i j subgraph_subset(2)[OF sg(1)] subgraph_subset(1)[OF sg(2)] by auto
  have "graph_homomorphism (LG E V) (S (max i j)) f"
  proof(rule graph_homomorphismI)
    from assms[unfolded graph_homomorphism_def edge_preserving labeled_graph.sel] e v
    show "vertices (LG E V) = Domain f"
     and "univalent f"
     and "LG E V = restrict (LG E V)"
     and "f `` vertices (LG E V) \<subseteq> vertices (S (max i j))" 
     and "edge_preserving f (edges (LG E V)) (edges (S (max i j)))"
     and "S (max i j) = restrict (S (max i j))" by auto
  qed
  thus ?thesis by auto
qed


text \<open>Lemma 3.
      Recall that in the paper, graph rules use finite graphs, i.e. both sides should be finite.
      We strengthen lemma 3 by requiring only the left hand side to be a finite graph.\<close>
lemma fair_chain_impl_consequence_graph:
  assumes "fair_chain Rs S" "\<And> R. R \<in> Rs \<Longrightarrow> subgraph (fst R) (snd R) \<and> finite_graph (fst R)"
  shows "consequence_graph Rs (chain_sup S)"
proof -
  { fix R assume a:"R \<in> Rs"
    have fin_v:"finite (vertices (fst R))" and fin_e: "finite (edges (fst R))"
      using assms(2)[OF a] by auto
    { fix f assume "graph_homomorphism (LG (edges (fst R)) (vertices (fst R))) (chain_sup S) f"
      with find_graph_occurence[OF fair_chainD(1)[OF assms(1)] fin_e fin_v]  
      obtain i where "graph_homomorphism (fst R) (S i) f" by auto
      from fair_chainD(2)[OF assms(1) a this] obtain j
         where "extensible R (S j) f" by blast
      hence "extensible R (chain_sup S) f" using fair_chainD(1)[OF assms(1)] by auto
    }
    hence "maintained R (chain_sup S)" unfolding maintained_def by auto
  } note mnt = this
  from assms have "chain S" unfolding fair_chain_def by auto
  thus ?thesis unfolding consequence_graph_def using mnt assms(2) by blast
qed

text \<open>We extract the weak universal property from the definition of weak pushout step.
      Again, the paper allows for arbitrary types in the quantifier,
          but we fix the type here in the definition that will be used in @{term pushout_step}.
          The type used here should suffice (and we cannot quantify over types anyways)\<close>
definition weak_universal ::
    "'x itself \<Rightarrow> ('a, 'c) Graph_PreRule \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow>
     ('c \<times> 'b) set \<Rightarrow> ('c \<times> 'b) set \<Rightarrow> bool" where
"weak_universal _ R G\<^sub>1 G\<^sub>2 f\<^sub>1 f\<^sub>2 \<equiv> (\<forall> h\<^sub>1 h\<^sub>2 G::('a, 'x) labeled_graph.
             (graph_homomorphism (snd R) G h\<^sub>1 \<and> graph_homomorphism G\<^sub>1 G h\<^sub>2 \<and> f\<^sub>1 O h\<^sub>2 \<subseteq> h\<^sub>1)
         \<longrightarrow> (\<exists> h. graph_homomorphism G\<^sub>2 G h \<and> h\<^sub>2 \<subseteq> h))"

lemma weak_universalD[dest]:
  assumes "weak_universal (t:: 'x itself) R (G\<^sub>1::('a, 'b) labeled_graph) G\<^sub>2 f\<^sub>1 f\<^sub>2"
  shows "\<And>  h\<^sub>1 h\<^sub>2 G::('a, 'x) labeled_graph.
         graph_homomorphism (snd R) G h\<^sub>1 \<Longrightarrow> graph_homomorphism G\<^sub>1 G h\<^sub>2 \<Longrightarrow> f\<^sub>1 O h\<^sub>2 \<subseteq> h\<^sub>1
         \<Longrightarrow> (\<exists> h. graph_homomorphism G\<^sub>2 G h \<and> h\<^sub>2 \<subseteq> h)"
  using assms unfolding weak_universal_def by metis

lemma weak_universalI[intro]:
  assumes "\<And> h\<^sub>1 h\<^sub>2 G::('a, 'x) labeled_graph.
         graph_homomorphism (snd R) G h\<^sub>1 \<Longrightarrow> graph_homomorphism G\<^sub>1 G h\<^sub>2 \<Longrightarrow> f\<^sub>1 O h\<^sub>2 \<subseteq> h\<^sub>1
         \<Longrightarrow> (\<exists> h. graph_homomorphism G\<^sub>2 G h \<and> h\<^sub>2 \<subseteq> h)"
  shows "weak_universal (t:: 'x itself) R (G\<^sub>1::('a, 'b) labeled_graph) G\<^sub>2 f\<^sub>1 f\<^sub>2"
  using assms unfolding weak_universal_def by force


text \<open>Definition 13\<close>
definition pushout_step ::
    "'x itself \<Rightarrow> ('a, 'c) Graph_PreRule \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow> bool" where
"pushout_step t R G\<^sub>1 G\<^sub>2 \<equiv> subgraph G\<^sub>1 G\<^sub>2 \<and> 
  (\<exists> f\<^sub>1 f\<^sub>2. graph_homomorphism (fst R) G\<^sub>1 f\<^sub>1 \<and>
           graph_homomorphism (snd R) G\<^sub>2 f\<^sub>2 \<and>
           f\<^sub>1 \<subseteq> f\<^sub>2 \<and>
           weak_universal t R G\<^sub>1 G\<^sub>2 f\<^sub>1 f\<^sub>2
  )"

text \<open>Definition 14\<close>
definition Simple_WPC ::
    "'x itself \<Rightarrow> (('a, 'b) Graph_PreRule) set \<Rightarrow> (('a, 'd) graph_seq) \<Rightarrow> bool" where
"Simple_WPC t Rs S \<equiv> set_of_graph_rules Rs
   \<and> (\<forall> i. (graph (S i) \<and> S i = S (Suc i)) \<or> (\<exists> R \<in> Rs. pushout_step t R (S i) (S (Suc i))))"

lemma Simple_WPCI [intro]:
  assumes "set_of_graph_rules Rs" "graph (S 0)"
          "\<And> i. (S i = S (Suc i)) \<or> (\<exists> R \<in> Rs. pushout_step t R (S i) (S (Suc i)))"
        shows "Simple_WPC t Rs S"
proof -
  have "graph (S i)" for i proof(induct i)
    case (Suc i)
    then show ?case using assms(3) unfolding pushout_step_def subgraph_def by metis
  qed (fact assms)
  thus ?thesis using assms unfolding Simple_WPC_def by auto
qed

lemma Simple_WPC_Chain[simp]:
  assumes "Simple_WPC t Rs S"
  shows "chain S"
proof -
  have "subgraph (S i) (S (Suc i))" for i using assms
    unfolding Simple_WPC_def pushout_step_def by (cases "graph (S i) \<and> S i = S (Suc i)",auto)
  thus ?thesis unfolding chain_def by auto
qed


text \<open>Definition 14, second part. \<close>
inductive WPC ::
    "'x itself \<Rightarrow> (('a, 'b) Graph_PreRule) set \<Rightarrow> (('a, 'd) graph_seq) \<Rightarrow> bool"
  where
    wpc_simpl [simp, intro]: "Simple_WPC t Rs S \<Longrightarrow> WPC t Rs S"
  | wpc_combo [simp, intro]: "chain S \<Longrightarrow> (\<And> i. \<exists> S'. S' 0 = S i \<and> chain_sup S' = S (Suc i) \<and> WPC t Rs S') \<Longrightarrow> WPC t Rs S"

lemma extensible_from_chainI:
  assumes ch:"chain S"
  and igh:"graph_homomorphism (S 0) C f"
  and ind:"\<And> f i. graph_homomorphism (S i) C f \<Longrightarrow>
                \<exists>h. (graph_homomorphism (S (Suc i)) C h) \<and> agree_on (S i) f h"
  shows "extensible (S 0,chain_sup S) C f"
proof -
  have ch:"chain S" using assms by auto
  hence r0:"\<exists>x. graph_homomorphism (S 0) C x \<and> (0 = 0 \<longrightarrow> x = f)"
    using igh by auto
  { fix i x
    assume "graph_homomorphism (S i) C x \<and> (i = 0 \<longrightarrow> x = f)"
    hence "graph_homomorphism (S i) C x" by auto
    from ind[OF this]
    have "\<exists>y. (graph_homomorphism (S (Suc i)) C y \<and> (Suc i = 0 \<longrightarrow> y = f)) \<and> agree_on (S i) x y"
      by auto
  }
  with r0
  have "\<exists> g. (\<forall> i. (graph_homomorphism (S i) C (g i) \<and> (i = 0 \<longrightarrow> g i = f))
                \<and> agree_on (S i) (g i) (g (Suc i)) )" by (rule dependent_nat_choice)
  then obtain g where
       mtn:"g 0 = f"
           "graph_homomorphism (S i) C (g i)"
           "agree_on (S i) (g i) (g (i + 1))" for i by auto
  from extend_for_chain[OF mtn ch] show ?thesis.
qed

text \<open>Towards Lemma 4, this is the key inductive property.\<close>
lemma wpc_least:
  assumes "WPC (t:: 'x itself) Rs S"
  shows "least t Rs (S 0) (chain_sup S)"
  using assms
proof(induction S)
  case (wpc_simpl t Rs S)
  hence gr:"set_of_graph_rules Rs"
    and ps:"\<And> i. S i = S (Suc i) \<or> (\<exists>R\<in>Rs. pushout_step t R (S i) (S (i + 1)))"
    unfolding Simple_WPC_def by auto
  have ch[intro]:"chain S" using wpc_simpl by auto
  show ?case
  proof fix C::"('a,'x) labeled_graph"
    assume cgC:"consequence_graph Rs C"
    show "maintained (S 0, chain_sup S) C"
    proof(standard,rule extensible_from_chainI,goal_cases)
      case (3 f x i)
      show ?case proof(cases "S i = S (Suc i)")
        case True
        with 3 show ?thesis by auto
      next
        case False
        with ps[of i,unfolded pushout_step_def] obtain R f\<^sub>1 f\<^sub>2 where
        R:"(fst R,snd R) \<in> Rs" and f\<^sub>1:"graph_homomorphism (fst R) (S i) f\<^sub>1"
        and wu:"weak_universal t R (S i) (S (i + 1)) f\<^sub>1 f\<^sub>2" by auto
        from graph_homomorphism_composes[OF f\<^sub>1 3(2)]
        have ih_comp:"graph_homomorphism (fst R) C (f\<^sub>1 O x)".
        with maintainedD[OF consequence_graphD(1)[OF cgC R]]
        have "extensible (fst R, snd R) C (f\<^sub>1 O x)" by auto
        from this[unfolded extensible_def prod.sel]
        obtain g where g:"graph_homomorphism (snd R) C g" "f\<^sub>1 O x \<subseteq> g"
          using agree_iff_subset[OF ih_comp] unfolding graph_homomorphism_def by auto
        from weak_universalD[OF wu g(1) 3(2) g(2)] obtain h where
          h:"graph_homomorphism (S (i + 1)) C h" "x \<subseteq> h" by auto
        hence "agree_on (S i) x h"
          by(subst agree_iff_subset[OF 3(2)], auto simp:graph_homomorphism_def)
        then show ?thesis using h(1) by auto
      qed
    qed auto
  qed auto
next
  case (wpc_combo S t Rs)
  hence ps:"\<And> i. \<exists>S'. S' 0 = S i \<and>
         chain_sup S' = S (Suc i) \<and>
         WPC t Rs S' \<and>
         least t Rs (S' 0) (chain_sup S')"
    and ch[intro]:"chain S" unfolding Simple_WPC_def by auto
  show ?case proof fix C :: "('a, 'x) labeled_graph"
    assume cgC:"consequence_graph Rs C"
    show "maintained (S 0, chain_sup S) C"
    proof(standard,rule extensible_from_chainI,goal_cases)
      case (3 f g i)
      from ps[of i] have "least t Rs (S i) (S (Suc i))" by auto
      with cgC have ss:"subgraph (S i) (S (Suc i))" "maintained (S i, S (Suc i)) C"
        unfolding least_def by auto
      from ss(2) 3(2) have "extensible (S i, S (Suc i)) C g" by auto
      thus ?case unfolding extensible_def prod.sel.
    qed auto
  qed auto
qed

text \<open>Lemma 4.\<close>
lemma wpc_least_consequence_graph:
  assumes "WPC t Rs S" "consequence_graph Rs (chain_sup S)"
  shows "least_consequence_graph t Rs (S 0) (chain_sup S)"
  using wpc_least assms unfolding least_consequence_graph_def by auto

end