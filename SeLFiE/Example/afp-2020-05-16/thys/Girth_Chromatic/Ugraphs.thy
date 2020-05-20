theory Ugraphs
imports
  Girth_Chromatic_Misc
begin

section \<open>Undirected Simple Graphs\<close>

text \<open>
  In this section, we define some basics of graph theory needed to formalize
  the Chromatic-Girth theorem.
\<close>

text \<open>
  For readability, we introduce synonyms for the types of vertexes, edges,
  graphs and walks.
\<close>
type_synonym uvert = nat
type_synonym uedge = "nat set"
type_synonym ugraph = "uvert set \<times> uedge set"
type_synonym uwalk = "uvert list"

abbreviation uedges :: "ugraph \<Rightarrow> uedge set" where
  "uedges G \<equiv> snd G"

abbreviation uverts :: "ugraph \<Rightarrow> uvert set" where
  "uverts G \<equiv> fst G"

fun mk_uedge :: "uvert \<times> uvert \<Rightarrow> uedge" where
   "mk_uedge (u,v) = {u,v}"

text \<open>All edges over a set of vertexes @{term S}:\<close>
definition "all_edges S \<equiv> mk_uedge ` {uv \<in> S \<times> S. fst uv \<noteq> snd uv}"

definition uwellformed :: "ugraph \<Rightarrow> bool" where
  "uwellformed G \<equiv> (\<forall>e\<in>uedges G. card e = 2 \<and> (\<forall>u \<in> e. u \<in> uverts G))"

fun uwalk_edges :: "uwalk \<Rightarrow> uedge list" where
    "uwalk_edges [] = []"
  | "uwalk_edges [x] = []"
  | "uwalk_edges (x # y # ys) = {x,y} # uwalk_edges (y # ys)"

definition uwalk_length :: "uwalk \<Rightarrow> nat" where
  "uwalk_length p \<equiv> length (uwalk_edges p)"

definition uwalks :: "ugraph \<Rightarrow> uwalk set" where
  "uwalks G \<equiv> {p. set p \<subseteq> uverts G \<and> set (uwalk_edges p) \<subseteq> uedges G \<and> p \<noteq> []}"

definition ucycles :: "ugraph \<Rightarrow> uwalk set" where
  "ucycles G \<equiv> {p. uwalk_length p \<ge> 3 \<and> p \<in> uwalks G \<and> distinct (tl p) \<and> hd p = last p}"

definition remove_vertex :: "ugraph \<Rightarrow> nat \<Rightarrow> ugraph" ("_ -- _" [60,60] 60) where
  "remove_vertex G u \<equiv> (uverts G - {u}, uedges G - {A \<in> uedges G. u \<in> A})"


subsection \<open>Basic Properties\<close>

lemma uwalk_length_conv: "uwalk_length p = length p - 1"
  by (induct p rule: uwalk_edges.induct) (auto simp: uwalk_length_def)

lemma all_edges_mono:
  "vs \<subseteq> ws \<Longrightarrow> all_edges vs \<subseteq> all_edges ws"
unfolding all_edges_def by auto

lemma all_edges_subset_Pow: "all_edges A \<subseteq> Pow A"
  by (auto simp: all_edges_def)

lemma in_mk_uedge_img: "(a,b) \<in> A \<or> (b,a) \<in> A \<Longrightarrow> {a,b} \<in> mk_uedge ` A"
  by (auto intro: rev_image_eqI)

lemma distinct_edgesI:
  assumes "distinct p" shows "distinct (uwalk_edges p)"
proof -
  from assms have "?thesis" "\<And>u. u \<notin> set p \<Longrightarrow> (\<And>v. u \<noteq> v \<Longrightarrow> {u,v} \<notin> set (uwalk_edges p))"
    by (induct p rule: uwalk_edges.induct) auto
  then show ?thesis by simp
qed

lemma finite_ucycles:
  assumes "finite (uverts G)"
  shows "finite (ucycles G)"
proof -
  have "ucycles G \<subseteq> {xs. set xs \<subseteq> uverts G \<and> length xs \<le> Suc (card (uverts G))}"
  proof (rule, simp)
    fix p assume "p \<in> ucycles G"
    then have "distinct (tl p)" and "set p \<subseteq> uverts G"
      unfolding ucycles_def uwalks_def by auto
    moreover
    then have "set (tl p) \<subseteq> uverts G"
      by (auto simp: list_set_tl)
    with assms have "card (set (tl p)) \<le> card (uverts G)"
      by (rule card_mono)
    then have "length (p) \<le> 1 + card (uverts G)"
      using distinct_card[OF \<open>distinct (tl p)\<close>] by auto
    ultimately show "set p \<subseteq> uverts G \<and> length p \<le> Suc (card (uverts G))" by auto
  qed
  moreover
  have "finite {xs. set xs \<subseteq> uverts G \<and> length xs \<le> Suc (card (uverts G))}"
    using assms by (rule finite_lists_length_le)
  ultimately
  show ?thesis by (rule finite_subset)
qed

lemma ucycles_distinct_edges:
  assumes "c \<in> ucycles G" shows "distinct (uwalk_edges c)"
proof -
  from assms have c_props: "distinct (tl c)" "4 \<le> length c" "hd c = last c"
    by (auto simp add: ucycles_def uwalk_length_conv)
  then have "{hd c, hd (tl c)} \<notin> set (uwalk_edges (tl c))"
  proof (induct c rule: uwalk_edges.induct)
    case (3 x y ys)
    then have "hd ys \<noteq> last ys" by (cases ys) auto
    moreover
    from 3 have "uwalk_edges (y # ys) = {y, hd ys} # uwalk_edges ys"
      by (cases ys) auto
    moreover
    { fix xs have "set (uwalk_edges xs) \<subseteq> Pow (set xs)"
        by (induct xs rule: uwalk_edges.induct) auto }
    ultimately
    show ?case using 3 by auto
  qed simp_all
  moreover
  from assms have "distinct (uwalk_edges (tl c))"
    by (intro distinct_edgesI) (simp add: ucycles_def)
  ultimately
  show ?thesis by (cases c rule: list_exhaust3) auto
qed

lemma card_left_less_pair:
  fixes A :: "('a :: linorder) set"
  assumes "finite A"
  shows "card {(a,b). a \<in> A \<and> b \<in> A \<and> a < b}
    = (card A * (card A - 1)) div 2"
using assms
proof (induct A)
  case (insert x A)

  show ?case
  proof (cases "card A")
    case (Suc n)
    have "{(a,b). a \<in> insert x A \<and> b \<in> insert x A \<and> a < b}
        = {(a,b). a \<in> A \<and> b \<in> A \<and> a < b} \<union> (\<lambda>a. if a < x then (a,x) else (x,a)) ` A"
      using \<open>x \<notin> A\<close> by (auto simp: order_less_le)
    moreover
    have "finite {(a,b). a \<in> A \<and> b \<in> A \<and> a < b}"
      using insert by (auto intro: finite_subset[of _ "A \<times> A"])
    moreover 
    have "{(a,b). a \<in> A \<and> b \<in> A \<and> a < b} \<inter> (\<lambda>a. if a < x then (a,x) else (x,a)) ` A = {}"
      using \<open>x \<notin> A\<close> by auto
    moreover have "inj_on (\<lambda>a. if a < x then (a, x) else (x, a)) A"
      by (auto intro: inj_onI split: if_split_asm)
    ultimately show ?thesis using insert Suc
      by (simp add: card_Un_disjoint card_image del: if_image_distrib)
  qed (simp add: card_eq_0_iff insert)
qed simp

lemma card_all_edges:
  assumes "finite A"
  shows "card (all_edges A) = card A choose 2"
proof -
  have inj_on_mk_uedge: "inj_on mk_uedge {(a,b). a < b}"
    by (rule inj_onI) (auto simp: doubleton_eq_iff)
  have "all_edges A = mk_uedge ` {(a,b). a \<in> A \<and> b \<in> A \<and> a < b}" (is "?L = ?R")
    by (auto simp: all_edges_def intro!: in_mk_uedge_img)
  then have "card ?L = card ?R" by simp
  also have "\<dots> = card {(a,b). a \<in> A \<and> b \<in> A \<and> a < b}"
    using inj_on_mk_uedge by (blast intro: card_image subset_inj_on)
  also have "\<dots> = (card A * (card A - 1)) div 2"
    using card_left_less_pair using assms by simp
  also have "\<dots> = (card A choose 2)"
    by (simp add: n_choose_2_nat)
  finally show ?thesis .
qed

lemma verts_Gu: "uverts (G -- u) = uverts G - {u}"
  unfolding remove_vertex_def by simp

lemma edges_Gu: "uedges (G -- u) \<subseteq> uedges G"
  unfolding remove_vertex_def by auto


subsection \<open>Girth, Independence and Vertex Colorings\<close>

definition girth :: "ugraph \<Rightarrow> enat" where
  "girth G \<equiv> INF p\<in> ucycles G. enat (uwalk_length p)"

definition independent_sets :: "ugraph \<Rightarrow> uvert set set" where
  "independent_sets Gr \<equiv> {vs. vs \<subseteq> uverts Gr \<and> all_edges vs \<inter> uedges Gr = {}}"

definition \<alpha> :: "ugraph \<Rightarrow> enat" where
   "\<alpha> G \<equiv> SUP vs \<in> independent_sets G. enat (card vs)"

definition vertex_colorings :: "ugraph \<Rightarrow> uvert set set set" where
  "vertex_colorings G \<equiv> {C. \<Union>C = uverts G \<and> (\<forall>c1\<in>C. \<forall>c2\<in>C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {}) \<and>
    (\<forall>c\<in>C. c \<noteq> {} \<and> (\<forall>u \<in> c. \<forall>v \<in> c. {u,v} \<notin> uedges G))}"

text \<open>The chromatic number $\chi$:\<close>
definition chromatic_number :: "ugraph \<Rightarrow> enat" where
  "chromatic_number G \<equiv> INF c\<in> (vertex_colorings G). enat (card c)"

lemma independent_sets_mono:
  "vs \<in> independent_sets G \<Longrightarrow> us \<subseteq> vs \<Longrightarrow> us \<in> independent_sets G"
  using Int_mono[OF all_edges_mono, of us vs "uedges G" "uedges G"]
  unfolding independent_sets_def by auto

lemma le_\<alpha>_iff:
  assumes "0 < k"
  shows "k \<le> \<alpha> Gr \<longleftrightarrow> k \<in> card ` independent_sets Gr" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain vs where "vs \<in> independent_sets Gr" and "k \<le> card vs"
    using assms unfolding \<alpha>_def enat_le_Sup_iff by auto
  moreover
  then obtain us where "us \<subseteq> vs" and "k = card us"
    using card_Ex_subset by auto
  ultimately
  have "us \<in> independent_sets Gr"  by (auto intro: independent_sets_mono)
  then show ?R using \<open>k = card us\<close> by auto
qed (auto intro: SUP_upper simp: \<alpha>_def)

lemma zero_less_\<alpha>:
  assumes "uverts G \<noteq> {}"
  shows "0 < \<alpha> G"
proof -
  from assms obtain a where "a \<in> uverts G" by auto
  then have "0 < enat (card {a})" "{a} \<in> independent_sets G"
    by (auto simp: independent_sets_def all_edges_def)
  then show ?thesis unfolding \<alpha>_def less_SUP_iff ..
qed

lemma \<alpha>_le_card:
  assumes "finite (uverts G)"
  shows "\<alpha> G \<le> card(uverts G)"
proof -
  { fix x assume "x \<in> independent_sets G"
    then have "x \<subseteq> uverts G" by (auto simp: independent_sets_def) }
  with assms show ?thesis unfolding \<alpha>_def
    by (intro SUP_least) (auto intro: card_mono)
qed

lemma \<alpha>_fin: "finite (uverts G) \<Longrightarrow> \<alpha> G \<noteq> \<infinity>"
  using \<alpha>_le_card[of G] by (cases "\<alpha> G") auto

lemma \<alpha>_remove_le:
  shows "\<alpha> (G -- u) \<le> \<alpha> G"
proof -
  have "independent_sets (G -- u) \<subseteq> independent_sets G" (is "?L \<subseteq> ?R")
    using all_edges_subset_Pow by (simp add: independent_sets_def remove_vertex_def) blast
  then show ?thesis unfolding \<alpha>_def
    by (rule SUP_subset_mono) simp
qed

text \<open>
  A lower bound for the chromatic number of a graph can be given in terms of
  the independence number
\<close>
lemma chromatic_lb:
  assumes wf_G: "uwellformed G"
    and fin_G: "finite (uverts G)"
    and neG: "uverts G \<noteq> {}"
  shows "card (uverts G) / \<alpha> G \<le> chromatic_number G"
proof -
  from wf_G have "(\<lambda>v. {v}) ` uverts G \<in> vertex_colorings G"
    by (auto simp: vertex_colorings_def uwellformed_def)
  then have "chromatic_number G \<noteq> top"
    by (simp add: chromatic_number_def) (auto simp: top_enat_def)
  then obtain vc where vc_vc: "vc \<in> vertex_colorings G"
    and vc_size:"chromatic_number G = card vc"
    unfolding chromatic_number_def by (rule enat_in_INF)

  have fin_vc_elems: "\<And>c. c \<in> vc \<Longrightarrow> finite c"
    using vc_vc by (intro finite_subset[OF _ fin_G]) (auto simp: vertex_colorings_def)

  have sum_vc_card: "(\<Sum>c \<in> vc. card c) = card (uverts G)"
      using fin_vc_elems vc_vc unfolding vertex_colorings_def
      by (simp add: card_Union_disjoint[symmetric] pairwise_def disjnt_def)

  have "\<And>c. c \<in> vc \<Longrightarrow> c \<in> independent_sets G"
    using vc_vc by (auto simp: vertex_colorings_def independent_sets_def all_edges_def)
  then have "\<And>c. c \<in> vc \<Longrightarrow> card c \<le> \<alpha> G"
    using vc_vc fin_vc_elems by (subst le_\<alpha>_iff) (auto simp add: vertex_colorings_def)
  then have "(\<Sum>c\<in>vc. card c) \<le> card vc * \<alpha> G"
    using sum_bounded_above[of vc card "\<alpha> G"]
    by (simp add: of_nat_eq_enat[symmetric] of_nat_sum)
  then have "ereal_of_enat (card (uverts G)) \<le> ereal_of_enat (\<alpha> G) * ereal_of_enat (card vc)"
    by (simp add: sum_vc_card ereal_of_enat_pushout ac_simps del: ereal_of_enat_simps)
  with zero_less_\<alpha>[OF neG] \<alpha>_fin[OF fin_G] vc_size show ?thesis
    by (simp add: ereal_divide_le_pos)
qed

end
