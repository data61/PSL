section \<open>Semantics in labeled graphs\<close>

theory LabeledGraphSemantics
imports LabeledGraphs
begin


text \<open>GetRel describes the main way we interpret graphs: as describing a set of binary relations.\<close>

definition getRel where
"getRel l G = {(x,y). (l,x,y) \<in> edges G}"

lemma getRel_dom:
  assumes "graph G"
  shows "(a,b) \<in> getRel l G \<Longrightarrow> a \<in> vertices G"
        "(a,b) \<in> getRel l G \<Longrightarrow> b \<in> vertices G"
  using assms unfolding getRel_def by auto

lemma getRel_subgraph[simp]:
  assumes "(y, z) \<in> getRel l G" "subgraph G G'"
  shows "(y,z) \<in> getRel l G'" using assms by (auto simp:getRel_def subgraph_def graph_union_iff)

lemma getRel_homR: (* slows down proofs in the common case *)
  assumes "(y, z) \<in> getRel l G" "(y,u) \<in> f" "(z,v) \<in> f"
  shows "(u, v) \<in> getRel l (map_graph f G)"
  using assms by (auto simp:getRel_def on_triple_def)

lemma getRel_hom[intro]: (* faster proofs in the common case *)
  assumes "(y, z) \<in> getRel l G" "y \<in> vertices G" "z \<in> vertices G"
  shows "(f y, f z) \<in> getRel l (map_graph_fn G f)"
  using assms by (auto intro!:getRel_homR)

lemma getRel_hom_map[simp]:
  assumes "graph G"
  shows "getRel l (map_graph_fn G f) = map_prod f f ` (getRel l G)"
proof
  { fix x y
    assume a:"(x, y) \<in> getRel l G"
    hence "x \<in> vertices G" "y\<in> vertices G" using assms unfolding getRel_def by auto
    hence "(f x, f y) \<in> getRel l (map_graph_fn G f)" using a by auto
  }
  then show "map_prod f f ` getRel l G \<subseteq> getRel l (map_graph_fn G f)" by auto
qed (cases G,auto simp:getRel_def)


text \<open>The thing called term in the paper is called @{term alligorical_term} here.
      This naming is chosen because an allegory has precisely these operations, plus identity. \<close>
(* Deviating from the paper in having a constant constructor.
   We'll use that constructor for top, bottom, etc.. *)
datatype 'v allegorical_term
 = A_Int "'v allegorical_term" "'v allegorical_term"
 | A_Cmp "'v allegorical_term" "'v allegorical_term"
 | A_Cnv "'v allegorical_term"
 | A_Lbl (a_lbl : 'v)


text \<open>The interpretation of terms, Definition 2.\<close>
fun semantics where
"semantics G (A_Int a b) = semantics G a \<inter> semantics G b" |
"semantics G (A_Cmp a b) = semantics G a O semantics G b" |
"semantics G (A_Cnv a) = converse (semantics G a)" |
"semantics G (A_Lbl l) = getRel l G"

notation semantics (":_:\<lbrakk>_\<rbrakk>" 55)

type_synonym 'v sentence = "'v allegorical_term \<times> 'v allegorical_term"

datatype 'v Standard_Constant = S_Top | S_Bot | S_Idt | S_Const 'v

text \<open>Definition 3. We don't define sentences but instead simply work with pairs of terms.\<close>
abbreviation holds where
"holds G S \<equiv> :G:\<lbrakk>fst S\<rbrakk> = :G:\<lbrakk>snd S\<rbrakk>"
notation holds (infix "\<Turnstile>" 55)

abbreviation subset_sentence where
"subset_sentence A B \<equiv> (A,A_Int A B)"

notation subset_sentence (infix "\<sqsubseteq>" 60)

text \<open>Lemma 1.\<close>
lemma sentence_iff[simp]:
  "G \<Turnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 = (:G:\<lbrakk>e\<^sub>1\<rbrakk> \<subseteq> :G:\<lbrakk>e\<^sub>2\<rbrakk>)" and
  eq_as_subsets:
  "G \<Turnstile> (e\<^sub>1, e\<^sub>2) = (G \<Turnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 \<and> G \<Turnstile> e\<^sub>2 \<sqsubseteq> e\<^sub>1)"
  by auto

lemma map_graph_in[intro]:
  assumes "graph G" "(a,b) \<in> :G:\<lbrakk>e\<rbrakk>"
  shows "(f a,f b) \<in> :map_graph_fn G f:\<lbrakk>e\<rbrakk>"
  using assms by(induct e arbitrary: a b,auto intro!:relcompI)

lemma semantics_subset_vertices:
  assumes "graph A" shows ":A:\<lbrakk>e\<rbrakk> \<subseteq> vertices A \<times> vertices A"
  using assms by(induct e,auto simp:getRel_def)
lemma semantics_in_vertices:
  assumes "graph A" "(a,b) \<in> :A:\<lbrakk>e\<rbrakk>"
  shows "a \<in> vertices A" "b \<in> vertices A"
  using assms by(induct e arbitrary:a b,auto simp:getRel_def)

lemma map_graph_semantics[simp]:
  assumes "graph A" and i:"inj_on f (vertices A)"
  shows ":map_graph_fn A f:\<lbrakk>e\<rbrakk> = map_prod f f ` (:A:\<lbrakk>e\<rbrakk>)"
proof(induct e)
  have io:"inj_on (map_prod f f) (vertices A \<times> vertices A)"
    using i unfolding inj_on_def by simp
  note s = semantics_subset_vertices[OF assms(1)]
  case (A_Int e1 e2) thus ?case by (auto simp:inj_on_image_Int[OF io s s]) next
  case (A_Cmp e1 e2)
  {  fix xa ya xb yb assume "(xa, ya) \<in> :A:\<lbrakk>e1\<rbrakk>" "(xb, yb) \<in> :A:\<lbrakk>e2\<rbrakk>" "f ya = f xb"
    moreover hence "ya = xb"
      using i[unfolded inj_on_def] semantics_in_vertices[OF assms(1)] by auto
    ultimately have "(f xa, f yb) \<in> map_prod f f ` ((:A:\<lbrakk>e1\<rbrakk>) O (:A:\<lbrakk>e2\<rbrakk>))" by auto
  }
  with A_Cmp show ?case by auto
qed (insert assms,auto)

lemma graph_union_semantics:
  shows "(:A:\<lbrakk>e\<rbrakk>) \<union> (:B:\<lbrakk>e\<rbrakk>) \<subseteq> :graph_union A B:\<lbrakk>e\<rbrakk>"
  by(induct e,auto simp:getRel_def)

lemma subgraph_semantics:
  assumes "subgraph A B" "(a,b) \<in> :A:\<lbrakk>e\<rbrakk>"
  shows "(a,b) \<in> :B:\<lbrakk>e\<rbrakk>"
  using assms by(induct e arbitrary: a b,auto intro!:relcompI)

lemma graph_homomorphism_semantics:
  assumes "graph_homomorphism A B f" "(a,b) \<in> :A:\<lbrakk>e\<rbrakk>" "(a,a') \<in> f" "(b,b') \<in> f"
  shows "(a',b') \<in> :B:\<lbrakk>e\<rbrakk>"
  using assms proof(induct e arbitrary: a b a' b')
  have g:"graph A" using assms unfolding graph_homomorphism_def2 by auto
  case (A_Cmp e1 e2)
  then obtain y where y:"(a, y) \<in> :A:\<lbrakk>e1\<rbrakk>" "(y, b) \<in> :A:\<lbrakk>e2\<rbrakk>" by auto
  hence "y\<in>vertices A" using semantics_in_vertices[OF g] by auto
  with A_Cmp obtain y' where "(y,y') \<in> f" unfolding graph_homomorphism_def by auto
  from A_Cmp(1)[OF assms(1) y(1) A_Cmp(5) this] A_Cmp(2)[OF assms(1) y(2) this A_Cmp(6)]
  show ?case by auto
next
  case (A_Lbl x) thus ?case by (auto simp:getRel_def graph_homomorphism_def2 graph_union_iff)
qed auto

lemma graph_homomorphism_nonempty:
  assumes "graph_homomorphism A B f" ":A:\<lbrakk>e\<rbrakk> \<noteq> {}"
  shows ":B:\<lbrakk>e\<rbrakk> \<noteq> {}"
proof-
  from assms have g:"graph A" unfolding graph_homomorphism_def by auto
  from assms obtain a b where ab:"(a,b) \<in> :A:\<lbrakk>e\<rbrakk>" by auto
  from semantics_in_vertices[OF g ab] obtain a' b' where
    "(a,a') \<in> f" "(b,b') \<in> f" using assms(1) unfolding graph_homomorphism_def by auto
  from graph_homomorphism_semantics[OF assms(1) ab this] show ?thesis by auto
qed

lemma getRel_map_fn[intro]:
  assumes "a2 \<in> vertices G" "b2 \<in> vertices G" "(a2,b2) \<in> getRel l G"
          "f a2 = a" "f b2 = b"
        shows "(a,b) \<in> getRel l (map_graph_fn G f)"
proof -
  from assms(1,2)
  have "((l, a2, b2), (l, f a2, f b2)) \<in> on_triple {(a, f a) |a. a \<in> vertices G}" by auto
  thus ?thesis using assms(3-) by (simp add:getRel_def BNF_Def.Gr_def Image_def,blast)
qed
  

end