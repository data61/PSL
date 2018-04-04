section {* Soundness for graphical diagrams *}

theory Ribbons_Graphical_Soundness imports
  Ribbons_Graphical
  More_Finite_Map
begin

text {* We prove that the proof rules for graphical ribbon proofs are sound
  with respect to the rules of separation logic.

  We impose an additional assumption to achieve soundness: that the
  Frame rule has no side-condition. This assumption is reasonable because there
  are several separation logics that lack such a side-condition, such as
  ``variables-as-resource''.

  We first describe how to extract proofchains from a diagram. This process is
  similar to the process of extracting commands from a diagram, which was
  described in @{theory Ribbons_Graphical}. When we extract a proofchain, we
  don't just include the commands, but the assertions in between them. Our
  main lemma for proving soundness says that each of these proofchains
  corresponds to a valid separation logic proof.
*}

subsection {* Proofstate chains *}

text {* When extracting a proofchain from a diagram, we need to keep track
  of which nodes we have processed and which ones we haven't. A
  proofstate, defined below, maps a node to ``Top'' if it hasn't been
  processed and ``Bot'' if it has. *}

datatype topbot = Top | Bot

type_synonym proofstate = "node \<rightharpoonup>\<^sub>f topbot"

text {* A proofstate chain contains all the nodes and edges of a graphical
  diagram, interspersed with proofstates that track which nodes have been
  processed at each point. *}

type_synonym ps_chain = "(proofstate, node + edge) chain"

text {* The @{term "next_ps \<sigma>"} function processes one node or one edge in a
  diagram, given the current proofstate @{term \<sigma>}. It processes a node
  @{term v} by replacing the mapping from @{term v} to @{term Top} with a
  mapping from @{term v} to @{term Bot}. It processes an edge @{term e}
  (whose source and target nodes are @{term vs} and @{term ws} respectively)
  by removing all the mappings from @{term vs} to @{term Bot}, and adding
  mappings from @{term ws} to @{term Top}. *}

fun next_ps :: "proofstate \<Rightarrow> node + edge \<Rightarrow> proofstate"
where
  "next_ps \<sigma> (Inl v) = \<sigma> \<ominus> {|v|} ++\<^sub>f [{|v|} |=> Bot]"
| "next_ps \<sigma> (Inr e) = \<sigma> \<ominus> fst3 e ++\<^sub>f [thd3 e |=> Top]"

text {* The function @{term "mk_ps_chain \<Pi> \<pi>"} generates from @{term \<pi>}, which
  is a list of nodes and edges, a proofstate chain, by interspersing the
  elements of @{term \<pi>} with the appropriate proofstates. The first argument
  @{term \<Pi>} is the part of the chain that has already been converted. *}

definition
  mk_ps_chain :: "[ps_chain, (node + edge) list] \<Rightarrow> ps_chain"
where
  "mk_ps_chain \<equiv> foldl (\<lambda>\<Pi> x. cSnoc \<Pi> x (next_ps (post \<Pi>) x))"

lemma mk_ps_chain_preserves_length:
  fixes \<pi> \<Pi>
  shows "chainlen (mk_ps_chain \<Pi> \<pi>) = chainlen \<Pi> + length \<pi>"
proof (induct \<pi> arbitrary: \<Pi>)
  case Nil
  show ?case by (unfold mk_ps_chain_def, auto)
next
  case (Cons x \<pi>)
  show ?case
  apply (unfold mk_ps_chain_def list.size foldl.simps)
  apply (fold mk_ps_chain_def)
  apply (auto simp add: Cons len_snoc)
  done
qed

text {* Distributing @{term mk_ps_chain} over @{term Cons}. *}
lemma mk_ps_chain_cons:
  "mk_ps_chain \<Pi> (x # \<pi>) = mk_ps_chain (cSnoc \<Pi> x (next_ps (post \<Pi>) x)) \<pi>"
by (auto simp add: mk_ps_chain_def)

text {* Distributing @{term mk_ps_chain} over @{term snoc}. *}
lemma mk_ps_chain_snoc:
  "mk_ps_chain \<Pi> (\<pi> @ [x])
    = cSnoc (mk_ps_chain \<Pi> \<pi>) x (next_ps (post (mk_ps_chain \<Pi> \<pi>)) x)"
by (unfold mk_ps_chain_def, auto)

text {* Distributing @{term mk_ps_chain} over @{term cCons}. *}
lemma mk_ps_chain_ccons:
  fixes \<pi> \<Pi>
  shows "mk_ps_chain (\<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>) \<pi> = \<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> mk_ps_chain \<Pi> \<pi> "
by (induct \<pi> arbitrary: \<Pi>, auto simp add: mk_ps_chain_cons mk_ps_chain_def)

lemma pre_mk_ps_chain:
  fixes \<Pi> \<pi>
  shows "pre (mk_ps_chain \<Pi> \<pi>) = pre \<Pi>"
apply (induct \<pi> arbitrary: \<Pi>)
apply (auto simp add: mk_ps_chain_def mk_ps_chain_cons pre_snoc)
done

text {* A chain which is obtained from the list @{term \<pi>}, has @{term \<pi>}
  as its list of commands. The following lemma states this in a slightly
  more general form, that allows for part of the chain to have already
  been processed. *}

lemma comlist_mk_ps_chain:
  "comlist (mk_ps_chain \<Pi> \<pi>) = comlist \<Pi> @ \<pi>"
proof (induct \<pi> arbitrary: \<Pi>)
  case Nil
  thus ?case by (auto simp add: mk_ps_chain_def)
next
  case (Cons x \<pi>')
  show ?case
  apply (unfold mk_ps_chain_def foldl.simps, fold mk_ps_chain_def)
  apply (auto simp add: Cons comlist_snoc)
  done
qed

text {* In order to perform induction over our diagrams, we shall wish
  to obtain ``smaller'' diagrams, by removing nodes or edges. However, the
  syntax and well-formedness constraints for diagrams are such that although
  we can always remove an edge from a diagram, we cannot (in general) remove
  a node -- the resultant diagram would not be a well-formed if an edge
  connected to that node.

  Hence, we consider ``partially-processed diagrams'' @{term "(G,S)"}, which
  comprise a diagram @{term G} and a set @{term S} of nodes. @{term S} denotes
  the subset of @{term G}'s initial nodes that have already been processed,
  and can be thought of as having been removed from @{term G}.

  We now give an updated version of the @{term "lins G"} function. This was
  originally defined in @{theory Ribbons_Graphical}. We provide an extra
  parameter, @{term S}, which denotes the subset of @{term G}'s initial nodes
  that shouldn't be included in the linear extensions. *}

definition lins2 :: "[node fset, diagram] \<Rightarrow> lin set"
where
  "lins2 S G \<equiv> {\<pi> :: lin .
    (distinct \<pi>)
  \<and> (set \<pi> = (fset G^V - fset S) <+> set G^E)
  \<and> (\<forall>i j v e. i < length \<pi> \<and> j < length \<pi>
    \<and> \<pi>!i = Inl v \<and> \<pi>!j = Inr e \<and> v |\<in>| fst3 e \<longrightarrow> i<j)
  \<and> (\<forall>j k w e. j < length \<pi> \<and> k < length \<pi>
    \<and> \<pi>!j = Inr e \<and> \<pi>!k = Inl w \<and> w |\<in>| thd3 e \<longrightarrow> j<k) }"

lemma lins2D:
  assumes "\<pi> \<in> lins2 S G"
  shows "distinct \<pi>"
    and "set \<pi> = (fset G^V - fset S) <+> set G^E"
    and "\<And>i j v e. \<lbrakk> i < length \<pi> ; j < length \<pi> ;
      \<pi>!i = Inl v ; \<pi>!j = Inr e ; v |\<in>| fst3 e \<rbrakk> \<Longrightarrow> i<j"
    and "\<And>i k w e. \<lbrakk> j < length \<pi> ; k < length \<pi> ;
      \<pi>!j = Inr e ; \<pi>!k = Inl w ; w |\<in>| thd3 e \<rbrakk> \<Longrightarrow> j<k"
using assms
apply (unfold lins2_def Collect_iff)
apply (elim conjE, assumption)+
apply blast+
done

lemma lins2I:
  assumes "distinct \<pi>"
    and "set \<pi> = (fset G^V - fset S) <+> set G^E"
    and "\<And>i j v e. \<lbrakk> i < length \<pi> ; j < length \<pi> ;
      \<pi>!i = Inl v ; \<pi>!j = Inr e ; v |\<in>| fst3 e \<rbrakk> \<Longrightarrow> i<j"
    and "\<And>j k w e. \<lbrakk> j < length \<pi> ; k < length \<pi> ;
      \<pi>!j = Inr e ; \<pi>!k = Inl w ; w |\<in>| thd3 e \<rbrakk> \<Longrightarrow> j<k"
  shows "\<pi> \<in> lins2 S G"
using assms
apply (unfold lins2_def Collect_iff, intro conjI)
apply assumption+
apply blast+
done

text {* When @{term S} is empty, the two definitions coincide. *}
lemma lins_is_lins2_with_empty_S:
  "lins G = lins2 {||} G"
by (unfold lins_def lins2_def, auto)

text {* The first proofstate for a diagram @{term G} is obtained by
  mapping each of its initial nodes to @{term Top}. *}
definition
  initial_ps :: "diagram \<Rightarrow> proofstate"
where
  "initial_ps G \<equiv> [ initials G |=> Top ]"

text {* The first proofstate for the partially-processed diagram @{term G} is
  obtained by mapping each of its initial nodes to @{term Top}, except those
  in @{term S}, which are mapped to @{term Bot}. *}
definition
  initial_ps2 :: "[node fset, diagram] \<Rightarrow> proofstate"
where
  "initial_ps2 S G \<equiv> [ initials G - S |=> Top ] ++\<^sub>f [ S |=> Bot ]"

text {* When @{term S} is empty, the above two definitions coincide. *}
lemma initial_ps_is_initial_ps2_with_empty_S:
  "initial_ps = initial_ps2 {||}"
apply (unfold fun_eq_iff, intro allI)
apply (unfold initial_ps_def initial_ps2_def)
apply simp
done

text {* The following function extracts the set of proofstate chains from
   a diagram. *}
definition
  ps_chains :: "diagram \<Rightarrow> ps_chain set"
where
  "ps_chains G \<equiv> mk_ps_chain (cNil (initial_ps G)) ` lins G"

text {* The following function extracts the set of proofstate chains from
   a partially-processed diagram. Nodes in @{term S} are excluded from
   the resulting chains. *}
definition
  ps_chains2 :: "[node fset, diagram] \<Rightarrow> ps_chain set"
where
  "ps_chains2 S G \<equiv> mk_ps_chain (cNil (initial_ps2 S G)) ` lins2 S G"

text {* When @{term S} is empty, the above two definitions coincide. *}
lemma ps_chains_is_ps_chains2_with_empty_S:
  "ps_chains = ps_chains2 {||}"
apply (unfold fun_eq_iff, intro allI)
apply (unfold ps_chains_def ps_chains2_def)
apply (fold initial_ps_is_initial_ps2_with_empty_S)
apply (fold lins_is_lins2_with_empty_S)
apply auto
done

text {* We now wish to describe proofstates chain that are well-formed. First,
  let us say that @{term "f ++\<^sub>fdisjoint g"} is defined, when @{term f} and
  @{term g} have disjoint domains, as @{term "f ++\<^sub>f g"}. Then, a well-formed
  proofstate chain consists of triples of the form @{term "(\<sigma> ++\<^sub>fdisjoint
  [{| v |} |=> Top], Inl v, \<sigma> ++\<^sub>fdisjoint [{| v |} |=> Bot])"}, where @{term v}
  is a node, or of the form @{term "(\<sigma> ++\<^sub>fdisjoint [{| vs |} |=> Bot], Inr e,
  \<sigma> ++\<^sub>fdisjoint [{| ws |} |=> Top])"}, where @{term e} is an edge with source
  and target nodes @{term vs} and @{term ws} respectively.

  The definition below describes a well-formed triple; we then lift this
  to complete chains shortly. *}

definition
  wf_ps_triple :: "proofstate \<times> (node + edge) \<times> proofstate \<Rightarrow> bool"
where
  "wf_ps_triple T = (case snd3 T of
    Inl v \<Rightarrow> (\<exists>\<sigma>. v |\<notin>| fmdom \<sigma>
      \<and> fst3 T = [ {|v|} |=> Top ] ++\<^sub>f \<sigma>
      \<and> thd3 T = [ {|v|} |=> Bot ] ++\<^sub>f \<sigma>)
  | Inr e \<Rightarrow> (\<exists>\<sigma>. (fst3 e |\<union>| thd3 e) |\<inter>| fmdom \<sigma> = {||}
      \<and> fst3 T = [ fst3 e |=> Bot ] ++\<^sub>f \<sigma>
      \<and> thd3 T = [ thd3 e |=> Top ] ++\<^sub>f \<sigma>))"

lemma wf_ps_triple_nodeI:
  assumes "\<exists>\<sigma>. v |\<notin>| fmdom \<sigma>  \<and>
    \<sigma>1 = [ {|v|} |=> Top ] ++\<^sub>f \<sigma> \<and>
    \<sigma>2 = [ {|v|} |=> Bot ] ++\<^sub>f \<sigma>"
  shows "wf_ps_triple (\<sigma>1, Inl v, \<sigma>2)"
using assms unfolding wf_ps_triple_def
by (auto simp add: fst3_simp snd3_simp thd3_simp)

lemma wf_ps_triple_edgeI:
  assumes "\<exists>\<sigma>. (fst3 e |\<union>| thd3 e) |\<inter>| fmdom \<sigma> = {||}
      \<and> \<sigma>1 = [ fst3 e |=> Bot ] ++\<^sub>f \<sigma>
      \<and> \<sigma>2 = [ thd3 e |=> Top ] ++\<^sub>f \<sigma>"
  shows "wf_ps_triple (\<sigma>1, Inr e, \<sigma>2)"
using assms unfolding wf_ps_triple_def
by (auto simp add: fst3_simp snd3_simp thd3_simp)

definition
  wf_ps_chain :: "ps_chain \<Rightarrow> bool"
where
  "wf_ps_chain \<equiv> chain_all wf_ps_triple"

lemma next_initial_ps2_vertex:
  "initial_ps2 ({|v|} |\<union>| S) G
  = initial_ps2 S G \<ominus> {|v|} ++\<^sub>f [ {|v|} |=> Bot ]"
apply (unfold initial_ps2_def)
apply transfer
apply (auto simp add: make_map_def map_diff_def map_add_def restrict_map_def)
done

lemma next_initial_ps2_edge:
  assumes "G = Graph V \<Lambda> E" and "G' = Graph V' \<Lambda> E'" and
    "V' = V - fst3 e" and "E' = removeAll e E" and "e \<in> set E" and
    "fst3 e |\<subseteq>| S" and "S |\<subseteq>| initials G" and "wf_dia G"
  shows "initial_ps2 (S - fst3 e) G' =
  initial_ps2 S G \<ominus> fst3 e ++\<^sub>f [ thd3 e |=> Top ]"
proof (insert assms, unfold initial_ps2_def, transfer)
  fix G V \<Lambda> E G' V' E' e S
  assume G_def: "G = Graph V \<Lambda> E" and G'_def: "G' = Graph V' \<Lambda> E'" and
    V'_def: "V' = V - fst3 e" and E'_def: "E' = removeAll e E" and
    e_in_E: "e \<in> set E" and fst_e_in_S: "fst3 e |\<subseteq>| S" and
    S_initials: "S |\<subseteq>| initials G" and wf_G: "wf_dia G"
  have "thd3 e |\<inter>| initials G = {||}"
    by (auto simp add: initials_def G_def e_in_E)
  show "make_map (initials G' - (S - fst3 e)) Top ++ make_map (S - fst3 e) Bot
    = map_diff (make_map (initials G - S) Top ++ make_map S Bot) (fst3 e)
        ++ make_map (thd3 e) Top"
  apply (unfold make_map_def map_diff_def)
  apply (unfold map_add_def restrict_map_def)
  apply (unfold minus_fset)
  apply (unfold fun_eq_iff initials_def)
  apply (unfold G_def G'_def V'_def E'_def)
  apply (unfold edges.simps vertices.simps)
  apply (simp add: less_eq_fset.rep_eq fmember.rep_eq e_in_E)
  apply safe
  apply (insert \<open>thd3 e |\<inter>| initials G = {||}\<close>)[1]
  apply (insert S_initials, fold fset_cong)[2]
  apply (unfold less_eq_fset.rep_eq initials_def filter_fset)
  apply (auto simp add: fmember.rep_eq G_def e_in_E)[1]
  apply (auto simp add: fmember.rep_eq G_def e_in_E)[1]
  apply (auto simp add: fmember.rep_eq G_def e_in_E)[1]
  apply (insert wf_G)[1]
  apply (unfold G_def vertices.simps edges.simps)
  apply (drule wf_dia_inv(3))
  apply (unfold acyclicity_def)
  apply (metis fst_e_in_S inter_fset le_iff_inf set_mp)
  apply (insert wf_G)[1]
  apply (unfold G_def vertices.simps edges.simps)
  apply (drule wf_dia_inv(4))
  apply (drule linearityD2)
  apply (fold fset_cong, unfold inter_fset fset_simps)
  apply (insert e_in_E, blast)[1]
  apply (insert wf_G)[1]
  apply (unfold G_def vertices.simps edges.simps)
  apply (drule wf_dia_inv(3))
  apply (metis (lifting) e_in_E G_def empty_iff fset_simps(1)
    finter_iff linearityD(2) notin_fset wf_G wf_dia_inv(4))
  apply (insert wf_G)[1]
  apply (unfold G_def vertices.simps edges.simps)
  apply (drule wf_dia_inv(4))
  apply (drule linearityD2)
  apply (fold fset_cong, unfold inter_fset fset_simps)
  apply (insert e_in_E, blast)[1]
  apply (insert wf_G)[1]
  apply (unfold G_def vertices.simps edges.simps)
  apply (drule wf_dia_inv(3))
  apply (metis (lifting) e_in_E G_def empty_iff fset_simps(1)
    finter_iff linearityD(2) notin_fset wf_G wf_dia_inv(4))
  apply (insert wf_G)
  apply (unfold G_def vertices.simps edges.simps)
  apply (drule wf_dia_inv(5))
  apply (unfold less_eq_fset.rep_eq union_fset)
  apply auto[1]
  apply (drule wf_dia_inv(5))
  apply (unfold less_eq_fset.rep_eq union_fset)
  apply auto[1]
  apply (drule wf_dia_inv(5))
  apply (unfold less_eq_fset.rep_eq union_fset)
  apply (auto simp add: e_in_E)[1]
  apply (drule wf_dia_inv(5))
  apply (unfold less_eq_fset.rep_eq union_fset)
  apply (auto simp add: e_in_E)[1]
  done
qed

lemma next_lins2_vertex:
  assumes "Inl v # \<pi> \<in> lins2 S G"
  assumes "v |\<notin>| S"
  shows "\<pi> \<in> lins2 ({|v|} |\<union>| S) G"
proof -
  note lins2D = lins2D[OF assms(1)]
  show ?thesis
  proof (intro lins2I)
    show "distinct \<pi>" using lins2D(1) by auto
  next
    have "set \<pi> = set (Inl v # \<pi>) - {Inl v}" using lins2D(1) by auto
    also have "... = (fset G^V - fset ({|v|} |\<union>| S)) <+> set G^E"
      using lins2D(2) by auto
    finally show "set \<pi> = (fset G^V - fset ({|v|} |\<union>| S)) <+> set G^E"
      by auto
  next
    fix i j v e
    assume "i < length \<pi>" "j < length \<pi>" "\<pi> ! i = Inl v"
      "\<pi> ! j = Inr e" "v |\<in>| fst3 e"
    thus "i < j" using lins2D(3)[of "i+1" "j+1"] by auto
  next
    fix j k w e
    assume "j < length \<pi>" "k < length \<pi>" "\<pi> ! j = Inr e"
      "\<pi> ! k = Inl w" "w |\<in>| thd3 e"
    thus "j < k" using lins2D(4)[of "j+1" "k+1"] by auto
  qed
qed

lemma next_lins2_edge:
  assumes "Inr e # \<pi> \<in> lins2 S (Graph V \<Lambda> E)"
      and "vs |\<subseteq>| S"
      and "e = (vs,c,ws)"
  shows "\<pi> \<in> lins2 (S - vs) (Graph (V - vs) \<Lambda> (removeAll e E))"
proof -
  note lins2D = lins2D[OF assms(1)]
  show ?thesis
  proof (intro lins2I, unfold vertices.simps edges.simps)
    show "distinct \<pi>"
    using lins2D(1) by auto
  next
    show "set \<pi> = (fset (V - vs) - fset (S - vs))
      <+> set (removeAll e E)"
    apply (insert lins2D(1) lins2D(2) assms(2))
    apply (unfold assms(3) vertices.simps edges.simps less_eq_fset.rep_eq, simp)
    apply (unfold diff_diff_eq)
    proof -
      have "\<forall>a aa b.
       insert (Inr (vs, c, ws)) (set \<pi>) = (fset V - fset S) <+> set E \<longrightarrow>
       fset vs \<subseteq> fset S \<longrightarrow>
       Inr (vs, c, ws) \<notin> set \<pi> \<longrightarrow>
       distinct \<pi> \<longrightarrow> (a, aa, b) \<in> set E \<longrightarrow> Inr (a, aa, b) \<notin> set \<pi> \<longrightarrow> b = ws"
     by (metis (lifting) InrI List.set_simps(2)
      prod.inject set_ConsD sum.simps(2))

     moreover have "\<forall>a aa b.
       insert (Inr (vs, c, ws)) (set \<pi>) = (fset V - fset S) <+> set E \<longrightarrow>
       fset vs \<subseteq> fset S \<longrightarrow>
       Inr (vs, c, ws) \<notin> set \<pi> \<longrightarrow>
       distinct \<pi> \<longrightarrow> (a, aa, b) \<in> set E \<longrightarrow> Inr (a, aa, b) \<notin> set \<pi> \<longrightarrow> aa = c"
     by (metis (lifting) InrI List.set_simps(2)
      prod.inject set_ConsD sum.simps(2))

     moreover have "\<forall>x. insert (Inr (vs, c, ws)) (set \<pi>) = (fset V - fset S) <+> set E \<longrightarrow>
         fset vs \<subseteq> fset S \<longrightarrow>
         Inr (vs, c, ws) \<notin> set \<pi> \<longrightarrow>
         distinct \<pi> \<longrightarrow> x \<in> set \<pi> \<longrightarrow> x \<in> (fset V - fset S) <+> set E - {(vs, c, ws)}"
      apply (unfold insert_is_Un[of _ "set \<pi>"])
      apply (fold assms(3))
      apply clarify
      apply (subgoal_tac "set \<pi> = ((fset V - fset S) <+> set E) - {Inr e}")
      by auto
    ultimately show "Inr (vs, c, ws) \<notin> set \<pi> \<and> distinct \<pi> \<Longrightarrow>
      insert (Inr (vs, c, ws)) (set \<pi>) = (fset V - fset S) <+> set E \<Longrightarrow>
      fset vs \<subseteq> fset S \<Longrightarrow> set \<pi> = (fset V - fset S) <+> set E - {(vs, c, ws)}"
    by blast
    qed
  next
    fix i j v e
    assume "i < length \<pi>" "j < length \<pi>" "\<pi> ! i = Inl v"
      "\<pi> ! j = Inr e" "v |\<in>| fst3 e"
    thus "i < j" using lins2D(3)[of "i+1" "j+1"] by auto
  next
    fix j k w e
    assume "j < length \<pi>" "k < length \<pi>" "\<pi> ! j = Inr e"
      "\<pi> ! k = Inl w" "w |\<in>| thd3 e"
    thus "j < k" using lins2D(4)[of "j+1" "k+1"] by auto
  qed
qed


text {* We wish to prove that every proofstate chain that can be obtained from
  a linear extension of @{term G} is well-formed and has as its final
  proofstate that state in which every terminal node in @{term G} is mapped
  to @{term Bot}.

  We first prove this for partially-processed diagrams, for
  then the result for ordinary diagrams follows as an easy corollary.

  We use induction on the size of the partially-processed diagram. The size of
  a partially-processed diagram @{term "(G,S)"} is defined as the number of
  nodes in @{term G}, plus the number of edges, minus the number of nodes in
  @{term S}. *}

lemmas [simp] = fmember.rep_eq

lemma wf_chains2:
  fixes k
  assumes "S |\<subseteq>| initials G"
      and "wf_dia G"
      and "\<Pi> \<in> ps_chains2 S G"
      and "fcard G^V + length G^E = k + fcard S"
  shows "wf_ps_chain \<Pi> \<and> (post \<Pi> = [ terminals G |=> Bot ])"
using assms
proof (induct k arbitrary: S G \<Pi>)
  case 0
  obtain V \<Lambda> E where G_def: "G = Graph V \<Lambda> E" by (metis diagram.exhaust)
  have "S |\<subseteq>| V"
    using "0.prems"(1) initials_in_vertices[of "G"]
    by (auto simp add: G_def)
  have "fcard V \<le> fcard S"
    using "0.prems"(4)
    by (unfold G_def, auto)
  from fcard_seteq[OF `S |\<subseteq>| V` this] have "S = V" by auto
  hence "E = []" using "0.prems"(4) by (unfold G_def, auto)
  have "initials G = V"
    by (unfold G_def `E=[]`, rule no_edges_imp_all_nodes_initial)
  have "terminals G = V"
    by (unfold G_def `E=[]`, rule no_edges_imp_all_nodes_terminal)
  have "{} <+> {} = {}" by auto
  have "lins2 S G = { [] }"
  apply (unfold G_def `S=V` `E=[]`)
  apply (unfold lins2_def, auto simp add: `{} <+> {} = {}`)
  done
  hence \<Pi>_def: "\<Pi> = \<lbrace> initial_ps2 S G \<rbrace>"
    using "0.prems"(3)
    by (auto simp add: ps_chains2_def mk_ps_chain_def)
  show ?case
  apply (intro conjI)
  apply (unfold \<Pi>_def wf_ps_chain_def, auto)
  apply (unfold post.simps initial_ps2_def `initials G = V` `terminals G = V`)
  apply (unfold `S=V`)
  apply (subgoal_tac "V - V = {||}", simp_all)
  done
next
  case (Suc k)
  obtain V \<Lambda> E where G_def: "G = Graph V \<Lambda> E" by (metis diagram.exhaust)
  from Suc.prems(3) obtain \<pi> where
    \<Pi>_def: "\<Pi> = mk_ps_chain \<lbrace> initial_ps2 S G \<rbrace> \<pi>" and
    \<pi>_in: "\<pi> \<in> lins2 S G"
    by (auto simp add: ps_chains2_def)
  note lins2 = lins2D[OF \<pi>_in]
  have "S |\<subseteq>| V"
    using Suc.prems(1) initials_in_vertices[of "G"]
    by (auto simp add: G_def)
  show ?case
  proof (cases \<pi>)
    case Nil
    from \<pi>_in have "V = S" "E = []"
    apply (-, unfold `\<pi> = []` lins2_def, simp_all)
    apply (unfold empty_eq_Plus_conv)
    apply (unfold G_def vertices.simps edges.simps, auto)
    by (metis `S |\<subseteq>| V` less_eq_fset.rep_eq subset_antisym)

    with Suc.prems(4) have False by (simp add: G_def)
    thus ?thesis by auto
  next
    case (Cons x \<pi>')
    note \<pi>_def = this
    show ?thesis
    proof (cases x)
      case (Inl v)
      note x_def = this

      have "v |\<notin>| S \<and> v |\<in>| V"
      apply (subgoal_tac "v \<in> fset V - fset S")
      apply (simp)
      apply (subgoal_tac "Inl v \<in> (fset V - fset S) <+> set E")
      apply (metis Inl_inject Inr_not_Inl PlusE)
      apply (metis lins2(1) lins2(2) Cons G_def Inl distinct.simps(2)
        distinct_length_2_or_more edges.simps vertices.simps)
      done
      hence v_notin_S: "v |\<notin>| S" and v_in_V: "v |\<in>| V" by auto

      have v_initial_not_S: "v |\<in>| initials G - S"
      apply (simp only: G_def initials_def vertices.simps edges.simps)
      apply (simp only: fminus_iff)
      apply (simp only: conj_commute, intro conjI, rule v_notin_S)
      apply (subgoal_tac
        "v \<in> fset (ffilter (\<lambda>v. \<forall>e\<in>set E. v |\<notin>| thd3 e) V)")
      apply simp
      apply (simp only: filter_fset, simp, simp only: conj_commute)
      apply (intro conjI ballI notI)
      apply (insert v_in_V, simp)
      proof -
        fix e :: edge
        assume "v \<in> fset (thd3 e)"
        then have "v |\<in>| (thd3 e)" by auto
        assume "e \<in> set E"
        hence "Inr e \<in> set \<pi>" using lins2(2) by (auto simp add: G_def)
        then obtain j where
          "j < length \<pi>" "0 < length \<pi>" "\<pi>!j = Inr e" "\<pi>!0 = Inl v"
        by (metis \<pi>_def x_def in_set_conv_nth length_pos_if_in_set nth_Cons_0)
        with lins2(4)[OF this `v |\<in>| (thd3 e)`] show False by auto
      qed

      def S' \<equiv> "{|v|} |\<union>| S"

      def \<Pi>' \<equiv> "mk_ps_chain \<lbrace> initial_ps2 S' G \<rbrace> \<pi>'"
      hence pre_\<Pi>': "pre \<Pi>' = initial_ps2 S' G"
      by (metis pre.simps(1) pre_mk_ps_chain)

      def \<sigma> \<equiv> "[ initials G - ({|v|} |\<union>| S) |=> Top ] ++\<^sub>f [ S |=> Bot ]"

      have "wf_ps_chain \<Pi>' \<and> (post \<Pi>' = [terminals G |=> Bot])"
      proof (intro Suc.hyps[of "S'"])
        show "S' |\<subseteq>| initials G"
        apply (unfold S'_def, auto)
        apply (metis fmember.rep_eq fminus_iff v_initial_not_S)
        by (metis Suc.prems(1) fmember.rep_eq fset_rev_mp)
     next
        show "wf_dia G" by (rule Suc.prems(2))
      next
        show "\<Pi>' \<in> ps_chains2 S' G"
        apply (unfold ps_chains2_def \<Pi>'_def)
        apply (intro imageI)
        apply (unfold S'_def)
        apply (intro next_lins2_vertex)
        apply (fold x_def, fold \<pi>_def)
        apply (rule \<pi>_in)
        by (metis v_notin_S)
      next
        show "fcard G^V + length G^E = k + fcard S'"
         apply (unfold S'_def)
         by (auto simp add: Suc.prems(4) fcard_finsert_disjoint[OF v_notin_S])
      qed
      hence
        wf_\<Pi>': "wf_ps_chain \<Pi>'" and
        post_\<Pi>': "post \<Pi>' = [terminals G |=> Bot]"
      by auto

      show ?thesis
      proof (intro conjI)
        have 1: "fmdom [ {|v|} |=> Bot ]
        |\<inter>| fmdom ([ initials G - ({|v|} |\<union>| S) |=> Top ] ++\<^sub>f
     [ S |=> Bot ]) = {||}"
        by (metis (no_types) fdom_make_fmap fmdom_add
          bot_least funion_iff finter_finsert_left le_iff_inf
          fminus_iff finsert_fsubset sup_ge1 v_initial_not_S)
        show "wf_ps_chain \<Pi>"
        using [[unfold_abs_def = false]]
        apply (simp only: \<Pi>_def \<pi>_def x_def mk_ps_chain_cons)
        apply simp
        apply (unfold mk_ps_chain_ccons)
        apply (fold next_initial_ps2_vertex S'_def)
        apply (fold \<Pi>'_def)
        apply (unfold wf_ps_chain_def chain_all.simps conj_commute)
        apply (intro conjI)
        apply (fold wf_ps_chain_def, rule wf_\<Pi>')
        apply (intro wf_ps_triple_nodeI exI[of _ "\<sigma>"] conjI)
        apply (unfold \<sigma>_def fmdom_add fdom_make_fmap)
        apply (metis finsertI1 fminus_iff funion_iff v_notin_S)
        apply (unfold pre_\<Pi>' initial_ps2_def S'_def)
        apply (unfold fmap_add_commute[OF 1])
        apply (unfold fmadd_assoc)
        apply (fold fmadd_assoc[of _ "[ S |=> Bot ]"])
        apply (unfold make_fmap_union sup.commute[of "{|v|}"])
        apply (unfold fminus_funion)
        using v_initial_not_S apply auto
        by (metis (hide_lams, no_types) finsert_absorb finsert_fminus_single finter_fminus
            inf_commute inf_idem v_initial_not_S)
      next
        show "post \<Pi> = [ terminals G |=> Bot ]"
        apply (unfold \<Pi>_def \<pi>_def x_def mk_ps_chain_cons, simp)
        apply (unfold mk_ps_chain_ccons post.simps)
        apply (fold next_initial_ps2_vertex S'_def)
        apply (fold \<Pi>'_def, rule post_\<Pi>')
        done
      qed
    next
      case (Inr e)
      note x_def = this
      def vs \<equiv> "fst3 e"
      def ws \<equiv> "thd3 e"

      obtain c where e_def: "e = (vs, c, ws)"
      by (metis vs_def ws_def fst3_simp thd3_simp prod_cases3)

      have "linearity E" and "acyclicity E" and
        e_in_V: "\<And>e. e \<in> set E \<Longrightarrow> fst3 e |\<union>| thd3 e |\<subseteq>| V"
      by (insert Suc.prems(2) wf_dia_inv, unfold G_def, blast)+
      note lin = linearityD[OF this(1)]

      have acy: "\<And>e. e \<in> set E \<Longrightarrow> fst3 e |\<inter>| thd3 e = {||}"
      apply (fold fset_cong, insert `acyclicity E`)
      apply (unfold acyclicity_def acyclic_def, auto)
      done

      note lins = lins2D[OF \<pi>_in]

      have e_in_E: "e \<in> set E"
      apply (subgoal_tac "set \<pi> = (fset G^V - fset S) <+> set G^E")
      apply (unfold \<pi>_def x_def G_def edges.simps, auto)[1]
      apply (simp add: lins(2))
      done

      have vs_in_S: "vs |\<subseteq>| S"
      apply (insert e_in_V[OF e_in_E])
      apply (unfold less_eq_fset.rep_eq)
      apply (intro subsetI)
      apply (unfold vs_def)
      apply (rule ccontr)
      apply (subgoal_tac "x \<in> fset V")
      prefer 2
      apply (auto)
      proof -
        fix v
        assume a: "v \<in> fset (fst3 e)"
        assume "v \<notin> fset S" and "v \<in> fset V"
        hence "Inl v \<in> set \<pi>"
        by (metis (lifting) DiffI G_def InlI lins(2) vertices.simps)
        then obtain i where
          "i < length \<pi>" "0 < length \<pi>" "\<pi>!i = Inl v"  "\<pi>!0 = Inr e"
        by (metis Cons Inr in_set_conv_nth length_pos_if_in_set nth_Cons_0)
        from lins(3)[OF this] show "False" by (auto simp add: a)
      qed

      have "ws |\<inter>| (initials G) = {||}"
      apply (insert e_in_V[OF e_in_E])
      apply (unfold initials_def less_eq_fset.rep_eq fmember.rep_eq, fold fset_cong)
      apply (unfold ws_def G_def, auto simp add: e_in_E)
      done

      def S' \<equiv> "S - vs"
      def V' \<equiv> "V - vs"
      def E' \<equiv> "removeAll e E"
      def G' \<equiv> "Graph V' \<Lambda> E'"

      def \<Pi>' \<equiv> "mk_ps_chain \<lbrace> initial_ps2 S' G' \<rbrace> \<pi>'"
      hence pre_\<Pi>': "pre \<Pi>' = initial_ps2 S' G'"
      by (metis pre.simps(1) pre_mk_ps_chain)

      def \<sigma> \<equiv> "[ initials G - S |=> Top ] ++\<^sub>f [ S - vs |=> Bot ]"

      have next_initial_ps2: "initial_ps2 S' G'
        = initial_ps2 S G \<ominus> vs ++\<^sub>f [ws |=> Top]"
      using next_initial_ps2_edge[OF G_def _ _ _ e_in_E _ Suc.prems(1)
        Suc.prems(2)] G'_def E'_def vs_def ws_def V'_def vs_in_S S'_def
      by auto

      have "wf_ps_chain \<Pi>' \<and> post \<Pi>' = [ terminals G' |=> Bot ]"
      proof (intro Suc.hyps[of "S'"])
        show "S' |\<subseteq>| initials G'"
        apply (insert Suc.prems(1))
        apply (unfold G'_def G_def initials_def)
        apply (unfold less_eq_fset.rep_eq S'_def E'_def V'_def)
        apply auto
        done
      next
        from Suc.prems(2) have "wf_dia (Graph V \<Lambda> E)"
          by (unfold G_def)
        note wf_G = wf_dia_inv[OF this]
        show "wf_dia G'"
        apply (unfold G'_def V'_def E'_def)
        apply (insert wf_G e_in_E vs_in_S Suc.prems(1))
        apply (unfold vs_def)
        apply (intro wf_dia)
        apply (unfold linearity_def initials_def G_def)
        apply (fold fset_cong, unfold less_eq_fset.rep_eq fmember.rep_eq)
        apply (simp, simp)
        apply (unfold acyclicity_def, rule acyclic_subset)
        apply (auto simp add: distinct_removeAll)
        apply (metis (lifting) IntI empty_iff)
        done
      next
        show "\<Pi>' \<in> ps_chains2 S' G'"
        apply (unfold \<Pi>_def \<Pi>'_def ps_chains2_def)
        apply (intro imageI)
        apply (unfold S'_def G'_def V'_def E'_def)
        apply (intro next_lins2_edge)
        apply (metis \<pi>_def G_def x_def \<pi>_in)
        by (simp only: vs_in_S e_def)+
      next
        have "vs |\<subseteq>| V" by (metis (lifting) `S |\<subseteq>| V` order_trans vs_in_S)
        have "distinct E" using `linearity E` linearity_def by auto
        show "fcard G'^V + length G'^E = k + fcard S'"
        apply (insert Suc.prems(4))
        apply (unfold G_def G'_def vertices.simps edges.simps)
        apply (unfold V'_def E'_def S'_def)
        apply (unfold fcard_funion_fsubset[OF `vs |\<subseteq>| V`])
        apply (unfold fcard_funion_fsubset[OF `vs |\<subseteq>| S`])
        apply (fold distinct_remove1_removeAll[OF `distinct E`])
        apply (unfold length_remove1)
        apply (simp add: e_in_E)
        apply (drule arg_cong[of _ _ "\<lambda>x. x - fcard vs - 1"])
        apply (subst (asm) add_diff_assoc2[symmetric])
        apply (simp add: fcard_mono[OF `vs |\<subseteq>| V`])
        apply (subst add_diff_assoc, insert length_pos_if_in_set[OF e_in_E], arith, auto)
        apply (subst add_diff_assoc, auto simp add: fcard_mono[OF `vs |\<subseteq>| S`])
        done
      qed
      hence
        wf_\<Pi>': "wf_ps_chain \<Pi>'" and
        post_\<Pi>': "post \<Pi>' = [ terminals G' |=> Bot ]"
      by auto

      have terms_same: "terminals G = terminals G'"
      apply (unfold G'_def G_def terminals_def edges.simps vertices.simps)
      apply (unfold E'_def V'_def)
      apply (fold fset_cong, auto simp add: e_in_E vs_def)
      done

      have 1: "fmdom [ fst3 e |=> Bot ] |\<inter>|
        fmdom([ ffilter (\<lambda>v. \<forall>e\<in>set E. v |\<notin>| thd3 e) V - S |=> Top ]
        ++\<^sub>f [ S - fst3 e |=> Bot ]) = {||}"
      apply (unfold fmdom_add fdom_make_fmap)
      apply (fold fset_cong)
      apply auto
      apply (metis in_mono less_eq_fset.rep_eq vs_def vs_in_S)
      done

      show ?thesis
      proof (intro conjI)
        show "wf_ps_chain \<Pi>"
        using [[unfold_abs_def = false]]
        apply (unfold \<Pi>_def \<pi>_def x_def mk_ps_chain_cons)
        apply simp
        apply (unfold mk_ps_chain_ccons)
        apply (fold vs_def ws_def)
        apply (fold next_initial_ps2)
        apply (fold \<Pi>'_def)
        apply (unfold wf_ps_chain_def chain_all.simps conj_commute)
        apply (intro conjI)
        apply (fold wf_ps_chain_def)
        apply (rule wf_\<Pi>')
        apply (intro wf_ps_triple_edgeI exI[of _ "\<sigma>"])
        apply (unfold e_def fst3_simp thd3_simp \<sigma>_def, intro conjI)
        apply (insert Suc.prems(1))
        apply (unfold pre_\<Pi>' initial_ps2_def initials_def)
        apply (insert vs_in_S acy[OF e_in_E])
        apply (fold fset_cong)
        apply (unfold less_eq_fset.rep_eq)[1]
        apply (unfold G_def G'_def vs_def ws_def V'_def E'_def S'_def)
        apply (unfold vertices.simps edges.simps)
        apply (unfold fmap_add_commute[OF 1])
        apply (fold fmadd_assoc)
        apply (unfold make_fmap_union)
        apply (auto simp add: fdom_make_fmap e_in_E)[1]
        apply simp
        apply (unfold fmadd_assoc)
        apply (unfold make_fmap_union)
        apply (metis (lifting) funion_absorb2 vs_def vs_in_S)
        apply (intro arg_cong2[of _ _ "[ S - fst3 e |=> Bot ]"
            "[ S - fst3 e |=> Bot ]" "op ++\<^sub>f"])
        apply (intro arg_cong2[of _ _ "Top" "Top" "make_fmap"])
        defer 1
        apply (simp, simp)
        apply (fold fset_cong)
        apply (unfold less_eq_fset.rep_eq fmember.rep_eq, simp)
        apply (elim conjE)
        apply (intro set_eqI iffI, simp_all)
        apply (elim conjE, intro disjI conjI ballI, simp)
        apply (case_tac "ea=e", simp_all)
        apply (elim disjE conjE, intro conjI ballI impI, simp_all)
        apply (insert e_in_E lin(2))[1]
        apply (subst (asm) (2) fset_cong[symmetric])
        apply (elim conjE)
        apply (subst (asm) inter_fset)
        apply (subst (asm) fset_simps)
        apply (insert disjoint_iff_not_equal)[1]
        apply blast
        apply (metis G_def Suc(3) e_in_E set_mp less_eq_fset.rep_eq wf_dia_inv')
        prefer 2
        apply (metis (lifting) IntI Suc(2) `ws |\<inter>| initials G = {||}`
            empty_iff fset_simps(1) in_mono inter_fset less_eq_fset.rep_eq ws_def)
        apply auto
        done
      next
        show "post \<Pi> = [terminals G |=> Bot]"
        apply (unfold \<Pi>_def \<pi>_def x_def mk_ps_chain_cons)
        apply simp
        apply (unfold mk_ps_chain_ccons post.simps)
        apply (fold vs_def ws_def)
        apply (fold next_initial_ps2)
        apply (fold \<Pi>'_def)
        apply (unfold terms_same)
        apply (rule post_\<Pi>')
        done
      qed
    qed
  qed
qed

corollary wf_chains:
  assumes "wf_dia G"
  assumes "\<Pi> \<in> ps_chains G"
  shows "wf_ps_chain \<Pi> \<and> post \<Pi> = [ terminals G |=> Bot ]"
apply (intro wf_chains2[of "{||}"], insert assms(2))
by (auto simp add: assms(1) ps_chains_is_ps_chains2_with_empty_S fcard_fempty)


subsection {* Interface chains *}

type_synonym int_chain = "(interface, assertion_gadget + command_gadget) chain"

text {* An interface chain is similar to a proofstate chain. However, where a
  proofstate chain talks about nodes and edges, an interface chain talks about
  the assertion-gadgets and command-gadgets that label those nodes and edges
  in a diagram. And where a proofstate chain talks about proofstates, an
  interface chain talks about the interfaces obtained from those proofstates.

  The following functions convert a proofstate chain into an
  interface chain. *}

definition
  ps_to_int :: "[diagram, proofstate] \<Rightarrow> interface"
where
  "ps_to_int G \<sigma> \<equiv>
    \<Otimes>v |\<in>| fmdom \<sigma>. case_topbot top_ass bot_ass (lookup \<sigma> v) (G^\<Lambda> v)"

definition
  ps_chain_to_int_chain :: "[diagram, ps_chain] \<Rightarrow> int_chain"
where
  "ps_chain_to_int_chain G \<Pi> \<equiv>
    chainmap (ps_to_int G) ((case_sum (Inl \<circ> G^\<Lambda>) (Inr \<circ> snd3))) \<Pi>"

lemma ps_chain_to_int_chain_simp:
  "ps_chain_to_int_chain (Graph V \<Lambda> E) \<Pi> =
    chainmap (ps_to_int (Graph V \<Lambda> E)) ((case_sum (Inl \<circ> \<Lambda>) (Inr \<circ> snd3))) \<Pi>"
by (simp add: ps_chain_to_int_chain_def)

subsection {* Soundness proof *}

text {*  We assume that @{term wr_com} always returns @{term "{}"}. This is
  equivalent to changing our axiomatization of separation logic such that the
  frame rule has no side-condition. One way to obtain a separation logic
  lacking a side-condition on its frame rule is to use variables-as-
  resource.

  We proceed by induction on the proof rules for graphical diagrams. We
  show that: (1) if a diagram @{term G} is provable w.r.t. interfaces
  @{term P} and @{term Q}, then @{term P} and @{term Q} are the top and bottom
  interfaces of @{term G}, and that the Hoare triple @{term "(asn P,
  c, asn Q)"} is provable for each command @{term c} that can be extracted
  from @{term G}; (2) if a command-gadget @{term C} is provable w.r.t.
  interfaces @{term P} and @{term Q}, then the Hoare triple @{term "(asn P,
  c, asn Q)"} is provable for each command @{term c} that can be extracted
  from @{term C}; and (3) if an assertion-gadget @{term A} is provable, and if
  the top and bottom interfaces of @{term A} are @{term P} and @{term Q}
  respectively, then the Hoare triple @{term "(asn P, c, asn Q)"} is provable
  for each command @{term c} that can be extracted from @{term A}. *}



lemma soundness_graphical_helper:
  assumes no_var_interference: "\<And>c. wr_com c = {}"
  shows
    "(prov_dia G P Q \<longrightarrow>
      (P = top_dia G \<and> Q = bot_dia G \<and>
      (\<forall>c. coms_dia G c \<longrightarrow> prov_triple (asn P, c, asn Q))))
   \<and> (prov_com C P Q \<longrightarrow>
      (\<forall>c. coms_com C c \<longrightarrow> prov_triple (asn P, c, asn Q)))
   \<and> (prov_ass A \<longrightarrow>
      (\<forall>c. coms_ass A c \<longrightarrow> prov_triple (asn (top_ass A), c, asn (bot_ass A))))"
proof (induct rule: prov_dia_prov_com_prov_ass.induct)
  case (Skip p)
  thus ?case
  apply (intro allI impI, elim conjE coms_skip_inv)
  apply (auto simp add: prov_triple.skip)
  done
next
  case (Exists G P Q x)
  thus ?case
  apply (intro allI impI, elim conjE coms_exists_inv)
  apply (auto simp add: prov_triple.exists)
  done
next
  case (Basic P c Q)
  thus ?case
  by (intro allI impI, elim conjE coms_basic_inv, auto)
next
  case (Choice G P Q H)
  thus ?case
  apply (intro allI impI, elim conjE coms_choice_inv)
  apply (auto simp add: prov_triple.choose)
  done
next
  case (Loop G P)
  thus ?case
  apply (intro allI impI, elim conjE coms_loop_inv)
  apply (auto simp add: prov_triple.loop)
  done
next
  case (Main G)
  thus ?case
  apply (intro conjI)
  apply (simp, simp)
  apply (intro allI impI)
  apply (elim coms_main_inv, simp)
  proof -
    fix c V \<Lambda> E
    fix \<pi>::"lin"
    fix cs::"command list"
    assume wf_G: "wf_dia (Graph V \<Lambda> E)"
    assume "\<And>v. v \<in> fset V \<Longrightarrow> \<forall>c. coms_ass (\<Lambda> v) c \<longrightarrow>
      prov_triple (asn (top_ass (\<Lambda> v)), c, asn (bot_ass (\<Lambda> v)))"
    hence prov_vertex: "\<And>v c P Q F. \<lbrakk> coms_ass (\<Lambda> v) c; v \<in> fset V;
      P = (top_ass (\<Lambda> v) \<otimes> F) ; Q = (bot_ass (\<Lambda> v) \<otimes> F) \<rbrakk>
      \<Longrightarrow> prov_triple (asn P, c, asn Q)"
    by (auto simp add: prov_triple.frame no_var_interference)
    assume "\<And>e. e \<in> set E \<Longrightarrow> \<forall>c. coms_com (snd3 e) c \<longrightarrow> prov_triple
      (asn (\<Otimes>v|\<in>|fst3 e. bot_ass (\<Lambda> v)),c,asn (\<Otimes>v|\<in>|thd3 e. top_ass (\<Lambda> v)))"
    hence prov_edge: "\<And>e c P Q F. \<lbrakk> e \<in> set E ; coms_com (snd3 e) c ;
      P = ((\<Otimes>v|\<in>|fst3 e. bot_ass (\<Lambda> v)) \<otimes> F) ;
      Q = ((\<Otimes>v|\<in>|thd3 e. top_ass (\<Lambda> v)) \<otimes> F) \<rbrakk>
      \<Longrightarrow> prov_triple (asn P, c, asn Q)"
    by (auto simp add: prov_triple.frame no_var_interference)
    assume len_cs: "length cs = length \<pi>"
    assume "\<forall>i<length \<pi>.
      case_sum (coms_ass \<circ> \<Lambda>) (coms_com \<circ> snd3) (\<pi> ! i) (cs ! i)"
    hence \<pi>_cs: "\<And>i. i < length \<pi> \<Longrightarrow>
      case_sum (coms_ass \<circ> \<Lambda>) (coms_com \<circ> snd3) (\<pi> ! i) (cs ! i)" by auto
    assume G_def: "G = Graph V \<Lambda> E"
    assume c_def: "c = foldr op ;; cs Skip"
    assume \<pi>_lin: "\<pi> \<in> lins (Graph V \<Lambda> E)"

    note lins = linsD[OF \<pi>_lin]

    def \<Pi> \<equiv> "mk_ps_chain \<lbrace> initial_ps G \<rbrace> \<pi>"

    have "\<Pi> \<in> ps_chains G" by (simp add: \<pi>_lin \<Pi>_def ps_chains_def G_def)
    hence 1: "post \<Pi> = [ terminals G |=> Bot ]"
      and 2: "chain_all wf_ps_triple \<Pi>"
    by (insert wf_chains G_def wf_G, auto simp add: wf_ps_chain_def)

    show "prov_triple (asn (\<Otimes>v|\<in>|initials (Graph V \<Lambda> E). top_ass (\<Lambda> v)),
      foldr op ;; cs Skip, asn (\<Otimes>v|\<in>|terminals (Graph V \<Lambda> E). bot_ass (\<Lambda> v)))"
    using [[unfold_abs_def = false]]
    apply (intro seq_fold[of _ "ps_chain_to_int_chain G \<Pi>"])
    apply (unfold len_cs)
    apply (unfold ps_chain_to_int_chain_def chainmap_preserves_length \<Pi>_def)
    apply (unfold mk_ps_chain_preserves_length, simp)
    apply (unfold pre_chainmap post_chainmap)
    apply (unfold pre_mk_ps_chain pre.simps)
    apply (fold \<Pi>_def, unfold 1)
    apply (unfold initial_ps_def)
    apply (unfold ps_to_int_def)
    apply (unfold fdom_make_fmap)
    apply (unfold G_def labelling.simps, fold G_def)
    apply (subgoal_tac "\<forall>v \<in> fset (initials G). top_ass (\<Lambda> v) =
      case_topbot top_ass bot_ass (lookup [ initials G |=> Top ] v) (\<Lambda> v)")
    apply (unfold iter_hcomp_cong, simp)
    apply (metis lookup_make_fmap topbot.simps(3))
    apply (subgoal_tac "\<forall>v \<in> fset (terminals G). bot_ass (\<Lambda> v) =
      case_topbot top_ass bot_ass (lookup [ terminals G |=> Bot ] v) (\<Lambda> v)")
    apply (unfold iter_hcomp_cong, simp)
    apply (metis lookup_make_fmap topbot.simps(4), simp)
    apply (unfold G_def, fold ps_chain_to_int_chain_simp G_def)
    proof -
      fix i
      assume "i < length \<pi>"
      hence "i < chainlen \<Pi>"
      by (metis \<Pi>_def add_0_left chainlen.simps(1)
        mk_ps_chain_preserves_length)
      hence wf_\<Pi>i: "wf_ps_triple (nthtriple \<Pi> i)"
        by (insert 2, simp add: chain_all_nthtriple)
      show "prov_triple (asn (fst3 (nthtriple (ps_chain_to_int_chain G \<Pi>) i)),
                 cs ! i, asn (thd3 (nthtriple (ps_chain_to_int_chain G \<Pi>) i)))"
      apply (unfold ps_chain_to_int_chain_def)
      apply (unfold nthtriple_chainmap[OF `i < chainlen \<Pi>`])
      apply (unfold fst3_simp thd3_simp)
      proof (cases "\<pi>!i")
        case (Inl v)

        have "snd3 (nthtriple \<Pi> i) = Inl v"
        apply (unfold snds_of_triples_form_comlist[OF `i < chainlen \<Pi>`])
        apply (auto simp add: \<Pi>_def comlist_mk_ps_chain Inl)
        done

        with wf_\<Pi>i wf_ps_triple_def obtain \<sigma> where
          v_notin_\<sigma>: "v |\<notin>| fmdom \<sigma>" and
          fst_\<Pi>i: "fst3 (nthtriple \<Pi> i) = [ {|v|} |=> Top ] ++\<^sub>f \<sigma>" and
          thd_\<Pi>i: "thd3 (nthtriple \<Pi> i) = [ {|v|} |=> Bot ] ++\<^sub>f \<sigma>" by auto

        show "prov_triple (asn (ps_to_int G (fst3 (nthtriple \<Pi> i))),
                   cs ! i, asn (ps_to_int G (thd3 (nthtriple \<Pi> i))))"
        apply (intro prov_vertex[where v=v])
        apply (metis (no_types) Inl `i < length \<pi>` \<pi>_cs o_def sum.simps(5))
        apply (metis (lifting) Inl lins(2) Inl_not_Inr PlusE `i < length \<pi>`
          nth_mem sum.simps(1) vertices.simps)
        apply (unfold fst_\<Pi>i thd_\<Pi>i)
        apply (unfold ps_to_int_def)
        apply (unfold fmdom_add fdom_make_fmap)
        apply (unfold finsert_is_funion[symmetric])
        apply (insert v_notin_\<sigma>)
        apply (unfold iter_hcomp_insert)
        apply (unfold lookup_union2 lookup_make_fmap1)
        apply (unfold G_def labelling.simps)
        apply (subgoal_tac "\<forall>va \<in> fset (fmdom \<sigma>). case_topbot top_ass bot_ass
          (lookup ([ {|v|} |=> Top ] ++\<^sub>f \<sigma>) va) (\<Lambda> va) =
          case_topbot top_ass bot_ass (lookup ([{|v|} |=> Bot] ++\<^sub>f \<sigma>) va)(\<Lambda> va)")
        apply (unfold iter_hcomp_cong, simp)
        apply (metis fmember.rep_eq lookup_union1, simp)
        done
      next
        case (Inr e)
        have "snd3 (nthtriple \<Pi> i) = Inr e"
        apply (unfold snds_of_triples_form_comlist[OF `i < chainlen \<Pi>`])
        apply (auto simp add: \<Pi>_def comlist_mk_ps_chain Inr)
        done

        with wf_\<Pi>i wf_ps_triple_def obtain \<sigma> where
          fst_e_disjoint_\<sigma>: "fst3 e |\<inter>| fmdom \<sigma> = {||}" and
          thd_e_disjoint_\<sigma>: "thd3 e |\<inter>| fmdom \<sigma> = {||}" and
          fst_\<Pi>i: "fst3 (nthtriple \<Pi> i) = [ fst3 e |=> Bot ] ++\<^sub>f \<sigma>" and
          thd_\<Pi>i: "thd3 (nthtriple \<Pi> i) = [ thd3 e |=> Top ] ++\<^sub>f \<sigma>"
        by (auto simp add: inf_sup_distrib2)

        show "prov_triple (asn (ps_to_int G (fst3 (nthtriple \<Pi> i))),
                   cs ! i, asn (ps_to_int G (thd3 (nthtriple \<Pi> i))))"
        apply (intro prov_edge[where e=e])
        apply (subgoal_tac "Inr e \<in> set \<pi>")
        apply (metis Inr_not_Inl PlusE edges.simps lins(2) sum.simps(2))
        apply (metis Inr `i < length \<pi>` nth_mem)
        apply (metis (no_types) Inr `i < length \<pi>` \<pi>_cs o_def sum.simps(6))
        apply (unfold fst_\<Pi>i thd_\<Pi>i)
        apply (unfold ps_to_int_def)
        apply (unfold G_def labelling.simps)
        apply (unfold fmdom_add fdom_make_fmap)
        apply (insert fst_e_disjoint_\<sigma>)
        apply (unfold iter_hcomp_union)
        apply (subgoal_tac "\<forall>v \<in> fset (fst3 e). case_topbot top_ass bot_ass
          (lookup ([ fst3 e |=> Bot ] ++\<^sub>f \<sigma>) v) (\<Lambda> v) = bot_ass (\<Lambda> v)")
        apply (unfold iter_hcomp_cong)
        apply (simp)
        apply (intro ballI)
        apply (subgoal_tac "v |\<notin>| fmdom \<sigma>")
        apply (unfold lookup_union2)
        apply (metis lookup_make_fmap topbot.simps(4))
        apply (metis fempty_iff finterI fmember.rep_eq)
        apply (insert thd_e_disjoint_\<sigma>)
        apply (unfold iter_hcomp_union)
        apply (subgoal_tac "\<forall>v \<in> fset (thd3 e). case_topbot top_ass bot_ass
          (lookup ([ thd3 e |=> Top ] ++\<^sub>f \<sigma>) v) (\<Lambda> v) = top_ass (\<Lambda> v)")
        apply (unfold iter_hcomp_cong)
        apply (subgoal_tac "\<forall>v \<in> fset (fmdom \<sigma>). case_topbot top_ass bot_ass
          (lookup ([ thd3 e |=> Top ] ++\<^sub>f \<sigma>) v) (\<Lambda> v) =
          case_topbot top_ass bot_ass (lookup ([fst3 e |=> Bot] ++\<^sub>f \<sigma>) v) (\<Lambda> v)")
        apply (unfold iter_hcomp_cong)
        apply simp
        apply (intro ballI)
        apply (subgoal_tac "v |\<in>| fmdom \<sigma>")
        apply (unfold lookup_union1, auto)
        apply (subgoal_tac "v |\<notin>| fmdom \<sigma>")
        apply (unfold lookup_union2)
        apply (metis lookup_make_fmap topbot.simps(3))
        by (metis fempty_iff finterI fmember.rep_eq)
      qed
    qed
  qed
qed

text {* The soundness theorem states that any diagram provable using the
  proof rules for ribbons can be recreated as a valid proof in separation
  logic. *}

corollary soundness_graphical:
  assumes "\<And>c. wr_com c = {}"
  assumes "prov_dia G P Q"
  shows "\<forall>c. coms_dia G c \<longrightarrow> prov_triple (asn P, c, asn Q)"
using soundness_graphical_helper[OF assms(1)] and assms(2) by auto

end