section \<open>Combined correctness\<close>
text \<open>This section does not correspond to any theorems in the paper.
      However, the main correctness proof is not a theorem in the paper either.
      As the paper sets out to prove that we can decide entailment and consistency,
      this file shows how to combine the results so far and indeed establish those properties. \<close>
theory CombinedCorrectness
  imports GraphRewriting StandardRules
begin

(* a somewhat concrete function to get the model if one exists *)
definition the_model where
"the_model C Rs
  \<equiv> let L = fst ` UNION Rs (edges o snd) \<union> {S_Bot,S_Top,S_Idt} \<union> S_Const ` C;
        Rules = Rs \<union> (standard_rules C L);
        sel = non_constructive_selector Rules 
     in the_lcg sel Rules (0,{})"

definition entailment_model where
"entailment_model C Rs init
  \<equiv> let L = fst ` UNION Rs (edges o snd) \<union> {S_Bot,S_Top,S_Idt} \<union> S_Const ` C \<union> fst ` edges init;
        Rules = Rs \<union> (standard_rules C L);
        sel = non_constructive_selector Rules 
     in the_lcg sel Rules (card (vertices init),edges init)"

abbreviation check_consistency where
  "check_consistency C Rs \<equiv> getRel S_Bot (the_model C Rs) = {}"

abbreviation check_entailment where
  "check_entailment C Rs R \<equiv> 
     let mdl = entailment_model C Rs (translation (fst R))
     in (0,1) \<in> :mdl:\<lbrakk>snd R\<rbrakk> \<or> getRel S_Bot mdl \<noteq> {}"

definition transl_rules where
  "transl_rules T = UNION T (\<lambda> (x,y). {(translation x, translation (A_Int x y)),(translation y, translation (A_Int y x))})"

lemma gr_transl_rules:
  "x \<in> transl_rules T \<Longrightarrow> graph_rule x"
  using graph_rule_translation unfolding transl_rules_def by blast
term entails

lemma check_consistency:
  assumes "finite T" "finite C"
  shows "check_consistency C (transl_rules T) \<longleftrightarrow> consistent (t::nat itself) C T"
   (is "?lhs = ?rhs")
proof -
  from assms(1) have fin_t:"finite (transl_rules T)" unfolding transl_rules_def by fast
  define L where
    "L = fst ` UNION (transl_rules T) (edges \<circ> snd) \<union> {S_Bot,S_Top,S_Idt} \<union> S_Const ` C"
  have "finite (UNION (transl_rules T) (edges \<circ> snd))" using fin_t gr_transl_rules by auto
  hence fin_l:"finite L" unfolding L_def using assms(2) by auto
  define Rules where "Rules = transl_rules T \<union> standard_rules C L"
  hence fin_r:"finite Rules" using assms(2) fin_t fin_l unfolding standard_rules_def by auto
  have incl_L:"fst ` UNION Rules (edges o snd) \<subseteq> L"
    unfolding L_def Rules_def by (auto elim:standard_rules_edges)
  have "\<forall>R\<in>transl_rules T. graph_rule R" using gr_transl_rules by blast
  moreover have "\<forall>R\<in> constant_rules C. graph_rule R" using constant_rules_graph_rule by auto
  moreover have "\<forall>R\<in> identity_rules L. graph_rule R" using identity_rules_graph_rule by auto
  moreover have "\<forall>R\<in> {top_rule S_Top,nonempty_rule}. graph_rule R" using are_rules(1,2) by fastforce
  ultimately have gr:"set_of_graph_rules Rules"
    unfolding set_of_graph_rules_def Rules_def ball_Un standard_rules_def
    by blast
  define sel where "sel = non_constructive_selector Rules"
  hence sel:"valid_selector Rules sel" using gr non_constructive_selector by auto
  define cfg where "cfg = the_lcg sel Rules (0, {})"
  have cfg:"cfg = the_model C (transl_rules T)"
    unfolding cfg_def sel_def Rules_def L_def the_model_def Let_def..
  have cfg_c:"least_consequence_graph TYPE('a + nat) Rules (graph_of (0,{})) cfg"
    unfolding cfg_def
    by (rule lcg_through_make_step[OF fin_r gr _ sel],auto)
  hence cfg_sdt:"maintainedA (standard_rules C L) cfg"
    and cfg_g: "graph cfg"
    and cfg_l:"least TYPE('a + nat) Rules (graph_of (0, {})) cfg"
    and cfg_m:"r \<in> transl_rules T \<Longrightarrow> maintained r cfg" for r
    unfolding Rules_def least_consequence_graph_def by auto
  have cfg_lbl:"fst ` edges cfg \<subseteq> L" 
    unfolding cfg_def by (auto intro!: the_lcg_edges[OF sel incl_L])
  have d1: "?lhs \<Longrightarrow> ?rhs" proof -
    assume ?lhs
    from maintained_standard_noconstants[OF cfg_sdt cfg_g cfg_lbl this[folded cfg]]
    obtain G :: "('a Standard_Constant, 'a + nat) labeled_graph"
      where G_std:"standard' C G"
      and m:"maintained r cfg \<Longrightarrow> maintained r G"
      for r :: "('a Standard_Constant, nat) Graph_PreRule"
      by blast
    hence g:"graph G" unfolding standard_def by auto
    have "(a,b)\<in>T \<Longrightarrow> G \<Turnstile> (a,b)" for a b proof(subst eq_as_subsets,standard)
      assume a:"(a,b)\<in>T"
      from a cfg_m[unfolded transl_rules_def,THEN m]
      show "G \<Turnstile> a \<sqsubseteq> b" by (subst maintained_holds_iff[OF g,symmetric]) blast
      from a cfg_m[unfolded transl_rules_def,THEN m]
      show "G \<Turnstile> b \<sqsubseteq> a" by (subst maintained_holds_iff[OF g,symmetric]) blast
    qed
    hence h:"(\<forall>S\<in>T. G \<Turnstile> S)" by auto
    with G_std show ?rhs unfolding model_def by blast
  qed
  have d2: "\<not> ?lhs \<Longrightarrow> ?rhs \<Longrightarrow> False" proof -
    assume "\<not> ?lhs"
    then obtain a b where ab:"(S_Bot,a,b) \<in> edges cfg"
      "a \<in> vertices cfg" "b \<in> vertices cfg"
      using cfg_g unfolding cfg getRel_def by auto
    assume ?rhs then obtain G :: "('a Standard_Constant, 'a + nat) labeled_graph"
      where G:"model C G T" by auto
    with model_def have std:"standard' C G" and holds:"\<forall>S\<in>T. G \<Turnstile> S" by fast+
    hence g:"graph G" unfolding standard_def by auto
    from maintained_holds_iff[OF g] holds
    have "maintainedA (transl_rules T) G" unfolding transl_rules_def by auto
    hence mnt:"maintainedA Rules G" unfolding Rules_def
      using standard_maintains_rules[OF std] by auto
    from consequence_graphI[OF _ _ g] gr[unfolded set_of_graph_rules_def] mnt
    have cg:"consequence_graph Rules G" by fast
    with cfg_l[unfolded least_def]
    have mtd:"maintained (graph_of (0, {}), cfg) G" by blast
    have "graph_homomorphism (fst (graph_of (0::nat, {}), cfg)) G {}"
      unfolding graph_homomorphism_def using g by auto
    with mtd maintained_def have "extensible (graph_of (0, {}), cfg) G {}" by auto
    then obtain g where "edges (map_graph g cfg) \<subseteq> edges G" "vertices cfg = Domain g"
      unfolding extensible_def graph_homomorphism_def2 graph_union_iff by auto
    hence "\<exists> a b. (S_Bot,a,b) \<in> edges G" using ab unfolding edge_preserving by auto
    thus False using std unfolding standard_def getRel_def by auto
  qed
  from d1 d2 show ?thesis by metis
qed


lemma check_entailment:
  assumes "finite T" "finite C"
  shows "check_entailment C (transl_rules T) S \<longleftrightarrow> entails (t::nat itself) C T (fst S, (A_Int (fst S) (snd S)))"
   (is "?lhs = ?rhs")
proof -
  from assms(1) have fin_t:"finite (transl_rules T)" unfolding transl_rules_def by fast
  define R where "R = transl_rule S"
  define init where "init = (card (vertices (fst R)), edges (fst R))"
  have gi[intro]:"graph (graph_of init)" and init:"graph_of init = translation (fst S)"
    using verts_in_translation[of "fst S"] unfolding inv_translation_def init_def R_def by auto
  define Rs where "Rs = transl_rules T"
  define L where
    "L = fst ` UNION Rs (edges \<circ> snd) \<union> {S_Bot,S_Top,S_Idt} \<union> S_Const ` C \<union> fst ` edges (fst R)"
  have "finite (UNION (transl_rules T) (edges \<circ> snd))" using fin_t gr_transl_rules by auto
  hence fin_l:"finite L" unfolding L_def Rs_def R_def using assms(2) by auto
  have fin_t:"finite Rs" using fin_t Rs_def by auto
  define Rules where "Rules = Rs \<union> standard_rules C L"
  hence fin_r:"finite Rules" using assms(2) fin_t fin_l unfolding standard_rules_def by auto
  have incl_L:"fst ` UNION Rules (edges o snd) \<subseteq> L" "fst ` snd init \<subseteq> L" 
    unfolding L_def Rules_def init_def by (auto elim:standard_rules_edges)
  have "\<forall>R\<in>transl_rules T. graph_rule R" using gr_transl_rules by blast
  moreover have "\<forall>R\<in> constant_rules C. graph_rule R" using constant_rules_graph_rule by auto
  moreover have "\<forall>R\<in> identity_rules L. graph_rule R" using identity_rules_graph_rule by auto
  moreover have "\<forall>R\<in> {top_rule S_Top,nonempty_rule}. graph_rule R" using are_rules(1,2) by fastforce
  ultimately have gr:"set_of_graph_rules Rules"
    unfolding set_of_graph_rules_def Rules_def ball_Un standard_rules_def Rs_def
    by blast
  define sel where "sel = non_constructive_selector Rules"
  hence sel:"valid_selector Rules sel" using gr non_constructive_selector by auto
  define cfg where "cfg = the_lcg sel Rules init"
  have cfg:"cfg = entailment_model C Rs (fst R)"
    unfolding cfg_def sel_def Rules_def L_def entailment_model_def Let_def init_def..
  have cfg_c:"least_consequence_graph TYPE('a + nat) Rules (graph_of init) cfg"
    unfolding cfg_def by (rule lcg_through_make_step[OF fin_r gr gi sel])
  hence cfg_sdt:"maintainedA (standard_rules C L) cfg"
    and cfg_g: "graph cfg"
    and cfg_l:"least TYPE('a + nat) Rules (graph_of init) cfg"
    and cfg_m:"r \<in> Rs \<Longrightarrow> maintained r cfg" for r
    unfolding Rules_def least_consequence_graph_def by auto
  have cfg_lbl:"fst ` edges cfg \<subseteq> L" unfolding cfg_def
    by (auto intro!: the_lcg_edges[OF sel incl_L])
  have "(0,1) \<in> :translation (fst S):\<lbrakk>fst S\<rbrakk>" by (fact translation_self)
  hence "(0,1) \<in> :graph_of init:\<lbrakk>fst S\<rbrakk>" unfolding init by auto
  from subgraph_semantics[OF _ this] cfg_l[unfolded least_def]
  have cfg_fst:"(0,1) \<in> :cfg:\<lbrakk>fst S\<rbrakk>" unfolding cfg_def by auto
  from semantics_in_vertices[OF cfg_g this]
  have cfg_01:"0 \<in> vertices cfg" "1 \<in> vertices cfg" "(0,1)\<in>vertices cfg\<times>vertices cfg" by auto
  have d1: "\<not> ?lhs \<Longrightarrow> ?rhs \<Longrightarrow> False" proof -
    assume "\<not> ?lhs"
    hence gr:"(0,1) \<notin> :cfg:\<lbrakk>snd S\<rbrakk>" "getRel S_Bot cfg = {}"
      unfolding entailment_model_def cfg R_def Rs_def Let_def by auto
    from maintained_standard_noconstants[OF cfg_sdt cfg_g cfg_lbl gr(2)]
    obtain G :: "('a Standard_Constant, 'a + nat) labeled_graph" and f g
      where fg:"G = map_graph_fn G (f \<circ> g)"
      and f:"G = map_graph_fn cfg f" "subgraph (map_graph_fn G g) cfg"
      and G_std:"standard' C G"
      and m:"\<And> r:: ('a Standard_Constant, nat) Graph_PreRule. maintained r cfg \<Longrightarrow> maintained r G"
      and e:"\<And> x y e. x \<in> vertices cfg \<Longrightarrow> y \<in> vertices cfg \<Longrightarrow> 
                          (g (f x), g (f y)) \<in> :map_graph_fn G g:\<lbrakk>e\<rbrakk> \<Longrightarrow> (x,y) \<in> :cfg:\<lbrakk>e\<rbrakk>"
      by clarify blast (* just blast also works, but clarify blast is much faster *)
    hence g:"graph G" unfolding standard_def by auto
    have "(a,b)\<in>T \<Longrightarrow> G \<Turnstile> (a,b)" for a b apply(subst eq_as_subsets)
      using cfg_m[unfolded transl_rules_def Rs_def,THEN m]
      unfolding maintained_holds_iff[OF g,symmetric] by blast
    hence h:"(\<forall>S\<in>T. G \<Turnstile> S)" by auto
    assume "?rhs"
    from this[unfolded entails_def model_def] G_std h have "G \<Turnstile> fst S \<sqsubseteq> snd S" by blast
    with cfg_fst cfg_g f(1) have "(f 0, f 1) \<in> :G:\<lbrakk>snd S\<rbrakk>" by auto
    then have "(g (f 0), g (f 1)) \<in> :map_graph_fn G g:\<lbrakk>snd S\<rbrakk>" using map_graph_in[OF g] by auto
    with e cfg_01(1,2) gr(1) show "False" by auto
  qed
  have "?lhs \<Longrightarrow> model C G T \<Longrightarrow> (a,b) \<in> :G:\<lbrakk>fst S\<rbrakk> \<Longrightarrow> (a,b) \<in> :G:\<lbrakk>snd S\<rbrakk>"
    for G :: "('a Standard_Constant, 'a + nat) labeled_graph" and a b proof -
    assume mod:"model C G T"
    from mod model_def have std:"standard' C G" and holds:"\<forall>S\<in>T. G \<Turnstile> S" by fast+
    hence g:"graph G" unfolding standard_def by auto
    with maintained_holds_iff[OF g] holds
    have "maintainedA Rs G" unfolding transl_rules_def Rs_def by auto
    hence mnt:"maintainedA Rules G" unfolding Rules_def
      using standard_maintains_rules[OF std] by auto
    from consequence_graphI[OF _ _ g] gr[unfolded set_of_graph_rules_def] mnt
    have cg:"consequence_graph Rules G" by fast
    with cfg_l[unfolded least_def] have mtd:"maintained (graph_of init, cfg) G" by auto
    assume ab:"(a,b) \<in> :G:\<lbrakk>fst S\<rbrakk>"
    hence abv:"a \<in> vertices G" "b \<in> vertices G" using semantics_in_vertices[OF g] by auto
    from ab translation[OF g] init
    obtain f where f:"graph_homomorphism (graph_of init) G f" "(0, a) \<in> f \<and> (1, b) \<in> f"
      by auto
    from maintainedD2[OF mtd f(1)] obtain g
      where g:"graph_homomorphism cfg G g" and "f \<subseteq> g" by blast
    with f have g01:"(0, a) \<in> g" "(1, b) \<in> g" by auto
    assume ?lhs
    then consider (maintained) "(0,1) \<in> :cfg:\<lbrakk>snd S\<rbrakk>" | (no_models) ":cfg:\<lbrakk>\<bottom>\<rbrakk> \<noteq> {}"
      using cfg_g unfolding cfg entailment_model_def Let_def Rs_def R_def by auto
    thus "(a,b) \<in> :G:\<lbrakk>snd S\<rbrakk>" proof(cases)
      case maintained
      from graph_homomorphism_semantics[OF g maintained g01] show ?thesis.
    next
      case no_models
      from graph_homomorphism_nonempty[OF g no_models]
      have "getRel S_Bot G \<noteq> {}" by auto
      hence False using std unfolding standard_def by auto
      thus ?thesis by auto
    qed
  qed
  hence d2:"?lhs \<Longrightarrow> ?rhs" unfolding entails_def by auto
  from d1 d2 show ?thesis by metis
qed

end