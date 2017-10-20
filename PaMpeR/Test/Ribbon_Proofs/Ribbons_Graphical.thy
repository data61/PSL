section {* Syntax and proof rules for graphical diagrams *}

theory Ribbons_Graphical imports 
  Ribbons_Interfaces
begin

text {* We introduce a graphical syntax for diagrams, describe how to extract 
  commands and interfaces, and give proof rules for graphical diagrams. *}

subsection {* Syntax of graphical diagrams *}

text {* Fix a type for node identifiers *}
typedecl node

text {* Note that this datatype is necessarily an overapproximation of 
  syntactically-wellformed diagrams, for the reason that we can't impose the 
  well-formedness constraints while maintaining admissibility of the datatype 
  declarations. So, we shall impose well-formedness in a separate definition. 
  *}
  
datatype assertion_gadget =
  Rib "assertion"
| Exists_dia "string" "diagram"
and command_gadget = 
  Com "command"
| Choose_dia "diagram" "diagram"
| Loop_dia "diagram"
and diagram = Graph 
  "node fset" 
  "node \<Rightarrow> assertion_gadget" 
  "(node fset \<times> command_gadget \<times> node fset) list"
type_synonym labelling = "node \<Rightarrow> assertion_gadget"
type_synonym edge = "node fset \<times> command_gadget \<times> node fset"

text {* Projecting components from a graph *}

fun vertices :: "diagram \<Rightarrow> node fset" ("_^V" [1000] 1000)
where "(Graph V \<Lambda> E)^V = V"

term "this (is^V) = (a test)^V"

fun labelling :: "diagram \<Rightarrow> labelling" ("_^\<Lambda>" [1000] 1000)
where "(Graph V \<Lambda> E)^\<Lambda> = \<Lambda>"

fun edges :: "diagram \<Rightarrow> edge list" ("_^E" [1000] 1000)
where "(Graph V \<Lambda> E)^E = E"

subsection {* Well formedness of graphical diagrams *}

definition acyclicity :: "edge list \<Rightarrow> bool"
where
  "acyclicity E \<equiv> acyclic (\<Union>e \<in> set E. fset (fst3 e) \<times> fset (thd3 e))"

definition linearity :: "edge list \<Rightarrow> bool"
where
  "linearity E \<equiv> 
    distinct E \<and> (\<forall>e \<in> set E. \<forall>f \<in> set E. e \<noteq> f \<longrightarrow> 
    fst3 e |\<inter>| fst3 f = {||} \<and>
    thd3 e |\<inter>| thd3 f = {||})"

lemma linearityD:
  assumes "linearity E"
  shows "distinct E"
  and "\<And>e f. \<lbrakk> e \<in> set E ; f \<in> set E ; e \<noteq> f \<rbrakk> \<Longrightarrow> 
    fst3 e |\<inter>| fst3 f = {||} \<and>
    thd3 e |\<inter>| thd3 f = {||}"
using assms unfolding linearity_def by auto

lemma linearityD2:
  "linearity E \<Longrightarrow> (\<forall>e f. e \<in> set E \<and> f \<in> set E \<and> e \<noteq> f \<longrightarrow> 
    fst3 e |\<inter>| fst3 f = {||} \<and>
    thd3 e |\<inter>| thd3 f = {||})"
unfolding linearity_def by auto

inductive
  wf_ass :: "assertion_gadget \<Rightarrow> bool" and
  wf_com :: "command_gadget \<Rightarrow> bool" and
  wf_dia :: "diagram \<Rightarrow> bool"
where
  wf_rib: "wf_ass (Rib p)" 
| wf_exists: "wf_dia G \<Longrightarrow> wf_ass (Exists_dia x G)"
| wf_com: "wf_com (Com c)"
| wf_choice: "\<lbrakk> wf_dia G ; wf_dia H \<rbrakk> \<Longrightarrow> wf_com (Choose_dia G H)"
| wf_loop: "wf_dia G \<Longrightarrow> wf_com (Loop_dia G)"
| wf_dia: "\<lbrakk> \<forall>e \<in> set E. wf_com (snd3 e) ; \<forall>v \<in> fset V. wf_ass (\<Lambda> v) ;
  acyclicity E ; linearity E ; \<forall>e \<in> set E. fst3 e |\<union>| thd3 e |\<subseteq>| V \<rbrakk> \<Longrightarrow> 
  wf_dia (Graph V \<Lambda> E)"

inductive_cases wf_dia_inv': "wf_dia (Graph V \<Lambda> E)"

lemma wf_dia_inv:  
  assumes "wf_dia (Graph V \<Lambda> E)"
  shows "\<forall>v \<in> fset V. wf_ass (\<Lambda> v)" 
    and "\<forall>e \<in> set E. wf_com (snd3 e)" 
    and "acyclicity E" 
    and "linearity E" 
    and "\<forall>e \<in> set E. fst3 e |\<union>| thd3 e |\<subseteq>| V"
using assms
apply -  (* This acts as an intro rule for &&& *)
apply (elim wf_dia_inv', simp)+
done

subsection {* Initial and terminal nodes *}

definition
  initials :: "diagram \<Rightarrow> node fset"
where
  "initials G = ffilter (\<lambda>v. (\<forall>e \<in> set G^E. v |\<notin>| thd3 e)) G^V"

definition
   terminals :: "diagram \<Rightarrow> node fset"
where
  "terminals G = ffilter (\<lambda>v. (\<forall>e \<in> set G^E. v |\<notin>| fst3 e)) G^V"

lemma no_edges_imp_all_nodes_initial:
  "initials (Graph V \<Lambda> []) = V"
by (auto simp add: initials_def)

lemma no_edges_imp_all_nodes_terminal:
  "terminals (Graph V \<Lambda> []) = V"
by (auto simp add: terminals_def)

lemma initials_in_vertices:
   "initials G |\<subseteq>| G^V"
unfolding initials_def by auto

lemma terminals_in_vertices:
   "terminals G |\<subseteq>| G^V"
unfolding terminals_def by auto

subsection {* Top and bottom interfaces *}

primrec
  top_ass :: "assertion_gadget \<Rightarrow> interface" and
  top_dia :: "diagram \<Rightarrow> interface"
where
  "top_dia (Graph V \<Lambda> E) = (\<Otimes>v |\<in>| initials (Graph V \<Lambda> E). top_ass (\<Lambda> v))"
| "top_ass (Rib p) = Ribbon p"
| "top_ass (Exists_dia x G) = Exists_int x (top_dia G)"

primrec
  bot_ass :: "assertion_gadget \<Rightarrow> interface" and
  bot_dia :: "diagram \<Rightarrow> interface"
where
  "bot_dia (Graph V \<Lambda> E) = (\<Otimes>v |\<in>| terminals (Graph V \<Lambda> E). bot_ass (\<Lambda> v))"
| "bot_ass (Rib p) = Ribbon p"
| "bot_ass (Exists_dia x G) = Exists_int x (bot_dia G)"


subsection {* Proof rules for graphical diagrams *}

inductive
  prov_dia :: "[diagram, interface, interface] \<Rightarrow> bool" and
  prov_com :: "[command_gadget, interface, interface] \<Rightarrow> bool" and
  prov_ass :: "assertion_gadget \<Rightarrow> bool"
where
  Skip: "prov_ass (Rib p)"
| Exists: "prov_dia G _ _ \<Longrightarrow> prov_ass (Exists_dia x G)"
| Basic: "prov_triple (asn P, c, asn Q) \<Longrightarrow> prov_com (Com c) P Q"
| Choice: "\<lbrakk> prov_dia G P Q ; prov_dia H P Q \<rbrakk> 
    \<Longrightarrow> prov_com (Choose_dia G H) P Q"
| Loop: "prov_dia G P P \<Longrightarrow> prov_com (Loop_dia G) P P"
| Main: "\<lbrakk> wf_dia G ; \<And>v. v \<in> fset G^V \<Longrightarrow> prov_ass (G^\<Lambda> v);
    \<And>e. e \<in> set G^E \<Longrightarrow> prov_com (snd3 e) 
      (\<Otimes>v |\<in>| fst3 e. bot_ass (G^\<Lambda> v))
      (\<Otimes>v |\<in>| thd3 e. top_ass (G^\<Lambda> v))\<rbrakk> 
    \<Longrightarrow> prov_dia G (top_dia G) (bot_dia G)"

inductive_cases main_inv: "prov_dia (Graph V \<Lambda> E) P Q"
inductive_cases loop_inv: "prov_com (Loop_dia G) P Q"
inductive_cases choice_inv: "prov_com (Choose_dia G H) P Q"
inductive_cases basic_inv: "prov_com (Com c) P Q"
inductive_cases exists_inv: "prov_ass (Exists_dia x G)"
inductive_cases skip_inv: "prov_ass (Rib p)"

subsection {* Extracting commands from diagrams *}

type_synonym lin = "(node + edge) list"

text {* A linear extension (lin) of a diagram is a list of its nodes and edges
  which respects the order of those nodes and edges. That is, if an edge
  @{term e} goes from node @{term v} to node @{term w}, then @{term v} and 
  @{term e} and @{term w} must have strictly increasing positions in the list. 
  *}

definition lins :: "diagram \<Rightarrow> lin set"
where
"lins G \<equiv> {\<pi> :: lin. 
    (distinct \<pi>) 
  \<and> (set \<pi> = (fset G^V) <+> (set G^E)) 
  \<and> (\<forall>i j v e. i < length \<pi> \<and> j < length \<pi> \<and> \<pi>!i = Inl v \<and> \<pi>!j = Inr e 
    \<and> v |\<in>| fst3 e \<longrightarrow> i<j) 
  \<and> (\<forall>j k w e. j < length \<pi> \<and> k < length \<pi> \<and> \<pi>!j = Inr e \<and> \<pi>!k = Inl w 
    \<and> w |\<in>| thd3 e \<longrightarrow> j<k) }"

lemma linsD:
  assumes "\<pi> \<in> lins G"
  shows "(distinct \<pi>)" 
    and "(set \<pi> = (fset G^V) <+> (set G^E))" 
    and "(\<forall>i j v e. i < length \<pi> \<and> j < length \<pi> 
     \<and> \<pi>!i = Inl v \<and> \<pi>!j = Inr e \<and> v |\<in>| fst3 e \<longrightarrow> i<j)"
    and "(\<forall>j k w e. j < length \<pi> \<and> k < length \<pi> 
     \<and> \<pi>!j = Inr e \<and> \<pi>!k = Inl w \<and> w |\<in>| thd3 e \<longrightarrow> j<k)"
using assms
apply -
apply (unfold lins_def Collect_iff)
apply (elim conjE, assumption)+
done

text {* The following lemma enables the inductive definition below to be
  proved monotonic. It does this by showing how one of the premises of the
  @{term coms_main} rule can be rewritten in a form that is more verbose but 
  easier to prove monotonic. *}

lemma coms_mono_helper:
  "(\<forall>i<length \<pi>. case_sum (coms_ass \<circ> \<Lambda>) (coms_com \<circ> snd3) (\<pi>!i) (cs!i)) 
  = 
  ((\<forall>i. i<length \<pi> \<and> (\<exists>v. (\<pi>!i) = Inl v) \<longrightarrow> 
    coms_ass (\<Lambda> (projl (\<pi>!i))) (cs!i)) \<and>
  (\<forall>i. i<length \<pi> \<and> (\<exists>e. (\<pi>!i) = Inr e) \<longrightarrow> 
    coms_com (snd3 (projr (\<pi>!i))) (cs!i)))"
apply (intro iffI)
apply auto[1]
apply (intro allI impI, case_tac "\<pi>!i", auto)
done
    
text {* The @{term coms_dia} function extracts a set of commands from a 
  diagram. Each command in @{term "coms_dia G"} is obtained by extracting a 
  command from each of @{term G}'s nodes and edges (using @{term coms_ass} or 
  @{term coms_com} respectively), then picking a linear extension @{term \<pi>} of 
  these nodes and edges (using @{term lins}), and composing the extracted 
  commands in accordance with @{term \<pi>}.
*}

inductive
  coms_dia :: "[diagram, command] \<Rightarrow> bool" and
  coms_ass :: "[assertion_gadget, command] \<Rightarrow> bool" and
  coms_com :: "[command_gadget, command] \<Rightarrow> bool"
where
  coms_skip: "coms_ass (Rib p) Skip"
| coms_exists: "coms_dia G c \<Longrightarrow> coms_ass (Exists_dia x G) c"
| coms_basic: "coms_com (Com c) c"
| coms_choice: "\<lbrakk> coms_dia G c; coms_dia H d \<rbrakk> \<Longrightarrow> 
    coms_com (Choose_dia G H) (Choose c d)"
| coms_loop: "coms_dia G c \<Longrightarrow> coms_com (Loop_dia G) (Loop c)"
| coms_main: "\<lbrakk> \<pi> \<in> lins (Graph V \<Lambda> E); length cs = length \<pi>;
    \<forall>i<length \<pi>. case_sum (coms_ass \<circ> \<Lambda>) (coms_com \<circ> snd3) (\<pi>!i) (cs!i) \<rbrakk> 
    \<Longrightarrow> coms_dia (Graph V \<Lambda> E) (foldr (op ;;) cs Skip)"
monos 
  coms_mono_helper

inductive_cases coms_skip_inv: "coms_ass (Rib p) c"
inductive_cases coms_exists_inv: "coms_ass (Exists_dia x G) c"
inductive_cases coms_basic_inv: "coms_com (Com c') c"
inductive_cases coms_choice_inv: "coms_com (Choose_dia G H) c"
inductive_cases coms_loop_inv: "coms_com (Loop_dia G) c"
inductive_cases coms_main_inv: "coms_dia G c"

end
