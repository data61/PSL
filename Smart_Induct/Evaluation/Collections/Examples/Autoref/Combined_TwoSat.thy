section \<open>Formalisation of 2SAT using Autoref with graph tabulation via Containers\<close>

theory Combined_TwoSat
imports Containers.TwoSat_Ex Simple_DFS "Containers.Mapping_Impl"
begin

subsection \<open>Representation of Formulas\<close>  

text \<open>Tell Autoref that literals are refined by themselves\<close>  
lemma [autoref_rules]: "(Lit,Lit)\<in>Id\<rightarrow>Id\<rightarrow>Id" by simp

text \<open>We represent formulas as lists of pairs of literals\<close>
type_synonym cnfi = "(lit \<times> lit) list"

text \<open>We define the relation between formula implementations and formula via
  an abstraction function and an invariant\<close>
definition cnf_\<alpha> :: "cnfi \<Rightarrow> cnf" where "cnf_\<alpha> cnfi = (uncurry Upair) ` set cnfi"
definition is_2sati :: "cnfi \<Rightarrow> bool" where "is_2sati cnfi \<equiv> \<forall>(l1,l2)\<in>set cnfi. l1\<noteq>l2"  
definition "cnfi_rel \<equiv> br cnf_\<alpha> is_2sati"

text \<open>We show that the concrete invariant matches our abstract invariant @{const is_2sat}\<close>
lemma is_2sati_correct: "is_2sati cnfi \<longleftrightarrow> is_2sat (cnf_\<alpha> cnfi)"  
  unfolding is_2sati_def is_2sat_def cnf_\<alpha>_def
  by (auto)

text \<open>Setup for Autoref, the conceptual types of formulas\<close>
consts i_cnf :: "interface"
lemmas [autoref_rel_intf] = REL_INTFI[of "cnfi_rel" i_cnf]

subsection \<open>Implication Graph\<close>

text \<open>We implement the implication graph as a function from nodes to 
  distinct lists of nodes. However, instead of iterating over the whole formula
  each time we query the successors of a node, we tabulate the complete successor
  function in a map. This map will later be implemented using the Containers framework.
  
  The function \<open>\<alpha>sl\<close> abstracts from a mapping to a successor function, 
  interpreting unmapped nodes to have empty successor lists.
\<close>
(* Intentionally restricting the types here: The concept is as general as 
  inserting elements into \<open>('a,'b list) mapping\<close>. *)
definition \<alpha>sl :: "(lit, lit list) mapping \<Rightarrow> lit \<Rightarrow> lit list"
  where "\<alpha>sl m \<equiv> the_default [] o Mapping.lookup m"

text \<open>The \<open>ins_edge\<close> option inserts a new element \<open>v\<close> into the successor list for node \<open>k\<close>\<close>
definition ins_edge :: "lit \<Rightarrow> lit \<Rightarrow> ((lit,lit list) mapping) \<Rightarrow> ((lit,lit list) mapping)"
  where "ins_edge k v m = (case Mapping.lookup m k of 
    None \<Rightarrow> Mapping.update k [v] m | Some l \<Rightarrow> Mapping.update k (remdups (v#l)) m)"

text \<open>Abstract meaning of the empty map and the \<open>ins_edge\<close> operation:\<close>      
lemma sl_abs[simp]: 
  "\<alpha>sl Mapping.empty = (\<lambda>_. [])"
  "\<alpha>sl (ins_edge k v m) = (\<alpha>sl m)(k := remdups (v#\<alpha>sl m k))"  
  unfolding \<alpha>sl_def ins_edge_def by(transfer; auto split: option.split; fail)+

text \<open>Auxiliary lemmas for inductive reasoning about list-representation of formula\<close>  
lemma cnf_\<alpha>_struct[simp]: 
  "cnf_\<alpha> [] = {}"
  "cnf_\<alpha> (cl # cls) = insert (uncurry Upair cl) (cnf_\<alpha> cls)" for cl cls
  by (auto simp: cnf_\<alpha>_def)

lemma is_2sati_struct[simp]:
  "is_2sati []" 
  "is_2sati ((l1,l2) # cnfi) \<longleftrightarrow> l1\<noteq>l2 \<and> is_2sati cnfi" for l1 l2 cnfi
  by(auto simp add: is_2sati_def)

text \<open>Finally, it is straightforward to tabulate the successor graph by folding 
  over the clause list:
\<close>
definition "ins_edges \<equiv> \<lambda>(l\<^sub>1,l\<^sub>2) m. ins_edge (negate l\<^sub>1) l\<^sub>2 (ins_edge (negate l\<^sub>2) l\<^sub>1 m)"
definition "tabulate cnfi = fold ins_edges cnfi Mapping.empty"

text \<open>The correctness proof is also straightforward, 
  although the necessary generalization for the induction 
  to go through makes it somewhat technical.
\<close>

lemma tabulate_aux1:
  "E_of_succ (\<lambda>v. set (\<alpha>sl (fold ins_edges cnfi M) v)) 
  = imp_graph (cnf_\<alpha> cnfi) \<union> E_of_succ (set o \<alpha>sl M)"
proof (induction cnfi arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons a cnfi)
  show ?case 
    by (simp add: Cons.IH)(simp add: E_of_succ_def ins_edges_def split!: prod.splits if_splits)
qed

lemma tabulate_aux2:
  "distinct (\<alpha>sl M v) \<Longrightarrow> distinct (\<alpha>sl (fold ins_edges cnfi M) v)"
  apply (induction cnfi arbitrary: M)
  apply simp
  apply (clarsimp simp: ins_edges_def)
  apply rprems
  apply auto 
  done

lemma tabulate_refines[autoref_rules]: 
  "(\<lambda>cnfi. \<alpha>sl (tabulate cnfi), imp_graph) \<in> cnfi_rel \<rightarrow> \<langle>Id\<rangle>succg_rel"
proof rule
  fix cnfi cnf
  assume "(cnfi,cnf)\<in>cnfi_rel"
  then show "(\<alpha>sl (tabulate cnfi), imp_graph cnf) \<in> \<langle>Id\<rangle>succg_rel"
    unfolding in_id_succg_rel_iff tabulate_def 
    using tabulate_aux1[of cnfi Mapping.empty] 
    using tabulate_aux2[of Mapping.empty _ cnfi]
    unfolding E_of_succ_def cnfi_rel_def br_def by auto
qed  
  

(* Non-tail-recursive version with simpler proof *)  
fun ig_succm :: "cnfi \<Rightarrow> (lit, lit list) mapping" where
  "ig_succm [] = Mapping.empty"
| "ig_succm (cl#cls) = ins_edges cl (ig_succm cls)"  

lemma ig_succm_refines: 
  "(\<lambda>cnfi. \<alpha>sl (ig_succm cnfi), imp_graph) \<in> cnfi_rel \<rightarrow> \<langle>Id\<rangle>succg_rel"
proof
  fix cnfi cnf
  assume "(cnfi,cnf)\<in>cnfi_rel"
  then show "(\<alpha>sl (ig_succm cnfi), imp_graph cnf) \<in> \<langle>Id\<rangle>succg_rel"
    unfolding in_id_succg_rel_iff
    apply (induction cnfi arbitrary: cnf rule: ig_succm.induct)
    apply (simp add: cnfi_rel_def in_br_conv)
    apply (force simp: cnfi_rel_def in_br_conv ins_edges_def)
    done
qed

subsection \<open>Variables of CNF\<close>
text \<open>The set of variables of a CNF is implemented by a distinct list\<close>
definition vars_of_cnfi :: "cnfi \<Rightarrow> var list"
where "vars_of_cnfi cnfi \<equiv> remdups (concat (map (\<lambda>(l1, l2). [var l1, var l2]) cnfi))"

lemma vars_of_cnfi_refine[autoref_rules]: 
  "(vars_of_cnfi, vars_of_cnf) \<in> cnfi_rel \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  by (fastforce simp: br_def vars_of_cnfi_def cnfi_rel_def
         vars_of_cnf_def cnf_\<alpha>_def list_set_rel_def)
  

subsection \<open>Implementing Satisfiability Check\<close>

context
  fixes cnfi cnf
  assumes A[autoref_rules]: "(cnfi,cnf)\<in>cnfi_rel"
begin  
  lemma 
    shows cnfi_finite_reachable[simp]: "finite ((imp_graph cnf)\<^sup>* `` {l})"
      and cnfi_finite_vars: "finite (vars_of_cnf cnf)"
      and cnfi_is_2sat: "is_2sat cnf"
    using A apply -
    apply (auto simp: finite_rtrancl_Image cnfi_rel_def br_def cnf_\<alpha>_def) [2]
    by (simp add: cnfi_rel_def br_def is_2sati_correct)
  
  lemma sat1_refine: "satisfiable cnf = (let gr = imp_graph cnf in
       \<forall>x\<in>vars_of_cnf cnf. \<not> ((Pos x, Neg x) \<in> gr\<^sup>* \<and> (Neg x, Pos x) \<in> gr\<^sup>* ))"
    using finite_2sat_iff[OF cnfi_finite_vars cnfi_is_2sat] by (simp add: Let_def)
    
  schematic_goal sati_refine: "(?f::?'c, satisfiable cnf) \<in> ?R"
    unfolding sat1_refine
    by autoref
    
end

concrete_definition sati uses sati_refine

text \<open>Setup of Containers-Framework to handle RBT-maps of literals\<close>
derive ccompare lit   derive (rbt) mapping_impl lit


export_code sati checking SML

export_code sati checking SML OCaml? Haskell? Scala

lemma sati_correct: "is_2sati cnfi \<Longrightarrow> sati cnfi \<longleftrightarrow> satisfiable (cnf_\<alpha> cnfi)"
  using sati.refine unfolding cnfi_rel_def br_def 
  by (auto dest: fun_relD)
  
lemma sati_autoref_rl[autoref_rules]: "(sati, satisfiable) \<in> cnfi_rel \<rightarrow> bool_rel"
  using sati.refine by auto

end
