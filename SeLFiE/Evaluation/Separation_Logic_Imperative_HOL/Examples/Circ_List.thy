section \<open>Circular Singly Linked Lists\<close>
theory Circ_List
imports List_Seg Imp_List_Spec
begin

text \<open>
  Example of circular lists, with efficient append, prepend, pop, and rotate
  operations.
\<close>

subsection \<open>Datatype Definition\<close>

type_synonym 'a cs_list = "'a node ref option"

text \<open>A circular list is described by a list segment, with special
  cases for the empty list:\<close>
fun cs_list :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "cs_list [] None = emp"
| "cs_list (x#l) (Some p) = lseg (x#l) (Some p) (Some p)"
| "cs_list _ _ = false"

lemma [simp]: "cs_list l None = \<up>(l=[])"
  by (cases l) auto

lemma [simp]: 
  "cs_list l (Some p) 
  = (\<exists>\<^sub>Ax ls. \<up>(l=x#ls) * lseg (x#ls) (Some p) (Some p))"
  apply (rule ent_iffI)
  apply (cases l) 
  apply simp
  apply sep_auto
  apply (cases l) 
  apply simp
  apply sep_auto
  done

subsection \<open>Precision\<close>
lemma cs_prec: 
  "precise cs_list"
  apply rule
  apply (case_tac p)
  apply clarsimp

  apply clarsimp
  apply (subgoal_tac "x=xa \<and> n=na", simp)

  apply (erule prec_frame_expl[OF lseg_prec1])
  apply frame_inference
  apply frame_inference

  apply (drule prec_frame[OF sngr_prec])
  apply frame_inference
  apply frame_inference
  apply simp
  done

lemma cs_imp_list_impl: "imp_list cs_list"
  apply unfold_locales
  apply (rule cs_prec)
  done
interpretation cs: imp_list cs_list by (rule cs_imp_list_impl)

subsection \<open>Operations\<close>
subsubsection \<open>Allocate Empty List\<close>
definition cs_empty :: "'a::heap cs_list Heap" where
  "cs_empty \<equiv> return None"

lemma cs_empty_rule: "<emp> cs_empty <cs_list []>"
  unfolding cs_empty_def
  by sep_auto

lemma cs_empty_impl: "imp_list_empty cs_list cs_empty" 
  by unfold_locales (sep_auto heap: cs_empty_rule)
interpretation cs: imp_list_empty cs_list cs_empty by (rule cs_empty_impl)

subsubsection \<open>Prepend Element\<close>
fun cs_prepend :: "'a \<Rightarrow> 'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
  "cs_prepend x None = do {
    p \<leftarrow> ref (Node x None); 
    p:=Node x (Some p); 
    return (Some p)
  }"
| "cs_prepend x (Some p) = do {
    n \<leftarrow> !p;
    q \<leftarrow> ref (Node (val n) (next n));
    p := Node x (Some q);
    return (Some p)
  }"

declare cs_prepend.simps [simp del]

lemma cs_prepend_rule: 
  "<cs_list l p> cs_prepend x p <cs_list (x#l)>"
  apply (cases p)
  apply simp_all
  apply (sep_auto simp: cs_prepend.simps)

  apply (sep_auto simp: cs_prepend.simps)
  done

lemma cs_prepend_impl: "imp_list_prepend cs_list cs_prepend"
  by unfold_locales (sep_auto heap: cs_prepend_rule)
interpretation cs: imp_list_prepend cs_list cs_prepend 
  by (rule cs_prepend_impl)

subsubsection \<open>Append Element\<close>
fun cs_append :: "'a \<Rightarrow> 'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
  "cs_append x None = do { 
    p \<leftarrow> ref (Node x None); 
    p:=Node x (Some p); 
    return (Some p) }"
| "cs_append x (Some p) = do {
    n \<leftarrow> !p;
    q \<leftarrow> ref (Node (val n) (next n));
    p := Node x (Some q);
    return (Some q)
  }"

declare cs_append.simps [simp del]

lemma cs_append_rule: 
  "<cs_list l p> cs_append x p <cs_list (l@[x])>"
  apply (cases p)
  apply simp_all
  apply (sep_auto simp: cs_append.simps)

  apply (sep_auto simp: cs_append.simps)
  apply (rule ent_frame_fwd)
  apply (rule_tac s=pp in lseg_append) (* frame_inference does no backtracking
    on instantiating schematics, hence we have to give it some help here. *)
  apply frame_inference
  apply (sep_auto)
  done

lemma cs_append_impl: "imp_list_append cs_list cs_append"
  by unfold_locales (sep_auto heap: cs_append_rule)
interpretation cs: imp_list_append cs_list cs_append
  by (rule cs_append_impl)

subsubsection \<open>Pop First Element\<close>
fun cs_pop :: "'a::heap cs_list \<Rightarrow> ('a\<times>'a cs_list) Heap" where
  "cs_pop None = raise STR ''Pop from empty list''"
| "cs_pop (Some p) = do {
    n1 \<leftarrow> !p;
    if next n1 = Some p then
      return (val n1,None) \<comment> \<open>Singleton list becomes empty list\<close>
    else do {
      let p2 = the (next n1);
      n2 \<leftarrow> !p2;
      p := Node (val n2) (next n2);
      return (val n1,Some p)
    }
  }"

declare cs_pop.simps[simp del]

lemma cs_pop_rule: 
  "<cs_list (x#l) p> cs_pop p <\<lambda>(y,p'). cs_list l p' * true * \<up>(y=x)>"
  apply (cases p)
  apply (sep_auto simp: cs_pop.simps)

  apply (cases l)
  apply (sep_auto simp: cs_pop.simps dflt_simps: option.sel)

  apply (sep_auto 
    simp: cs_pop.simps 
    dflt_simps: option.sel 
    eintros del: exI)
  (* Some unfortunate quantifier fiddling :( *)
  apply (rule_tac x=aa in exI)
  apply (rule_tac x=list in exI)
  apply (rule_tac x=pp in exI)
  apply clarsimp
  apply (rule exI)
  apply sep_auto
  done

lemma cs_pop_impl: "imp_list_pop cs_list cs_pop"
  apply unfold_locales 
  apply (sep_auto heap: cs_pop_rule elim!: neq_NilE)
  done
interpretation cs: imp_list_pop cs_list cs_pop by (rule cs_pop_impl)

subsubsection \<open>Rotate\<close>
fun cs_rotate :: "'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
  "cs_rotate None = return None"
| "cs_rotate (Some p) = do {
    n \<leftarrow> !p;
    return (next n)
  }"

declare cs_rotate.simps [simp del]

lemma cs_rotate_rule: 
  "<cs_list l p> cs_rotate p <cs_list (rotate1 l)>"
  apply (cases p)
  apply (sep_auto simp: cs_rotate.simps)

  apply (cases l)
  apply simp

  apply (case_tac list)
  apply simp
  apply (sep_auto simp: cs_rotate.simps)

  apply (sep_auto simp: cs_rotate.simps)
  apply (rule ent_frame_fwd)
  apply (rule_tac s="pp" in lseg_append)
  apply frame_inference
  apply sep_auto
  done

lemma cs_rotate_impl: "imp_list_rotate cs_list cs_rotate"
  apply unfold_locales 
  apply (sep_auto heap: cs_rotate_rule)
  done
interpretation cs: imp_list_rotate cs_list cs_rotate by (rule cs_rotate_impl)

subsection \<open>Test\<close>
definition "test \<equiv> do {
  l \<leftarrow> cs_empty;
  l \<leftarrow> cs_append ''a'' l;
  l \<leftarrow> cs_append ''b'' l;
  l \<leftarrow> cs_append ''c'' l;
  l \<leftarrow> cs_prepend ''0'' l;
  l \<leftarrow> cs_rotate l;
  (v1,l)\<leftarrow>cs_pop l;
  (v2,l)\<leftarrow>cs_pop l;
  (v3,l)\<leftarrow>cs_pop l;
  (v4,l)\<leftarrow>cs_pop l;
  return [v1,v2,v3,v4]
}"

definition "test_result \<equiv> [''a'', ''b'', ''c'', ''0'']"

lemma "<emp> test <\<lambda>r. \<up>(r=test_result) * true>"
  unfolding test_def test_result_def
  apply (sep_auto)
  done
  
export_code test checking SML_imp

ML_val \<open>
  val res = @{code test} ();
  if res = @{code test_result} then () else raise Match;
\<close>

hide_const (open) test test_result

end
