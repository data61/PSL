section \<open>\isaheader{Examples from ITP-2010 slides (adopted to ICF v2)}\<close>
theory itp_2010
imports 
  Collections.Collections 
  Collections.Code_Target_ICF
begin

text \<open>
  Illustrates the various possibilities how to use the ICF in your own 
  algorithms by simple examples. The examples all use the data refinement
  scheme, and either define a generic algorithm or fix the operations.
\<close>


subsection "List to Set"
text \<open>
  In this simple example we do conversion from a list to a set.
  We define an abstract algorithm.
  This is then refined by a generic algorithm using a locale and by a generic 
  algorithm fixing its operations as parameters.
\<close>
  subsubsection "Straightforward version"
  \<comment> \<open>Abstract algorithm\<close>
  fun set_a where
    "set_a [] s = s" |
    "set_a (a#l) s = set_a l (insert a s)"

  \<comment> \<open>Correctness of aa\<close>
  lemma set_a_correct: "set_a l s = set l \<union> s"
    by (induct l arbitrary: s) auto

  \<comment> \<open>Generic algorithm\<close>

  setup Locale_Code.open_block \<comment> \<open>Required to make definitions inside locales
    executable\<close>
  fun (in StdSetDefs) set_i where
    "set_i [] s = s" |
    "set_i (a#l) s = set_i l (ins a s)"
  setup Locale_Code.close_block

  \<comment> \<open>Correct implementation of ca\<close>
  lemma (in StdSet) set_i_impl: "invar s \<Longrightarrow> invar (set_i l s) \<and> \<alpha> (set_i l s) = set_a l (\<alpha> s)"
    by (induct l arbitrary: s) (auto simp add: correct)

  \<comment> \<open>Instantiation\<close>
  (* We need to declare a constant to make the code generator work *)

  definition "hs_seti == hs.set_i"
  (*declare hs.set_i.simps[folded hs_seti_def, code]*)

  lemmas hs_set_i_impl = hs.set_i_impl[folded hs_seti_def]

export_code hs_seti checking SML

  \<comment> \<open>Code generation\<close>
  ML \<open>@{code hs_seti}\<close> 
  (*value "hs_seti [1,2,3::nat] hs_empty"*)

  subsubsection "Tail-Recursive version"
  \<comment> \<open>Abstract algorithm\<close>
  fun set_a2 where
    "set_a2 [] = {}" |
    "set_a2 (a#l) = (insert a (set_a2 l))"

  \<comment> \<open>Correctness of aa\<close>
  lemma set_a2_correct: "set_a2 l = set l"
    by (induct l) auto

  \<comment> \<open>Generic algorithm\<close>
  setup Locale_Code.open_block
  fun (in StdSetDefs) set_i2 where
    "set_i2 [] = empty ()" |
    "set_i2 (a#l) = (ins a (set_i2 l))"
  setup Locale_Code.close_block

  \<comment> \<open>Correct implementation of ca\<close>
  lemma (in StdSet) set_i2_impl: "invar s \<Longrightarrow> invar (set_i2 l) \<and> \<alpha> (set_i2 l) = set_a2 l"
    by (induct l) (auto simp add: correct)

  \<comment> \<open>Instantiation\<close>
  definition "hs_seti2 == hs.set_i2"
  (*declare hsr.set_i2.simps[folded hs_seti2_def, code]*)

  lemmas hs_set_i2_impl = hs.set_i2_impl[folded hs_seti2_def]

  \<comment> \<open>Code generation\<close>
  ML \<open>@{code hs_seti2}\<close> 
  (*value "hs_seti [1,2,3::nat] hs_empty"*)

subsubsection "With explicit operation parameters"

  \<comment> \<open>Alternative for few operation parameters\<close>
  fun set_i' where
    "!!ins. set_i' ins [] s = s" |
    "!!ins. set_i' ins (a#l) s = set_i' ins l (ins a s)"

  lemma (in StdSet) set_i'_impl:
    "invar s \<Longrightarrow> invar (set_i' ins l s) \<and> \<alpha> (set_i' ins l s) = set_a l (\<alpha> s)"
    by (induct l arbitrary: s) (auto simp add: correct)

  \<comment> \<open>Instantiation\<close>
  definition "hs_seti' == set_i' hs.ins"
  lemmas hs_set_i'_impl = hs.set_i'_impl[folded hs_seti'_def]

  \<comment> \<open>Code generation\<close>
  ML \<open>@{code hs_seti'}\<close> 
  (*value "hs_seti' [1,2,3::nat] hs_empty"*)


subsection "Filter Average"
text \<open>
  In this more complex example, we develop a function that filters from a set all
  numbers that are above the average of the set.
 
  First, we formulate this as a generic algorithm using a locale.
  This solution shows how the ICF v2 overcomes some technical problems that
  ICF v1 had: 
  \begin{itemize}
    \item Iterators are now polymorphic in the type, even inside locales.
      Hence, there is no special handling of iterators, as it was required
      in ICF v1.
    \item The Locale-Code package handles code generation for the instantiated
      locale. There is no need for lengthy boilerplate code as it was required
      in ICF v1.
  \end{itemize}


  Another possibility is to fix the used 
  implementations beforehand. Changing the implementation is still easy by
  changing the used operations. In this example, all used operations are 
  introduced by abbbreviations, localizing the required changes to a small part
  of the theory. This approach is more powerful, as operations are now 
  polymorphic also in the element type. However, it only allows as single 
  instantiation at a time, which is no option for generic algorithms.
\<close>

  abbreviation "average S == \<Sum>S div card S"

subsubsection "Generic Algorithm"
  locale MyContext =
    StdSet ops for ops :: "(nat,'s,'more) set_ops_scheme"
  begin
    definition avg_aux :: "'s \<Rightarrow> nat\<times>nat" 
      where
      "avg_aux s == iterate s (\<lambda>x (c,s). (c+1, s+x)) (0,0)"

    definition "avg s == case avg_aux s of (c,s) \<Rightarrow> s div c"

    definition "filter_le_avg s == let a=avg s in
      iterate s (\<lambda>x s. if x\<le>a then ins x s else s) (empty ())"

    lemma avg_aux_correct: "invar s \<Longrightarrow> avg_aux s = (card (\<alpha> s), \<Sum>(\<alpha> s) )"
      apply (unfold avg_aux_def)
      apply (rule_tac 
        I="\<lambda>it (c,sum). c=card (\<alpha> s - it) \<and> sum=\<Sum>(\<alpha> s - it)" 
        in iterate_rule_P)
      apply auto
      apply (subgoal_tac "\<alpha> s - (it - {x}) = insert x (\<alpha> s - it)")
      apply auto
      apply (subgoal_tac "\<alpha> s - (it - {x}) = insert x (\<alpha> s - it)")
      apply auto
      done

    lemma avg_correct: "invar s \<Longrightarrow> avg s = average (\<alpha> s)"
      unfolding avg_def
      using avg_aux_correct
      by auto

    lemma filter_le_avg_correct: 
      "invar s \<Longrightarrow> 
        invar (filter_le_avg s) \<and> 
        \<alpha> (filter_le_avg s) = {x\<in>\<alpha> s. x\<le>average (\<alpha> s)}"
      unfolding filter_le_avg_def Let_def
      apply (rule_tac
        I="\<lambda>it r. invar r \<and> \<alpha> r = {x\<in>\<alpha> s - it. x\<le>average (\<alpha> s)}"
        in iterate_rule_P)
      apply (auto simp add: correct avg_correct)
      done
  end

  setup Locale_Code.open_block
  interpretation hs_ctx: MyContext hs_ops by unfold_locales
  interpretation rs_ctx: MyContext rs_ops by unfold_locales
  setup Locale_Code.close_block

  definition "hs_flt_avg_test \<equiv> hs.to_list 
    o hs_ctx.filter_le_avg 
    o hs.from_list"
  definition "rs_flt_avg_test \<equiv> rs.to_list 
    o rs_ctx.filter_le_avg 
    o rs.from_list"

  
  text "Code generation"
  ML_val \<open>
    if @{code hs_flt_avg_test} (map @{code nat_of_integer} [1,2,3,4,6,7])
    <> @{code rs_flt_avg_test} (map @{code nat_of_integer} [1,2,3,4,6,7])
    then error "Oops"
    else ()
\<close> 
  

subsubsection "Using abbreviations"

  type_synonym 'a my_set = "'a hs"
  abbreviation "my_\<alpha> == hs.\<alpha>"
  abbreviation "my_invar == hs.invar"
  abbreviation "my_empty == hs.empty"
  abbreviation "my_ins == hs.ins"
  abbreviation "my_iterate == hs.iteratei"
  lemmas my_correct = hs.correct
  lemmas my_iterate_rule_P = hs.iterate_rule_P

  definition avg_aux :: "nat my_set \<Rightarrow> nat\<times>nat" 
    where
    "avg_aux s == my_iterate s (\<lambda>_. True) (\<lambda>x (c,s). (c+1, s+x)) (0,0)"

  definition "avg s == case avg_aux s of (c,s) \<Rightarrow> s div c"

  definition "filter_le_avg s == let a=avg s in
    my_iterate s (\<lambda>_. True) (\<lambda>x s. if x\<le>a then my_ins x s else s) (my_empty ())"

  lemma avg_aux_correct: "my_invar s \<Longrightarrow> avg_aux s = (card (my_\<alpha> s), \<Sum>(my_\<alpha> s) )"
    apply (unfold avg_aux_def)
    apply (rule_tac 
      I="\<lambda>it (c,sum). c=card (my_\<alpha> s - it) \<and> sum=\<Sum>(my_\<alpha> s - it)" 
      in my_iterate_rule_P)
    apply auto
    apply (subgoal_tac "my_\<alpha> s - (it - {x}) = insert x (my_\<alpha> s - it)")
    apply auto
    apply (subgoal_tac "my_\<alpha> s - (it - {x}) = insert x (my_\<alpha> s - it)")
    apply auto
    done

  lemma avg_correct: "my_invar s \<Longrightarrow> avg s = average (my_\<alpha> s)"
    unfolding avg_def
    using avg_aux_correct
    by auto

  lemma filter_le_avg_correct: 
    "my_invar s \<Longrightarrow> 
    my_invar (filter_le_avg s) \<and> 
    my_\<alpha> (filter_le_avg s) = {x\<in>my_\<alpha> s. x\<le>average (my_\<alpha> s)}"
    unfolding filter_le_avg_def Let_def
    apply (rule_tac
      I="\<lambda>it r. my_invar r \<and> my_\<alpha> r = {x\<in>my_\<alpha> s - it. x\<le>average (my_\<alpha> s)}"
      in my_iterate_rule_P)
    apply (auto simp add: my_correct avg_correct)
    done


  definition "test_set == my_ins (1::nat) (my_ins 2 (my_ins 3 (my_empty ())))"

  export_code avg_aux avg filter_le_avg test_set in SML module_name Test

end
