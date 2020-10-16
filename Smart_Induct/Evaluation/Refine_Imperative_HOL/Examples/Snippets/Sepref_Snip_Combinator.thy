section \<open>Snippet to Define Custom Combinators\<close>
theory Sepref_Snip_Combinator
imports "../../IICF/IICF"
begin

  subsection \<open>Definition of the Combinator\<close>
  
  text \<open>
    Currently, when defining new combinators, you are largely on your own.
    If you can show your combinator equivalent to some other, already existing, 
    combinator, you should apply this equivalence in the monadify phase.

    In this example, we show the development of a map combinator from scratch.
    \<close>

  text \<open>We set ourselves in to a context where we fix the abstract and concrete 
    arguments of the monadic map combinator, as well as the refinement assertions,
    and a frame, that represents the remaining heap content, and may be read by the map-function. \<close>
  context 
    fixes f :: "'a \<Rightarrow> 'b nres"
    fixes l :: "'a list"

    fixes fi :: "'ai \<Rightarrow> 'bi Heap"
    fixes li :: "'ai list"

    fixes A A' :: "'a \<Rightarrow> 'ai \<Rightarrow> assn" \<comment> \<open>Refinement for list elements before and after map-function. 
      Different, as map function may invalidate list elements!\<close>
    fixes B :: "'b \<Rightarrow> 'bi \<Rightarrow> assn"

    fixes F :: assn \<comment> \<open>Symbolic frame, representing all heap content the map-function body may access\<close>

    notes [[sepref_register_adhoc f l]] \<comment> \<open>Register for operation id\<close>

    assumes f_rl: "hn_refine (hn_ctxt A x xi * F) (fi xi) (hn_ctxt A' x xi * F) B (f$x)"
      \<comment> \<open>Refinement for \<open>f\<close>\<close>

  begin  

    text \<open>We implement our combinator using the monadic refinement framework.\<close>
    definition "mmap \<equiv> RECT (\<lambda>mmap. 
      \<lambda>[] \<Rightarrow> RETURN [] 
    | x#xs \<Rightarrow> do { x \<leftarrow> f x; xs \<leftarrow> mmap xs; RETURN (x#xs) }) l"

    subsection \<open>Synthesis of Implementation\<close>

    text \<open>In order to propagate the frame \<open>F\<close> during synthesis, we use a trick: We wrap the
      frame into a dummy refinement assertion. This way, sepref recognizes the frame just as
      another context element, and does correct propagation.\<close>
    definition "F_assn (x::unit) (y::unit) \<equiv> F"
    lemma F_unf: "hn_ctxt F_assn x y = F"
      by (auto simp: F_assn_def hn_ctxt_def)

    text \<open>We build a combinator rule to refine \<open>f\<close>. We need a combinator rule here,
      because \<open>f\<close> does not only depend on its formal arguments, but also on the frame 
      (represented as dummy argument). \<close>  
    lemma f_rl': "hn_refine (hn_ctxt A x xi * hn_ctxt (F_assn) dx dxi) (fi xi) (hn_ctxt A' x xi * hn_ctxt (F_assn) dx dxi) B (f$x)" 
      unfolding F_unf by (rule f_rl)

    text \<open>Then we use the Sepref tool to synthesize an implementation of \<open>mmap\<close>.\<close>  
    schematic_goal mmap_impl:
      notes [sepref_comb_rules] = hn_refine_frame[OF f_rl']
      shows "hn_refine (hn_ctxt (list_assn A) l li * hn_ctxt (F_assn) dx dxi) (?c::?'c Heap) ?\<Gamma>' ?R mmap"
      unfolding mmap_def "HOL_list.fold_custom_empty"
      apply sepref_dbg_keep
      done

    text \<open>We unfold the wrapped frame\<close>  
    lemmas mmap_impl' = mmap_impl[unfolded F_unf]
  
  end

  subsection \<open>Setup for Sepref\<close>
  text \<open>Outside the context, we extract the synthesized implementation as a new constant, and set up
    code theorems for the fixed-point combinators.\<close>
  concrete_definition mmap_impl uses mmap_impl'
  prepare_code_thms mmap_impl_def

  text \<open>Moreover, we have to manually declare arity and monadify theorems.
    The arity theorem ensures that we always have a constant number of operators, and 
    the monadify theorem determines an execution order: The list-argument is evaluated first.
    \<close>
  lemma mmap_arity[sepref_monadify_arity]: "mmap \<equiv> \<lambda>\<^sub>2f l. SP mmap$(\<lambda>\<^sub>2x. f$x)$l" by simp
  lemma mmap_mcomb[sepref_monadify_comb]: "mmap$f$x \<equiv> (\<bind>)$(EVAL$x)$(\<lambda>\<^sub>2x. SP mmap$f$x)" by simp

  text \<open>We can massage the refinement theorem @{thm mmap_impl.refine} a bit, to get a valid 
    combinator rule\<close>
  print_statement hn_refine_cons_pre[OF _ mmap_impl.refine, sepref_prep_comb_rule, no_vars]

  lemma mmap_comb_rl[sepref_comb_rules]:
    assumes "P \<Longrightarrow>\<^sub>t hn_ctxt (list_assn A) l li * F"
        \<comment> \<open>Initial frame\<close>
      and "\<And>x xi. hn_refine (hn_ctxt A x xi * F) (fi xi) (Q x xi) B (f x)"
        \<comment> \<open>Refinement of map-function\<close>
      and "\<And>x xi. Q x xi \<Longrightarrow>\<^sub>t hn_ctxt A' x xi * F"
        \<comment> \<open>Recover refinement for list-element and original frame from what map-function produced\<close>
    shows "hn_refine P (mmap_impl fi li) (hn_ctxt (list_assn A') l li * F) (list_assn B) (mmap$(\<lambda>\<^sub>2x. f x)$l)"
    unfolding APP_def PROTECT2_def
    using hn_refine_cons_pre[OF _ mmap_impl.refine, sepref_prep_comb_rule, of P A l li F fi Q B f A']
    using assms
    by simp

  subsection \<open>Example\<close>  

  text \<open>Finally, we can test our combinator. Note how the 
    map-function accesses the array on the heap, which is not among its arguments. 
    This is only possible as we passed around a frame. \<close>    

  sepref_thm test_mmap 
    is "\<lambda>l. do { let a = op_array_of_list [True,True,False]; mmap (\<lambda>x. do { mop_list_get a (x mod 3) }) l }"
    :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a list_assn bool_assn"
    unfolding HOL_list.fold_custom_empty
    by sepref

  subsection \<open>Limitations\<close>  
  text \<open>
    Currently, the major limitation is that combinator rules are fixed to specific data types.
    In our example, we did an implementation for HOL lists. We cannot come up with an alternative implementation, 
    for, e.g., array-lists, but have to use a different abstract combinator.

    One workaround is to use some generic operations, as is done for foreach-loops, which require
    a generic to-list operation. However, in this case, we produce unwanted intermediate lists, and
    would have to add complicated a-posteriori deforestation optimizations.
    \<close>

end
