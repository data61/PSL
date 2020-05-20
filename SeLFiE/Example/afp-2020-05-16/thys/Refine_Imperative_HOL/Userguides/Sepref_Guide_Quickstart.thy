section \<open>Quickstart Guide\<close>
theory Sepref_Guide_Quickstart
imports "../IICF/IICF"
begin
  subsection \<open>Introduction\<close>
  text \<open>
    Sepref is an Isabelle/HOL tool to semi-automatically synthesize
    imperative code from abstract specifications.

    The synthesis works by replacing operations on abstract data 
    by operations on concrete data, leaving the structure of the program 
    (mostly) unchanged. Speref proves a refinement theorem, stating the 
    relation between the abstract and generated concrete specification. 
    The concrete specification can then be converted to executable code using 
    the Isabelle/HOL code generator.

    This quickstart guide is best appreciated in the Isabelle IDE (currently Isabelle/jedit),
    such that you can use cross-referencing and see intermediate proof states.
    \<close>

  subsubsection \<open>Prerequisites\<close>
  text \<open>
    Sepref is a tool for experienced Isabelle/HOL users. So, this 
    quickstart guide assumes some familiarity with Isabelel/HOL, and will not 
    explain standard Isabelle/HOL techniques.

    Sepref is based on Imperative/HOL (@{theory "HOL-Imperative_HOL.Imperative_HOL"}) and the Isabelle Refinement Framework (@{theory Refine_Monadic.Refine_Monadic}).
    It makes extensive use of the Separation logic formalization for Imperative/HOL (@{theory Separation_Logic_Imperative_HOL.Sep_Main}).
    
    For a thorough introduction to these tools, we refer to their documentation.
    However, we try to explain their most basic features when we use them.
    \<close>


  subsection \<open>First Example\<close>
  text \<open>As a first example, let's compute a minimum value in a non-empty list,
    wrt.~ some linear order.

    We start by specifying the problem:
    \<close>
  definition min_of_list :: "'a::linorder list \<Rightarrow> 'a nres" where
    "min_of_list l \<equiv> ASSERT (l\<noteq>[]) \<then> SPEC (\<lambda>x. \<forall>y\<in>set l. x\<le>y)"

  text \<open>This specification asserts the precondition and then specifies 
    the valid results \<open>x\<close>. The \<open>\<then>\<close> operator is a bind-operator on monads.

    Note that the Isabelle Refinement Framework works with a set/exception monad
    over the type @{typ "_ nres"}, where @{term FAIL} is the exception, 
    and @{term "RES X"} specifies a set @{term X} of possible results.
    @{term SPEC} is just the predicate-version of @{term RES} 
    (actually @{term "SPEC \<Phi>"} is a syntax abbreviation for @{term "RES (Collect \<Phi>)"}).
    
    Thus, @{term min_of_list} will fail if the list is empty, and otherwise 
    nondeterministically return one of the minimal elements.
    \<close>

  subsubsection \<open>Abstract Algorithm\<close>
  text \<open>
    Next, we develop an abstract algorithm for the problem. 
    A natural choice for a functional programmer is folding over the list,
    initializing the fold with the first element.
    \<close>
  definition min_of_list1 :: "'a::linorder list \<Rightarrow> 'a nres" 
    where "min_of_list1 l \<equiv> ASSERT (l\<noteq>[]) \<then> RETURN (fold min (tl l) (hd l))"

  text \<open>Note that @{term RETURN} returns exactly one (deterministic) result. \<close>  

  text \<open>We have to show that our implementation actually refines the specification\<close>
  lemma min_of_list1_refine: "(min_of_list1,min_of_list) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    text \<open>This lemma has to be read as follows: If the argument given to 
      @{const min_of_list1} and @{const min_of_list} are related 
      by @{const Id} (i.e.\ are identical), then the result of @{const min_of_list1} is
      a refinement of the result of @{const min_of_list}, wrt.\ relation @{const Id}.

      For an explanation, lets simplify the statement first:
      \<close>
    apply (clarsimp intro!: nres_relI)
    text \<open>The @{typ "_ nres"} type defines the refinement ordering, which is a lifted subset ordering,
      with @{term FAIL} being the greatest element. This means, that we can assume a 
      non-empty list during the refinement proof 
      (otherwise, the RHS will be @{term FAIL}, and the statement becomes trivial)

      The Isabelle Refinement Framework provides various techniques to extract verification 
      conditions from given goals, we use the standard VCG here:
      \<close>
    unfolding min_of_list_def min_of_list1_def
    apply (refine_vcg)
    text \<open>The VCG leaves us with a standard HOL goal, which is easily provable\<close>
    by (auto simp: neq_Nil_conv Min.set_eq_fold[symmetric])

  text \<open>A more concise proof of the same lemma omits the initial simplification, 
    which we only inserted to explain the refinement ordering: \<close>  
  lemma "(min_of_list1,min_of_list) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    unfolding min_of_list_def[abs_def] min_of_list1_def[abs_def]
    apply (refine_vcg)
    by (auto simp: neq_Nil_conv Min.set_eq_fold[symmetric])

  subsubsection \<open>Refined Abstract Algorithm\<close>
  text \<open>Now, we have a nice functional implementation. 
    However, we are interested in an imperative implementation.
    Ultimately, we want to implement the list by an array. 
    Thus, we replace folding over the list by indexing into the list,
    and also add an index-shift to get rid of the @{term hd} and @{term tl}.
    \<close>
  definition min_of_list2 :: "'a::linorder list \<Rightarrow> 'a nres" 
    where "min_of_list2 l \<equiv> ASSERT (l\<noteq>[]) \<then> RETURN (fold (\<lambda>i. min (l!(i+1))) [0..<length l - 1] (l!0))"

  text \<open>Proving refinement is straightforward, using the @{thm [source] fold_idx_conv} lemma.\<close>    
  lemma min_of_list2_refine: "(min_of_list2, min_of_list1)\<in>Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding min_of_list2_def[abs_def] min_of_list1_def[abs_def]
    apply refine_vcg
    apply clarsimp_all
    apply (rewrite in "_=\<hole>" fold_idx_conv)
    by (auto simp: nth_tl hd_conv_nth)

  subsubsection \<open>Imperative Algorithm\<close>  
  text \<open>The version @{const min_of_list2} already looks like the desired imperative version,
    only that we have lists instead of arrays, and would like to replace the folding over 
    @{term "[0..<length l -1]"} by a for-loop. 

    This is exactly what the Sepref-tool does. The following command synthesizes 
    an imperative version \<open>min_of_list3\<close> of the algorithm for natural numbers, 
    which uses an array instead of a list:
    \<close> 
  sepref_definition min_of_list3 is min_of_list2 :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding min_of_list2_def[abs_def] 
    by sepref

  text \<open>The generated constant represents an Imperative/HOL program, and
    is executable: \<close>  
  thm min_of_list3_def  
  export_code min_of_list3 checking SML_imp

  text \<open>Also note that the Sepref tool applied a deforestation optimization: 
    It recognizes a fold over @{term "[0..<n]"}, and implements it by the 
    tail-recursive function @{const "imp_for'"}, which uses a counter instead of 
    an intermediate list. 

    There are a couple of optimizations, which come in the form of two sets of 
    simplifier rules, which are applied one after the other:
    \<close>
  thm sepref_opt_simps
  thm sepref_opt_simps2
  text \<open>They are just named theorem collections, e.g., \<open>sepref_opt_simps add/del\<close> 
    can be used to modify them.\<close>


  text \<open>Moreover, a refinement theorem is generated, which states the correspondence between
    @{const min_of_list3} and @{const min_of_list2}: \<close>
  thm min_of_list3.refine
  text \<open>It states the relations between the parameter and the result of 
    the concrete and abstract function. The parameter is related by 
    @{term "array_assn nat_assn"}. Here, @{term "array_assn A"} relates arrays 
    with lists, such that the elements are related @{term A} --- in our case by 
    \<open>nat_assn\<close>, which relates natural numbers to themselves. 
    We also say that we @{emph \<open>implement\<close>} lists of nats by arrays of nats.
    The result is also implemented by natural numbers. 

    Moreover, the parameters may be stored on the heap, and we have to indicate whether
    the function keeps them intact or not. Here, we use the annotation \<open>_\<^sup>k\<close> (for @{emph \<open>keep\<close>}) to indicate 
    that the parameter is kept intact, and \<open>_\<^sup>d\<close> (for @{emph \<open>destroy\<close>}) to indicate that it is destroyed.
    \<close>

  subsubsection \<open>Overall Correctness Statement\<close>
  text \<open>Finally, we can use transitivity of refinement to link our implementation to
    the specification. The @{attribute FCOMP} attribute is able to compose refinement 
    theorems:\<close>
  theorem min_of_list3_correct: "(min_of_list3,min_of_list) \<in> (array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    using min_of_list3.refine[FCOMP min_of_list2_refine, FCOMP min_of_list1_refine] .

  text \<open>While the above statement is suited to re-use the algorithm within the sepref-framework,
    a more low-level correctness theorem can be stated using separation logic.
    This has the advantage that understanding the statement depends on less 
    definitional overhead:\<close>  
  lemma "l\<noteq>[] \<Longrightarrow> <array_assn nat_assn l a> min_of_list3 a <\<lambda>x. array_assn nat_assn l a * \<up>(\<forall>y\<in>set l. x\<le>y)>\<^sub>t"
    text \<open>The proof of this theorem has to unfold the several layers of the Sepref framework,
      down to the separation logic layer. An explanation of these layers is out of scope of this
      quickstart guide, we just present some proof techniques that often work. In the best case,
      the fully automatic proof will work:\<close>
    by (sep_auto 
      simp: min_of_list_def pure_def pw_le_iff refine_pw_simps
      heap: min_of_list3_correct[THEN hfrefD, of l a, THEN hn_refineD, simplified])
    
  text \<open>If the automatic method does not work, here is a more explicit proof, 
    that can be adapted for proving similar statements:\<close>  
  lemma "l\<noteq>[] \<Longrightarrow> <array_assn nat_assn l a> min_of_list3 a <\<lambda>x. array_assn nat_assn l a * \<up>(\<forall>y\<in>set l. x\<le>y)>\<^sub>t"
  proof -
    text \<open>We inlined the definition of @{const min_of_list}. 
      This will yield two proof obligations later, which we discharge as auxiliary lemmas here
      \<close>
    assume [simp]: "l\<noteq>[]"
    have [simp]: "nofail (min_of_list l)" 
      by (auto simp: min_of_list_def refine_pw_simps)
    have 1: "\<And>x. RETURN x \<le> min_of_list l \<Longrightarrow> \<forall>y\<in>set l. x\<le>y"  
      by (auto simp: min_of_list_def pw_le_iff refine_pw_simps)

    note rl = min_of_list3_correct[THEN hfrefD, of l a, THEN hn_refineD, simplified]
    text \<open>This should yield a Hoare-triple for @{term "min_of_list3 a"}, 
      which can now be used to prove the desired statement via a consequence rule\<close>
    show ?thesis
      apply (rule cons_rule[OF _ _ rl])
      text \<open>The preconditions should match, however, @{method sep_auto} is also able to discharge
        more complicated implications here. Be sure to simplify with @{thm [source] pure_def},
        if you have parameters that are not stored on the heap (in our case, we don't, but include the
        simplification anyway.)\<close> 
      apply (sep_auto simp: pure_def)  
      text \<open>The heap-parts of the postcondition should also match. 
        The pure parts require the auxiliary statements that we proved above.\<close>
      apply (sep_auto simp: pure_def dest!: 1)  
      done
    qed  
    

  subsubsection \<open>Using the Algorithm\<close> 
  text \<open>As an example, we now want to use our algorithm to compute the minimum value
    of some concrete list. In order to use an algorithm, we have to declare both, 
    it's abstract version and its implementation to the Sepref tool. 
    \<close>
  sepref_register min_of_list
    \<comment> \<open>This command registers the abstract version, and generates 
        an @{emph \<open>interface type\<close>} for it. We will explain interface types later,  
        and only note that, by default, the interface type corresponds to the operation's
        HOL type.\<close>
  declare min_of_list3_correct[sepref_fr_rules]  
    \<comment> \<open>This declares the implementation to Sepref\<close>

  text \<open>Now we can define the abstract version of our example algorithm.
    We compute the minimum value of pseudo-random lists of a given length
    \<close>  
  primrec rand_list_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
    "rand_list_aux s 0 = []"
  | "rand_list_aux s (Suc n) = (let s = (1664525 * s + 1013904223) mod 2^32 in s # rand_list_aux s n)"
  definition "rand_list \<equiv> rand_list_aux 42"

  definition "min_of_rand_list n = min_of_list (rand_list n)"

  text \<open>And use Sepref to synthesize a concrete version\<close>
  text \<open>We use a feature of Sepref to combine imperative and purely functional code,
    and leave the generation of the list purely functional, then copy it into an array,
    and invoke our algorithm. We have to declare the @{const rand_list} operation:\<close>
  sepref_register rand_list
  lemma [sepref_import_param]: "(rand_list,rand_list)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel" by auto

  text \<open>Here, we use a feature of Sepref to import parametricity theorems.
    Note that the parametricity theorem we provide here is trivial, as 
    @{const nat_rel} is identity, and @{const list_rel} as well as @{term "(\<rightarrow>)"} 
    preserve identity. 
    However, we have to specify a parametricity theorem that reflects the 
    structure of the involved types.
  \<close>

  text \<open>Finally, we can invoke Sepref\<close>
  sepref_definition min_of_rand_list1 is "min_of_rand_list" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding min_of_rand_list_def[abs_def]
    text \<open>We construct a plain list, however, the implementation of @{const min_of_list}
      expects an array. We have to insert a conversion, which is conveniently done
      with the @{method rewrite} method:
      \<close>
    apply (rewrite in "min_of_list \<hole>" array_fold_custom_of_list)
    by sepref
  text \<open>In the generated code, we see that the pure @{const rand_list} function 
    is invoked, its result is converted to an array, which is then passed to 
    @{const min_of_list3}.

    Note that @{command sepref_definition} prints the generated theorems to the 
    output on the end of the proof. Use the output panel, or hover the mouse over 
    the by-command to see this output.
  \<close>

  text \<open>The generated algorithm can be exported\<close>
  export_code min_of_rand_list1 checking SML OCaml? Haskell? Scala
  text \<open>and executed\<close>
  ML_val \<open>@{code min_of_rand_list1} (@{code nat_of_integer} 100) ()\<close>
  text \<open>Note that Imperative/HOL for ML generates a function from unit, 
    and applying this function triggers execution.\<close>

subsection \<open>Binary Search Example\<close>
text \<open>As second example, we consider a simple binary search algorithm.
  We specify the abstract problem, i.e., finding an element in a sorted list.
\<close>
definition "in_sorted_list x xs \<equiv> ASSERT (sorted xs) \<then> RETURN (x\<in>set xs)"

text \<open>And give a standard iterative implementation:\<close>
definition "in_sorted_list1_invar x xs \<equiv> \<lambda>(l,u,found).
    (l\<le>u \<and> u\<le>length xs)
  \<and> (found \<longrightarrow> x\<in>set xs)
  \<and> (\<not>found \<longrightarrow> (x\<notin>set (take l xs) \<and> x\<notin>set (drop u xs))
  )"

definition "in_sorted_list1 x xs \<equiv> do {
  let l=0;
  let u=length xs;
  (_,_,r) \<leftarrow> WHILEIT (in_sorted_list1_invar x xs)
    (\<lambda>(l,u,found). l<u \<and> \<not>found) (\<lambda>(l,u,found). do {
      let i = (l+u) div 2;
      ASSERT (i<length xs); \<comment> \<open>Added here to help synthesis to prove precondition for array indexing\<close>
      let xi = xs!i;
      if x=xi then
        RETURN (l,u,True)
      else if x<xi then
        RETURN (l,i,False)
      else  
        RETURN (i+1,u,False)
  
    }) (l,u,False);
  RETURN r  
}"

text \<open>Note that we can refine certain operations only if we can prove that their 
  preconditions are matched. For example, we can refine list indexing to array 
  indexing only if we can prove that the index is in range. This proof has to be 
  done during the synthesis procedure. However, such precondition proofs may be 
  hard, in particular for automatic methods, and we have to do them anyway when 
  proving correct our abstract implementation. Thus, it is a good idea to assert
  the preconditions in the abstract implementation. This way, they are immediately
  available during synthesis (recall, when refining an assertion, you may assume
  the asserted predicate @{thm le_ASSERTI}).
  
  An alternative is to use monadic list operations that already assert their precondition.
  The advantage is that you cannot forget to assert the precondition, the disadvantage
  is that the operation is monadic, and thus, nesting it into other operations is more cumbersome.
  In our case, the operation would be @{const mop_list_get} 
  (Look at it's simplified definition to get an impression what it does). 
\<close>
thm mop_list_get_alt

text \<open>We first prove the refinement correct\<close>
context begin
private lemma isl1_measure: "wf (measure (\<lambda>(l,u,f). u-l + (if f then 0 else 1)))" by simp

private lemma neq_nlt_is_gt:
  fixes a b :: "'a::linorder"  
  shows "a\<noteq>b \<Longrightarrow> \<not>(a<b) \<Longrightarrow> a>b" by simp

private lemma isl1_aux1:
  assumes "sorted xs"
  assumes "i<length xs"
  assumes "xs!i < x"
  shows "x\<notin>set (take i xs)"
  using assms
  by (auto simp: take_set leD sorted_nth_mono)

private lemma isl1_aux2: 
  assumes "x \<notin> set (take n xs)"
  shows "x\<notin>set (drop n xs) \<longleftrightarrow> x\<notin>set xs"
  apply (rewrite in "_ = \<hole>" append_take_drop_id[of n,symmetric])
  using assms
  by (auto simp del: append_take_drop_id)

lemma in_sorted_list1_refine: "(in_sorted_list1, in_sorted_list)\<in>Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding in_sorted_list1_def[abs_def] in_sorted_list_def[abs_def]
  apply (refine_vcg isl1_measure)
  apply (vc_solve simp: in_sorted_list1_invar_def isl1_aux1 isl1_aux2 solve: asm_rl)
  apply (auto simp: take_set set_drop_conv leD sorted_nth_mono) []
  apply (auto simp: take_set leD sorted_nth_mono dest: neq_nlt_is_gt) []
  done
end  

text \<open>First, let's synthesize an implementation where the list elements are natural numbers. 
  We will discuss later how to generalize the implementation for arbitrary types.

  For technical reasons, the Sepref tool works with uncurried functions. That is, every
  function has exactly one argument. You can use the @{term uncurry} function,
  and we also provide abbreviations @{term uncurry2} up to @{term uncurry5}.
  If a function has no parameters, @{term uncurry0} adds a unit parameter.
\<close>
sepref_definition in_sorted_list2 is "uncurry in_sorted_list1" :: "nat_assn\<^sup>k *\<^sub>a (array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding in_sorted_list1_def[abs_def]
  by sepref  

export_code in_sorted_list2 checking SML
lemmas in_sorted_list2_correct = in_sorted_list2.refine[FCOMP in_sorted_list1_refine]
  
subsection \<open>Basic Troubleshooting\<close>
text \<open>
  In this section, we will explain how to investigate problems with the Sepref tool.
  Most cases where @{method sepref} fails are due to some 
  missing operations, unsolvable preconditions, or an odd setup. 
\<close>

subsubsection \<open>Example\<close>
text \<open>We start with an example. Recall the binary search algorithm. 
  This time, we forget to assert the precondition of the indexing operation.
\<close>
definition "in_sorted_list1' x xs \<equiv> do {
  let l=0;
  let u=length xs;
  (_,_,r) \<leftarrow> WHILEIT (in_sorted_list1_invar x xs)
    (\<lambda>(l,u,found). l<u \<and> \<not>found) (\<lambda>(l,u,found). do {
      let i = (l+u) div 2;
      let xi = xs!i; \<comment> \<open>It's not trivial to show that \<open>i\<close> is in range\<close>
      if x=xi then
        RETURN (l,u,True)
      else if x<xi then
        RETURN (l,i,False)
      else  
        RETURN (i+1,u,False)
  
    }) (l,u,False);
  RETURN r  
}"

text \<open>We try to synthesize the implementation. Note that @{command sepref_thm} behaves like 
  @{command sepref_definition}, but actually defines no constant. It only generates a refinement theorem.\<close>
sepref_thm in_sorted_list2 is "uncurry in_sorted_list1'" :: "nat_assn\<^sup>k *\<^sub>a (array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding in_sorted_list1'_def[abs_def]
  (* apply sepref  Fails *)
  \<comment> \<open>If @{method sepref} fails, you can use @{method sepref_dbg_keep} to get some more information.\<close>
  apply sepref_dbg_keep
  \<comment> \<open>This prints a trace of the different phases of sepref, and stops when the first phase fails.
    It then returns the internal proof state of the tool, which can be inspected further.
    
    Here, the translation phase fails. The translation phase translates the control structures and operations of
    the abstract program to their concrete counterparts. To inspect the actual problem, we let translation run 
    until the operation where it fails:\<close>
  supply [[goals_limit=1]] \<comment> \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
  apply sepref_dbg_trans_keep
  \<comment> \<open>Things get stuck at a goal with predicate @{const hn_refine}. This is the internal refinement predicate,
    @{term "hn_refine \<Gamma> c \<Gamma>' R a"} means, that, for operands whose refinement is described by @{term \<Gamma>},
    the concrete program @{term c} refines the abstract program @{term a}, such that, afterwards, the operands
    are described by @{term \<Gamma>'}, and the results are refined by @{term R}.
    
    Inspecting the first subgoal reveals that we got stuck on refining the abstract operation
    @{term "RETURN $ (op_list_get $ b $ xf)"}. Note that the @{term "($)"} is just a constant for function 
    application, which is used to tame Isabelle's higher-order unification algorithms. You may use 
    \<open>unfolding APP_def\<close>, or even \<open>simp\<close> to get a clearer picture of the failed goal.

    If a translation step fails, it may be helpful to execute as much of the translation step as possible:\<close>
  apply sepref_dbg_trans_step_keep
  \<comment> \<open>The translation step gets stuck at proving @{term "pre_list_get (b, xf)"}, which is the 
    precondition for list indexing.\<close>
  apply (sepref_dbg_side_keep) \<comment> \<open>If you think the side-condition should be provable, this command 
    returns the left-over subgoals after some preprocessing and applying auto\<close>
  (* apply sepref_dbg_side_unfold (* Preprocessing only*) *)
  oops  

subsubsection \<open>Internals of Sepref\<close>
text \<open>
  Internally, @{method sepref} consists of multiple phases that are executed
  one after the other. Each phase comes with its own debugging method, which 
  only executes that phase. We illustrate this by repeating the refinement of
  @{const "min_of_list2"}. This time, we use @{command sepref_thm}, which only
  generates a refinement theorem, but defines no constants:
\<close>

sepref_thm min_of_list3' is min_of_list2 :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  \<comment> \<open>The \<open>sepref_thm\<close> or \<open>sepref_definition\<close> command assembles a schematic 
    goal statement.\<close>
  unfolding min_of_list2_def[abs_def] 
  \<comment> \<open>The preprocessing phase converts the goal into 
    the @{const "hn_refine"}-form. Moreover, it adds interface type 
    annotations for the parameters. (for now, the interface type is just the HOL 
    type of the parameter, in our case, @{typ "nat list"})\<close>
  apply sepref_dbg_preproc
  \<comment> \<open>The next phase applies a consequence rule for the postcondition and
    result. This is mainly for technical reasons.\<close>
  apply sepref_dbg_cons_init
  \<comment> \<open>The next phase tries to identify the abstract operations, and inserts
    tag-constants for function application and abstraction. These tags are for 
    technical reasons, working around Isabelle/HOL's unifier idiosyncrasies.

    Operation identification assigns a single constant to each abstract operation,
    which is required for technical reasons. Note that there are terms in HOL, 
    which qualify as a single operation, but consists of multiple constants, 
    for example, @{term "{x}"}, which is just syntactic sugar for 
    @{term [source] "insert x {}"}. In our case, the operation identification 
    phase rewrites the assertion operations followed by a bind to a single 
    operation @{const op_ASSERT_bind}, and renames some operations to more 
    canonical names.\<close>
  apply sepref_dbg_id
  \<comment> \<open>Now that it is clear which operations to execute, we have to specify an 
    execution order. Note that HOL has no notion of execution at all. However,
    if we want to translate to operations that depend on a heap, we need a notion 
    of execution order. We use the \<open>nres\<close>-monad's bind operation as sequencing operator,
    and flatten all nested operations, using left-to-right evaluation order.\<close>
  apply sepref_dbg_monadify
  \<comment> \<open>The next step just prepares the optimization phase,
    which will be executed on the translated program. It just applies the rule   
    @{thm TRANS_init}.\<close>
  apply sepref_dbg_opt_init
  \<comment> \<open>The translation phase does the main job of translating the abstract program
    to the concrete one. It has rules how to translate abstract operations to
    concrete ones. For technical reasons, it differentiates between 
    operations, which have only first-order arguments (e.g., @{const length})   
    and combinators, which have also higher-order arguments (e.g., @{const fold}).

    The basic idea of translation is to repeatedly apply the translation rule for the
    topmost combinator/operator, and thus recursively translate the whole program.
    The rules may produce various types of side-conditions, which are resolved by the tool.\<close>
  apply sepref_dbg_trans
  \<comment> \<open>The next phase applies some simplification rules to optimize the translated program.
    It essentially simplifies first with the rules @{thm [source] sepref_opt_simps}, and
    then with @{thm [source] sepref_opt_simps2}.\<close>
  apply sepref_dbg_opt
  \<comment> \<open>The next two phases resolve the consequence rules introduced by the \<open>cons_init\<close> phase.\<close>
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  \<comment> \<open>The translation phase and the consequence rule solvers may postpone some
    side conditions on yet-unknown refinement assertions. These are solved in the 
    last phase.\<close>
  apply sepref_dbg_constraints
  done

text \<open>In the next sections, we will explain, by example, how to troubleshoot 
  the various phases of the tool. We will focus on the phases that are most 
  likely to fail.\<close>

subsubsection \<open>Initialization\<close>
text \<open>A common mistake is to forget the keep/destroy markers for the
  refinement assertion, or specify a refinement assertion with a non-matching
  type. This results in a type-error on the command\<close>

(* Forgot keep/destroy *)
(*sepref_thm min_of_list3' is min_of_list2 :: "(array_assn nat_assn) \<rightarrow>\<^sub>a nat_assn"*)

(* Wrong type (@{term hs.assn} is for sets (hashset), not for lists) *)
(*sepref_thm min_of_list3' is min_of_list2 :: "(hs.assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"*)

(* Operand must be function to nres *)
(*sepref_thm test is "\<lambda>x. 2+x" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"*)
(* Correct: *)
sepref_thm test_add_2 is "\<lambda>x. RETURN (2+x)" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  by sepref

(* Type correct, but nonsense: Yields a proof failed message, as the tool
  expects a refinement assertion *)
(*sepref_thm min_of_list3' is min_of_list2 :: "undefined"*)

subsubsection \<open>Translation Phase\<close>
text \<open>In most cases, the translation phase will fail. Let's try the following refinement:\<close>
sepref_thm test is "\<lambda>l. RETURN (l!1 + 2)" :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  text \<open>The @{method sepref} method will just fail. To investigate further, we use
    @{method sepref_dbg_keep}, which executes the phases until the first one fails.
    It returns with the proof state before the failed phase, and, moreover, outputs
    a trace of the phases, such that you can easily see which phase failed.
    \<close>
  apply sepref_dbg_keep
  \<comment> \<open>In the trace, we see that the translation phase failed. We are presented
    the tool's internal goal state just before translation. If a phase fails,
    the usual procedure is to start the phase in debug mode, and see how far it gets.
    The debug mode of the translation phase stops at the first operation or combinator
    it cannot translate. Note, it is a good idea to limit the visible goals, as printing 
    goals in Isabelle can be very, very slow :(\<close>
  supply [[goals_limit = 1]]
  apply sepref_dbg_trans_keep
  \<comment> \<open>Here, we see that translation gets stuck at \<open>op_list_get\<close>. This may have 
    two reasons: Either there is no rule for this operation, or a side condition 
    cannot be resolved. We apply a single translation step in debug mode, i.e., 
    the translation step is applied as far as possible, leaving unsolved side conditions:\<close>
  apply sepref_dbg_trans_step_keep
  \<comment> \<open>This method reports that the "Apply rule" phase produced a wrong number of subgoals.
    This phase is expected to solve the goal, but left some unsolved side condition, which we
    are presented in the goal state. We can either guess  
    what @{term pre_list_get} means and why it cannot be solved, or try to partially
    solve the side condition:\<close>
  apply sepref_dbg_side_keep
  \<comment> \<open>From the remaining subgoal, one can guess that there might be a problem 
    with too short lists, where index \<open>1\<close> does not exist.\<close>
  (** You may use the following methods instead of sepref_dbg_side_keep to have 
    more control on how far the side-condition is solved. By default, you will see
    the result of auto after unfolding the internal tags.
  apply sepref_dbg_side_unfold apply simp
  *)
  oops
text \<open>Inserting an assertion into the abstract program solves the problem:\<close>
sepref_thm test is "\<lambda>l. ASSERT (length l > 1) \<then> RETURN (l!1 + 2)" :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  by sepref

text \<open>Here is an example for an unimplemented operation:\<close>
sepref_thm test is "\<lambda>l. RETURN (Min (set l))" :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  supply [[goals_limit = 1]]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  \<comment> \<open>Translation stops at the \<open>set\<close> operation\<close>
  apply sepref_dbg_trans_step_keep
  \<comment> \<open>This tactic reports that the "Apply rule" phase failed, which means that 
    there is no applicable rule for the \<open>set\<close> operation on arrays.\<close>
  oops  
  
subsection \<open>The Isabelle Imperative Collection Framework (IICF)\<close>
text \<open>
  The IICF provides a library of imperative data structures, and some 
  management infrastructure. The main idea is to have interfaces and implementations.

  An interface specifies an abstract data type (e.g., @{typ "_ list"}) and some operations with preconditions 
  on it (e.g., @{term "(@)"} or @{term "nth"} with in-range precondition). 

  An implementation of an interface provides a refinement assertion from the abstract data type to
  some concrete data type, as well as implementations for (a subset of) the interface's operations.
  The implementation may add some more implementation specific preconditions.
  
  The default interfaces of the IICF are in the folder \<open>IICF/Intf\<close>, and the standard implementations are in
  \<open>IICF/Impl\<close>.
\<close>

subsubsection \<open>Map Example\<close>
text \<open>Let's implement a function that maps a finite set to an initial 
  segment of the natural numbers
\<close>
definition "nat_seg_map s \<equiv> 
  ASSERT (finite s) \<then> SPEC (\<lambda>m. dom m = s \<and> ran m = {0..<card s})"

text \<open>We implement the function by iterating over the set, and building the map\<close>
definition "nat_seg_map1 s \<equiv> do {
  ASSERT (finite s);
  (m,_) \<leftarrow> FOREACHi (\<lambda>it (m,i). dom m = s-it \<and> ran m = {0..<i} \<and> i=card (s - it)) 
    s (\<lambda>x (m,i). RETURN (m(x\<mapsto>i),i+1)) (Map.empty,0);
  RETURN m
}"

lemma nat_seg_map1_refine: "(nat_seg_map1, nat_seg_map) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro fun_relI)
  unfolding nat_seg_map1_def[abs_def] nat_seg_map_def[abs_def]
  apply (refine_vcg)
  apply (vc_solve simp: it_step_insert_iff solve: asm_rl dest: domD)
  done
  
text \<open>We use hashsets @{term "hs.assn"} and hashmaps (@{term "hm.assn"}). \<close>
sepref_definition nat_seg_map2 is nat_seg_map1 :: "(hs.assn id_assn)\<^sup>k \<rightarrow>\<^sub>a hm.assn id_assn nat_assn"
  unfolding nat_seg_map1_def[abs_def]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  \<comment> \<open>We got stuck at \<open>op_map_empty\<close>. This is because Sepref is very conservative 
    when it comes to guessing implementations. Actually, no constructor operation 
    will be assigned a default operation, with some obvious exceptions for numbers and Booleans.\<close>
  oops

text \<open>
  Assignment of implementations to constructor operations is done by rewriting them to
  synonyms which are bound to a specific implementation. For hashmaps, we have 
  @{const op_hm_empty}, and the rules @{thm [source] hm.fold_custom_empty}.
\<close>
sepref_definition nat_seg_map2 is nat_seg_map1 :: "(hs.assn id_assn)\<^sup>k \<rightarrow>\<^sub>a hm.assn id_assn nat_assn"
  unfolding nat_seg_map1_def[abs_def]
  \<comment> \<open>We can use the @{method rewrite} method for position-precise rewriting:\<close>
  apply (rewrite in "FOREACHi _ _ _ \<hole>" "hm.fold_custom_empty")
  by sepref

export_code nat_seg_map2 checking SML

lemmas nat_seg_map2_correct = nat_seg_map2.refine[FCOMP nat_seg_map1_refine]

subsection \<open>Specification of Preconditions\<close> (*Move up! *)
text \<open>In this example, we will discuss how to specify precondition of operations, 
  which are required for refinement to work.
  Consider the following function, which increments all members of a list by one:
\<close>
definition "incr_list l \<equiv> map ((+) 1) l"
text \<open>We might want to implement it as follows\<close>
definition "incr_list1 l \<equiv> fold (\<lambda>i l. l[i:=1 + l!i]) [0..<length l] l"
  
lemma incr_list1_refine: "(incr_list1, incr_list)\<in>Id \<rightarrow> Id"
proof (intro fun_relI; simp)
  fix l :: "'a list"
  { fix n m
    assume "n\<le>m" and "length l = m"
    hence "fold (\<lambda>i l. l[i:=1+l!i]) [n..<m] l = take n l @ map (((+))1) (drop n l)"
      apply (induction  arbitrary: l rule: inc_induct)
      apply simp
      apply (clarsimp simp: upt_conv_Cons take_Suc_conv_app_nth)
      apply (auto simp add: list_eq_iff_nth_eq nth_Cons split: nat.split)
      done
  }
  from this[of 0 "length l"] show "incr_list1 l = incr_list l"
    unfolding incr_list_def incr_list1_def
    by simp
qed

text \<open>Trying to refine this reveals a problem:\<close>
sepref_thm incr_list2 is "RETURN o incr_list1" :: "(array_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding incr_list1_def[abs_def]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_keep
  \<comment> \<open>We get stuck at the precondition of @{const op_list_get}.
    Indeed, we cannot prove the generated precondition, as the translation process
    dropped any information from which we could conclude that the index is in range.\<close>
  oops

  text \<open>
    Of course, the fold loop has the invariant that the length of the list does not change,
    and thus, indexing is in range. We only cannot prove it during the automatic synthesis.

    Here, the only solution is to do a manual refinement into the nres-monad, 
    and adding an assertion that indexing is always in range.

    We use the @{const nfoldli} combinator, which generalizes @{const fold} in two directions:
    \<^enum> The function is inside the nres monad
    \<^enum> There is a continuation condition. If this is not satisfied, the fold returns immediately, 
      dropping the rest of the list.
    \<close>

definition "incr_list2 l \<equiv> nfoldli 
  [0..<length l] 
  (\<lambda>_. True)  
  (\<lambda>i l. ASSERT (i<length l) \<then> RETURN (l[i:=1+l!i]))
  l"

text \<open>
  Note: Often, it is simpler to prove refinement of the abstract specification, rather
  than proving refinement to some intermediate specification that may have already done
  refinements "in the wrong direction". In our case, proving refinement of @{const incr_list1}
  would require to generalize the statement to keep track of the list-length invariant,
  while proving refinement of @{const incr_list} directly is as easy as proving the original 
  refinement for @{const incr_list1}.
\<close>
lemma incr_list2_refine: "(incr_list2,RETURN o incr_list) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof (intro nres_relI fun_relI; simp)  
  fix l :: "'a list"
  show "incr_list2 l \<le> RETURN (incr_list l)"
    unfolding incr_list2_def incr_list_def
    \<comment> \<open>@{const nfoldli} comes with an invariant proof rule. In order to use it, we have to specify
      the invariant manually:\<close>
    apply (refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 s. s = map (((+))1) (take (length l1) l) @ drop (length l1) l"])
    apply (vc_solve 
      simp: upt_eq_append_conv upt_eq_Cons_conv
      simp: nth_append list_update_append upd_conv_take_nth_drop take_Suc_conv_app_nth
      solve: asm_rl
    )
    done
qed

sepref_definition incr_list3 is "incr_list2" :: "(array_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding incr_list2_def[abs_def]
  by sepref

lemmas incr_list3_correct = incr_list3.refine[FCOMP incr_list2_refine]

subsection \<open>Linearity and Copying\<close>
text \<open>Consider the following implementation of an operation to swap to list 
  indexes. While it is perfectly valid in a functional setting, an imperative 
  implementation has a problem here: Once the update a index \<open>i\<close> is done,
  the old value cannot be read from index \<open>i\<close> any more. We try to implement the
  list with an array:\<close>
sepref_thm swap_nonlinear is "uncurry2 (\<lambda>l i j. do {
  ASSERT (i<length l \<and> j<length l);
  RETURN (l[i:=l!j, j:=l!i])
})" :: "(array_assn id_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a array_assn id_assn"
  supply [[goals_limit = 1]]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep \<comment> \<open>(1) We get stuck at an @{const op_list_get} operation\<close>
  apply sepref_dbg_trans_step_keep \<comment> \<open>(2) Further inspection reveals that the "recover pure" 
    phase fails, and we are left with a subgoal of the form 
    @{term "CONSTRAINT is_pure (array_assn id_assn)"}. Constraint side conditions are 
    deferrable side conditions: They are produced as side-conditions, and if they cannot 
    be solved immediately, they are deferred and processed later, latest at the end of the synthesis.
    However, definitely unsolvable constraints are not deferred, but halt the translation phase immediately,
    and this is what happened here: At (1) we can see that the refinement for the array we want to access is 
    @{term "hn_invalid (array_assn id_assn)"}. This means, the data structure was destroyed by some preceding 
    operation. The @{const hn_invalid} only keeps a record of this fact. When translating an operation that uses
    an invalidated parameter, the tool tries to restore the invalidated parameter: This only works if the data 
    structure was purely functional, i.e., not stored on the heap. This is where the @{term is_pure} constraint
    comes from. However, arrays are always stored on the heap, so this constraint is definitely unsolvable,
    and thus immediately rejected instead of being deferred. 

    Note: There are scenarios where a constraint gets deferred @{emph \<open>before\<close>} it becomes definitely unsolvable.
      In these cases, you only see the problem after the translation phase, and it may be somewhat tricky to figure
      out the reason.\<close> (* TODO: Check for unsolvable constraints after each translation step, and refuse refinements that render
      any constraints unsolvable. Make this debuggable, e.g. by injecting those constraints as additional side 
      conditions! *)
  oops

text \<open>The fix for our swap function is quite obvious. Using a temporary storage 
  for the intermediate value, we write:\<close>
sepref_thm swap_with_tmp is "uncurry2 (\<lambda>l i j. do {
  ASSERT (i<length l \<and> j<length l);
  let tmp = l!i;
  RETURN (l[i:=l!j, j:=tmp])
})" :: "(array_assn id_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a array_assn id_assn"
  by sepref

text \<open>Note that also the argument must be marked as destroyed \<open>()\<^sup>d\<close>. Otherwise, we get a similar error as above,
  but in a different phase: \<close>
sepref_thm swap_with_tmp is "uncurry2 (\<lambda>l i j. do {
  ASSERT (i<length l \<and> j<length l);
  let tmp = l!i;
  RETURN (l[i:=l!j, j:=tmp])
})" :: "(array_assn id_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a array_assn id_assn"
  apply sepref_dbg_keep \<comment> \<open>We get stuck at a frame, which would require restoring an invalidated array\<close>
  apply sepref_dbg_cons_solve_keep \<comment> \<open>Which would only work if arrays were pure\<close>
  oops
  
text \<open>If copying is really required, you have to insert it manually. 
  Reconsider the example @{const incr_list} from above. This time,
  we want to preserve the original data (note the \<open>()\<^sup>k\<close> annotation):
\<close>
sepref_thm incr_list3_preserve is "incr_list2" :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding incr_list2_def[abs_def]
  \<comment> \<open>We explicitly insert a copy-operation on the list, before it is passed to the fold operation\<close>
  apply (rewrite in "nfoldli _ _ _ \<hole>" op_list_copy_def[symmetric])
  by sepref

subsection \<open>Nesting of Data Structures\<close>
text \<open>
  Sepref and the IICF support nesting of data structures with some limitations:
    \<^item> Only the container or its elements can be visible at the same time. 
      For example, if you have a product of two arrays, you can either see the
      two arrays, or the product. An operation like \<open>snd\<close> would have to destroy 
      the product, loosing the first component. Inside a case distinction, you
      cannot access the compound object.
    
      These limitations are somewhat relaxed for pure data types, which can always 
      be restored.
    \<^item> Most IICF data structures only support pure component types. 
      Exceptions are HOL-lists, and the list-based set and multiset implementations
      \<open>List_MsetO\<close> and \<open>List_SetO\<close> (Here, the \<open>O\<close> stands for \<open>own\<close>, which means 
      that the data-structure owns its elements.).

\<close>

text \<open>Works fine:\<close>
sepref_thm product_ex1 is "uncurry0 (do {
    let p = (op_array_replicate 5 True, op_array_replicate 2 False);
    case p of (a1,a2) \<Rightarrow> RETURN (a1!2)
  })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref


text \<open>Fails: We cannot access compound type inside case distinction\<close>
sepref_thm product_ex2 is "uncurry0 (do {
    let p = (op_array_replicate 5 True, op_array_replicate 2 False);
    case p of (a1,a2) \<Rightarrow> RETURN (snd p!1)
  })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  oops

text \<open>Works fine, as components of product are pure, such that product can be restored inside case.\<close>
sepref_thm product_ex2 is "uncurry0 (do {
    let p = (op_list_replicate 5 True, op_list_replicate 2 False);
    case p of (a1,a2) \<Rightarrow> RETURN (snd p!1)
  })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref_dbg_keep

text \<open>Trying to create a list of arrays, first attempt: \<close>
sepref_thm set_of_arrays_ex is "uncurry0 (RETURN (op_list_append [] op_array_empty))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn (array_assn nat_assn)"
  unfolding "arl.fold_custom_empty"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  supply [[goals_limit = 1, unify_trace_failure]]
  (*apply (rule arl_append_hnr[to_hnr])*)
  \<comment> \<open>Many IICF data structures, in particular the array based ones, requires the element types
    to be of @{class default}. If this is not the case, Sepref will simply find no refinement for
    the operations. Be aware that type-class related mistakes are hard to debug in Isabelle/HOL,
    above we sketched how to apply the refinement rule that is supposed to match with unifier 
    tracing switched on. The @{attribute to_hnr} attribute is required to convert the rule from 
    the relational form to the internal @{const hn_refine} form. Note that some rules are already 
    in @{const hn_refine} form, and need not be converted, e.g., @{thm hn_Pair}.\<close>
  oops

text \<open>So lets choose a circular singly linked list (csll), which does not require its elements to be of default type class\<close>
sepref_thm set_of_arrays_ex is "uncurry0 (RETURN (op_list_append [] op_array_empty))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a csll.assn (array_assn nat_assn)"
  unfolding "csll.fold_custom_empty"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  \<comment> \<open>We end up with an unprovable purity-constraint: As many IICF types, csll 
    only supports pure member types. We expect this restriction to be lifted in 
    some future version.\<close>
  oops

text \<open>Finally, there are a few data structures that already support nested element types, for example, functional lists:\<close>
sepref_thm set_of_arrays_ex is "uncurry0 (RETURN (op_list_append [] op_array_empty))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (array_assn nat_assn)"
  unfolding "HOL_list.fold_custom_empty"
  by sepref


subsection \<open>Fixed-Size Data Structures\<close>
text \<open>For many algorithms, the required size of a data structure is already known,
  such that it is not necessary to use data structures with dynamic resizing.

  The Sepref-tool supports such data structures, however, with some limitations.
\<close>

subsubsection \<open>Running Example\<close>
text \<open>
  Assume we want to read a sequence of natural numbers in the range @{term "{0..<N}"},
  and drop duplicate numbers. The following abstract algorithm may work:
\<close>

definition "remdup l \<equiv> do {
  (s,r) \<leftarrow> nfoldli l (\<lambda>_. True) 
    (\<lambda>x (s,r). do {
      ASSERT (distinct r \<and> set r \<subseteq> set l \<and> s = set r); \<comment> \<open>Will be required to prove that list does not grow too long\<close>
      if x\<in>s then RETURN (s,r) else RETURN (insert x s, r@[x])
    }) 
    ({},[]);
  RETURN r
}"

text \<open>We want to use \<open>remdup\<close> in our abstract code, so we have to register it.\<close>
sepref_register remdup

text \<open>The straightforward version with dynamic data-structures is: \<close>
sepref_definition remdup1 is "remdup" :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_assn"
  unfolding remdup_def[abs_def]
  \<comment> \<open>Lets use a bit-vector for the set\<close>
  apply (rewrite in "nfoldli _ _ _ \<hole>" ias.fold_custom_empty)
  \<comment> \<open>And an array-list for the list\<close>
  apply (rewrite in "nfoldli _ _ _ \<hole>" arl.fold_custom_empty)
  by sepref

subsubsection \<open>Initialization of Dynamic Data Structures\<close>
text \<open>Now let's fix an upper bound for the numbers in the list.
  Initializations and statically sized data structures must always be fixed variables,
  they cannot be computed inside the refined program. 

  TODO: Lift this restriction at least for initialization hints that do not occur 
    in the refinement assertions.
\<close>
context fixes N :: nat begin

sepref_definition remdup1_initsz is "remdup" :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_assn"
  unfolding remdup_def[abs_def]
  \<comment> \<open>Many of the dynamic array-based data structures in the IICF can be 
    pre-initialized to a certain size. THis initialization is only a hint, 
    and has no abstract consequences. The list data structure will still be 
    resized if it grows larger than the initialization size.\<close>
  apply (rewrite in "nfoldli _ _ _ \<hole>" ias_sz.fold_custom_empty[of N])
  apply (rewrite in "nfoldli _ _ _ \<hole>" arl_sz.fold_custom_empty[of N])
  by sepref

end

text \<open>To get a usable function, we may add the fixed \<open>N\<close> as a parameter, effectively converting
  the initialization hint to a parameter, which, however, has no abstract meaning\<close>

definition "remdup_initsz (N::nat) \<equiv> remdup"
lemma remdup_init_hnr: 
  "(uncurry remdup1_initsz, uncurry remdup_initsz) \<in> nat_assn\<^sup>k *\<^sub>a (list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_assn"
  using remdup1_initsz.refine unfolding remdup_initsz_def[abs_def]
  unfolding hfref_def hn_refine_def
  by (auto simp: pure_def)


subsubsection \<open>Static Data Structures\<close>

text \<open>We use a locale to hide local declarations. Note: This locale will never be interpreted,
  otherwise all the local setup, that does not make sense outside the locale, would become visible.
  TODO: This is probably some abuse of locales to emulate complex private setup, 
      including declaration of constants and lemmas.
\<close>
locale my_remdup_impl_loc = 
  fixes N :: nat 
  assumes "N>0" \<comment> \<open>This assumption is not necessary, but used to illustrate the 
    general case, where the locale may have such assumptions\<close>
begin
  text \<open>For locale hierarchies, the following seems not to be available directly in Isabelle,
    however, it is useful when transferring stuff between the global theory and the locale\<close>
  lemma my_remdup_impl_loc_this: "my_remdup_impl_loc N" by unfold_locales

  text \<open>
    Note that this will often require to use \<open>N\<close> as a usual constant, which 
    is refined. For pure refinements, we can use the @{attribute sepref_import_param}
    attribute, which will convert a parametricity theorem to a rule for Sepref:
    \<close>  
  sepref_register N
  lemma N_hnr[sepref_import_param]: "(N,N)\<in>nat_rel" by simp
  thm N_hnr
  text \<open>Alternatively, we could directly prove the following rule, which, however, is 
    more cumbersome: \<close>
  lemma N_hnr': "(uncurry0 (return N), uncurry0 (RETURN N))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    by sepref_to_hoare sep_auto

  text \<open>Next, we use an array-list with a fixed maximum capacity. 
    Note that the capacity is part of the refinement assertion now.
  \<close>
  sepref_definition remdup1_fixed is "remdup" :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a marl_assn N nat_assn"
    unfolding remdup_def[abs_def]
    apply (rewrite in "nfoldli _ _ _ \<hole>" ias_sz.fold_custom_empty[of N])
    apply (rewrite in "nfoldli _ _ _ \<hole>" marl_fold_custom_empty_sz[of N])
    supply [[goals_limit = 1]]
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    apply sepref_dbg_trans_step_keep
    \<comment> \<open>In order to append to the array list, we have to show that the size is not yet exceeded.
      This may require to add some assertions on the abstract level. We already have added
      some assertions in the definition of @{const remdup}.\<close>
    oops
  
  text \<open>Moreover, we add a precondition on the list\<close>
  sepref_definition remdup1_fixed is "remdup" :: "[\<lambda>l. set l \<subseteq> {0..<N}]\<^sub>a (list_assn nat_assn)\<^sup>k \<rightarrow> marl_assn N nat_assn"
    unfolding remdup_def[abs_def]
    apply (rewrite in "nfoldli _ _ _ \<hole>" ias_sz.fold_custom_empty[of N])
    apply (rewrite in "nfoldli _ _ _ \<hole>" marl_fold_custom_empty_sz[of N])
    supply [[goals_limit = 1]]
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    apply sepref_dbg_trans_step_keep
    apply sepref_dbg_side_keep
    \<comment> \<open>We can start from this subgoal to find missing lemmas\<close>
    oops

  text \<open>We can prove the remaining subgoal, e.g., by @{method auto} with the following
    lemma declared as introduction rule:\<close>  
  lemma aux1[intro]: "\<lbrakk> set l \<subset> {0..<N}; distinct l \<rbrakk> \<Longrightarrow> length l < N"  
    apply (simp add: distinct_card[symmetric])
    apply (drule psubset_card_mono[rotated])
    apply auto
    done

  text \<open>We use some standard boilerplate to define the constant globally, although
    being inside the locale. This is required for code-generation.\<close>  
  sepref_thm remdup1_fixed is "remdup" :: "[\<lambda>l. set l \<subseteq> {0..<N}]\<^sub>a (list_assn nat_assn)\<^sup>k \<rightarrow> marl_assn N nat_assn"
    unfolding remdup_def[abs_def]
    apply (rewrite in "nfoldli _ _ _ \<hole>" ias_sz.fold_custom_empty[of N])
    apply (rewrite in "nfoldli _ _ _ \<hole>" marl_fold_custom_empty_sz[of N])
    by sepref
    
  concrete_definition (in -) remdup1_fixed uses "my_remdup_impl_loc.remdup1_fixed.refine_raw" is "(?f,_)\<in>_"
  prepare_code_thms (in -) remdup1_fixed_def
  lemmas remdup1_fixed_refine[sepref_fr_rules] = remdup1_fixed.refine[OF my_remdup_impl_loc_this] 
  text \<open>The @{command concrete_definition} command defines the constant globally, without any locale assumptions. For this,
    it extracts the definition from the theorem, according to the specified pattern. Note, you have to
    include the uncurrying into the pattern, e.g., \<open>(uncurry ?f,_)\<in>_\<close>.

    The @{command prepare_code_thms} command sets up code equations for recursion combinators that may have been synthesized. 
    This is required as the code generator works with equation systems, while the heap-monad works with 
    fixed-point combinators.
    
    Finally, the third lemma command imports the refinement lemma back into the locale, and registers it
    as refinement rule for Sepref.
    \<close>

  text \<open>Now, we can refine @{const remdup} to @{term "remdup1_fixed N"} inside the 
    locale. The latter is a global constant with an unconditional definition, thus code
    can be generated for it.\<close>  

  text \<open>Inside the locale, we can do some more refinements: \<close>  
  definition "test_remdup \<equiv> do {l \<leftarrow> remdup [0..<N]; RETURN (length l) }"
  text \<open>Note that the abstract @{const test_remdup} is just an abbreviation for 
    @{term "my_remdup_impl_loc.test_remdup N"}.
    Whenever we want Sepref to treat a compound term like a constant, we have to wrap the term into
    a @{const PR_CONST} tag. While @{command sepref_register} does this automatically, 
    the \<open>PR_CONST\<close> has to occur in the refinement rule.\<close>
  sepref_register "test_remdup"
  sepref_thm test_remdup1 is 
    "uncurry0 (PR_CONST test_remdup)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding test_remdup_def PR_CONST_def
    by sepref
  concrete_definition (in -) test_remdup1 uses my_remdup_impl_loc.test_remdup1.refine_raw is "(uncurry0 ?f,_)\<in>_"
  prepare_code_thms (in -) test_remdup1_def
  lemmas test_remdup1_refine[sepref_fr_rules] = test_remdup1.refine[of N]

end    

text \<open>Outside the locale, a refinement of @{term my_remdup_impl_loc.test_remdup} also makes sense,
  however, with an extra argument @{term N}.\<close>

thm test_remdup1.refine
lemma test_remdup1_refine_aux: "(test_remdup1, my_remdup_impl_loc.test_remdup) \<in> [my_remdup_impl_loc]\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn"
  using test_remdup1.refine
  unfolding hfref_def hn_refine_def
  by (auto simp: pure_def)

text \<open>We can also write a more direct precondition, as long as it implies the locale\<close>
lemma test_remdup1_refine: "(test_remdup1, my_remdup_impl_loc.test_remdup) \<in> [\<lambda>N. N>0]\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn"
  apply (rule hfref_cons[OF test_remdup1_refine_aux _ entt_refl entt_refl entt_refl])
  by unfold_locales
  
export_code test_remdup1 checking SML

text \<open>We can also register the abstract constant and the refinement, to use it in further refinements\<close>
sepref_register my_remdup_impl_loc.test_remdup
lemmas [sepref_fr_rules] = test_remdup1_refine


subsubsection \<open>Static Data Structures with Custom Element Relations\<close>

text \<open>In the previous section, we have presented a refinement using an array-list
  without dynamic resizing. However, the argument that we actually could append 
  to this array was quite complicated.

  Another possibility is to use bounded refinement relations, i.e., 
  a refinement relation intersected with a condition for the abstract object.
  In our case, @{term "nbn_assn N"} relates natural numbers less than \<open>N\<close> to themselves.

  We will repeat the above development, using the bounded relation approach:
\<close>

definition "bremdup l \<equiv> do {
  (s,r) \<leftarrow> nfoldli l (\<lambda>_. True) 
    (\<lambda>x (s,r). do {
      ASSERT (distinct r \<and> s = set r); \<comment> \<open>Less assertions than last time\<close>
      if x\<in>s then RETURN (s,r) else RETURN (insert x s, r@[x])
    }) 
    ({},[]);
  RETURN r
}"
sepref_register bremdup

locale my_bremdup_impl_loc = 
  fixes N :: nat 
  assumes "N>0" \<comment> \<open>This assumption is not necessary, but used to illustrate the 
    general case, where the locale may have such assumptions\<close>
begin
  lemma my_bremdup_impl_loc_this: "my_bremdup_impl_loc N" by unfold_locales

  sepref_register N
  lemma N_hnr[sepref_import_param]: "(N,N)\<in>nat_rel" by simp

  text \<open>Conceptually, what we insert in our list are elements, and
    these are less than \<open>N\<close>.\<close>
  abbreviation "elem_assn \<equiv> nbn_assn N"

  lemma aux1[intro]: "\<lbrakk> set l \<subset> {0..<N}; distinct l \<rbrakk> \<Longrightarrow> length l < N"  
    apply (simp add: distinct_card[symmetric])
    apply (drule psubset_card_mono[rotated])
    apply auto
    done

  sepref_thm remdup1_fixed is "remdup" :: "[\<lambda>l. set l \<subseteq> {0..<N}]\<^sub>a (list_assn elem_assn)\<^sup>k \<rightarrow> marl_assn N elem_assn"
    unfolding remdup_def[abs_def]
    apply (rewrite in "nfoldli _ _ _ \<hole>" ias_sz.fold_custom_empty[of N])
    apply (rewrite in "nfoldli _ _ _ \<hole>" marl_fold_custom_empty_sz[of N])
    by sepref
    
  concrete_definition (in -) bremdup1_fixed uses "my_bremdup_impl_loc.remdup1_fixed.refine_raw" is "(?f,_)\<in>_"
  prepare_code_thms (in -) bremdup1_fixed_def
  lemmas remdup1_fixed_refine[sepref_fr_rules] = bremdup1_fixed.refine[OF my_bremdup_impl_loc_this] 

  definition "test_remdup \<equiv> do {l \<leftarrow> remdup [0..<N]; RETURN (length l) }"
  sepref_register "test_remdup"

  text \<open>This refinement depends on the (somewhat experimental) subtyping feature 
    to convert from @{term nat_assn} to @{term elem_assn}, based on context information\<close>
  sepref_thm test_remdup1 is 
    "uncurry0 (PR_CONST test_remdup)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding test_remdup_def PR_CONST_def
    by sepref

  concrete_definition (in -) test_bremdup1 uses my_bremdup_impl_loc.test_remdup1.refine_raw is "(uncurry0 ?f,_)\<in>_"
  prepare_code_thms (in -) test_bremdup1_def
  lemmas test_remdup1_refine[sepref_fr_rules] = test_bremdup1.refine[of N]

end    

lemma test_bremdup1_refine_aux: "(test_bremdup1, my_bremdup_impl_loc.test_remdup) \<in> [my_bremdup_impl_loc]\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn"
  using test_bremdup1.refine
  unfolding hfref_def hn_refine_def
  by (auto simp: pure_def)

lemma test_bremdup1_refine: "(test_bremdup1, my_bremdup_impl_loc.test_remdup) \<in> [\<lambda>N. N>0]\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn"
  apply (rule hfref_cons[OF test_bremdup1_refine_aux _ entt_refl entt_refl entt_refl])
  by unfold_locales
  
export_code test_bremdup1 checking SML

text \<open>We can also register the abstract constant and the refinement, to use it in further refinements\<close>
sepref_register test_bremdup: my_bremdup_impl_loc.test_remdup \<comment> \<open>Specifying a base-name for 
    the theorems here, as default name clashes with existing names.\<close>
lemmas [sepref_fr_rules] = test_bremdup1_refine

subsubsection \<open>Fixed-Value Restriction\<close>
text \<open>Initialization only works with fixed values, not with dynamically computed values\<close>
sepref_definition copy_list_to_array is "\<lambda>l. do {
  let N = length l; \<comment> \<open>Introduce a \<open>let\<close>, such that we have a single variable as size-init\<close>
  let l' = op_arl_empty_sz N;
  nfoldli l (\<lambda>x. True) (\<lambda>x s. mop_list_append s x) l'
}" :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_assn"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  supply [[unify_trace_failure, goals_limit=1]]
  (*apply (rule arl_sz.custom_hnr[to_hnr])*)
  \<comment> \<open>The problem manifests itself in trying to carry an abstract variable 
    (the argument to \<open>op_arl_empty_sz\<close>) to the concrete program (the second argument of \<open>hn_refine\<close>).
    However, the concrete program can only depend on the concrete variables, so unification fails.\<close>
  oops


subsubsection \<open>Matrix Example\<close>

text \<open>
  We first give an example for implementing point-wise matrix operations, using
  some utilities from the (very prototype) matrix library.

  Our matrix library uses functions @{typ "'a mtx"} (which is @{typ "nat\<times>nat \<Rightarrow> 'a"})
  as the abstract representation. The (currently only) implementation is by arrays,
  mapping points at coordinates out of range to @{term 0}.
\<close>

text \<open>Pointwise unary operations are those that modify every point
  of a matrix independently. Moreover, a zero-value must be mapped to a zero-value.
  As an example, we duplicate every value on the diagonal of a matrix
\<close>

text \<open>Abstractly, we apply the following function to every value.
  The first parameter are the coordinates.\<close>
definition mtx_dup_diag_f:: "nat\<times>nat \<Rightarrow> 'a::{numeral,times,mult_zero} \<Rightarrow> 'a"
  where "mtx_dup_diag_f \<equiv> \<lambda>(i,j) x. if i=j then x*(2) else x"

text \<open>We refine this function to a heap-function,
  using the identity mapping for values.\<close>
context 
  fixes dummy :: "'a::{numeral,times,mult_zero}"
  notes [[sepref_register_adhoc "PR_CONST (2::'a)"]]
    \<comment> \<open>Note: The setup for numerals, like \<open>2\<close>, is a bit subtle in that
      numerals are always treated as constants, but have to be registered
      for any type they shall be used with. By default, they are only 
      registered for @{typ int} and @{typ nat}.\<close>
  notes [sepref_import_param] = IdI[of "PR_CONST (2::'a)"]
  notes [sepref_import_param] = IdI[of "(*)::'a\<Rightarrow>_", folded fun_rel_id_simp]
begin

sepref_definition mtx_dup_diag_f1 is "uncurry (RETURN oo (mtx_dup_diag_f::_\<Rightarrow>'a\<Rightarrow>_))" :: "(prod_assn nat_assn nat_assn)\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding mtx_dup_diag_f_def
  by sepref

end

text \<open>Then, we instantiate the corresponding locale, to get an implementation for 
  array matrices. Note that we restrict ourselves to square matrices here: \<close>
interpretation dup_diag: amtx_pointwise_unop_impl N N mtx_dup_diag_f id_assn mtx_dup_diag_f1
  apply standard
  applyS (simp add: mtx_dup_diag_f_def) []
  applyS (rule mtx_dup_diag_f1.refine)
  done

text \<open>We introduce an abbreviation for the abstract operation.
  Note: We do not have to register it (this is done once and for all 
    for @{const mtx_pointwise_unop}), nor do we have to declare a refinement rule 
    (done by \<open>amtx_pointwise_unop_impl\<close>-locale)   
\<close> 
abbreviation "mtx_dup_diag \<equiv> mtx_pointwise_unop mtx_dup_diag_f"

text \<open>The operation is usable now:\<close>
sepref_thm mtx_dup_test is "\<lambda>m. RETURN (mtx_dup_diag (mtx_dup_diag m))" :: "(asmtx_assn N int_assn)\<^sup>d \<rightarrow>\<^sub>a asmtx_assn N int_assn"
  by sepref

text \<open>Similarly, there are operations to combine to matrices, and to compare two matrices:\<close>

interpretation pw_add: amtx_pointwise_binop_impl N M "(((+))::(_::monoid_add) \<Rightarrow> _)" id_assn "return oo ((+))"
  for N M
  apply standard
  apply simp
  apply (sepref_to_hoare) apply sep_auto \<comment> \<open>Alternative to 
    synthesize concrete operation, for simple ad-hoc refinements\<close>
  done
abbreviation "mtx_add \<equiv> mtx_pointwise_binop ((+))"

sepref_thm mtx_add_test is "uncurry2 (\<lambda>m1 m2 m3. RETURN (mtx_add m1 (mtx_add m2 m3)))" 
  :: "(amtx_assn N M int_assn)\<^sup>d *\<^sub>a (amtx_assn N M int_assn)\<^sup>d *\<^sub>a (amtx_assn N M int_assn)\<^sup>k \<rightarrow>\<^sub>a amtx_assn N M int_assn"
  by sepref

text \<open>A limitation here is, that the first operand is destroyed on a coarse-grained level.
  Although adding a matrix to itself would be valid, our tool does not support this.
  (However, you may use an unary operation)\<close>
sepref_thm mtx_dup_alt_test is "(\<lambda>m. RETURN (mtx_add m m))" 
  :: "(amtx_assn N M int_assn)\<^sup>d \<rightarrow>\<^sub>a amtx_assn N M int_assn"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  \<comment> \<open>We get stuck at a @{const COPY} goal, indicating that a matrix has to be copied.\<close>
  apply sepref_dbg_trans_step_keep
  \<comment> \<open>Which only works for pure refinements\<close>
  oops

text \<open>Of course, you can always copy the matrix manually:\<close>
sepref_thm mtx_dup_alt_test is "(\<lambda>m. RETURN (mtx_add (op_mtx_copy m) m))" 
  :: "(amtx_assn N M int_assn)\<^sup>k \<rightarrow>\<^sub>a amtx_assn N M int_assn"
  by sepref

text \<open>A compare operation checks that all pairs of entries fulfill some property \<open>f\<close>, and
  at least one entry fullfills a property \<open>g\<close>.\<close>
interpretation pw_lt: amtx_pointwise_cmpop_impl N M "((\<le>)::(_::order) \<Rightarrow> _)" "((\<noteq>)::(_::order) \<Rightarrow> _)" id_assn "return oo (\<le>)" "return oo (\<noteq>)"
  for N M
  apply standard
  apply simp
  apply simp
  apply (sepref_to_hoare) apply sep_auto
  apply (sepref_to_hoare) apply sep_auto
  done
abbreviation "mtx_lt \<equiv> mtx_pointwise_cmpop (\<le>) (\<noteq>)"

sepref_thm test_mtx_cmp is "(\<lambda>m. do { RETURN (mtx_lt (op_amtx_dfltNxM N M 0) m) })" :: "(amtx_assn N M int_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref \<comment> \<open>Note: Better fold over single matrix (currently no locale for that), instead of creating a new matrix.\<close>

text \<open>In a final example, we store some coordinates in a set, and then
  use the stored coordinates to access the matrix again. This illustrates how 
  bounded relations can be used to maintain extra information, i.e., coordinates 
  being in range\<close>

context
  fixes N M :: nat
  notes [[sepref_register_adhoc N M]]
  notes [sepref_import_param] = IdI[of N] IdI[of M]
begin
  text \<open>We introduce an assertion for coordinates\<close>
  abbreviation "co_assn \<equiv> prod_assn (nbn_assn N) (nbn_assn M)"
  text \<open>And one for integer matrices\<close>
  abbreviation "mtx_assn \<equiv> amtx_assn N M int_assn"

  definition "co_set_gen \<equiv> do {
    nfoldli [0..<N] (\<lambda>_. True) (\<lambda>i. nfoldli [0..<M] (\<lambda>_. True) (\<lambda>j s. 
      if max i j - min i j \<le> 1 then RETURN (insert (i,j) s)
      else RETURN s
    )) {}
  }"

  sepref_definition co_set_gen1 is "uncurry0 co_set_gen" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hs.assn co_assn"
    unfolding co_set_gen_def
    apply (rewrite "hs.fold_custom_empty")
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    \<comment> \<open>We run into the problem that the Sepref tool uses \<open>nat_assn\<close> to refine natural
      numbers, and only later tries to convert it to \<open>nbn_assn\<close>. However, at this point, the
      information is already lost.\<close>
    oops

  text \<open>We can use a feature of Sepref, to annotate the desired assertion directly 
    into the abstract program. For this, we use @{thm [source] annotate_assn}, 
    which inserts the (special) constant @{const ASSN_ANNOT}, which is just identity, 
    but enforces refinement with the given assertion.\<close>  
  sepref_definition co_set_gen1 is "uncurry0 (PR_CONST co_set_gen)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hs.assn co_assn"
    unfolding co_set_gen_def PR_CONST_def
    apply (rewrite "hs.fold_custom_empty")
    apply (rewrite in "insert \<hole> _" annotate_assn[where A=co_assn])
      \<comment> \<open>Annotate the pair as coordinate before insertion\<close>
    by sepref
  lemmas [sepref_fr_rules] = co_set_gen1.refine

  sepref_register "co_set_gen"

  text \<open>Now we can use the entries from the set as coordinates, 
    without any worries about them being out of range\<close>
  sepref_thm co_set_use is "(\<lambda>m. do {
    co \<leftarrow> co_set_gen;
    FOREACH co (\<lambda>(i,j) m. RETURN ( m((i,j) := 1))) m
  })" :: "mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
    by sepref
    

end

subsection \<open>Type Classes\<close>
text \<open>TBD\<close>
subsection \<open>Higher-Order\<close>
text \<open>TBD\<close>

subsection \<open>A-Posteriori Optimizations\<close>
text \<open>The theorem collection @{attribute sepref_opt_simps}
  and @{attribute sepref_opt_simps2} contain simplifier lemmas that are
  applied, in two stages, to the generated Imperative/HOL program.

  This is the place where some optimizations, such as deforestation, and
  simplifying monad-expressions using the monad laws, take place.
\<close>
thm sepref_opt_simps
thm sepref_opt_simps2

subsection \<open>Short-Circuit Evaluation\<close>
text \<open>Consider\<close>
sepref_thm test_sc_eval is "RETURN o (\<lambda>l. length l > 0 \<and> hd l)" :: "(list_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  \<comment> \<open>Got stuck, as the operands of \<open>\<and>\<close> are evaluated before applying the operator, i.e.,
    \<open>hd\<close> is also applied to empty lists\<close>
  oops

sepref_thm test_sc_eval is "RETURN o (\<lambda>l. length l > 0 \<and> hd l)" :: "(list_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding short_circuit_conv \<comment> \<open>Enables short-circuit evaluation 
    by rewriting \<open>\<and>\<close>, \<open>\<or>\<close>, and \<open>\<longrightarrow>\<close> to \<open>if\<close>-expressions\<close>
  by sepref

end
