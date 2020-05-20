section \<open>Common Proof Methods and Idioms\<close> 
theory Idioms 
imports "../Sep_Main" Open_List Circ_List Hash_Set_Impl
begin 
text_raw\<open>\label{thy:ex:idioms}\<close>

  text \<open>
    This theory gives a short documentation of common proof techniques and 
    idioms for the separation logic framework. For this purpose, it presents
    some proof snippets (inspired by the other example theories), and heavily
    comments on them.
\<close>

  subsection \<open>The Method \<open>sep_auto\<close>\<close>
  text \<open>The most versatile method of our framework is \<open>sep_auto\<close>,
    which integrates the verification condition generator, the entailment
    solver and some pre- and postprocessing tactics based on the simplifier 
    and classical reasoner. It can be applied to a Hoare-triple or entailment
    subgoal, and will try to solve it, and any emerging new goals. It stops
    when the goal is either solved or it gets stuck somewhere.\<close>

  text \<open>As a simple example for \<open>sep_auto\<close> consider the following
    program that does some operations on two circular lists:\<close>
  definition "test \<equiv> do {
    l1 \<leftarrow> cs_empty;
    l2 \<leftarrow> cs_empty;
    l1 \<leftarrow> cs_append ''a'' l1;
    l2 \<leftarrow> cs_append ''c'' l2;
    l1 \<leftarrow> cs_append ''b'' l1;
    l2 \<leftarrow> cs_append ''e'' l2;
    l2 \<leftarrow> cs_prepend ''d'' l2;
    l2 \<leftarrow> cs_rotate l2;
    return (l1,l2)
  }"
  
  text \<open>The \<open>sep_auto\<close> method does all the 
    necessary frame-inference automatically, and thus manages to prove
    the following lemma in one step:\<close>
  lemma "<emp> 
    test 
    <\<lambda>(l1,l2). cs_list [''a'',''b''] l1 
      * cs_list [''c'',''e'',''d''] l2>\<^sub>t"
    unfolding test_def
    apply (sep_auto)
    done

  text \<open>\<open>sep_auto\<close> accepts all the section-options of the classical
    reasoner and simplifier, e.g., \<open>simp add/del:\<close>, \<open>intro:\<close>.
    Moreover, it has some more section options, the most useful being 
    \<open>heap add/del:\<close> to add or remove Hoare-rules that are applied
    with frame-inference. A complete documentation of the accepted options can
    be found in Section~\ref{sec:auto:overview}.
\<close>

  text \<open>As a typical example, consider the following proof:\<close>
  lemma complete_ht_rehash: 
    "<is_hashtable l ht> ht_rehash ht 
    <\<lambda>r. is_hashtable l ht * is_hashtable (ls_rehash l) r>"
  proof -
    have LEN: " l \<noteq> [] \<Longrightarrow> Suc 0 < 2 * length l" by (cases l) auto
    show ?thesis
      apply (rule cons_pre_rule[OF ht_imp_len])
      unfolding ht_rehash_def
      apply (sep_auto 
        heap: complete_ht_new_sz complete_ht_copy
        simp: ls_rehash_def LEN
      ) \<comment> \<open>Here we add a heap-rule, and some simp-rules\<close>
      done
  qed

  subsection \<open>Applying Single Rules\<close>
  text \<open>\paragraph{Hoare Triples} In this example, we show how to do
    a proof step-by-step.\<close>

  lemma
    "<os_list xs n> os_prepend x n <os_list (x # xs)>"
    unfolding os_prepend_def
    txt \<open>The rules to deconstruct compound statements are contained in the
      \<open>sep_decon_rules\<close> collection\<close>
    thm sep_decon_rules
    apply (rule sep_decon_rules)
    txt \<open>The rules for statement that deend on the heap are
      contained in the \<open>sep_heap_rules\<close> collection. The
      \<open>fi_rule\<close>-lemma prepares frame inference for them\<close>
    apply (rule sep_heap_rules[THEN fi_rule])
    apply frame_inference \<comment> \<open>This method does the frame-inference\<close>
    
    txt \<open>The consequence rule comes in three versions, 
      \<open>const_rule\<close>, \<open>cons_pre_rule\<close>, 
      and \<open>cons_post_rule\<close>\<close>
    apply (rule cons_post_rule) 
    apply (rule sep_decon_rules)

    txt \<open>A simplification unfolds \<open>os_list\<close> and extract the
      pure part of the assumption\<close>
    apply (clarsimp)

    txt \<open>We can use \<open>ent_ex_postI\<close> to manually introduce 
      existentials in entailsments\<close>
    apply (rule_tac x=xa in ent_ex_postI)
    apply (rule_tac x=n in ent_ex_postI)
    txt \<open>The simplifier has a setup for assertions, so it will do the rest\<close>
    apply simp
    done

  text \<open>Note that the proof above can be done with \<open>sep_auto\<close>,
    the "Swiss army knife" of our framework\<close>
  lemma
    "<os_list xs n> os_prepend x n <os_list (x # xs)>"
    unfolding os_prepend_def by sep_auto

  text \<open>\paragraph{Entailment} This example presents an actual proof
    from the circular list theory, where we have to manually apply a
    rule and give some hints to frame inference\<close>
  lemma cs_append_rule: 
    "<cs_list l p> cs_append x p <cs_list (l@[x])>"
    apply (cases p)
    apply (sep_auto simp: cs_append.simps)

    apply (sep_auto simp: cs_append.simps heap: lseg_append)
    txt \<open>At this point, we are left with an entailment subgoal that sep-auto
      cannot solve. A closer look reveals that we could use the rule
      \<open>lseg_append\<close>. 
      
      With the \<open>ent_frame_fwd\<close>-rule, we can manually apply a rule to
      solve an entailment, involving frame inference. In this case, we have
      the additional problem that frame-inference guesses
      a wrong instantiation, and is not able to infer the frame.
      So we have to pre-instantiate the rule, as done below.\<close>
    apply (rule_tac s1=pp in ent_frame_fwd[OF lseg_append])
    apply frame_inference \<comment> \<open>Now frame-inference is able to infer the frame\<close>

    txt \<open>Now we are left with a trivial entailment, modulo commutativity of
      star. This can be handled by the entailment solver:\<close>
    apply solve_entails
    done



  subsection \<open>Functions with Explicit Recursion\<close>
  text \<open>If the termination argument of a function depends on one of
    its parameters, we can use the function package. For example, 
    the following function inserts elements from a list into a hash-set:\<close>

  fun ins_from_list 
    :: "('x::{heap,hashable}) list \<Rightarrow> 'x hashset \<Rightarrow> 'x hashset Heap" 
    where
    "ins_from_list [] hs = return hs" |
    "ins_from_list (x # l) hs = do { hs \<leftarrow> hs_ins x hs; ins_from_list l hs }"

  text \<open>Proofs over such functions are usually done by structural
    induction on the explicit parameter, in this case, on the list\<close>
  lemma ins_from_list_correct:
    "<is_hashset s hs> ins_from_list l hs <is_hashset (s\<union>set l)>\<^sub>t"
  proof (induction l arbitrary: hs s)
    case (Cons x l) 
    txt \<open>In the induction step, the induction hypothesis has to be 
      declared as a heap-rule, as \<open>sep_auto\<close> currently does not
      look for potential heap-rules among the premises of the subgoal\<close>
    show ?case by (sep_auto heap: Cons.IH)
  qed sep_auto


  subsection \<open>
    Functions with Recursion Involving the Heap
\<close>
  text \<open>If the termination argument of a function depends on data stored on
    the heap, \<open>partial_function\<close> is a useful tool.

    Note that, despite the name, proving a Hoare-Triple \<open><\<dots>> \<dots> <\<dots>>\<close>
    for something defined with \<open>partial_function\<close> implies total 
    correctness.
\<close>

  text \<open>In the following example, we compute the sum of a list, using an
    iterator. Note that the partial-function package does not provide a
    code generator setup by default, so we have to add a \<open>[code]\<close>
    attribute manually\<close>
  partial_function (heap) os_sum' :: "int os_list_it \<Rightarrow> int \<Rightarrow> int Heap" 
    where [code]:
    "os_sum' it s = do {
      b \<leftarrow> os_it_has_next it;
      if b then do {
        (x,it') \<leftarrow> os_it_next it;
        os_sum' it' (s+x)
      } else return s
    }"

  text \<open>The proof that the function is correct can be done by induction
    over the representation of the list that we still have to iterate over.
    Note that for iterators over sets, we need induction on finite sets,
    cf. also \<open>To_List_Ga.thy\<close>\<close>

  lemma os_sum'_rule: 
    "<os_is_it l p l' it> 
    os_sum' it s 
    <\<lambda>r. os_list l p * \<up>(r = s + sum_list l')>\<^sub>t"
  proof (induct l' arbitrary: it s)
    case Nil thus ?case
      txt \<open>To unfold the definition of a partial function, we have to use 
        \<open>subst\<close>. Note that \<open>simp\<close> would loop, unfolding the
        function arbitrarily deep\<close>
      apply (subst os_sum'.simps)
      txt \<open>\<open>sep_auto\<close> accepts all the section parameters that 
        \<open>auto\<close> does, eg. \<open>intro:\<close>\<close>
      apply (sep_auto intro: os.quit_iteration)
      done
  next
    case (Cons x l')
    show ?case
      apply (subst os_sum'.simps)
      txt \<open>Additionally, \<open>sep_auto\<close> accepts some more section 
        parameters. The most common one, \<open>heap:\<close>, declares rules 
        to be used with frame inference. See Section~\ref{sec:auto:overview}
        for a complete overview.\<close>
      apply (sep_auto heap: Cons.hyps)
      done
  qed


  subsection \<open>Precision Proofs\<close>
  text \<open>
    Precision lemmas show that an assertion uniquely determines some of its
    parameters. Our example shows that two list segments from the same start 
    pointer and with the same list, also have to end at the same end pointer.
\<close>
  
  lemma lseg_prec3: 
    "\<forall>q q'. h \<Turnstile> (lseg l p q * F1) \<and>\<^sub>A (lseg l p q' * F2) \<longrightarrow> q=q'"
    apply (intro allI)
  proof (induct l arbitrary: p F1 F2)
    case Nil thus ?case 
      apply simp \<comment> \<open>A precision solver for references and arrays is included
        in the standard simplifier setup. Building a general precision solver
        remains future work.\<close>
      by metis \<comment> \<open>Unfortunately, the simplifier cannot cope with arbitrarily  
        directed equations, so we have to use some more powerful tool\<close>
  next
    case (Cons x l)
    show ?case
      apply clarsimp
  
      apply (subgoal_tac "na=n")
  
      txt \<open>The \<open>prec_frame\<close> and \<open>prec_frame'\<close> rules are 
        useful to do precision proofs\<close>
      apply (erule prec_frame'[OF Cons.hyps])
      apply frame_inference
      apply frame_inference
  
      apply (drule prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
  qed
end
