(*<*)
theory Refine_Monadic_Userguide
imports "../Refine_Dflt_Only_ICF"
begin
(*>*)

text_raw \<open>\isasection{Old Monadic Refinement Framework Userguide}\<close>

section \<open>Introduction\<close>
text \<open>
  This is the old userguide from Refine-Monadic. It contains the
  manual approach of using the mondaic refinement framework with the
  Isabelle Collection Framework. An alternative, more simple approach is
  provided by the Automatic Refinement Framework and the 
  Generic Collection Framework.

  The Isabelle/HOL refinement framework is a library that supports
  program and data refinement.

  Programs are specified using a nondeterminism monad: 
  An element of the monad type is either a set of results, or
  the special element @{term "FAIL"}, that indicates a failed assertion.

  The bind-operation of the monad applies a function to all elements of the
  result-set, and joins all possible results.

  On the monad type, an ordering \<open>\<le>\<close> is defined, that is lifted subset
  ordering, where @{term "FAIL"} is the greatest element. Intuitively,
  @{term "S\<le>S'"} means that program \<open>S\<close> refines program \<open>S'\<close>, 
  i.e., all results of \<open>S\<close> are also results of \<open>S'\<close>, and 
  \<open>S\<close> may only fail if \<open>S'\<close> also fails.
\<close>

section \<open>Guided Tour\<close>
text \<open>
  In this section, we provide a small example program development in our 
  framework. All steps of the development are heavily commented.
\<close>

subsection \<open>Defining Programs\<close>
text \<open>
  A program is defined using the Haskell-like do-notation, that is provided by
  the Isabelle/HOL library. We start with a simple example, that iterates
  over a set of numbers, and computes the maximum value and the sum of
  all elements.
\<close>

definition sum_max :: "nat set \<Rightarrow> (nat\<times>nat) nres" where
  "sum_max V \<equiv> do {
    (_,s,m) \<leftarrow> WHILE (\<lambda>(V,s,m). V\<noteq>{}) (\<lambda>(V,s,m). do {
      x\<leftarrow>SPEC (\<lambda>x. x\<in>V); 
      let V=V-{x};
      let s=s+x;
      let m=max m x;
      RETURN (V,s,m)
    }) (V,0,0);
    RETURN (s,m)
  }"

text \<open>
  The type of the nondeterminism monad is @{typ "'a nres"}, where @{typ "'a"}
  is the type of the results. Note that this program has only one possible
  result, however, the order in which we iterate over the elements of the set
  is unspecified.

  This program uses the following statements provided by our framework:
  While-loops, bindings, return, and specification. We briefly explain the
  statements here. A complete reference can be found in 
  Section~\ref{sec:stmt_ref}.

  A while-loop has the form @{term "WHILE b f \<sigma>\<^sub>0"}, where @{term "b"} is the
  continuation condition, @{term "f"} is the loop body, and @{term "\<sigma>\<^sub>0"} is
  the initial state. In our case, the state used for the loop is a triple
  @{term "(V,s,m)"}, where @{term "V"} is the set of remaining elements,
  @{term "s"} is the sum of the elements seen so far, and @{term "m"} is 
  the maximum of the elements seen so far.
  The @{term "WHILE b f \<sigma>\<^sub>0"} construct describes a partially correct loop,
  i.e., it describes only those results that can be reached by finitely many
  iterations, and ignores infinite paths of the loop. In order to 
  prove total correctness, the construct @{term "WHILE\<^sub>T b f \<sigma>\<^sub>0"} is used. It
  fails if there exists an infinite execution of the loop.

  A binding @{term [source] "do {x\<leftarrow>(S\<^sub>1::'a nres); S\<^sub>2}"} nondeterministically 
  chooses a result of 
  @{term "S\<^sub>1"}, binds it to variable @{term "x"}, and then continues with 
  @{term "S\<^sub>2"}. If @{term "S\<^sub>1"} is @{const "FAIL"}, the 
  bind statement also fails. 

  The syntactic form @{term [source] "do { let x=V; (S::'a \<Rightarrow> 'b nres)}"} 
  assigns the value \<open>V\<close> to variable \<open>x\<close>, and continues with 
  \<open>S\<close>. 

  The return statement @{term "RETURN x"} specifies precisely the result 
  \<open>x\<close>. 

  The specification statement @{term "SPEC \<Phi>"} describes all results that 
  satisfy the predicate \<open>\<Phi>\<close>. This is the source of nondeterminism in
  programs, as there may be more than one such result. In our case, we describe
  any element of set \<open>V\<close>.

  Note that these statement are shallowly embedded into Isabelle/HOL, i.e.,
  they are ordinary Isabelle/HOL constants. The main advantage is, that any 
  other construct and datatype from Isabelle/HOL may be used inside programs.
  In our case, we use Isabelle/HOL's predefined operations on sets and natural
  numbers. Another advantage is that extending the framework with new commands
  becomes fairly easy.
\<close>

subsection \<open>Proving Programs Correct\<close>
text \<open>
  The next step in the program development is to prove the program correct
  w.r.t.\ a specification. In refinement notion, we have to prove that the
  program \<open>S\<close> refines a specification \<open>\<Phi>\<close> if the precondition
  \<open>\<Psi>\<close> holds, i.e., @{term "\<Psi> \<Longrightarrow> S \<le> SPEC \<Phi>"}.

  For our purposes, we prove that @{const "sum_max"} really computes the sum 
  and the maximum.
\<close>

text \<open>
  As usual, we have to think of a loop invariant first. In our case, this
  is rather straightforward. The main complication is introduced by the
  partially defined \<open>Max\<close>-operator of the Isabelle/HOL standard library.
\<close>
definition "sum_max_invar V\<^sub>0 \<equiv> \<lambda>(V,s::nat,m).
             V\<subseteq>V\<^sub>0
           \<and> s=\<Sum>(V\<^sub>0-V) 
           \<and> m=(if (V\<^sub>0-V)={} then 0 else Max (V\<^sub>0-V)) 
           \<and> finite (V\<^sub>0-V)"


text \<open>
  We have extracted the most complex verification condition 
  --- that the invariant is preserved by the loop body --- to
  an own lemma. For complex proofs, it is always a good idea to do that,
  as it makes the proof more readable.
\<close>
lemma sum_max_invar_step:
  assumes "x\<in>V" "sum_max_invar V\<^sub>0 (V,s,m)"
  shows "sum_max_invar V\<^sub>0 (V-{x},s+x,max m x)"
  txt \<open>In our case the proof is rather straightforward, it only
    requires the lemma @{thm [source] it_step_insert_iff}, that handles
    the @{term "(V\<^sub>0-(V-{x}))"} terms that occur in the invariant.\<close>
  using assms unfolding sum_max_invar_def by (auto simp: it_step_insert_iff)

text \<open>
  The correctness is now proved by first invoking the verification condition
  generator, and then discharging the verification conditions by 
  \<open>auto\<close>. Note that we have to apply the 
  @{thm [source] sum_max_invar_step} lemma, {\em before} we unfold the 
  definition of the invariant to discharge the remaining verification 
  conditions.
\<close>
theorem sum_max_correct:
  assumes PRE: "V\<noteq>{}" 
  shows "sum_max V \<le> SPEC (\<lambda>(s,m). s=\<Sum>V \<and> m=Max V)"
  txt \<open>
    The precondition \<open>V\<noteq>{}\<close> is necessary, as the
    \<open>Max\<close>-operator from Isabelle/HOL's standard library is not defined
    for empty sets.
\<close>
  using PRE unfolding sum_max_def
  apply (intro WHILE_rule[where I="sum_max_invar V"] refine_vcg) \<comment> \<open>Invoke vcg\<close>
  txt \<open>Note that we have explicitely instantiated 
    the rule for the while-loop with the invariant. If this is not done,
    the verification condition generator will stop at the WHILE-loop.
\<close>
  apply (auto intro: sum_max_invar_step) \<comment> \<open>Discharge step\<close>
  unfolding sum_max_invar_def \<comment> \<open>Unfold invariant definition\<close>
  apply (auto) \<comment> \<open>Discharge remaining goals\<close>
  done

text \<open>
  In this proof, we specified the invariant explicitely.
  Alternatively, we may annotate the invariant at the while loop,
  using the syntax @{term "WHILE\<^bsup>I\<^esup> b f \<sigma>\<^sub>0"}. Then, the verification condition
  generator will use the annotated invariant automatically.
\<close>

text_raw\<open>\paragraph{Total Correctness}\<close>
text \<open>
  Now, we reformulate our program to use a total correct while loop,
  and annotate the invariant at the loop. The invariant is strengthened by
  stating that the set of elements is finite.
\<close>

definition "sum_max'_invar V\<^sub>0 \<sigma> \<equiv> 
  sum_max_invar V\<^sub>0 \<sigma> 
  \<and> (let (V,_,_)=\<sigma> in finite (V\<^sub>0-V))"

definition sum_max' :: "nat set \<Rightarrow> (nat\<times>nat) nres" where
  "sum_max' V \<equiv> do {
    (_,s,m) \<leftarrow> WHILE\<^sub>T\<^bsup>sum_max'_invar V\<^esup> (\<lambda>(V,s,m). V\<noteq>{}) (\<lambda>(V,s,m). do {
      x\<leftarrow>SPEC (\<lambda>x. x\<in>V); 
      let V=V-{x};
      let s=s+x;
      let m=max m x;
      RETURN (V,s,m)
    }) (V,0,0);
    RETURN (s,m)
  }"


theorem sum_max'_correct:
  assumes NE: "V\<noteq>{}" and FIN: "finite V"
  shows "sum_max' V \<le> SPEC (\<lambda>(s,m). s=\<Sum>V \<and> m=Max V)"
  using NE FIN unfolding sum_max'_def
  apply (intro refine_vcg) \<comment> \<open>Invoke vcg\<close>

  txt \<open>This time, the verification condition generator uses the annotated
    invariant. Moreover, it leaves us with a variant. We have to specify a 
    well-founded relation, and show that the loop body respects this
    relation. In our case, the set \<open>V\<close> decreases in each step, and
    is initially finite. We use the relation @{const "finite_psubset"} and the
    @{const "inv_image"} combinator from the Isabelle/HOL standard library.\<close>
  apply (subgoal_tac "wf (inv_image finite_psubset fst)",
    assumption) \<comment> \<open>Instantiate variant\<close>
  apply simp \<comment> \<open>Show variant well-founded\<close>

  unfolding sum_max'_invar_def \<comment> \<open>Unfold definition of invariant\<close>
  apply (auto intro: sum_max_invar_step) \<comment> \<open>Discharge step\<close>

  unfolding sum_max_invar_def \<comment> \<open>Unfold definition of invariant completely\<close>
  apply (auto intro: finite_subset) \<comment> \<open>Discharge remaining goals\<close>
  done

subsection \<open>Refinement\<close>
text \<open>
  The next step in the program development is to refine the initial program
  towards an executable program. This usually involves both, program refinement
  and data refinement. Program refinement means changing the structure of the 
  program. Usually, some specification statements are replaced by more concrete
  implementations. Data refinement means changing the used data types towards
  implementable data types. 

  In our example, we implement the set \<open>V\<close> with a distinct list,
  and replace the specification statement @{term "SPEC (\<lambda>x. x\<in>V)"} by
  the head operation on distinct lists. For the lists, we use
  the list-set data structure provided by the Isabelle Collection Framework
  \cite{L09_collections,LL10}.

  For this example, we write the refined program ourselves.
  An automation of this task can be achieved with the automatic refinement tool,
  which is available as a prototype in Refine-Autoref. Usage examples are in
  ex/Automatic-Refinement. 
\<close>

definition sum_max_impl :: "nat ls \<Rightarrow> (nat\<times>nat) nres" where
  "sum_max_impl V \<equiv> do {
    (_,s,m) \<leftarrow> WHILE (\<lambda>(V,s,m). \<not>ls.isEmpty V) (\<lambda>(V,s,m). do {
      x\<leftarrow>RETURN (the (ls.sel V (\<lambda>x. True)));
      let V=ls.delete x V;
      let s=s+x;
      let m=max m x;
      RETURN (V,s,m)
    }) (V,0,0);
    RETURN (s,m)
  }"

text \<open>
  Note that we replaced the operations on sets by the respective operations
  on lists (with the naming scheme \<open>ls.xxx\<close>). The specification 
  statement was replaced by @{term "the (ls.sel V (\<lambda>x. True))"}, i.e.,
  selection of an element that satisfies the predicate @{term "(\<lambda>x. True)"}.
  As @{const "ls.sel"} returns an option datatype, we extract the value with
  @{const "the"}. Moreover, we omitted the loop invariant, as we don't need it
  any more.
\<close>

text \<open>
  Next, we have to show that our concrete pogram actually refines
  the abstract one.
\<close>
theorem sum_max_impl_refine: 
  assumes "(V,V')\<in>build_rel ls.\<alpha> ls.invar" 
  shows "sum_max_impl V \<le> \<Down>Id (sum_max V')"
  txt \<open>
    Let \<open>R\<close> be a
    {\em refinement relation\footnote{Also called coupling invariant.}},
    that relates concrete and abstract values. 
  
    Then, the function @{term "\<Down>R"} maps a result-set over abstract values to
    the greatest result-set over concrete values that is compatible 
    w.r.t.\ \<open>R\<close>. The value @{const "FAIL"} is mapped to itself.

    Thus, the proposition @{term "S \<le> \<Down>R S'"} means, that \<open>S\<close> refines
    \<open>S'\<close> w.r.t.\ \<open>R\<close>, i.e., every value in the result of 
    \<open>S\<close> can be abstracted to a value in the result of \<open>S'\<close>.
    
    Usually, the refinement relation consists of an invariant \<open>I\<close> and
    an abstraction function \<open>\<alpha>\<close>. In this case, we may use the
    @{term "build_rel I \<alpha>"}-function to define the refinement relation.
    
    In our example, we assume that the input is in the refinement relation 
    specified by list-sets, and show that the output is in the identity 
    relation. We use the identity here, as we do not change the datatypes of 
    the output.
\<close>

  txt \<open>The proof is done automatically by the refinement verification 
    condition generator.
    Note that the theory \<open>Collection_Bindings\<close> sets up all the 
    necessary lemmas to discharge refinement conditions for the collection
    framework.\<close>
  using assms unfolding sum_max_impl_def sum_max_def
  apply (refine_rcg) \<comment> \<open>Decompose combinators, generate data refinement goals\<close>

  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply (auto simp add: 
    ls.correct refine_hsimp refine_rel_defs) \<comment> \<open>Discharge proof obligations\<close>
  done

text \<open>
  Refinement is transitive, so it is easy to show that the concrete
  program meets the specification.
\<close>
theorem sum_max_impl_correct:
  assumes "(V,V')\<in>build_rel ls.\<alpha> ls.invar" and "V'\<noteq>{}"
  shows "sum_max_impl V \<le> SPEC (\<lambda>(s,m). s=\<Sum>V' \<and> m=Max V')"
proof -
  note sum_max_impl_refine
  also note sum_max_correct
  finally show ?thesis using assms .
qed

text \<open>
  Just for completeness, we also refine the total correct program in the
  same way. 
\<close>
definition sum_max'_impl :: "nat ls \<Rightarrow> (nat\<times>nat) nres" where
  "sum_max'_impl V \<equiv> do {
    (_,s,m) \<leftarrow> WHILE\<^sub>T (\<lambda>(V,s,m). \<not>ls.isEmpty V) (\<lambda>(V,s,m). do {
      x\<leftarrow>RETURN (the (ls.sel V (\<lambda>x. True)));
      let V=ls.delete x V;
      let s=s+x;
      let m=max m x;
      RETURN (V,s,m)
    }) (V,0,0);
    RETURN (s,m)
  }"

theorem sum_max'_impl_refine: 
  "(V,V')\<in>build_rel ls.\<alpha> ls.invar \<Longrightarrow> sum_max'_impl V \<le> \<Down>Id (sum_max' V')"
  unfolding sum_max'_impl_def sum_max'_def
  apply refine_rcg
  apply refine_dref_type
  apply (auto simp: refine_hsimp ls.correct refine_rel_defs)
  done

theorem sum_max'_impl_correct:
  assumes "(V,V')\<in>build_rel ls.\<alpha> ls.invar" and "V'\<noteq>{}"
  shows "sum_max'_impl V \<le> SPEC (\<lambda>(s,m). s=\<Sum>V' \<and> m=Max V')"
  using ref_two_step[OF sum_max'_impl_refine sum_max'_correct] assms
  txt \<open>Note that we do not need the finiteness precondition, as list-sets are
    always finite. However, in order to exploit this, we have to
    unfold the \<open>build_rel\<close> construct, that relates the list-set on
    the concrete side to the set on the abstract side.
\<close>
  apply (auto simp: build_rel_def)
  done

subsection \<open>Code Generation\<close>
text \<open>
  In order to generate code from the above definitions,
  we convert the function defined in our monad to an ordinary, deterministic
  function, for that the Isabelle/HOL code generator can generate code.

  For partial correct algorithms, we can generate code inside a deterministic
  result monad. The domain of this monad is a flat complete lattice, where
  top means a failed assertion and bottom means nontermination. (Note that 
  executing a function in this monad will never return bottom, 
  but just diverge).
  The construct @{term "nres_of x"} embeds the deterministic into the
  nondeterministic monad. 

  Thus, we have to construct a function \<open>?sum_max_code\<close> such that:
\<close>
schematic_goal sum_max_code_aux: "nres_of ?sum_max_code \<le> sum_max_impl V"
  txt \<open>This is done automatically by the transfer procedure of
    our framework.\<close>
  unfolding sum_max_impl_def
  apply (refine_transfer)
  done

text \<open>
  In order to define the function from the above lemma, we can use the
  command \<open>concrete_definition\<close>, that is provided by our framework:
\<close>
concrete_definition sum_max_code for V uses sum_max_code_aux

text \<open>This defines a new constant \<open>sum_max_code\<close>:\<close>
thm sum_max_code_def
text \<open>And proves the appropriate refinement lemma:\<close>
thm sum_max_code.refine

text \<open>Note that the \<open>concrete_definition\<close> command is sensitive to
  patterns of the form \<open>RETURN _\<close> and \<open>nres_of\<close>, in which case
  the defined constant will not contain the \<open>RETURN\<close> 
  or \<open>nres_of\<close>. In any other case, the defined constant will just be 
  the left hand side of the refinement statement.
\<close>

text \<open>Finally, we can prove a correctness statement that is independent
  from our refinement framework:\<close>
theorem sum_max_code_correct: 
  assumes "ls.\<alpha> V \<noteq> {}"
  shows "sum_max_code V = dRETURN (s,m) \<Longrightarrow> s=\<Sum>(ls.\<alpha> V) \<and> m=Max (ls.\<alpha> V)"
    and "sum_max_code V \<noteq> dFAIL"
  txt \<open>The proof is done by transitivity, and unfolding some 
    definitions:\<close>
  using nres_correctD[OF order_trans[OF sum_max_code.refine sum_max_impl_correct,
    of V "ls.\<alpha> V"]] assms
  by (auto simp: refine_rel_defs)
 

text \<open>For total correctness, the approach is the same. The 
  only difference is, that we use @{const "RETURN"} instead 
  of @{const "nres_of"}:\<close>
schematic_goal sum_max'_code_aux: 
  "RETURN ?sum_max'_code \<le> sum_max'_impl V"
  unfolding sum_max'_impl_def
  apply (refine_transfer)
  done

concrete_definition sum_max'_code for V uses sum_max'_code_aux

theorem sum_max'_code_correct: 
  "\<lbrakk>ls.\<alpha> V \<noteq> {}\<rbrakk> \<Longrightarrow> sum_max'_code V = (\<Sum>(ls.\<alpha> V), Max (ls.\<alpha> V))"
  using order_trans[OF sum_max'_code.refine sum_max'_impl_correct,
    of V "ls.\<alpha> V"]
  by (auto simp: refine_rel_defs)

text \<open>
  If we use recursion combinators, a plain function can only be generated,
  if the recursion combinators can be defined. Alternatively, for total correct
  programs, we may generate a (plain) function that internally uses the 
  deterministic monad, and then extracts the result.
\<close>

schematic_goal sum_max''_code_aux: 
  "RETURN ?sum_max''_code \<le> sum_max'_impl V"
  unfolding sum_max'_impl_def
  apply (refine_transfer the_resI) \<comment> \<open>Using @{text "the_resI"} for internal monad and result extraction\<close>
  done

concrete_definition sum_max''_code for V uses sum_max''_code_aux

theorem sum_max''_code_correct: 
  "\<lbrakk>ls.\<alpha> V \<noteq> {}\<rbrakk> \<Longrightarrow> sum_max''_code V = (\<Sum>(ls.\<alpha> V), Max (ls.\<alpha> V))"
  using order_trans[OF sum_max''_code.refine sum_max'_impl_correct,
    of V "ls.\<alpha> V"]
  by (auto simp: refine_rel_defs)


text \<open>Now, we can generate verified code with the Isabelle/HOL code
  generator:\<close>
export_code sum_max_code sum_max'_code sum_max''_code checking SML
export_code sum_max_code sum_max'_code sum_max''_code checking OCaml?
export_code sum_max_code sum_max'_code sum_max''_code checking Haskell?
export_code sum_max_code sum_max'_code sum_max''_code checking Scala

subsection \<open>Foreach-Loops\<close>
text \<open>
  In the \<open>sum_max\<close> example above, we used a while-loop to iterate over
  the elements of a set. As this pattern is used commonly, there is
  an abbreviation for it in the refinement framework. The construct 
  @{term "FOREACH S f \<sigma>\<^sub>0"} iterates \<open>f::'x\<Rightarrow>'s\<Rightarrow>'s\<close> for each element 
  in \<open>S::'x set\<close>, starting with state \<open>\<sigma>\<^sub>0::'s\<close>.
  
  With foreach-loops, we could have written our example as follows:
\<close>

definition sum_max_it :: "nat set \<Rightarrow> (nat\<times>nat) nres" where
  "sum_max_it V \<equiv> FOREACH V (\<lambda>x (s,m). RETURN (s+x,max m x)) (0,0)"

theorem sum_max_it_correct:
  assumes PRE: "V\<noteq>{}" and FIN: "finite V" 
  shows "sum_max_it V \<le> SPEC (\<lambda>(s,m). s=\<Sum>V \<and> m=Max V)"
  using PRE unfolding sum_max_it_def
  apply (intro FOREACH_rule[where I="\<lambda>it \<sigma>. sum_max_invar V (it,\<sigma>)"] refine_vcg)
  apply (rule FIN) \<comment> \<open>Discharge finiteness of iterated set\<close>
  apply (auto intro: sum_max_invar_step) \<comment> \<open>Discharge step\<close>
  unfolding sum_max_invar_def \<comment> \<open>Unfold invariant definition\<close>
  apply (auto) \<comment> \<open>Discharge remaining goals\<close>
  done

definition sum_max_it_impl :: "nat ls \<Rightarrow> (nat\<times>nat) nres" where
  "sum_max_it_impl V \<equiv> FOREACH (ls.\<alpha> V) (\<lambda>x (s,m). RETURN (s+x,max m x)) (0,0)"
text \<open>Note: The nondeterminism for iterators is currently resolved at
  transfer phase, where they are replaced by iterators from the ICF.\<close>

lemma sum_max_it_impl_refine: 
  notes [refine] = inj_on_id
  assumes "(V,V')\<in>build_rel ls.\<alpha> ls.invar" 
  shows "sum_max_it_impl V \<le> \<Down>Id (sum_max_it V')"
  unfolding sum_max_it_impl_def sum_max_it_def
  txt \<open>Note that we specified \<open>inj_on_id\<close> as additional introduction 
    rule. This is due to the very general iterator refinement rule, that may
    also change the set over that is iterated.\<close>
  using assms
  apply refine_rcg \<comment> \<open>This time, we don't need the 
    @{text "refine_dref_type"} heuristics, as no schematic refinement 
    relations are generated.\<close>
  apply (auto simp: refine_hsimp refine_rel_defs)
  done

schematic_goal sum_max_it_code_aux: 
  "RETURN ?sum_max_it_code \<le> sum_max_it_impl V"
  unfolding sum_max_it_impl_def
  apply (refine_transfer)
  done

text \<open>Note that the transfer method has replaced the iterator by an iterator
  from the Isabelle Collection Framework.\<close>

thm sum_max_it_code_aux
concrete_definition sum_max_it_code for V uses sum_max_it_code_aux

theorem sum_max_it_code_correct: 
  assumes "ls.\<alpha> V \<noteq> {}" 
  shows "sum_max_it_code V = (\<Sum>(ls.\<alpha> V), Max (ls.\<alpha> V))" 
proof -
  note sum_max_it_code.refine[of V]
  also note sum_max_it_impl_refine[of V "ls.\<alpha> V"]
  also note sum_max_it_correct
  finally show ?thesis using assms by (auto simp: refine_rel_defs)
qed

export_code sum_max_it_code checking SML
export_code sum_max_it_code checking OCaml?
export_code sum_max_it_code checking Haskell?
export_code sum_max_it_code checking Scala

definition "sum_max_it_list \<equiv> sum_max_it_code o ls.from_list"
ML_val \<open>
  @{code sum_max_it_list} (map @{code nat_of_integer} [1,2,3,4,5])
\<close>


section \<open>Pointwise Reasoning\<close>

text \<open>
  In this section, we describe how to use pointwise reasoning to prove
  refinement statements and other relations between element of the 
  nondeterminism monad.

  Pointwise reasoning is often a powerful tool to show refinement between
  structurally different program fragments.
\<close>

text \<open>
  The refinement framework defines the predicates 
  @{const "nofail"} and @{const "inres"}.
  @{term "nofail S"} states that \<open>S\<close> does not fail,
  and @{term "inres S x"} states that one possible result of \<open>S\<close> is
  \<open>x\<close> (Note that this includes the case that \<open>S\<close> fails).

  Equality and refinement can be stated using @{const "nofail"} and 
  @{const "inres"}:
  @{thm [display] pw_eq_iff}
  @{thm [display] pw_le_iff}

  Useful corollaries of this lemma are 
  @{thm [source] pw_leI}, @{thm [source] pw_eqI}, and @{thm [source] pwD}.

  Once a refinement has been expressed via nofail/inres, the simplifier can be
  used to propagate the nofail and inres predicates inwards over the structure
  of the program. The relevant lemmas are contained in the named theorem 
  collection \<open>refine_pw_simps\<close>.

  As an example, we show refinement of two structurally different programs here,
  both returning some value in a certain range:
\<close>
lemma "do { ASSERT (fst p > 2); SPEC (\<lambda>x. x\<le>(2::nat)*(fst p + snd p)) }
  \<le> do { let (x,y)=p; z\<leftarrow>SPEC (\<lambda>z. z\<le>x+y); 
          a\<leftarrow>SPEC (\<lambda>a. a\<le>x+y); ASSERT (x>2); RETURN (a+z)}"
  apply (rule pw_leI)
  apply (auto simp add: refine_pw_simps split: prod.split)

  apply (rename_tac a b x)
  apply (case_tac "x\<le>a+b")
  apply (rule_tac x=0 in exI)
  apply simp
  apply (rule_tac x="a+b" in exI)
  apply (simp)
  apply (rule_tac x="x-(a+b)" in exI)
  apply simp
  done

section "Arbitrary Recursion (TBD)"
text \<open>
  While-loops are suited to express tail-recursion.
  In order to express arbitrary recursion, the refinement framework provides
  the nrec-mode for the \<open>partial_function\<close> command, as well as the fixed 
  point combinators @{const "REC"} (partial correctness) and 
  @{const "RECT"} (total correctness).

  Examples for \<open>partial_function\<close> can be found in 
  \<open>ex/Refine_Fold\<close>. Examples for the recursion combinators can be found
  in \<open>ex/Recursion\<close> and \<open>ex/Nested_DFS\<close>.
\<close>

section \<open>Reference\<close>
  subsection \<open>Statements\<close> text_raw \<open>\label{sec:stmt_ref}\<close>
  text \<open>
    \begin{description}
      \item[@{const "SUCCEED"}] The empty set of results. Least element of
        the refinement ordering.
      \item[@{const "FAIL"}] Result that indicates a failing assertion.
        Greatest element of the refinement ordering.
      \item{@{term "RES X"}} All results from set \<open>X\<close>.
      \item[@{term "RETURN x"}] Return single result \<open>x\<close>. Defined in 
        terms of \<open>RES\<close>: @{lemma "RETURN x = RES {x}" by simp}.
      \item[@{term "EMBED r"}] Embed partial-correctness option type, i.e.,
        succeed if \<open>r=None\<close>, otherwise return value of \<open>r\<close>.
      \item[@{term "SPEC \<Phi>"}] Specification. 
        All results that satisfy predicate \<open>\<Phi>\<close>. Defined in terms of
        @{term "RES"}: @{lemma "SPEC \<Phi> = RES (Collect \<Phi>)" by simp}
      \item[@{term [source] "bind M f"}] Binding. 
        Nondeterministically choose a result from 
        \<open>M\<close> and apply \<open>f\<close> to it. Note that usually the 
        \<open>do\<close>-notation is used, i.e., \<open>do {x\<leftarrow>M; f x}\<close> or
        \<open>do {M;f}\<close> if the result of \<open>M\<close> is not important.
        If \<open>M\<close> fails, @{term [source] "bind M f"} also fails.
      \item[@{term "ASSERT \<Phi>"}] Assertion. Fails
        if \<open>\<Phi>\<close> does not hold, otherwise returns \<open>()\<close>.
        Note that the default usage with the do-notation is: 
        @{term [source] "do {ASSERT \<Phi>; f}"}.

      \item[@{term "ASSUME \<Phi>"}] Assumption. Succeeds
        if \<open>\<Phi>\<close> does not hold, otherwise returns \<open>()\<close>. Note that
        the default usage with the do-notation is: 
        @{term [source] "do {ASSUME \<Phi>; f}"}.

      \item[@{term "REC body"}] Recursion for partial correctness. 
        May be used to express arbitrary recursion. Returns \<open>SUCCEED\<close> on
        nontermination.
      \item[@{term "RECT body"}] Recursion for total correctness. 
        Returns \<open>FAIL\<close> on nontermination.
      \item[@{term "WHILE b f \<sigma>\<^sub>0"}] Partial correct while-loop. 
        Start with state \<open>\<sigma>\<^sub>0\<close>,
        and repeatedly apply \<open>f\<close> as long as \<open>b\<close> holds for the
        current state. Non-terminating paths are ignored, i.e., they do not
        contribute a result.
      \item[@{term "WHILE\<^sub>T b f \<sigma>\<^sub>0"}] Total correct while-loop. If there is a
        non-terminating path, the result is @{term "FAIL"}.
      \item[@{term "WHILE\<^bsup>I\<^esup> b f \<sigma>\<^sub>0"}, @{term "WHILE\<^sub>T\<^bsup>I\<^esup> b f \<sigma>\<^sub>0"}] While-loop with
        annotated invariant. It is asserted that the invariant holds.
      \item[@{term "FOREACH S f \<sigma>\<^sub>0"}] Foreach loop.
        Start with state \<open>\<sigma>\<^sub>0\<close>, and transform
        the state with \<open>f x\<close> for each element \<open>x\<in>S\<close>. Asserts that 
        \<open>S\<close> is finite.
      \item[@{term "FOREACH\<^bsup>I\<^esup> S f \<sigma>\<^sub>0"}] Foreach-loop with 
        annotated invariant. 

        Alternative syntax: @{term "FOREACHi I S f \<sigma>\<^sub>0"}.

        The invariant is a predicate of type
        \<open>I::'a set \<Rightarrow> 'b \<Rightarrow> bool\<close>, where \<open>I it \<sigma>\<close> means, that
        the invariant holds for the remaining set of elements \<open>it\<close> and
        current state \<open>\<sigma>\<close>. 
      \item[@{term "FOREACH\<^sub>C S c f \<sigma>\<^sub>0"}] Foreach-loop with explicit continuation 
        condition.

        Alternative syntax: @{term "FOREACHc S c f \<sigma>\<^sub>0"}.

        If \<open>c::'\<sigma>\<Rightarrow>bool\<close> becomes false for the current state,
        the iteration immediately terminates.
      \item[@{term "FOREACH\<^sub>C\<^bsup>I\<^esup> S c f \<sigma>\<^sub>0"}] Foreach-loop with explicit continuation 
        condition and annotated invariant.

        Alternative syntax: @{term "FOREACHci I S c f \<sigma>\<^sub>0"}.
      \item[\<open>partial_function (nrec)\<close>] Mode of the partial function 
        package for the nondeterminism monad.
    \end{description}
\<close>

    subsection \<open>Refinement\<close>
    text \<open>
      \begin{description}
        \item{@{term_type "(\<le>) :: 'a nres \<Rightarrow> 'a nres \<Rightarrow> bool"}} 
          Refinement ordering.
          \<open>S \<le> S'\<close> means, that every result in 
          \<open>S\<close> is also a result in \<open>S'\<close>. 
          Moreover, \<open>S\<close> may only fail if \<open>S'\<close> fails.
          \<open>\<le>\<close> forms a complete lattice, with least element 
          \<open>SUCCEED\<close> and greatest element \<open>FAIL\<close>.
        \item{@{term "\<Down>R"}} Concretization. Takes a refinement relation
          \<open>R::('c\<times>'a) set\<close> that relates concrete to abstract values, 
          and returns a concretization function 
          @{term "\<Down>R :: 'a nres \<Rightarrow> 'c nres"}.
        \item{@{term "\<Up>R"}} Abstraction. Takes a refinement relation and
          returns an abstraction function. 
          The functions \<open>\<Down>R\<close> and \<open>\<Up>R\<close> form a Galois-connection,
          i.e., we have: \<open>S \<le> \<Down>R S' \<longleftrightarrow> \<Up>R S \<le> S'\<close>.
        \item{@{term "build_rel \<alpha> I"}} Builds a refinement relation from
          an abstraction function and an invariant. Those refinement relations
          are always single-valued.
        \item{@{term "nofail S"}} Predicate that states that \<open>S\<close> does
          not fail.
        \item{@{term "inres S x"}} Predicate that states that \<open>S\<close> 
          includes result \<open>x\<close>. Note that a failing program includes all
          results.
      \end{description}
\<close>


    subsection\<open>Proof Tools\<close>
      text \<open>
        \begin{description}
          \item{Verification Condition Generator:}
            \begin{description}
              \item[Method:] \<open>intro refine_vcg\<close>
              \item[Attributes:] \<open>refine_vcg\<close>
            \end{description}

            Transforms a subgoal of the
            form \<open>S \<le> SPEC \<Phi>\<close> into verification conditions by 
            decomposing the structure of \<open>S\<close>. Invariants for loops 
            without annotation must be specified explicitely by instantiating
            the respective proof-rule for the loop construct, e.g., 
            \<open>intro WHILE_rule[where I=\<dots>] refine_vcg\<close>.

            \<open>refine_vcg\<close> is a named theorems collection that contains
            the rules that are used by default.

          \item{Refinement Condition Generator:}
            \begin{description}
              \item[Method:] \<open>refine_rcg\<close> [thms]. 
              \item[Attributes:] \<open>refine0\<close>, \<open>refine\<close>, 
                \<open>refine2\<close>.
              \item[Flags:] \<open>refine_no_prod_split\<close>.
            \end{description}
            Tries to prove a subgoal of the form \<open>S \<le> \<Down>R S'\<close> by 
            decomposing the structure of \<open>S\<close> and \<open>S'\<close>. 
            The rules to be used are contained in the theorem collection 
            \<open>refine\<close>. More rules may be passed as argument to the method.
            Rules contained in \<open>refine0\<close> are always 
            tried first, and rules in \<open>refine2\<close> are tried last. 
            Usually, rules that decompose both programs equally
            should be put into \<open>refine\<close>. Rules that may make big steps,
            without decomposing the program further, should be put into
            \<open>refine0\<close> (e.g., @{thm [source] Id_refine}). Rules that 
            decompose the programs differently and shall be used as last resort
            before giving up should be put into \<open>refine2\<close>, e.g., 
            @{thm [source] remove_Let_refine}.

            By default, this procedure will invoke the splitter to split
            product types in the goals. This behaviour can be disabled by
            setting the flag \<open>refine_no_prod_split\<close>.
          \item{Refinement Relation Heuristics:}
            \begin{description}
              \item[Method:] \<open>refine_dref_type\<close> [(trace)].
              \item[Attributes:] \<open>refine_dref_RELATES\<close>,  
                \<open>refine_dref_pattern\<close>.
              \item[Flags:] \<open>refine_dref_tracing\<close>.
            \end{description}
            Tries to instantiate schematic refinement relations based on their
            type. By default, this rule is applied to all subgoals. 
            Internally, it uses the rules declared as 
            \<open>refine_dref_pattern\<close> to introduce a goal of the form
            \<open>RELATES ?R\<close>, that is then solved by exhaustively 
            applying rules declared as \<open>refine_dref_RELATES\<close>.
            
            The flag \<open>refine_dref_tracing\<close> controls tracing of 
            resolving \<open>RELATES\<close>-goals. Tracing may also be enabled by
            passing (trace) as argument.

          \item{Pointwise Reasoning Simplification Rules:}
            \begin{description}
              \item[Attributes:] \<open>refine_pw_simps\<close>
            \end{description}
            A theorem collection that contains 
            simplification lemmas to push inwards @{term "nofail"} and
            @{term "inres"} predicates into program constructs.

          \item{Refinement Simp Rules:}
            \begin{description}
              \item[Attributes:] \<open>refine_hsimp\<close>
            \end{description}
            A theorem collection that contains some
            simplification lemmas that are useful to prove membership in 
            refinement relations.

          \item{Transfer:}
            \begin{description}
              \item[Method:] \<open>refine_transfer\<close> [thms] 
              \item[Attribute:] \<open>refine_transfer\<close>
            \end{description}
            Tries to prove a subgoal of the form \<open>\<alpha> f \<le> S\<close> by 
            decomposing the structure of \<open>f\<close> and \<open>S\<close>. 
            This is usually used in connection
            with a schematic lemma, to generate \<open>f\<close> from the structure
            of \<open>S\<close>.

            The theorems declared as \<open>refine_transfer\<close> are used to do
            the transfer. More theorems may be passed as arguments to the method. 
            Moreover, some simplification for nested abstraction 
            over product types (\<open>\<lambda>(a,b) (c,d). \<dots>\<close>) is done, and the
            monotonicity prover is used on monotonicity goals.

            There is a standard setup for \<open>\<alpha>=RETURN\<close> 
            (transfer to plain function for total correct code generation), and
            \<open>\<alpha>=nres_of\<close> (transfer to deterministic result monad, for 
            partial correct code generation).

          \item{Automatic Refinement:}
            \begin{description}
              \item[Method:] \<open>refine_autoref\<close> 
              \item[Attributes:] ...
            \end{description}
            See automatic refinement package for documentation (TBD)

          \item{Concrete Definition:}
            \begin{description}
              \item[Command:] 
               \<open>concrete_definition name [attribs] for params uses thm\<close>
               where \<open>attribs\<close> and the \<open>for\<close>-part are optional.

               Declares a new constant from the left-hand side of a refinement
               lemma. Has special handling for left-hand sides of the forms 
               \<open>RETURN _\<close> and \<open>nres_of\<close>, in which cases those 
               topmost functions are not included in the defined constant.

               The refinement lemma is folded with the new constant and 
               registered as \<open>name.refine\<close>.
              \item[Command:]
              \<open>prepare_code_thms thms\<close> takes a list of definitional 
                theorems and sets up lemmas for the code generator for those 
                definitions. This includes handling of recursion combinators.
            \end{description}
        \end{description}
\<close>


    subsection\<open>Packages\<close> 
      text \<open>
        The following parts of the refinement framework are not included
        by default, but can be imported if necessary:
        \begin{description}
          \item{Collection-Bindings:} Sets up refinement rules for the 
            Isabelle Collection Framework. With this theory loaded, the
            refinement condition generator will discharge most data refinements
            using the ICF automatically. Moreover, the transfer procedure
            will replace \<open>FOREACH\<close>-statements by the corresponding 
            ICF-iterators.
        \end{description}
\<close>

end
