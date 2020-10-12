section \<open>Reference Guide\<close>
theory Sepref_Guide_Reference
imports "../IICF/IICF" (*"~~/src/Doc/Isar_Ref/Base"*)
begin
text \<open>This guide contains a short reference of the most 
  important Sepref commands, methods, and attributes, as well as
  a short description of the internal working, and troubleshooting information
  with examples.

  Note: To get an impression how to actually use the Sepref-tool, read the
  quickstart guide first!
\<close>

subsection \<open>The Sepref Method\<close>
text \<open>The @{method sepref} method is the central method of the tool.
  Given a schematic goal of the form \<open>hn_refine \<Gamma> ?c ?\<Gamma>' ?R f\<close>, it tries 
  to synthesize terms for the schematics and prove the theorem. Note that the
  \<open>?\<Gamma>'\<close> and \<open>?R\<close> may also be fixed terms, in which case frame inference is used 
  to match the generated assertions with the given ones.
  \<open>\<Gamma>\<close> must contain a description of the available refinements on the heap, the 
  assertion for each variable must be marked with a \<open>hn_ctxt\<close> tag. 

  Alternatively, a term of the form \<open>(?c,f)\<in>[P]\<^sub>a A\<rightarrow>R\<close> is accepted, where \<open>A\<close> 
  describes the refinement and preservation of the arguments, and \<open>R\<close> the refinement 
  of the result. \<open>f\<close> must be in uncurried form (i.e. have exactly one argument).

  We give some very basic examples here. In practice, you would almost always use
  the higher-level commands @{command sepref_definition} and @{command sepref_register}.
\<close>

text \<open>In its most primitive form, the Sepref-tool is applied like this:\<close>
schematic_goal 
  notes [id_rules] = itypeI[of x "TYPE(nat)"] itypeI[of a "TYPE(bool list)"]
  shows "hn_refine 
    (hn_ctxt nat_assn x xi * hn_ctxt (array_assn bool_assn) a ai) 
    (?c::?'c Heap) ?\<Gamma>' ?R 
    (do { ASSERT (x<length a); RETURN (a!x) })"
  by sepref

text \<open>The above command asks Sepref to synthesize a program, in a heap context where there 
  is a natural number, refined by \<open>nat_assn\<close>, and a list of booleans, refined 
  by \<open>array_assn bool_assn\<close>. The \<open>id_rules\<close> declarations declare the abstract variables to the 
  operation identification heuristics, such that they are recognized as operands.\<close>

text \<open>Using the alternative hfref-form, we can write:\<close>
schematic_goal "(uncurry (?c), uncurry (\<lambda>x a. do {ASSERT (x<length a); RETURN (a!x)}))
  \<in> nat_assn\<^sup>k *\<^sub>a (array_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref
text \<open>This uses the specified assertions to derive the rules for 
  operation identification automatically. For this, it uses the
  assertion-interface bindings declared in @{attribute intf_of_assn}.
  If there is no such binding, it uses the HOL type as interface type.
\<close>
thm intf_of_assn

text \<open>
  The sepref-method is split into various phases, which we will explain now
\<close>

subsubsection \<open>Preprocessing Phase\<close>
text \<open>
  This tactic converts a goal in \<open>hfref\<close> form to the more basic \<open>hn_refine\<close> form.
  It uses the theorems from @{attribute intf_of_assn} to add interface type declarations
  for the generated operands. The final result is massaged by rewriting with
  @{attribute to_hnr_post}, and then with @{attribute sepref_preproc}.

  Moreover, this phase ensures that there is a constraint slot goal (see section on constraints).
\<close>

text \<open>The method @{method sepref_dbg_preproc} gives direct access to the preprocessing phase.\<close>
thm sepref_preproc
thm intf_of_assn
thm to_hnr_post \<comment> \<open>Note: These rules are only instantiated for up to 5 arguments. 
  If you have functions with more arguments, you need to add corresponding theorems here!\<close>

subsubsection \<open>Consequence Rule  Phase\<close>
text \<open>This phase rewrites \<open>hn_invalid _ x y\<close> assertions in the postcondition to 
  \<open>hn_ctxt (\<lambda>_ _. true) x y\<close> assertions, which are trivial to discharge. 
  Then, it applies @{thm [source] CONS_init}, to make postcondition and 
  result relation schematic, and introduce (separation logic) implications to
  the originals, which are discharged after synthesis.
\<close>
text \<open>Use @{method sepref_dbg_cons_init} for direct access to this phase.
  The method @{method weaken_hnr_post} performs the rewriting of \<open>hn_invalid\<close>
  to \<open>\<lambda>_ _. true\<close> postconditions, and may be useful on its own for proving 
  combinator rules. 
\<close>

subsubsection \<open>Operation Identification Phase\<close>
text \<open>The purpose of this phase is to identify the conceptual operations in the given program.
  Consider, for example, a map @{term_type "m::'k\<rightharpoonup>'v"}. 
  If one writes @{term "m(k\<mapsto>v)"}, this is a map update. However, in Isabelle/HOL maps
  are encoded as functions @{typ "'k \<Rightarrow> 'v option"}, and the map update is just syntactic
  sugar for @{term [source] "fun_upd m k (Some v)"}. And, likewise, map lookup is just 
  function application.

  However, the Sepref tool must be able to distinguish between maps and functions into the
  option type, because maps shall be refined, to e.g., hash-tables, while functions into the
  option type shall be not. Consider, e.g., the term @{term "Some x"}. Shall \<open>Some\<close> be 
  interpreted as the constructor of the option datatype, or as a map, mapping each element to
  itself, and perhaps be implemented with a hashtable.
  
  Moreover, for technical reasons, the translation phase of Sepref expects each operation 
  to be a single constant applied to its operands. This criterion is neither matched by map 
  lookup (no constant, just application of the first to the second operand), nor map update 
  (complex expression, involving several constants).

  The operation identification phase uses a heuristics to find the conceptual types in a term
  (e.g., discriminate between map and function to option), and rewrite the operations to single 
  constants (e.g. @{const op_map_lookup} for map lookup). The heuristics is a type-inference 
  algorithm combined with rewriting. Note that the inferred conceptual type does not necessarily
  match the HOL type, nor does it have a semantic meaning, other than guiding the heuristics.

  The heuristics store a set of typing rules for constants, in @{attribute id_rules}.
  Moreover, it stores two sets of rewrite rules, in @{attribute pat_rules} 
  and @{attribute def_pat_rules}. A term is typed by first trying to apply a rewrite rule, and
  then applying standard Hindley-Milner type inference rules for application and abstraction. 
  Constants (and free variables) are typed
  using the \<open>id_rules\<close>. If no rule for a constant exists, one is inferred from the constant's 
  signature. This does not work for free variables, such that rules must be available
  for all free variables. Rewrite rules from \<open>pat_rules\<close> are backtracked over, while rewrite rules
  from \<open>def_pat_rules\<close> are always tried first and never backtracked over.
  
  If typing succeeds, the result is the rewritten term.

  For example, consider the type of maps. Their interface (or conceptual) type is 
  @{typ "('k,'v) i_map"}. The \<open>id_rule\<close> for map lookup is @{thm "op_map_lookup.itype"}.
  Moreover, there is a rule to rewrite function application to map lookup (@{thm pat_map_lookup}). 
  It can be backtracked over, such that also functions into the option type are possible.
\<close>
thm op_map_lookup.itype
thm pat_map_lookup
thm id_rules
text \<open>
  The operation identification phase, and all further phases, work on a tagged 
  version of the input term, where all function applications are replaced by the
  tagging constant @{term "($)"}, and all abstractions are replaced by 
  @{term "\<lambda>x. PROTECT2 (t x) DUMMY"} (syntax: @{term "\<lambda>x. (#t x#)"}, 
  input syntax: @{term "\<lambda>\<^sub>2x. t x"}). This is required to tame Isabelle's 
  higher-order unification. However, it makes tagged terms quite unreadable, and it
  may be helpful to \<open>unfold APP_def PROTECT2_def\<close> to get back the untagged form when inspecting
  internal states for debugging purposes.

  To prevent looping, rewrite-rules can use @{term "($')"} on the RHS. This is
  a synonym for @{term "($)"}, and gets rewritten to @{term "($)"} after the operation
  identification phase. During the operation identification phase, it prevents infinite
  loops of pattern rewrite rules.


  Interface type annotations can be added to the term using @{const CTYPE_ANNOT} 
  (syntax @{term "t:::\<^sub>iTYPE('a)"}).

  In many cases, it is desirable to treat complex terms as a single constant, 
  a standard example are constants defined inside locales, which may have locale 
  parameters attached. Those terms can be wrapped into an @{const PR_CONST} tag,
  which causes them to be treated like a single constant. Such constants must always 
  have \<open>id_rules\<close>, as the interface type inference from the signature does not apply here.
\<close>

subsubsection \<open>Troubleshooting Operation Identification\<close>
text \<open>
  If the operation identification fails, in most cases one has forgotten to register 
  an \<open>id_rule\<close> for a free variable or complex \<open>PR_CONST\<close> constant, or the identification 
  rule is malformed. Note that, in practice, identification rules are registered by 
  the @{command sepref_register} (see below), which catches many malformed rules, and
  handles \<open>PR_CONST\<close> tagging automatically. Another frequent source of errors here is 
  forgetting to register a constant with a conceptual type other than its signature. 
  In this case, operation identification gets stuck trying to unify the signature's type with
  the interface type, e.g., @{typ "'k \<Rightarrow> 'v option"} with @{typ "('k,'v)i_map"}.

  The method @{method sepref_dbg_id} invokes the id-phase in isolation.
  The method @{method sepref_dbg_id_keep} returns the internal state where type 
  inference got stuck. It returns a sequence of all stuck states, which can be inspected
  using @{command back}. 

  The methods @{method sepref_dbg_id_init},@{method sepref_dbg_id_step}, 
  and @{method sepref_dbg_id_solve} can be used to single-step the operation 
  identification phase. Here, solve applies single steps until the current subgoal is discharged.
  Be aware that application of single steps allows no automatic backtracking, such that backtracking
  has to be done manually.
\<close>

text \<open>Examples for identification errors\<close>
context 
  fixes N::nat 
  notes [sepref_import_param] = IdI[of N]
begin
  sepref_thm N_plus_2_example is "uncurry0 (RETURN (N+2))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    apply sepref_dbg_keep
    apply sepref_dbg_id_keep
    \<comment> \<open>Forgot to register \<open>n\<close>\<close>
    oops

  text \<open>Solution: Register \<open>n\<close>, be careful not to export meaningless registrations from context!\<close>
  context
    notes [[sepref_register_adhoc N]]
  begin
    sepref_thm N_plus_2_example is "uncurry0 (RETURN (N+2))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" by sepref
  end  
end

definition "my_map \<equiv> op_map_empty"
lemmas [sepref_fr_rules] = hm.empty_hnr[folded my_map_def]

sepref_thm my_map_example is "uncurry0 (RETURN (my_map(False\<mapsto>1)))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hm.assn bool_assn nat_assn"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  \<comment> \<open>Stuck at refinement for function update on map\<close>
  oops

text \<open>Solution: Register with correct interface type\<close>
sepref_register my_map :: "('k,'v) i_map"
sepref_thm my_map_example is "uncurry0 (RETURN (my_map(False\<mapsto>1)))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hm.assn bool_assn nat_assn"
  by sepref


subsubsection \<open>Monadify Phase\<close>
text \<open>
  The monadify phase rewrites the program such that every operation becomes 
  visible on the monad level, that is, nested HOL-expressions are flattened.
  Also combinators (e.g. if, fold, case) may get flattened, if special rules 
  are registered for that.

  Moreover, the monadify phase fixes the number of operands applied to an operation,
  using eta-expansion to add missing operands. 

  Finally, the monadify phase handles duplicate parameters to an operation, by
  inserting a @{const COPY} tag. This is necessary as our tool expects the 
  parameters of a function to be separate, even for read-only 
  parameters@{footnote \<open>Using fractional permissions or some other more fine grained
    ownership model might lift this restriction in the future.\<close>}. 
\<close>

text \<open>The monadify phase consists of a number of sub-phases.
  The method @{method sepref_dbg_monadify} executes the monadify phase,
  the method @{method sepref_dbg_monadify_keep} stops at a failing sub-phase
  and presents the internal goal state before the failing sub-phase.
\<close>

subsubsection \<open>Monadify: Arity\<close>
text \<open>In the first sub-phase, the rules from @{attribute sepref_monadify_arity} 
  are used to standardize the number of operands applied to a constant.
  The rules work by rewriting each constant to a lambda-expression with the 
  desired number of arguments, and the using beta-reduction to account for
  already existing arguments. Also higher-order arguments can be enforced,
  for example, the rule for fold enforces three arguments, the function itself
  having two arguments (@{thm fold_arity}).

  In order to prevent arity rules being applied infinitely often, 
  the @{const SP} tag can be used on the RHS. It prevents anything inside 
  from being changed, and gets removed after the arity step.

  The method @{method sepref_dbg_monadify_arity} gives you direct access to this phase.

  In the Sepref-tool, we use the terminology @{emph \<open>operator/operation\<close>} for a function that
  only has first-order arguments, which are evaluated before the function is applied (e.g. @{term "(+)"}),
  and @{emph \<open>combinator\<close>} for operations with higher-order arguments or custom 
  evaluation orders (e.g. @{term "fold"}, @{term "If"}).

  Note: In practice, most arity (and combinator) rules are declared automatically
    by @{command sepref_register} or @{command sepref_decl_op}. Manual declaration
    is only required for higher-order functions.
\<close>
thm sepref_monadify_arity

subsubsection \<open>Monadify: Combinators\<close>
text \<open>The second sub-phase flattens the term. 
  It has a rule for every function into @{typ "_ nres"} type, that determines
  the evaluation order of the arguments. First-order arguments are evaluated before
  an operation is applied. Higher-order arguments are treated specially, as they
  are evaluated during executing the (combinator) operation. The rules are in
  @{attribute sepref_monadify_comb}.

  Evaluation of plain (non-monadic) terms is triggered by wrapping them into
  the @{const EVAL} tag. The @{attribute sepref_monadify_comb} rules may also contain
  rewrite-rules for the @{const EVAL} tag, for example to unfold plain combinators
  into the monad (e.g. @{thm dflt_plain_comb}). If no such rule applies, the 
  default method is to interpret the head of the term as a function, and recursively
  evaluate the arguments, using left-to-right evaluation order. The head of 
  a term inside @{const EVAL} must not be an abstraction. Otherwise, the 
  @{const EVAL} tag remains in the term, and the next sub-phase detects this 
  and fails.

  The method @{method sepref_dbg_monadify_comb} executes the combinator-phase 
  in isolation.
\<close>

subsubsection \<open>Monadify: Check-Eval\<close>
text \<open>This phase just checks for remaining @{const EVAL} tags in the term,
  and fails if there are such tags. The method @{method sepref_dbg_monadify_check_EVAL}
  gives direct access to this phase.

  Remaining @{const EVAL} tags indicate
  higher-order functions without an appropriate setup of the combinator-rules
  being used. For example:
\<close>
definition "my_fold \<equiv> fold"
sepref_thm my_fold_test is "\<lambda>l. do { RETURN (my_fold (\<lambda>x y. x+y*2) l 0)}" :: "(list_assn nat_assn)\<^sup>k\<rightarrow>\<^sub>anat_assn"
  apply sepref_dbg_keep
  apply sepref_dbg_monadify_keep
  \<comment> \<open>An \<open>EVAL\<close>-tag with an abstraction remains. This is b/c the default heuristics
    tries to interpret the function inside the fold as a plain value argument.\<close>
  oops

text \<open>Solution: Register appropriate arity and combinator-rules\<close>
lemma my_fold_arity[sepref_monadify_arity]: "my_fold \<equiv> \<lambda>\<^sub>2f l s. SP my_fold$(\<lambda>\<^sub>2x s. f$x$s)$l$s" by auto

text \<open>The combinator-rule rewrites to the already existing and set up combinator @{term nfoldli}:\<close>
lemma monadify_plain_my_fold[sepref_monadify_comb]: 
  "EVAL$(my_fold$(\<lambda>\<^sub>2x s. f x s)$l$s) \<equiv> (\<bind>)$(EVAL$l)$(\<lambda>\<^sub>2l. (\<bind>)$(EVAL$s)$(\<lambda>\<^sub>2s. nfoldli$l$(\<lambda>\<^sub>2_. True)$(\<lambda>\<^sub>2x s. EVAL$(f x s))$s))"
  by (simp add: fold_eq_nfoldli my_fold_def)

sepref_thm my_fold_test is "\<lambda>l. do { RETURN (my_fold (\<lambda>x y. x+y*2) l 0)}" :: "(list_assn nat_assn)\<^sup>k\<rightarrow>\<^sub>anat_assn"
  by sepref

subsubsection \<open>Monadify: Dup\<close>
text \<open>The last three phases, \<open>mark_params\<close>, \<open>dup\<close>, \<open>remove_pass\<close> are to detect 
  duplicate parameters, and insert \<open>COPY\<close> tags. 
  The first phase, \<open>mark_params\<close>, adds @{const PASS} tags around all parameters.
  Parameters are bound variables and terms that have a refinement in the 
  precondition.

  The second phase detects duplicate parameters and inserts @{const COPY} tags
  to remove them. Finally, the last phase removes the @{const PASS} tags again.

  The methods @{method sepref_dbg_monadify_mark_params}, 
  @{method sepref_dbg_monadify_dup}, and @{method sepref_dbg_monadify_remove_pass}
  gives you access to these phases.
\<close>

subsubsection \<open>Monadify: Step-Through Example\<close>
text \<open>
  We give an annotated example of the monadify phase.
  Note that the program utilizes a few features of monadify:
    \<^item> The fold function is higher-order, and gets flattened
    \<^item> The first argument to fold is eta-contracted. The missing argument is added.
    \<^item> The multiplication uses the same argument twice. A copy-tag is inserted.
\<close>
sepref_thm monadify_step_thru_test is "\<lambda>l. do {
    let i = length l;
    RETURN (fold (\<lambda>x. (+) (x*x)) l i)
  }" :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id

  apply sepref_dbg_monadify_arity \<comment> \<open>Second operand of fold-function is added\<close>
  apply sepref_dbg_monadify_comb \<comment> \<open>Flattened. \<open>fold\<close> rewritten to \<open>monadic_nfoldli\<close>.\<close>
  (*apply (unfold APP_def PROTECT2_def) (* Make term readable for inspection*) *)
  apply sepref_dbg_monadify_check_EVAL \<comment> \<open>No \<open>EVAL\<close> tags left\<close>
  apply sepref_dbg_monadify_mark_params \<comment> \<open>Parameters marked by \<open>PASS\<close>. Note the multiplication \<open>x*x\<close>.\<close>
  (*apply (unfold APP_def PROTECT2_def) (* Make term readable for inspection*) *)
  apply sepref_dbg_monadify_dup \<comment> \<open>\<open>COPY\<close> tag inserted.\<close>
  (*apply (unfold APP_def PROTECT2_def) (* Make term readable for inspection*) *)
  apply sepref_dbg_monadify_remove_pass \<comment> \<open>\<open>PASS\<close> tag removed again\<close>
  (*apply (unfold APP_def PROTECT2_def) (* Make term readable for inspection*) *)
  
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

subsubsection \<open>Optimization Init Phase\<close>
text \<open>This phase, accessed by @{method sepref_dbg_opt_init}, just applies the 
  rule @{thm TRANS_init} to set up a subgoal for a-posteriori optimization\<close>

subsubsection \<open>Translation Phase\<close>
text \<open>
  The translation phase is the main phase of the Sepref tool. 
  It performs the actual synthesis of the imperative program from
  the abstract one. For this, it integrates various components, among others,
  a frame inference tool, a semantic side-condition solver and a monotonicity prover.

  The translation phase consists of two major sub-phases: 
  Application of translation rules and solving of deferred constraints.

  The method @{method sepref_dbg_trans} executes the translation phase,
  @{method sepref_dbg_trans_keep} executes the translation phase, 
  presenting the internal goal state of a failed sub-phase.

  The translation rule phase repeatedly applies translation steps, until the 
  subgoal is completely solved. 

  The main idea of the translation phase is, that for every abstract variable \<open>x\<close> in scope,
  the precondition contains an assertion of the form @{term "hn_ctxt A x xi"}, indicating how
  this variable is implemented. Common abbreviations are 
  @{term "hn_val R x xi \<equiv> hn_ctxt (pure R) x xi"} 
  and @{term "hn_invalid A x xi \<equiv> hn_ctxt (invalid_assn A) x xi"}.
\<close>

subsubsection \<open>Translation: Step\<close>
text \<open>
  A translation step applies a single synthesis step for an operator,
  or solves a deferred side-condition. 

  There are two types of translation steps: Combinator steps and operator steps.
  A combinator step consists of applying a rule from @{attribute sepref_comb_rules}
  to the goal-state. If no such rule applies, the rules are tried again after rewriting
  the precondition with @{attribute sepref_frame_normrel_eqs} (see frame-inference).
  The premises of the combinator rule become new subgoals, which are solved by 
  subsequent steps. No backtracking is applied over combinator rules. 
  This restriction has been introduced to make the tool more deterministic, and hence
  more manageable. 

  An operator step applies an operator rule (from @{attribute sepref_fr_rules}) 
  with frame-inference, and then tries to solve the resulting side conditions 
  immediately. If not all side-conditions can be solved, it backtracks over the 
  application of the operator rule. 

  Note that, currently, side conditions to operator rules cannot contain 
  synthesis goals themselves. Again, this restriction reduces the tool's 
  complexity by avoiding deep nesting of synthesis. However, it hinders
  the important feature of generic algorithms, where an operation can issue 
  synthesis subgoals for required operations it is built from (E.g., set union
  can be implemented by insert and iteration). Our predecessor tool, Autoref,
  makes heavy use of this feature, and we consider dropping the restriction in 
  the near future.

  An operator-step itself consists of several sub-phases:
  \<^descr>[Align goal] Splits the precondition into the arguments actually occurring in
    the operation, and the rest (called frame).
  \<^descr>[Frame rule] Applies a frame rule to focus on the actual arguments. Moreover,
    it inserts a subgoal of the form @{term "RECOVER_PURE \<Gamma> \<Gamma>'"}, which is used 
    to restore invalidated arguments if possible. Finally, it generates an assumption
    of the form @{term "vassn_tag \<Gamma>'"}, which means that the precondition holds
    on some heap. This assumption is used to extract semantic information from the 
    precondition during side-condition solving.

  \<^descr>[Recover pure] This phase tries to recover invalidated arguments. 
    An invalidated argument is one that has been destroyed by a previous operation.
    It occurs in the precondition as @{term "hn_invalid A x xi"}, which indicates
    that there exists a heap where the refinement holds. However, if the refinement 
    assertion \<open>A\<close> does not depend on the heap (is \<^emph>\<open>pure\<close>), the invalidated argument
    can be recovered. The purity assumption is inserted as a constraint (see constraints),
    such that it can be deferred.
  \<^descr>[Apply rule] This phase applies a rule from @{attribute sepref_fr_rules} to
    the subgoal. If there is no matching rule, matching is retried after rewriting
    the precondition with @{attribute sepref_frame_normrel_eqs}. If this does not succeed
    either, a consequence rule is used on the precondition. The implication becomes an 
    additional side condition, which will be solved by the frame inference tool.

    To avoid too much backtracking, the new precondition
    is massaged to have the same structure as the old one, i.e., it contains a (now schematic)
    refinement assertion for each operand. This excludes rules for which the frame inference
    would fail anyway.

    If a matching rule is found, it is applied and all new subgoals are solved by the 
    side-condition solver. If this fails, the tool backtracks over the application of 
    the @{attribute sepref_fr_rules}-rules. Note that direct matches prevent precondition 
    simplification, and matches after precondition simplification prevent the consequence 
    rule to be applied.

  
  The method @{method sepref_dbg_trans_step} performs a single translation step.
  The method @{method sepref_dbg_trans_step_keep} presents the internal goal state 
  on failure. If it fails in the \<open>apply-rule\<close> phase, it presents the sequence of 
  states with partially unsolved side conditions for all matching rules. 
\<close>

subsubsection \<open>Translation: Side Conditions\<close>
text \<open>The side condition solver is used to discharge goals that arise as 
  side-conditions to the translation rules. It does a syntactic discrimination 
  of the side condition type, and then invokes the appropriate solver. Currently,
  it supports the following side conditions:
  \<^descr>[Merge] (\<open>_\<or>\<^sub>A_ \<Longrightarrow>\<^sub>t _\<close>). These are used to merge postconditions from different 
    branches of the program (e.g. after an if-then-else). They are solved by the 
    frame inference tool (see section on frame inference).
  \<^descr>[Frame] (\<open>_ \<Longrightarrow>\<^sub>t _\<close>). Used to match up the current precondition against the 
    precondition of the applied rule. Solved by the frame inference tool (see section on frame inference).
  \<^descr>[Independence] (\<open>INDEP (?R x\<^sub>1 \<dots> x\<^sub>n)\<close>). Deprecated. Used to instantiate a 
    schematic variable such that it does not depend on any bound variables any more. 
    Originally used to make goals more readable, we are considering of dropping this.
  \<^descr>[Constraints] (\<open>CONSTRAINT _ _\<close>) Apply solver for deferrable constraints (see section on constraints).
  \<^descr>[Monotonicity] (\<open>mono_Heap _\<close>) Apply monotonicity solver. Monotonicity subgoals occur when
    translating recursion combinators. Monadic expressions are monotonic by construction, and 
    this side-condition solver just forwards to the monotonicity prover of the partial 
    function package, after stripping any preconditions from the subgoal, which are 
    not supported by the case split mechanism of the monotonicity prover (as of Isabelle2016).
  \<^descr>[Prefer/Defer] (\<open>PREFER_tag _\<close>/\<open>DEFER_tag\<close>). Deprecated. Invoke the tagged solver of 
    the Autoref tool. Used historically for importing refinements from the Autoref tool,
    but as Sepref becomes more complete imports from Autoref are not required any more.
  \<^descr>[Resolve with Premise] \<open>RPREM _\<close> Resolve subgoal with one of its premises. 
    Used for translation of recursion combinators. 
  \<^descr>[Generic Algorithm] \<open>GEN_ALGO _ _\<close> Triggers resolution with a rule from
    @{attribute sepref_gen_algo_rules}. This is a poor-man's version of generic 
    algorithm, which is currently only used to synthesize to-list conversions for foreach-loops.
  \<^descr>[Fallback] (Any pattern not matching the above, nor being a \<open>hn_refine\<close> goal).
    Unfolds the application and abstraction tagging, as well as @{term bind_ref_tag} tags 
    which are inserted by several translation rules to indicate the value a variable has 
    been bound to, and then tries to solve the goal by @{method auto}, after freezing 
    schematic variables. This tactic is used to discharge semantic side conditions, e.g.,
    in-range conditions for array indexing. 


  Methods: @{method sepref_dbg_side} to apply a side-condition solving step,
    @{method sepref_dbg_side_unfold} to apply the unfolding of application and binding tags and 
    @{method sepref_dbg_side_keep} to return the internal state after failed side-condition solving.
\<close>

subsubsection \<open>Translation: Constraints\<close>
text \<open>During the translation phase, the refinement of operands is not 
  always known immediately, such that schematic variables may occur as refinement 
  assertions. Side conditions on those refinement assertions cannot be discharged 
  until the schematic variable gets instantiated. 

  Thus, side conditions may be tagged with @{const CONSTRAINT}. 
  If the side condition solver encounters a constraint side condition, it first removes
  the constraint tag (@{thm CONSTRAINT_I}) and freezes all schematic variables to prevent them from 
  accidentally getting instantiated. Then it simplifies with @{attribute constraint_simps} and
  tries to solve the goal using rules from 
  @{attribute safe_constraint_rules} (no backtracking) 
  and @{attribute constraint_rules} (with backtracking).

  If solving the constraint is not successful, only the safe rules are applied, and the 
  remaining subgoals are moved to a special \<open>CONSTRAINT_SLOT\<close> subgoal, that always is the 
  last subgoal, and is initialized by the preprocessing phase of Sepref.
  Moving the subgoal to the constraint slot looks for Isabelle's tacticals like the subgoal 
  has been solved. In reality, it is only deferred and must be solved later.
  
  Constraints are used in several phases of Sepref, and all constraints are solved
  at the end of the translation phase, and at the end of the Sepref invocation.
  
  Methods: 
    \<^item> @{method solve_constraint} to apply constraint solving, the @{const CONSTRAINT}-tag is optional.
    \<^item> @{method safe_constraint} to apply safe rules, the @{const CONSTRAINT}-tag is optional.
    \<^item> @{method print_slot} to print the contents of the constraint slot.

\<close>

subsubsection \<open>Translation: Merging and Frame Inference\<close>
text \<open>Frame inference solves goals of the form \<open>\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>'\<close>.
  For this, it matches \<open>hn_ctxt\<close> components in \<open>\<Gamma>'\<close> with those in \<open>\<Gamma>\<close>.
  Matching is done according to the refined variables. 
  The matching pairs and the rest is then treated differently: 
  The rest is resolved by repeatedly applying the rules from @{thm frame_rem_thms}.
  The matching pairs are resolved by repeatedly applying rules from 
  @{thm frame_thms} and @{attribute sepref_frame_match_rules}. 
  Any non-frame premise of these rules must be solved immediately by the 
  side-condition's constraint or fallback tactic (see above). The tool backtracks over rules.
  If no rule matches (or side-conditions cannot be solved), it simplifies the goal 
  with @{attribute sepref_frame_normrel_eqs} and tries again.

  For merge rules, the theorems @{thm merge_thms} 
  and @{attribute sepref_frame_merge_rules} are used.

  Note that a smart setup of frame and match rules together with side conditions makes 
  the frame matcher a powerful tool for encoding structural and semantic information 
  into relations. An example for structural information are the match rules for lists,
  which forward matching of list assertions to matching of the element assertions,
  maintaining the congruence assumption that the refined elements are actually elements 
  of the list: @{thm list_match_cong}.
  An example for semantic information is the bounded assertion, which intersects
  any given assertion with a predicate on the abstract domain. The frame matcher is 
  set up such that it can convert between bounded assertions, generating semantic 
  side conditions to discharge implications between bounds (@{thm b_assn_subtyping_match}). 

  This is essentially a subtyping mechanism on the level of refinement assertions,
  which is quite useful for maintaining natural side conditions on operands. 
  A standard example is to maintain a list of array indices: The refinement assertion 
  for array indices is @{term nat_assn} restricted to indices that are in range:
  @{term "nbn_assn N"}. When inserting natural numbers into this list, one has to 
  prove that they are actually in range (conversion from @{term nat_assn} to @{term nbn_assn}).
  Elements of the list can be used as natural numbers (conversion from @{term nbn_assn} 
  to @{term nat_assn}). Additionally, the side condition solver can derive that the predicate
  holds on the abstract variable (via the @{const vassn_tag} inserted by the operator steps). 
\<close>

subsubsection \<open>Translation: Annotated Example\<close>

context 
  fixes N::nat 
  notes [[sepref_register_adhoc N]]
  notes [sepref_import_param] = IdI[of N]
begin

text \<open>This worked example utilizes the following features of the translation phase:
  \<^item> We have a fold combinator, which gets translated by its combinator rule
  \<^item> We add a type annotation which enforces converting the natural numbers
    inserted into the list being refined by \<open>nbn_assn N\<close>, i.e., smaller than \<open>N\<close>.
  \<^item> We can only prove the numbers inserted into the list to be smaller than \<open>N\<close>  
    because the combinator rule for \<open>If\<close> inserts congruence assumptions.
  \<^item> By moving the elements from the list to the set, they get invalidated.
    However, as \<open>nat_assn\<close> is pure, they can be recovered later, allowing us to 
    mark the list argument as read-only.
\<close>

sepref_thm filter_N_test is "\<lambda>l. RETURN (fold (\<lambda>x s.
  if x<N then insert (ASSN_ANNOT (nbn_assn N) x) s else s
) l op_hs_empty)" :: "(list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a hs.assn (nbn_assn N)"

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  
  apply sepref_dbg_opt_init

  apply sepref_dbg_trans_step \<comment> \<open>Combinator rule for bind, 
    generating two \<open>hn_refine\<close> goals, and a frame rule to
    separate the bound variable from the rest.\<close>
  apply sepref_dbg_trans_step \<comment> \<open>Rule for empty hashset, solves goal\<close>
  apply sepref_dbg_trans_step \<comment> \<open>Combinator rule for nfoldli (@{thm hn_monadic_nfoldli_rl'})\<close>
    apply sepref_dbg_trans_step \<comment> \<open>INDEP\<close>
    apply sepref_dbg_trans_step \<comment> \<open>INDEP\<close>
    apply sepref_dbg_trans_step \<comment> \<open>Frame to get list and initial state\<close>
    apply sepref_dbg_trans_step \<comment> \<open>Refinement of continuation condition\<close>
    apply sepref_dbg_trans_step \<comment> \<open>Frame to recover state after continuation condition\<close>

    \<comment> \<open>Loop body\<close>
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    \<comment> \<open>At this point, we arrived at the \<open>nbn_rel\<close> annotation. 
      There is enough information to show \<open>x'a < N\<close>\<close>
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step
    \<comment> \<open>At this point, we have to merge the postconditions from the two if 
      branches. \<open>nat_rel\<close> gets merged with \<open>invalid_assn (nbn_assn n)\<close>, 
      yielding \<open>invalid_assn nat_assn\<close>\<close>
    apply sepref_dbg_trans_step
    apply sepref_dbg_trans_step \<comment> \<open>Frame rule separating bound variable from rest\<close>

    apply sepref_dbg_trans_step \<comment> \<open>Frame rule separating fold-state from rest\<close>
    apply sepref_dbg_trans_step \<comment> \<open>Merging elements of list before body 
      with elements of list after body, to get refinement for resulting list\<close>
    
    apply sepref_dbg_trans_step \<comment> \<open>Frame rule from initial bind, separating 
      bound variable from the rest\<close>

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
  done



end

subsubsection \<open>Optimization Phase\<close>
text \<open>The optimization phase simplifies the generated
  program, first with @{attribute sepref_opt_simps}, and
  then with @{attribute sepref_opt_simps2}. 
  For simplification, the tag @{const CNV} is used, which is discharged
  with @{thm CNV_I} after simplification. 

  Method @{method sepref_dbg_opt} gives direct access to this phase.
  The simplification is used to beautify the generated code.
  The most important simplifications collapse code that does not 
  depend on the heap to plain expressions (using the monad laws), and
  apply certain deforestation optimizations.
  
  Consider the following example:
\<close>

sepref_thm opt_example is "\<lambda>n. do { let r = fold (+) [1..<n] 0; RETURN (n*n+2) }"
  :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  \<comment> \<open>The generated program contains many superfluous binds, moreover, it actually 
    generates a list and then folds over it\<close>
  supply [[show_main_goal]]
  apply sepref_dbg_opt
  \<comment> \<open>The superfluous binds have been collapsed, and the fold over the list
    has been replaced by @{const imp_for'}, which uses a counter.\<close>
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

subsubsection \<open>Cons-Solve Phases\<close>
text \<open>These two phases, accessible via @{method sepref_dbg_cons_solve},
  applies the frame inference tool to solve the two implications generated
  by the consequence rule phase.
\<close>

subsubsection \<open>Constraints Phase\<close>
text \<open>
  This phase, accessible via @{method sepref_dbg_constraints}, solve the
  deferred constraints that are left, and then removes the \<open>CONSTRAINT_SLOT\<close> 
  subgoal.
\<close>

subsection \<open>Refinement Rules\<close>
text \<open>
  There are two forms of specifying refinement between an Imperative/HOL program
  and an abstract program in the \<open>nres\<close>-monad.
  The \<open>hn_refine\<close> form (also hnr-form) is the more low-level form.
  The term @{term "P \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"} states that, under precondition \<open>P\<close>, for 
  a heap described by \<open>\<Gamma>\<close>, the Imperative/HOL program \<open>c\<close> produces a heap described by 
  \<open>\<Gamma>'\<close> and the result is refined by \<open>R\<close>. Moreover, the abstract result is among the possible 
  results of the abstract program \<open>a\<close>.
  
  This low-level form formally enforces no restrictions on its arguments, however, there are
  some assumed by our tool:
    \<^item> \<open>\<Gamma>\<close> must have the form \<open>hn_ctxt A\<^sub>1 x\<^sub>1 xi\<^sub>1 * \<dots> * hn_ctxt A\<^sub>n x\<^sub>n xi\<^sub>n\<close>
    \<^item> \<open>\<Gamma>'\<close> must have the form \<open>hn_ctxt B\<^sub>1 x\<^sub>1 xi\<^sub>1 * \<dots> * hn_ctxt B\<^sub>n x\<^sub>n xi\<^sub>n\<close>
      where either \<open>B\<^sub>i = A\<^sub>i\<close> or \<open>B\<^sub>i = invalid_assn A\<^sub>i\<close>. This means that each argument to
      the program is either preserved or destroyed.
    \<^item> \<open>R\<close> must not contain a \<open>hn_ctxt\<close> tag.
    \<^item> \<open>a\<close> must be in protected form (@{term "($)"} and @{term "PROTECT2"} tags)

  The high-level \<open>hfref\<close> form formally enforces these restrictions. Moreover,
  it assumes \<open>c\<close> and \<open>a\<close> to be presented as functions from exactly one argument.
  For constants or functions with more arguments, you may use @{term uncurry0} 
  and @{term uncurry}. (Also available @{term uncurry2} to @{term uncurry5}).

  The general form is \<open>PC \<Longrightarrow> (uncurry\<^sub>x f, uncurry\<^sub>x g) \<in> [P]\<^sub>a A\<^sub>1\<^sup>k\<^sup>1 *\<^sub>a \<dots> *\<^sub>a A\<^sub>n\<^sup>k\<^sup>n \<rightarrow> R\<close>,
  where \<open>ki\<close> is \<open>k\<close> if the argument is preserved (kept) or \<open>d\<close> is it is destroyed.
  \<open>PC\<close> are preconditions of the rule that do not depend on the arguments, usually
  restrictions on the relations. \<open>P\<close> is a predicate on the single argument of \<open>g\<close>,
  representing the precondition that depends on the arguments.

  Optionally, \<open>g\<close> may be of the form \<open>RETURN o\<dots>o g'\<close>, in which case the rule 
  applies to a plain function.

  If there is no precondition, there is a shorter 
  syntax: @{term "Args\<rightarrow>\<^sub>aR \<equiv> [\<lambda>_. True]\<^sub>a Args\<rightarrow>R"}.

  For example, consider @{thm [source] arl_swap_hnr[unfolded pre_list_swap_def]}.
  It reads @{term "CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 arl_swap, uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_swap))
    \<in> [\<lambda>((l, i), j). i < length l \<and> j < length l]\<^sub>a 
    (arl_assn A)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> arl_assn A"}

  We have three arguments, the list and two indexes. The refinement assertion \<open>A\<close>
  for the list elements must be pure, and the indexes must be in range.
  The original list is destroyed, the indexes are kept.
\<close>
thm arl_swap_hnr[unfolded pre_list_swap_def, no_vars]

subsubsection \<open>Converting between hfref and hnr form\<close>
text \<open>A subgoal in hfref form is converted to hnr form by
  the preprocessing phase of Sepref (see there for a description).

  Theorems with hnr/hfref conclusions can be converted
  using @{attribute to_hfref}/@{attribute to_hnr}.
  This conversion is automatically done for rules registered with 
  @{attribute sepref_fr_rules}, such that this attribute accepts both forms.

  Conversion to hnr-form can be controlled by specifying 
  @{attribute to_hnr_post} unfold-rules, which are applied after the conversion.

  Note: These currently contain hard-coded rules to handle \<open>RETURN o\<dots>o _\<close> for up 
    to six arguments. If you have more arguments, you need to add corresponding rules here,
    until this issue is fixed and the tool can produce such rules automatically.
    
  Similarly, @{attribute to_hfref_post} is applied after conversion to hfref form.
\<close>

thm to_hnr_post
thm to_hfref_post

subsubsection \<open>Importing Parametricity Theorems\<close>
text \<open>For pure refinements, it is sometimes simpler to specify a parametricity 
  theorem than a hnr/hfref theorem, in particular as there is a large number of 
  parametricity theorems readily available, in the parametricity component or Autoref,
  and in the Lifting/Transfer tool.
  
  Autoref uses a set-based notation for parametricity theorems 
  (e.g. @{term "((@),(@)) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"}), 
  while lifting/transfer uses a predicate based notation (e.g. 
    @{term "rel_fun (list_all2 A) (rel_fun (list_all2 A) (list_all2 A)) (@) (@)"}).

  Currently, we only support the Autoref style, but provide a few lemmas that 
  ease manual conversion from the Lifting/Transfer style.

  Given a parametricity theorem, the attribute @{attribute sepref_param}
  converts it to a hfref theorem, the attribute 
  @{attribute sepref_import_param} does the conversion and registers the result
  as operator rule.
  Relation variables are converted to assertion variables with an \<open>is_pure\<close> constraint.

  The behaviour can be customized by @{attribute sepref_import_rewrite}, which
  contains rewrite rules applied in the last but one step of the conversion, before
  converting relation variables to assertion variables. 
  These theorems can be used to convert relations to there corresponding assertions,
  e.g., @{thm list_assn_pure_conv[symmetric]} converts a list relation to a list 
  assertion.


  For debugging purposes, the attribute @{attribute sepref_dbg_import_rl_only}
  converts a parametricity theorem to a hnr-theorem. This is the first step of 
  the standard conversion, followed by a conversion to hfref form.
\<close>

thm sepref_import_rewrite
thm param_append \<comment> \<open>Parametricity theorem for append\<close>
thm param_append[sepref_param] \<comment> \<open>Converted to hfref-form. 
  \<open>list_rel\<close> is rewritten to \<open>list_assn\<close>, and the relation variable is replaced by an 
  assertion variable and a \<open>is_pure\<close> constraint.\<close>
thm param_append[sepref_dbg_import_rl_only]


text \<open>For re-using Lifting/Transfer style theorems, the constants 
  @{const p2rel} and @{const rel2p} may be helpful, however, there is no
  automation available yet.

  Usage examples can be found in, e.g., @{theory Refine_Imperative_HOL.IICF_Multiset}, where we 
  import parametricity lemmas for multisets from the Lifting/Transfer package.
\<close>

thm p2rel \<comment> \<open>Simp rules to convert predicate to relational style\<close>
thm rel2p \<comment> \<open>Simp rules to convert relational to predicate style\<close>


subsection \<open>Composition\<close>

subsubsection \<open>Fref-Rules\<close>
text \<open>
  In standard parametricity theorems as described above, one cannot specify
  preconditions for the parameters, e.g., @{term hd} is only parametric for 
  non-empty lists. 

  As of Isabelle2016, the Lifting/Transfer package cannot specify
  such preconditions at all.

  Autoref's parametricity tool can specify such preconditions by using first-order rules,
  (cf. @{thm param_hd}). However, currently, @{attribute sepref_import_param} cannot handle 
  these first-order rules. 

  Instead, Sepref supports the fref-format for parametricity rules, which resembles the 
  hfref-format: Abstract and concrete objects are functions with exactly one parameter, 
  uncurried if necessary. Moreover, there is an explicit precondition.
  The syntax is \<open>(uncurry\<^sub>x f, uncurry\<^sub>x g) \<in> [P]\<^sub>f (...(R\<^sub>1\<times>\<^sub>rR\<^sub>2)\<times>\<^sub>r...)\<times>\<^sub>rR\<^sub>n) \<rightarrow> R\<close>,
  and without precondition, we have \<open>(...(R\<^sub>1\<times>\<^sub>rR\<^sub>2)\<times>\<^sub>r...)\<times>\<^sub>rR\<^sub>n) \<rightarrow>\<^sub>f R\<close>. 
  Note the left-bracketing of the tuples, which is non-standard in Isabelle.
  As we currently have no syntax for a left-associative product relation, we
  use the right-associative syntax @{term "(\<times>\<^sub>r)"} and explicit brackets.

  The attribute @{attribute to_fref} can convert (higher-order form) parametricity 
  theorems to the fref-form.
\<close>

subsubsection \<open>Composition of hfref and fref theorems\<close>
text \<open>
  fref and hfref theorems can be composed, if the 
  abstract function or the first theorem equals the concrete function of the 
  second theorem. Currently, we can compose an hfref with an fref theorem, 
  yielding a hfref theorem, and two fref-theorems, yielding an fref theorem.
  As we do not support refinement of heap-programs, but only refinement \<^emph>\<open>into\<close> heap 
  programs, we cannot compose two hfref theorems.

  The attribute @{attribute FCOMP} does these compositions and normalizes the result.
  Normalization consists of precondition simplification, and distributing composition
  over products, such that composition can be done argument-wise. 
  For this, we unfold with @{attribute fcomp_norm_unfold}, and then simplify with
  @{attribute fcomp_norm_simps}.

  The \<open>FCOMP\<close> attribute tries to convert its arguments to hfref/fref form, such that
  it also accepts hnr-rules and parametricity rules.

  The standard use-case for \<open>FCOMP\<close> is to compose multiple refinement steps to
  get the final correctness theorem. Examples for this are in the quickstart guide.

  Another use-case for \<open>FCOMP\<close> is to compose a refinement theorem of a 
  container operation, that refines the elements by identity, with a parametricity theorem
  for the container operation, that adds a (pure) refinement of the elements.
  In practice, the high-level utilities @{command sepref_decl_op} and 
  @{command sepref_decl_impl} are used for this purpose. Internally, they use \<open>FCOMP\<close>.
\<close>

thm fcomp_norm_unfold
thm fcomp_norm_simps

thm array_get_hnr_aux \<comment> \<open>Array indexing, array elements are refined by identity\<close>
thm "op_list_get.fref" \<comment> \<open>Parametricity theorem for list indexing\<close>

thm array_get_hnr_aux[FCOMP op_list_get.fref] \<comment> \<open>Composed theorem\<close>

\<comment> \<open>Note the definition @{thm array_assn_def}\<close>
context
  notes [fcomp_norm_unfold] = array_assn_def[symmetric]
begin
  thm array_get_hnr_aux[FCOMP op_list_get.fref] \<comment> \<open>Composed theorem, \<open>array_assn\<close> folded.\<close>
end

subsection \<open>Registration of Interface Types\<close>
text \<open>
  An interface type represents some conceptual type, which is encoded to a 
  more complex type in HOL. For example, the interface type @{typ "('k,'v)i_map"}
  represents maps, which are encoded as @{typ "'k \<Rightarrow> 'v option"} in HOL.

  New interface types must be registered by the command @{command sepref_decl_intf}.
\<close>

sepref_decl_intf ('a,'b) i_my_intf is "'a*'a \<Rightarrow> 'b option"
\<comment> \<open>Declares @{typ "('a,'b) i_my_intf"} as new interface type, and registers it
  to correspond to @{typ "'a*'a \<Rightarrow> 'b option"}. 
  Note: For HOL, the interface type is just an arbitrary new type, which is 
    not related to he corresponding HOL type.\<close>

sepref_decl_intf ('a,'b) i_my_intf2 (infix "*\<rightarrow>\<^sub>i" 0) is "'a*'a \<Rightarrow> 'b option"
\<comment> \<open>There is also a version that declares infix-syntax for the interface type.
  In this case we have @{typ "'a *\<rightarrow>\<^sub>i 'b"}. @{typ "'a\<rightharpoonup>'b"}
  Be aware of syntax space pollution, as the syntax for interface types and 
  HOL types is the same.\<close>



subsection \<open>Registration of Abstract Operations\<close>
text \<open>
  Registering a new abstract operation requires some amount of setup,
  which is automated by the \<open>sepref_register\<close> tool. Currently, it only 
  works for operations, not for combinators. 

  The @{command sepref_register} command takes a list of terms and registers 
  them as operators. Optionally, each term can have an interface type annotation. 

  If there is no interface type annotation, the interface type is derived from the 
  terms HOL type, which is rewritten by the theorems from @{attribute map_type_eqs}.
  This rewriting is useful for bulk-setup of many constants with conceptual types 
  different from there HOL-types. 
  Note that the interface type must correspond to the HOL type of the registered term,
  otherwise, you'll get an error message.

  If the term is not a single constant or variable, and does not already start 
  with a @{const PR_CONST} tag, such a tag will be added, and also a pattern rule 
  will be registered to add the tag on operator identification.
  
  If the term has a monadic result type (@{typ "_ nres"}), also an 
  arity and combinator rule for the monadify phase are generated.

  There is also an attribute version @{attribute "sepref_register_adhoc"}.
  It has the same syntax, and generates the same theorems, but does not give
  names to the theorems. It's main application is to conveniently register fixed
  variables of a context. Warning: Make sure not to export such an attribute from 
  the context, as it may become meaningless outside the context, or worse, confuse 
  the tool.
\<close>

text \<open>Example for bulk-registration, utilizing type-rewriting\<close>

definition "map_op1 m n \<equiv> m(n\<mapsto>n+1)"
definition "map_op2 m n \<equiv> m(n\<mapsto>n+2)"
definition "map_op3 m n \<equiv> m(n\<mapsto>n+3)"
definition "map_op_to_map (m::'a\<rightharpoonup>'b) \<equiv> m"

context
  notes [map_type_eqs] = map_type_eqI[of "TYPE('a\<rightharpoonup>'b)" "TYPE(('a,'b)i_map)"]
begin
  sepref_register map_op1 map_op2 map_op3 
  \<comment> \<open>Registered interface types use \<open>i_map\<close>\<close>
  sepref_register map_op_to_map :: "('a\<rightharpoonup>'b) \<Rightarrow> ('a,'b) i_map"
  \<comment> \<open>Explicit type annotation is not rewritten\<close>
end

text \<open>Example for insertion of \<open>PR_CONST\<close> tag and attribute-version\<close>

context
  fixes N :: nat and D :: int
  notes [[sepref_register_adhoc N D]]
  \<comment> \<open>In order to use \<open>N\<close> and \<open>D\<close> as operators (constant) inside this context,
    they have to be registered. However, issuing a \<open>sepref_register\<close> command 
    inside the context would export meaningless registrations to the global 
    theory.\<close>

  notes [sepref_import_param] = IdI[of N] IdI[of D]
  \<comment> \<open>For declaring refinement rules, the \<open>sepref_import_param\<close> attribute comes 
    in handy here. If this is not possible, you have to work with nested contexts,
    proving the refinement lemmas in the first level, and declaring them as
    \<open>sepref_fr_rules\<close> on the second level.\<close>

begin
  definition "newlist \<equiv> replicate N D"

  sepref_register newlist
  print_theorems
  \<comment> \<open>\<open>PR_CONST\<close> tag is added, pattern rule is generated\<close>

  sepref_register other_basename_newlist: newlist
  print_theorems
  \<comment> \<open>The base name for the generated theorems can be overridden\<close>

  sepref_register yet_another_basename_newlist: "PR_CONST newlist"
  print_theorems
  \<comment> \<open>If \<open>PR_CONST\<close> tag is specified, no pattern rule is generated automatically\<close>

end

text \<open>Example for mcomb/arity theorems\<close>
definition "select_a_one l \<equiv> SPEC (\<lambda>i. i<length l \<and> l!i = (1::nat))"

sepref_register "select_a_one"
  print_theorems
  \<comment> \<open>Arity and mcomb theorem is generated\<close>


text \<open>
  The following command fails, as the specified interface type does not
  correspond to the HOL type of the term:
  @{theory_text \<open>sepref_register hd :: "(nat,nat) i_map"\<close>}
\<close>

subsection \<open>High-Level tools for Interface/Implementation Declaration\<close>
text \<open>
  The Imperative Isabelle Collections Framework (IICF), which comes with Sepref,
  has a concept of interfaces, which specify a set of abstract operations for
  a conceptual type, and implementations, which implement these operations.
  
  Each operation may have a natural precondition, which is established already 
  for the abstract operation. Many operations come in a plain version, and a 
  monadic version which asserts the precondition. Implementations may 
  strengthen the precondition with implementation specific preconditions.

  Moreover, each operation comes with a parametricity lemma. 
  When registering an implementation, the refinement of the implementation is
  combined with the parametricity lemma to allow for (pure) refinements of the 
  element types.

  @{rail \<open>@@{command sepref_decl_op} ('(' @{text flags} ')')? \<newline>
      (@{text name} @':')?  @{text term} @'::' @{text term} \<newline>
      (@'where' @{text props})? \<close>}  
  
  The command @{command sepref_decl_op} declares an abstract operation.
  It takes a term defining the operation, and a parametricity relation.
  It generates the monadic version from the plain version, defines constants
  for the operations, registers them, and tries to prove parametricity lemmas
  automatically. Parametricity must be proved for the operation, and for the 
  precondition. If the automatic parametricity proofs fail, the user gets 
  presented goals that can be proven manually.

  Optionally, a basename for the operation can be specified. If none is specified, 
  a heuristics tries to derive one from the specified term.

  A list of properties (separated by space and/or \<open>and\<close>) can be specified, 
  which get constraint-preconditions of the relation. 

  Finally, the following flags can be specified. Each flag can be prefixed by \<open>no_\<close> 
  to invert its meaning:
  \<^descr>[mop] (default: true) Generate monadic version of operation
  \<^descr>[ismop] (default: false) Indicate that given term is the monadic version
  \<^descr>[rawgoals] (default: false) Present raw goals to user, without attempting to prove them
  \<^descr>[def] (default: true) Define a constant for the specified term. Otherwise, use the specified term literally.

\<close>

text \<open>
  
  @{rail \<open>@@{command sepref_decl_impl} ('(' @{text flags} ')')? \<newline>
    (@{text name} @':')? (@'[' @{text term} @']')? \<newline>
    @{text thm} (@'uses' @{text thm})?
    \<close>}  

  The @{command sepref_decl_impl} command declares an implementation of an interface operation.
  It takes a refinement theorem for the implementation, and combines it with the corresponding
  parametricity theorem. After \<open>uses\<close>, one can override the parametricity theorem to be used.
  A heuristics is used to merge the preconditions of the refinement and parametricity theorem.
  This heuristics can be overridden by specifiying the desired precondition inside \<open>[\<dots>]\<close>.
  Finally, the user gets presented remaining subgoals that cannot be solved by the heuristics.
  The command accepts the following flags:
  \<^descr>[mop] (default: true) Generate implementation for monadic version
  \<^descr>[ismop] (default: false) Declare that the given theorems refer to the monadic version
  \<^descr>[transfer] (default: true) Try to automatically transfer the implementation's precondition
    over the argument relation from the parametricity theorem.
  \<^descr>[rawgoals] (default: false) Do not attempt to solve or simplify the goals
  \<^descr>[register] (default: true) Register the generated theorems as operation rules. 
\<close>

subsection \<open>Defining synthesized Constants\<close>
text \<open>
  The @{command sepref_definition} allows one to specify a name, an abstract term and
  a desired refinement relation in hfref-form. It then sets up a goal that can be
  massaged (usually, constants are unfolded and annotations/implementation specific 
  operations are added) and then solved by @{method sepref}.
  After the goal is solved, the command extracts the synthesized term and defines it as
  a constant with the specified name. Moreover, it sets up code equations for the constant,
  correctly handling recursion combinators. Extraction of code equations is controlled by the
  \<open>prep_code\<close> flag. Examples for this command can be found in the quickstart guide.
\<close>

end
