section \<open>Quickstart Guide\<close>
theory Quickstart_Guide
imports "../IMP2"
begin

  subsection \<open>Introductory Examples\<close>
  text \<open>IMP2 provides commands to define program snippets or procedures together with their specification.\<close>

  procedure_spec div_ab (a,b) returns c 
    assumes \<open>b\<noteq>0\<close> 
    ensures \<open>c=a\<^sub>0 div b\<^sub>0\<close> 
    defines \<open>c = a/b\<close>
    by vcg_cs
  
  text \<open>The specification consists of the signature (name, parameters, return variables),
    precondition, postcondition, and program text.\<close>  
    
  text \<open>
    \<^descr>[Signature] The procedure name and variable names must be valid Isabelle names. 
      The \<open>returns\<close> declaration is optional, by default, nothing is returned. 
      Multiple values can be returned by \<open>returns (x\<^sub>1,...,x\<^sub>n)\<close>.
      
    \<^descr>[Precondition] An Isabelle formula. Parameter names are valid variables.
    \<^descr>[Postcondition] An Isabelle formula over the return variables, and parameter names suffixed with \<open>\<^sub>0\<close>.
    \<^descr>[Program Text] The procedure body, in a C-like syntax.
  \<close>  
    
  text \<open>The @{command procedure_spec} command will open a proof to show that the program satisfies the specification.
    The default way of discharging this goal is by using IMP2's verification condition generator, followed by
    manual discharging of the generated VCs as necessary.
    
    Note that the @{method vcg_cs} method will apply @{method clarsimp} to all generated VCs, which, in our case,
    already solves them. You can use @{method vcg} to get the raw VCs.
  \<close>
  
  text \<open>If the VCs have been discharged, @{command procedure_spec} adds prologue and epilogue code 
    for parameter passing, defines a constant for the procedure, and lifts the pre- and postcondition  
    over the constant definition.
  \<close>
  thm div_ab_spec \<comment> \<open>Final theorem proved\<close>
  thm div_ab_def  \<comment> \<open>Constant definition, with parameter passing code\<close>
    
  text \<open>The final theorem has the form \<^term>\<open>HT_mods \<pi> vs P c Q\<close>,
    where \<open>\<pi>\<close> is an arbitrary procedure environment, 
    \<open>vs\<close> is a syntactic approximation of the (global) variables modified by the procedure,
    \<open>P,Q\<close> are the pre- and postcondition, lifted over the parameter passing code,
    and \<open>c\<close> is the defined constant for the procedure. 
  
    The precondition is a function \<^typ>\<open>state\<Rightarrow>bool\<close>. It starts with a series of variable bindings 
    that map program variables to logical variables,
    followed by precondition that was specified, wrapped in a \<^const>\<open>BB_PROTECT\<close> constant, 
    which serves as a tag for the VCG, and is defined as the identity (@{thm BB_PROTECT_def}).
    
    The final theorem is declared to the VCG, such that the specification will be 
    used automatically for calls to this procedure.
  \<close>
  
  procedure_spec use_div_ab(a) returns r assumes \<open>a\<noteq>0\<close> ensures \<open>r=1\<close> defines \<open>r = div_ab(a,a)\<close> by vcg_cs
  
  
  subsubsection \<open>Variant and Invariant Annotations\<close>
  
  text \<open>Loops must be annotated with variants and invariants.\<close>
  procedure_spec mult_ab(a,b) returns c assumes \<open>True\<close> ensures "c=a\<^sub>0*b\<^sub>0"
  defines \<open>
    if (a<0) {a = -a; b = -b};
    c=0;
    while (a>0) 
      @variant \<open>a\<close>
      @invariant \<open>0\<le>a \<and> a\<le>\<bar>a\<^sub>0\<bar> \<and> c = ( \<bar>a\<^sub>0\<bar> - a) * b\<^sub>0 * sgn a\<^sub>0\<close>
    {
      c=c+b;
      a=a-1
    }
  \<close>
    apply vcg_cs
     apply (auto simp: algebra_simps)
    done
    
  text \<open>The variant and invariant can use the program variables.
    Variables suffixed with \<open>\<^sub>0\<close> refer to the values of parameters at the start of the program.
  
    The variant must be an expression of type \<^typ>\<open>int\<close>, which decreases with every loop iteration and is always \<open>\<ge>0\<close>.
    
    \<^bold>\<open>Pitfall\<close>: If the variant has a more general type, e.g., \<^typ>\<open>'a\<close>, an explicit type annotation
      must be added. Otherwise, you'll get an ugly error message directly from Isabelle's type checker!
  \<close>  
    
  subsubsection \<open>Recursive Procedures\<close>
  text \<open>IMP2 supports mutually recursive procedures. All procedures of a mutually recursive specification
    have to be specified and proved simultaneously. 
    
    Each procedure has to be annotated with a variant over the parameters. 
    On a recursive call, the variant of the callee for the arguments must be smaller than the 
    variant of the caller (for its initial arguments).
    
    Recursive invocations inside the specification have to be tagged by the \<open>rec\<close> keyword.
  \<close>

  recursive_spec
    odd_imp(n) returns b assumes "n\<ge>0" ensures \<open>b\<noteq>0 \<longleftrightarrow> odd n\<^sub>0\<close> variant \<open>n\<close> 
    defines \<open>if (n==0) b=0 else b=rec even_imp(n-1)\<close>
  and
    even_imp(n) returns b assumes "n\<ge>0" ensures \<open>b\<noteq>0 \<longleftrightarrow> even n\<^sub>0\<close> variant \<open>n\<close> 
    defines \<open>if (n==0) b=1 else b=rec odd_imp(n-1)\<close>
    by vcg_cs
  
  text \<open>After proving the VCs, constants are defined as usual, and the correctness theorems 
    are lifted and declared to the VCG for future use.\<close>  
  thm odd_imp_spec even_imp_spec
    
  
  subsection \<open>The VCG\<close>
  text \<open>The VCG is designed to produce human-readable VCs. 
    It takes care of presenting the VCs with reasonable variable names, 
    and a location information from where a VC originates.
  \<close>
  
  procedure_spec mult_ab'(a,b) returns c assumes \<open>True\<close> ensures "c=a\<^sub>0*b\<^sub>0"
  defines \<open>
    if (a<0) {a = -a; b = -b};
    c=0;
    while (a>0) 
      @variant \<open>a\<close>
      @invariant \<open>0\<le>a \<and> a\<le>\<bar>a\<^sub>0\<bar> \<and> c = ( \<bar>a\<^sub>0\<bar> - a) * b\<^sub>0 * sgn a\<^sub>0\<close>
    {
      c=c+b;
      a=a-1
    }
  \<close>
  apply vcg
  text \<open>The \<^term>\<open>\<paragraph>xxx\<close> tags in the premises give a hint to the origin of each VC. 
    Moreover, the variable names are derived from the actual variable names in the program.\<close>
  by (auto simp: algebra_simps)
  
  (* program-spec, procedure-spec   *)
  
  subsection \<open>Advanced Features\<close>
  
  subsubsection \<open>Custom Termination Relations\<close>
  text \<open>Both for loops and recursive procedures, a custom termination relation can be specified, with the 
  \<open>relation\<close> annotation. The variant must be a function into the domain of this relation.
  
  \<^bold>\<open>Pitfall\<close>: You have to ensure, by type annotations, that the most general type of 
    the relation and variant fit together. Otherwise, ugly low-level errors will be the result.
  \<close>
  
  procedure_spec mult_ab''(a,b) returns c assumes \<open>True\<close> ensures "c=a\<^sub>0*b\<^sub>0"
  defines \<open>
    if (a<0) {a = -a; b = -b};
    c=0;
    while (a>0) 
      @relation \<open>measure nat\<close>
      @variant \<open>a\<close>
      @invariant \<open>0\<le>a \<and> a\<le>\<bar>a\<^sub>0\<bar> \<and> c = ( \<bar>a\<^sub>0\<bar> - a) * b\<^sub>0 * sgn a\<^sub>0\<close>
    {
      c=c+b;
      a=a-1
    }
  \<close>
  by vcg_cs (auto simp: algebra_simps)
  
  recursive_spec relation \<open>measure nat\<close>
    odd_imp'(n) returns b assumes "n\<ge>0" ensures \<open>b\<noteq>0 \<longleftrightarrow> odd n\<^sub>0\<close> variant \<open>n\<close> 
    defines \<open>if (n==0) b=0 else b=rec even_imp'(n-1)\<close>
  and
    even_imp'(n) returns b assumes "n\<ge>0" ensures \<open>b\<noteq>0 \<longleftrightarrow> even n\<^sub>0\<close> variant \<open>n\<close> 
    defines \<open>if (n==0) b=1 else b=rec odd_imp'(n-1)\<close>
    by vcg_cs
  

  subsubsection \<open>Partial Correctness\<close>  
  text \<open>IMP2 supports partial correctness proofs only for while-loops. 
    Recursive procedures must always be proved totally correct\<^footnote>\<open>Adding partial correctness for recursion 
      is possible, however, compared to total correctness, showing that the prove rule is sound 
      requires some effort that we have not (yet) invested.\<close>\<close>
  
  procedure_spec (partial) nonterminating() returns a assumes True ensures \<open>a=0\<close> defines 
    \<open>while (a\<noteq>0) @invariant \<open>True\<close>
      a=a-1\<close>
    by vcg_cs
      
        
      
  subsubsection \<open>Arrays\<close>
  text \<open>IMP2 provides one-dimensional arrays of integers, which are indexed by integers.
    Arrays do not have to be declared or allocated. By default, every index maps to zero.
    
    In the specifications, arrays are modeled as functions of type \<^typ>\<open>int\<Rightarrow>int\<close>.
  \<close>

  lemma array_sum_aux: "l\<^sub>0\<le>l \<Longrightarrow> {l\<^sub>0..<l + 1} = insert l {l\<^sub>0..<l}" for l\<^sub>0 l :: int by auto
  
  procedure_spec array_sum(a,l,h) returns s assumes "l\<le>h" ensures \<open>s = (\<Sum>i=l\<^sub>0..<h\<^sub>0. a\<^sub>0 i)\<close> defines 
    \<open> s=0; 
      while (l<h) 
        @variant \<open>h-l\<close>
        @invariant \<open>l\<^sub>0\<le>l \<and> l\<le>h \<and> s = (\<Sum>i=l\<^sub>0..<l. a i)\<close>
      { s = s+a[l]; l=l+1 } \<close>
    apply vcg_cs
    apply (simp add: array_sum_aux)
    done
    

  
  subsection \<open>Proving Techniques\<close>
  
  text \<open>This section contains a small collection of techniques to tackle large proofs.\<close>
  
  subsubsection \<open>Auxiliary Lemmas\<close>
  text \<open>Prove auxiliary lemmas, and try to keep the actual proof of the specification small.
    As a rule of thumb: All VCs that cannot be solved by a simple @{method auto} invocation
    should go to an auxiliary lemma. 
    
    The auxiliary lemma may either re-state the whole VC, or only prove the ``essence'' of the VC, 
    such that the rest of its proof becomes automatic again.
    See the @{const array_sum} program above for an example or the latter case.
    
    \<^bold>\<open>Pitfall\<close> When extracting auxiliary lemmas, it is too easy to get too general types, which
      may render the lemmas unprovable. As an example, omitting the explicit type constraints
      from @{thm [source] "array_sum_aux"} will yield an unprovable statement.
  \<close>
  
  subsubsection \<open>Inlining\<close>
  text \<open>More complex procedure bodies can be modularized by either splitting them into 
    multiple procedures, or using inlining and @{command program_spec} to explicitly prove a 
    specification for a part of a program. Cf.\ the insertion sort example for the latter technique. \<close>
  
  subsubsection \<open>Functional Refinement\<close>
  text \<open>
    Sometimes, it makes sense to state the algorithm functionally first, and then prove that
    the implementation behaves like the functional program, and, separately, that the functional 
    program is correct. Cf.\ the mergesort example.
  \<close>

  subsubsection \<open>Data Refinement\<close>
  text \<open>Moreover, it sometimes makes sense to abstract the concrete variables to abstract types, 
    over which the algorithm is then specified. For example, an array \<open>a\<close> with a range \<open>l..<h\<close> can 
    be understood as a list. Or an array can be used as a bitvector set. 
    Cf.\ the mergesort and dedup examples. \<close>  
  
  
  subsection \<open>Troubleshooting\<close>
  text \<open>We list a few common problems and their solutions here\<close>
  
  subsubsection \<open>Invalid Variables in Annotations\<close>
  text \<open>Undeclared variables in annotations are highlighted, however, no warning or error is produced. 
  Usually, the generated VCs will not be provable. The most common mistake is to 
  forget the \<open>\<^sub>0\<close> suffix when referring to parameter values in (in)variants and postconditions.\<close>

  text \<open>Note the highlighting of unused variables in the following example\<close>
  procedure_spec foo(x1,x2) returns y assumes "x1>x2+x3" ensures "y = x1\<^sub>0+x2" defines \<open>
      y=0;
    while (x1>0)
      @variant \<open>y + x3\<close>
      @invariant \<open>y>x3\<close>
      {
        x1=x2
      }
  \<close>
  oops
  
  text \<open>Even worse, if the most general type of an annotation becomes too general,
    as free variables have type \<^typ>\<open>'a\<close> by default, you will see an internal type error.
    
    Try replacing the variant or invariant with a free variable in the above example.
  \<close> (* TODO: Is there an expects-error unit-test command in Isabelle already? *)

  subsubsection \<open>Wrong Annotations\<close>
  text \<open>For total correctness, you must annotate a loop variant and invariant. 
    For partial correctness, you must annotate an invariant, but \<^bold>\<open>no variant\<close>.
    
    When not following this rule, the VCG will get stuck in an internal state
  \<close>

  procedure_spec (partial) foo () assumes True ensures True defines \<open>
    while (n>0) @variant \<open>n\<close> @invariant \<open>True\<close>
    { n=n-1 }
  \<close>
    apply vcg
    oops
    
    
  subsubsection \<open>Calls to Undefined Procedures\<close>  
  text \<open>Calling an undefined procedure usually results in a type error, as the procedure 
    name gets interpreted as an Isabelle term, e.g., either it refers to an existing constant, 
    or is interpreted as a free variable\<close>
  
  (* term \<open>\<^imp>\<open> undefined() \<close>\<close> (* Type unification failed *) *)
    
  subsection \<open>Missing Features\<close>
  text \<open>This is an (incomplete) list of missing features.\<close>

  subsubsection \<open>Elaborate Warnings and Errors\<close>
  text \<open>Currently, the IMP2 tools only produce minimal error and warning messages.
    Quite often, the user sees the raw error message as produced by Isabelle unfiltered, 
    including all internal details of the tools. 
  \<close>
    
  subsubsection \<open>Static Type Checking\<close>
  text \<open>We do no static type checking at all. 
    In particular, we do not check, nor does our semantic enforce, that procedures are called 
    with the same number of arguments as they were declared. 
    Programs that violate this convention may even have provable properties, as argument 
    and parameter passing is modeled as macros on top of the semantics, and the semantics has no
    notion of failure.
  \<close>
  
  subsubsection \<open>Structure Types\<close>
  text \<open>Every variable is an integer arrays. Plain integer variables are implemented as 
    macros on top of this, by referring to index \<open>0\<close>.
    
    The most urgent addition to increase usability would be record types. 
    With them, we could model encapsulation and data refinement more explicitly, by
    collecting all parts of a data structure in a single (record-typed) variable.

    An easy way of adding record types would follow a similar route as arrays, 
    modeling values of variables as a recursive tree-structured datatype.
    
    @{theory_text [display] \<open>datatype val = PRIM int | STRUCT "fname \<Rightarrow> val" | ARRAY "int \<Rightarrow> val"\<close>}

    However, for modeling the semantics, we most likely want to introduce an explicit error state,
    to distinguish type errors (e.g. accessing a record field of an integer value) from nontermination.
    \<close>

  subsubsection \<open>Function Calls as Expressions\<close>  
  text \<open>Currently, function calls are modeled as statements, and thus, cannot be nested into 
    expressions. Doing so would require to simultaneously specify the semantics of 
    commands and expressions, which makes things more complex. 
    
    As the language is intended to be simple, we have not done this.
  \<close>
    
  subsubsection \<open>Ghost Variables\<close>  
  text \<open>Ghost variables are a valuable tool for expressing (data) refinement, 
    and hinting the VCG towards the abstract algorithm structure.
    
    We believe that we can add ghost variables with annotations on top of the VCG,
    without actually changing the program semantics.
  \<close>
  
  subsubsection \<open>Concurrency\<close>
  text \<open>IMP2 is a single threaded language. 
    We have no current plans to add concurrency, as this would greatly complicate both the 
    semantics and the VCG, which is contrary to the goal of a simple language for educational 
    purposes.
  \<close>

  subsubsection \<open>Pointers and Memory\<close>
  text \<open>Adding pointers and memory allocation to IMP2 is theoretically possible, but, again, 
    this would complicate the semantics and the VCG.

    However, as the author has some experience in VCGs using separation logic, he might actually
    add pointers and memory allocation to IMP2 in the near future.
  \<close>

end
