(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*<*)
theory ICF_Userguide
imports 
  "../ICF/Collections"
  "../Lib/Code_Target_ICF"
begin
(*>*)

text_raw \<open>\isasection{Isabelle Collections Framework Userguide}\label{thy:Userguide}\<close>


section "Introduction"
text \<open>
  This is the Userguide for the (old) Isabelle Collection Framework.
  It does not cover the Generic Collection Framework, nor the 
  Automatic Refinement Framework.

  The Isabelle Collections Framework defines interfaces of various collection types and provides some standard implementations and generic algorithms.

  The relation between the data structures of the collection framework and standard Isabelle types (e.g. for sets and maps) is established by abstraction functions.

  Amongst others, the following interfaces and data-structures are provided by the Isabelle Collections Framework (For a complete list, see the overview section
  in the implementations chapter of the proof document):
  \begin{itemize}
    \item Set and map implementations based on (associative) lists, red-black trees, hashing and tries.
    \item An implementation of a FIFO-queue based on two stacks.
    \item Annotated lists implemented by finger trees.
    \item Priority queues implemented by binomial heaps, skew binomial heaps, and annotated lists (via finger trees).
  \end{itemize}

  The red-black trees are imported from the standard isabelle library. The binomial and skew binomial heaps are
  imported from the {\em Binomial-Heaps} entry of the archive of formal proofs. The finger trees are imported from
  the {\em Finger-Trees} entry of the archive of formal proofs.
\<close>

subsection "Getting Started"
text \<open>
  To get started with the Isabelle Collections Framework (assuming that you are already familiar with Isabelle/HOL and Isar),
  you should first read the introduction (this section), that provides many basic examples. More examples are in the examples/ subdirectory of the collection
  framework.
  Section~\ref{sec:userguide.structure} explains the concepts of the Isabelle Collections Framework in more detail.
  Section~\ref{sec:userguide.ext} provides information on extending the framework along with detailed examples, and 
  Section~\ref{sec:userguide.design} contains a discussion on the design of this framework.
  There is also a paper \cite{LammichLochbihler2010ITP} on the design of the Isabelle Collections Framework available.
\<close>

subsection "Introductory Example"
text \<open>
  We introduce the Isabelle Collections Framework by a simple example.

  Given a set of elements represented by a red-black tree, and a list, 
  we want to filter out all elements that are not contained in the set. 
  This can be done by Isabelle/HOL's @{const filter}-function\footnote{Note that Isabelle/HOL uses the list comprehension syntax @{term [source] "[x\<leftarrow>l. P x]"}
  as syntactic sugar for filtering a list.}:
\<close>

definition rbt_restrict_list :: "'a::linorder rs \<Rightarrow> 'a list \<Rightarrow> 'a list"
where "rbt_restrict_list s l == [ x\<leftarrow>l. rs.memb x s ]"

text \<open>
  The type @{typ "'a rs"} is the type of sets backed by red-black trees.
  Note that the element type of sets backed by red-black trees must be
  of sort \<open>linorder\<close>.
  The function @{const rs.memb} tests membership on such sets.
\<close>  

text \<open>Next, we show correctness of our function:\<close>
lemma rbt_restrict_list_correct: 
  assumes [simp]: "rs.invar s"
  shows "rbt_restrict_list s l = [x\<leftarrow>l. x\<in>rs.\<alpha> s]"
  by (simp add: rbt_restrict_list_def rs.memb_correct)

text \<open>
  The lemma @{thm [source] rs.memb_correct}: @{thm [display] rs.memb_correct[no_vars]} 

  states correctness of the @{const rs.memb}-function. 
  The function @{const rs.\<alpha>} maps a red-black-tree to the set that it represents.
  Moreover, we have to explicitely keep track of the invariants of the used data structure,
  in this case red-black trees. 
  The premise @{thm (prem 1) rs.memb_correct} represents the invariant assumption for the collection data structure.
  Red-black-trees are invariant-free, so this defaults to @{term "True"}.
  For uniformity reasons, these (unnecessary) invariant assumptions are present in all correctness lemmata.

  Many of the correctness lemmas for standard RBT-set-operations are summarized by the lemma @{thm [source] rs.correct}:
    @{thm [display] rs.correct[no_vars]}
\<close>

text \<open>
  All implementations provided by this library are compatible with the Isabelle/HOL code-generator.
  Now follow some examples of using the code-generator.
  Note that the code generator can only generate code for plain constants 
  without arguments, while the operations like @{const rs.memb} have arguments,
  that are only hidden by an abbreviation.
\<close>

text \<open>
  There are conversion functions from lists to sets and, vice-versa, from sets to lists:
\<close>

definition "conv_tests \<equiv> (
  rs.from_list [1::int .. 10],
  rs.to_list (rs.from_list [1::int .. 10]),
  rs.to_sorted_list (rs.from_list [1::int,5,6,7,3,4,9,8,2,7,6]),
  rs.to_rev_list (rs.from_list [1::int,5,6,7,3,4,9,8,2,7,6])
)"

ML_val \<open>@{code conv_tests}\<close>

text \<open>
  Note that sets make no guarantee about ordering, hence the only thing we can 
  prove about conversion from sets to lists is:
    @{thm [source] rs.to_list_correct}: @{thm [display] rs.to_list_correct[no_vars]}

  Some sets, like red-black-trees, also support conversion to sorted lists,
  and we have:
    @{thm [source] rs.to_sorted_list_correct}: @{thm [display] rs.to_sorted_list_correct[no_vars]} and
    @{thm [source] rs.to_rev_list_correct}: @{thm [display] rs.to_rev_list_correct[no_vars]} 
\<close>

definition "restrict_list_test \<equiv> rbt_restrict_list (rs.from_list [1::nat,2,3,4,5]) [1::nat,9,2,3,4,5,6,5,4,3,6,7,8,9]"

ML_val \<open>@{code restrict_list_test}\<close>

definition "big_test n = (rs.from_list [(1::int)..n])"

ML_val \<open>@{code big_test} (@{code int_of_integer} 9000)\<close>

subsection "Theories"
text \<open>
  To make available the whole collections framework to your formalization, 
  import the theory @{theory Collections.Collections} which includes everything. Here is a
  small selection:
  \begin{description}
    \item[@{theory Collections.SetSpec}] Specification of sets and set functions
    \item[@{theory Collections.SetGA}] Generic algorithms for sets
    \item[@{theory Collections.SetStdImpl}] Standard set implementations (list, rb-tree, hashing, tries)
    \item[@{theory Collections.MapSpec}] Specification of maps
    \item[@{theory Collections.MapGA}] Generic algorithms for maps
    \item[@{theory Collections.MapStdImpl}] Standard map implementations (list,rb-tree, hashing, tries)
    \item[@{theory Collections.ListSpec}] Specification of lists
    \item[@{theory Collections.Fifo}] Amortized fifo queue
    \item[@{theory Collections.DatRef}] Data refinement for the while combinator
  \end{description}

\<close>

subsection "Iterators"
text \<open>An important concept when using collections are iterators. An iterator is a kind of generalized fold-functional.
  Like the fold-functional, it applies a function to all elements of a set and modifies a state. There are
  no guarantees about the iteration order. But, unlike the fold functional, you can prove useful properties of iterations
  even if the function is not left-commutative. Proofs about iterations are done in invariant style, establishing an
  invariant over the iteration.

  The iterator combinator for red-black tree sets is @{const rs.iterate}, and the proof-rule that is usually used is:
    @{thm [source] rs.iteratei_rule_P}: @{thm [display] rs.iteratei_rule_P[no_vars]}

  The invariant @{term I} is parameterized with the set of remaining elements that have not yet been iterated over and the
  current state. The invariant has to hold for all elements remaining and the initial state: @{term "I (rs.\<alpha> S) \<sigma>0"}. 
  Moreover, the invariant has to be preserved by an iteration step: 
    @{term [display] "\<And>x it \<sigma>. \<lbrakk>x \<in> it; it \<subseteq> rs.\<alpha> S; I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)"}
  And the proposition to be shown for the final state must be a consequence of the invarant for no 
  elements remaining: @{term "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"}. 

  A generalization of iterators are {\em interruptible iterators} where iteration is only continues while some condition on the state holds.
  Reasoning over interruptible iterators is also done by invariants: 
    @{thm [source] rs.iteratei_rule_P}: @{thm [display] rs.iteratei_rule_P[no_vars]}

  Here, interruption of the iteration is handled by the premise
    @{term [display] "\<And>\<sigma> it. \<lbrakk>it \<subseteq> rs.\<alpha> S; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"}
  that shows the proposition from the invariant for any intermediate state of the 
  iteration where the continuation condition 
  does not hold (and thus the iteration is interrupted).
\<close>

text \<open>
  As an example of reasoning about results of iterators, we implement a function
  that converts a hashset to a list that contains precisely the elements of the set.
\<close>

definition "hs_to_list' s == hs.iteratei s (\<lambda>_. True) (#) []"

text \<open>
  The correctness proof works by establishing the invariant that the list contains
  all elements that have already been iterated over.
  Again @{term "hs.invar s"} denotes the invariant for hashsets which defaults to @{term "True"}.
\<close>
lemma hs_to_list'_correct: 
  assumes INV: "hs.invar s"
  shows "set (hs_to_list' s) = hs.\<alpha> s"
  apply (unfold hs_to_list'_def)
  apply (rule_tac 
    I="\<lambda>it \<sigma>. set \<sigma> = hs.\<alpha> s - it"
    in hs.iterate_rule_P[OF INV])
  txt \<open>The resulting proof obligations are easily discharged using auto:\<close>
  apply auto
  done

text \<open>
  As an example for an interruptible iterator, 
  we define a bounded existential-quantification over the list elements.
  As soon as the first element is found that fulfills the predicate,
  the iteration is interrupted.
  The state of the iteration is simply a boolean, indicating the (current) result of the quantification:
\<close>

definition "hs_bex s P == hs.iteratei s (\<lambda>\<sigma>. \<not> \<sigma>) (\<lambda>x \<sigma>. P x) False"

lemma hs_bex_correct: 
  "hs.invar s \<Longrightarrow> hs_bex s P \<longleftrightarrow> (\<exists>x\<in>hs.\<alpha> s. P x)"
  apply (unfold hs_bex_def)
  txt \<open>The invariant states that the current result matches the result of the quantification
    over the elements already iterated over:\<close>
  apply (rule_tac 
    I="\<lambda>it \<sigma>. \<sigma> \<longleftrightarrow> (\<exists>x\<in>hs.\<alpha> s - it. P x)" 
    in hs.iteratei_rule_P)
  txt \<open>The resulting proof obligations are easily discharged by auto:\<close>
  apply auto
  done


section "Structure of the Framework"
text_raw \<open>\label{sec:userguide.structure}\<close>
text \<open>
  The concepts of the framework are roughly based on the object-oriented concepts of interfaces, implementations and generic algorithms.

  The concepts used in the framework are the following:
  \begin{description}
    \item[Interfaces] An interface describes some concept by providing an abstraction mapping $\alpha$ to a related Isabelle/HOL-concept.
      The definition is generic in the datatype used to implement the concept (i.e. the concrete data structure). An interface is specified by means 
      of a locale that fixes the abstraction mapping and an invariant.
      For example, the set-interface contains an abstraction mapping to sets, and is specified by the locale \<open>SetSpec.set\<close>.
      An interface roughly matches the concept of a (collection) interface in Java, e.g. {\em java.util.Set}.
  
    \item[Functions] A function specifies some functionality involving interfaces. A function is specified by means of a locale.
                      For example, membership query for a set is specified by the locale @{const [source] SetSpec.set_memb} and
                      equality test between two sets is a function specified by @{const [source] SetSpec.set_equal}.
                      A function roughly matches a method declared in an interface, e.g. {\em java.util.Set\#contains, java.util.Set\#equals}.

    \item[Operation Records] In order to reference an interface with a standard
      set of operations, those operations are summarized in a record, and there 
      is a locale that fixes this record, and makes available all operations.
      For example, the locale @{const [source] SetSpec.StdSet} fixes a record
      of standard set operations and assumes their correctness. It also defines 
      abbreviations to easily access the members of the record. Internally,
      all the standard operations, like @{const hs.memb}, are introduced by
      interpretation of such an operation locale.

    \item[Generic Algorithms] A generic algorithm specifies, in a generic way,
      how to implement a function using other functions. Usually, a generic 
      algorithm lives in a locale that imports the necessary operation locales.
      For example, the locale @{const SetGA.cart_loc} defines a generic 
      algorithm for the cartesian product between two sets.

      There is no direct match of generic algorithms in the Java
      Collections Framework. The most related concept are abstract
      collection interfaces, that provide some default algorithms,
      e.g. {\em java.util.AbstractSet}.  The concept of {\em Algorithm} in
      the C++ Standard Template Library \cite{C++STL} matches the concept
      of Generic Algorithm quite well.


    \item[Implementation] An implementation of an interface provides a
       data structure for that interface together with an abstraction
       mapping and an invariant. Moreover, it provides implementations
       for some (or all) functions of that interface.  For example,
       red-black trees are an implementation of the set-interface,
       with the abstraction mapping @{const rs.\<alpha>} and invariant
       @{const rs.invar}; and the constant @{const rs.ins} implements
       the insert-function, as can be verified by 
       @{lemma "set_ins rs.\<alpha> rs.invar rs.ins" by unfold_locales}.
       An implementation matches a concrete collection
       interface in Java, e.g. {\em java.util.TreeSet}, and the
       methods implemented by such an interface, e.g. {\em
       java.util.TreeSet\#add}. 


    \item[Instantiation] An instantiation of a generic algorithm
        provides actual implementations for the used functions. For
        example, the generic cartesian-product algorithm can be
        instantiated to use red-black-trees for both arguments, and output
        a list, as will be illustrated below in Section~\ref{sec:inst_gen_algo}.
        While some of the functions
        of an implementation need to be implemented specifically, many
        functions may be obtained by instantiating generic algorithms.
        In Java, instantiation of a generic algorithm is matched most
        closely by inheriting from an abstract collection
        interface. In the C++ Standard Template Library instantiation
        of generic algorithms is done implicitely by the compiler.

  \end{description}

\<close>


  subsection "Instantiation of Generic Algorithms" text_raw \<open>\label{sec:inst_gen_algo}\<close>
  
  text \<open>A generic algorithm is instantiated by interpreting its locale with 
    the wanted implementations. For example, to obtain a cartesian product
    between two red-black trees, yielding a list, we can do the following:\<close>
  setup Locale_Code.open_block
  interpretation rrl: cart_loc rs_ops rs_ops ls_ops by unfold_locales
  setup Locale_Code.close_block
  setup \<open>ICF_Tools.revert_abbrevs "rrl"\<close>

  text \<open>It is then available under the expected name:\<close>
  term "rrl.cart"

  text \<open>Note the three lines of boilerplate code, that work around some 
    technical problems of Isabelle/HOL: The \<open>Locale_Code.open_block\<close> and
    \<open>Locale_Code.close_block\<close> commands set up code generation for any 
    locale that is interpreted in between them. They also have to be specified
    if an existing locale that already has interpretations is extended by
    new definitions.

    The \<open>ICF_Tools.revert_abbrevs "rrl"\<close> reverts all 
    abbreviations introduced by the locale, such that the displayed 
    information becomes nicer.
\<close>


  subsection "Naming Conventions"
  text \<open>
    The Isabelle Collections Framework follows these general naming conventions.
    Each implementation has a two-letter (or three-letter) and a one-letter (or two-letter) abbreviation, that are used as prefixes for the related constants, lemmas and instantiations.

    The two-letter and three-letter abbreviations should be unique over all interfaces and instantiations, the one-letter abbreviations should be unique
    over all implementations of the same interface.
    Names that reference the implementation of only one interface are prefixed with that implementation's two-letter abbreviation (e.g. @{const hs.ins} for insertion into a HashSet (hs,h)),
    names that reference more than one implementation are prefixed with the one-letter (or two-letter) abbreviations (e.g. @{const rrl.cart} for the cartesian 
    product between two RBT-Sets, yielding a list-set)
    
    The most important abbreviations are:
    \begin{description}
      \item[lm,l] List Map
      \item[lmi,li] List Map with explicit invariant
      \item[rm,r] RB-Tree Map
      \item[hm,h] Hash Map
      \item[ahm,a] Array-based hash map
      \item[tm,t] Trie Map
      \item[ls,l] List Set
      \item[lsi,li] List Set with explicit invariant
      \item[rs,r] RB-Tree Set
      \item[hs,h] Hash Set
      \item[ahs,a] Array-based hash map
      \item[ts,t] Trie Set
    \end{description}

    Each function \<open>name\<close> of an interface \<open>interface\<close> is declared in a locale \<open>interface_name\<close>. This locale provides a fact \<open>name_correct\<close>. For example, there is the locale @{const set_ins} providing
    the fact @{thm [source] set_ins.ins_correct}.
    An implementation instantiates the locales of all implemented functions, using its two-letter abbreviation as instantiation prefix. For example, the HashSet-implementation instantiates the locale @{const set_ins} 
    with the prefix {\em hs}, yielding the lemma @{thm [source] hs.ins_correct}. Moreover, an implementation with two-letter abbreviation {\em aa} provides a lemma \<open>aa.correct\<close> 
    that summarizes the correctness facts for the basic 
    operations. It should only contain those facts that are safe to be used with the simplifier. E.g., the correctness facts for basic operations on hash sets are available via the lemma @{thm [source] hs.correct}.

\<close>

section "Extending the Framework"
text_raw \<open>\label{sec:userguide.ext}\<close>
text \<open>
  The best way to add new features, i.e., interfaces, functions, 
  generic algorithms, or implementations to the collection framework is to use 
  one of the existing items as example. 
\<close>


section "Design Issues"
text_raw \<open>\label{sec:userguide.design}\<close>
  text \<open>
    In this section, we motivate some of the design decisions of the Isabelle Collections Framework and report our experience with alternatives.
    Many of the design decisions are justified by restrictions of Isabelle/HOL and the code generator, so that there may be better
    options if those restrictions should vanish from future releases of Isabelle/HOL.
\<close>

  text \<open>
    The main design goals of this development are:
    \begin{enumerate}
      \item\label{dg_unified} Make available various implementations of collections under a unified interface.
      \item\label{dg_extensible} It should be easy to extend the framework by new interfaces, functions, algorithms, and implementations.
      \item\label{dg_concise} Allow simple and concise reasoning over functions using collections.
      \item\label{dg_genalgo} Allow generic algorithms, that are independent of the actual data structure that is used.
      \item\label{dg_exec} Support generation of executable code.
      \item\label{dg_control} Let the user precisely control what data structures are used in the implementation.
    \end{enumerate}
\<close>

  subsection \<open>Data Refinement\<close>
  text \<open>
    In order to allow simple reasoning over collections, we use a data refinement approach. Each collection
    interface has an abstraction function that maps it on a related Isabelle/HOL concept (abstract level).
    The specification of functions are also relative to the abstraction.
    This allows most of the correctness reasoning to be done on the abstract level. On this level,
    the tool support is more elaborated and one is not yet fixed to a concrete implementation.
    In a next step, the abstract specification is refined to use an actual implementation (concrete level). The correctness properties
    proven on the abstract level usually transfer easily to the concrete level.

    Moreover, the user has precise control how the refinement is done, i.e. what data structures are used. An alternative would be to do refinement
    completely automatic, as e.g. done in the code generator setup of the Theory~{\em Executable-Set}. This has the advantage that it induces less writing overhead.
    The disadvantage is that the user looses a great amount of control over the refinement. For example, in {\em Executable-Set}, all sets have to be represented by lists,
    and there is no possibility to represent one set differently from another. 

    For a more detailed discussion of the data refinement issue, we refer to
    the monadic refinement framework, that is available in the AFP 
    (@{url "http://isa-afp.org/entries/Refine_Monadic.shtml"})
\<close>

  subsection \<open>Operation Records\<close>
  text \<open>
    In order to allow convenient access to the most frequently used functions 
    of an interface,
    we have grouped them together in a record, and defined a locale that only
    fixes this record. This greatly reduces the boilerplate required to define
    a new (generic) algorithm, as only the operation locale (instead of every
    single function) has to be included in the locale for the generic algorithm.

    Note however, that parameters of locales are monomorphic inside the locale.
    Thus, we have to import an own instance for the locale for every element
    type of a set, or key/value type of a map. 
    For iterators, where this problem was most annoying, we have installed a
    workaround that allows polymorphic iterators even inside locales.
\<close>

  subsection \<open>Locales for Generic Algorithms\<close>
  text \<open>
    A generic algorithm is defined within a locale, that includes the required 
    functions (or operation locales). If many instances of the same interface
    are required, prefixes are used to distinguish between them. This makes
    the code for a generic algorithm quite consise and readable.

    However, there are some technical issues that one has to consider:
    \begin{itemize}
      \item  When fixing parameters in the declaration of the locale, their
        types will be inferred independently of the definitions later done in
        the locale context. In order to get the correct types, one has to add 
        explicit type constraints.
      \item The code generator has problems with generating code from 
        definitions inside a locale. Currently, the \<open>Locale_Code\<close>-package
        provides a rather convenient workaround for that issue: It requires the 
        user to enclose interpretations and definitions of new constants inside
        already interpreted locales within two special commands, that set up
        the code generator appropriately.
    \end{itemize}
\<close>

  subsection \<open>Explicit Invariants vs Typedef\<close>
  text \<open>
    The interfaces of this framework use explicit invariants.
    This provides a more general specification which allows some operations to
    be implemented more efficiently, cf. @{const "lsi.ins_dj"} 
    in @{theory Collections.ListSetImpl_Invar}.
    
    Most implementations, however, hide the invariant in a typedef and setup
    the code generator appropriately.
    In that case, the invariant is just @{term "\<lambda>_. True"}, and removed 
    automatically by the simplifier and classical reasoner.
    However, it still shows up in some premises and conclusions due to
    uniformity reasons.
\<close>

(*<*)
end
(*>*)
