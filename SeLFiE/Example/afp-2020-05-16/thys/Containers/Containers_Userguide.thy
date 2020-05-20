(* Title:      Containers/Containers_Userguide.thy
   Author:     Andreas Lochbihler, ETH Zurich *)
(*<*)
theory Containers_Userguide imports
  Card_Datatype
  List_Proper_Interval
  Containers
begin
(*>*)
chapter \<open>User guide\<close>
text_raw \<open>\label{chapter:Userguide}\<close>

text \<open>
  This user guide shows how to use and extend the lightweight containers framework (LC).
  For a more theoretical discussion, see \cite{Lochbihler2013ITP}.
  This user guide assumes that you are familiar with refinement in the code generator \cite{HaftmannBulwahn2013codetut,HaftmannKrausKuncarNipkow2013ITP}.
  The theory \<open>Containers_Userguide\<close> generates it; so if you want to experiment with the examples, you can find their source code there.
  Further examples can be found in the @{dir \<open>Examples\<close>} folder.
\<close>

section \<open>Characteristics\<close>

text_raw \<open>
  \isastyletext
  \begin{itemize}
\<close>
text_raw \<open>
  \isastyletext
  \item \textbf{Separate type classes for code generation}
    \\
    LC follows the ideal that type classes for code generation should be separate from the standard type classes in Isabelle.
    LC's type classes are designed such that every type can become an instance, so well-sortedness errors during code generation can always be remedied.
\<close>
text_raw \<open>
  \isastyletext
  \item \textbf{Multiple implementations}
    \\
    LC supports multiple simultaneous implementations of the same container type.
    For example, the following implements at the same time
    (i)~the set of @{typ bool} as a distinct list of the elements,
    (ii)~@{typ "int set"} as a RBT of the elements or as the RBT of the complement, and
    (iii)~sets of functions as monad-style lists:
    \par
\<close>
value "({True}, {1 :: int}, - {2 :: int, 3}, {\<lambda>x :: int. x * x, \<lambda>y. y + 1})"
text_raw \<open>
    \isastyletext
    \par
    The LC type classes are the key to simultaneously supporting different implementations.

  \item \textbf{Extensibility}
    \\
    The LC framework is designed for being extensible.
    You can add new containers, implementations and element types any time.
  \end{itemize}
\<close>

section \<open>Getting started\<close>
text_raw \<open>\label{section:getting:started}\<close>

text \<open>
  Add the entry theory @{theory Containers.Containers} for LC to the end of your imports.
  This will reconfigure the code generator such that it implements the types @{typ "'a set"} for sets and @{typ "('a, 'b) mapping"} for maps with one of the data structures supported.
  As with all the theories that adapt the code generator setup, it is important that @{theory Containers.Containers} comes at the end of the imports.

  Run the following command, e.g., to check that LC works correctly and implements sets of @{typ int}s as red-black trees (RBT):
\<close>

value [code] "{1 :: int}"

text \<open>
  This should produce @{value [names_short] "{1 :: int}"}.
  Without LC, sets are represented as (complements of) a list of elements, i.e., @{term "set [1 :: int]"} in the example.
\<close>

text \<open>
  If your exported code does not use your own types as elements of sets or maps and you have not declared any code equation for these containers, then your \isacommand{export{\isacharunderscore}code} command will use LC to implement @{typ "'a set"} and @{typ "('a, 'b) mapping"}.
  
  Our running example will be arithmetic expressions.
  The function @{term "vars e"} computes the variables that occur in the expression @{term e}
\<close>

type_synonym vname = string
datatype expr = Var vname | Lit int | Add expr expr
fun vars :: "expr \<Rightarrow> vname set" where
  "vars (Var v) = {v}"
| "vars (Lit i) = {}"
| "vars (Add e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 \<union> vars e\<^sub>2"

value "vars (Var ''x'')"

text \<open>
  To illustrate how to deal with type variables, we will use the following variant where variable names are polymorphic:
\<close>

datatype 'a expr' = Var' 'a | Lit' int | Add' "'a expr'" "'a expr'"
fun vars' ::  "'a expr' \<Rightarrow> 'a set" where
  "vars' (Var' v) = {v}"
| "vars' (Lit' i) = {}"
| "vars' (Add' e\<^sub>1 e\<^sub>2) = vars' e\<^sub>1 \<union> vars' e\<^sub>2"

value "vars' (Var' (1 :: int))"

section \<open>New types as elements\<close>

text \<open>
  This section explains LC's type classes and shows how to instantiate them.
  If you want to use your own types as the elements of sets or the keys of maps, you must instantiate up to eight type classes: @{class ceq} (\S\ref{subsection:ceq}), @{class ccompare} (\S\ref{subsection:ccompare}), @{class set_impl} (\S\ref{subsection:set_impl}), @{class mapping_impl} (\S\ref{subsection:mapping_impl}), @{class cenum} (\S\ref{subsection:cenum}), @{class finite_UNIV} (\S\ref{subsection:finite_UNIV}), @{class card_UNIV} (\S\ref{subsection:card_UNIV}), and @{class cproper_interval} (\S\ref{subsection:cproper_interval}).
  Otherwise, well-sortedness errors like the following will occur:
\begin{verbatim}
*** Wellsortedness error:
*** Type expr not of sort {ceq,ccompare}
*** No type arity expr :: ceq
*** At command "value"
\end{verbatim}

  In detail, the sort requirements on the element type @{typ "'a"} are:
  \begin{itemize}
  \item @{class ceq} (\S\ref{subsection:ceq}), @{class ccompare} (\S\ref{subsection:ccompare}), and @{class set_impl} (\S\ref{subsection:set_impl}) for @{typ "'a set"} in general
  \item @{class cenum} (\S\ref{subsection:cenum}) for set comprehensions @{term "{x. P x}"},
  \item @{class card_UNIV}, @{class cproper_interval} for @{typ "'a set set"} and any deeper nesting of sets (\S\ref{subsection:card_UNIV}),%
   \footnote{%
     These type classes are only required for set complements (see \S\ref{subsection:well:sortedness}).
   }
    and
  \item @{class equal},%
    \footnote{%
      We deviate here from the strict separation of type classes, because it does not make sense to store types in a map on which we do not have equality, because the most basic operation @{term "Mapping.lookup"} inherently requires equality.
    }
    @{class ccompare} (\S\ref{subsection:ccompare}) and @{class mapping_impl} (\S\ref{subsection:mapping_impl}) for @{typ "('a, 'b) mapping"}.
  \end{itemize}
\<close>

subsection \<open>Equality testing\<close>
text_raw \<open>\label{subsection:ceq}\<close>

(*<*)context fixes dummy :: "'a :: {cenum, ceq, ccompare, set_impl, mapping_impl}" begin(*>*)
text \<open>
  The type class @{class ceq} defines the operation @{term [source] "CEQ('a) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) option" } for testing whether two elements are equal.%
  \footnote{%
    Technically, the type class @{class ceq} defines the operation @{term [source] ceq}.
    As usage often does not fully determine @{term [source] ceq}'s type, we use the notation @{term "CEQ('a)"} that explicitly mentions the type.
    In detail, @{term "CEQ('a)"} is translated to @{term [source] "CEQ('a) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) option" } including the type constraint.
    We do the same for the other type class operators:
    @{term "CCOMPARE('a)"} constrains the operation @{term [source] ccompare} (\S\ref{subsection:ccompare}), 
    @{term [source] "SET_IMPL('a)"} constrains the operation @{term [source] set_impl}, (\S\ref{subsection:set_impl}),
    @{term [source] "MAPPING_IMPL('a)"} (constrains the operation @{term [source] mapping_impl}, (\S\ref{subsection:mapping_impl}), and
    @{term "CENUM('a)"} constrains the operation @{term [source] cenum}, \S\ref{subsection:cenum}.
  }
  The test is embedded in an \<open>option\<close> value to allow for types that do not support executable equality test such as @{typ "'a \<Rightarrow> 'b"}.
  Whenever possible, @{term "CEQ('a)"} should provide an executable equality operator.
  Otherwise, membership tests on such sets will raise an exception at run-time.

  For data types, the \<open>derive\<close> command can automatically instantiates of @{class ceq},
  we only have to tell it whether an equality operation should be provided or not (parameter \<open>no\<close>).
\<close>
(*<*)end(*>*)

derive (eq) ceq expr

datatype example = Example
derive (no) ceq example

text \<open>
  In the remainder of this subsection, we look at how to manually instantiate a type for @{class ceq}.
  First, the simple case of a type constructor \<open>simple_tycon\<close> without parameters that already is an instance of @{class equal}:
\<close>
typedecl simple_tycon
axiomatization where simple_tycon_equal: "OFCLASS(simple_tycon, equal_class)"
instance simple_tycon :: equal by (rule simple_tycon_equal)

instantiation simple_tycon :: ceq begin
definition "CEQ(simple_tycon) = Some (=)"
instance by(intro_classes)(simp add: ceq_simple_tycon_def)
end

text \<open>
  For polymorphic types, this is a bit more involved, as the next example with @{typ "'a expr'"} illustrates (note that we could have delegated all this to \<open>derive\<close>). 
  First, we need an operation that implements equality tests with respect to a given equality operation on the polymorphic type.
  For data types, we can use the relator which the transfer package (method \<open>transfer\<close>) requires and the BNF package generates automatically.
  As we have used the old datatype package for @{typ "'a expr'"}, we must define it manually:
\<close>

context fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" begin
fun expr'_rel :: "'a expr' \<Rightarrow> 'b expr' \<Rightarrow> bool"
where
  "expr'_rel (Var' v)      (Var' v')        \<longleftrightarrow> R v v'"
| "expr'_rel (Lit' i)        (Lit' i')         \<longleftrightarrow> i = i'"
| "expr'_rel (Add' e\<^sub>1 e\<^sub>2) (Add' e\<^sub>1' e\<^sub>2') \<longleftrightarrow> expr'_rel e\<^sub>1 e\<^sub>1' \<and> expr'_rel e\<^sub>2 e\<^sub>2'"
| "expr'_rel _                 _                \<longleftrightarrow> False"
end

text \<open>If we give HOL equality as parameter, the relator is equality:\<close>

lemma expr'_rel_eq: "expr'_rel (=) e\<^sub>1 e\<^sub>2 \<longleftrightarrow> e\<^sub>1 = e\<^sub>2"
by(induct e\<^sub>1 e\<^sub>2 rule: expr'_rel.induct) simp_all
text \<open>
  Then, the instantiation is again canonical:
\<close>
instantiation expr' :: (ceq) ceq begin
definition
  "CEQ('a expr') =
  (case ID CEQ('a) of None \<Rightarrow> None | Some eq \<Rightarrow> Some (expr'_rel eq))"
instance
  by(intro_classes)
    (auto simp add: ceq_expr'_def expr'_rel_eq[abs_def] 
          dest: Collection_Eq.ID_ceq 
          split: option.split_asm)
end
(*<*)context fixes dummy :: "'a :: ceq" begin(*>*)
text \<open>
  Note the following two points:
  First, the instantiation should avoid to use @{term "(=)"} on terms of the polymorphic type.
  This keeps the LC framework separate from the type class @{class equal}, i.e., every choice of @{typ "'a"}
  in @{typ "'a expr'"} can be of sort @{class "ceq"}.
  The easiest way to achieve this is to obtain the equality test from @{term "CEQ('a)"}.
  Second, we use @{term "ID CEQ('a)"} instead of @{term "CEQ('a)"}.
  In proofs, we want that the simplifier uses assumptions like \<open>CEQ('a) = Some \<dots>\<close> for rewriting.
  However, @{term "CEQ('a)"} is a nullary constant, so the simplifier reverses such an equation, i.e., it only rewrites \<open>Some \<dots>\<close> to @{term "CEQ('a :: ceq)"}.
  Applying the identity function @{term "ID"} to @{term "CEQ('a :: ceq)"} avoids this, and the code generator eliminates all occurrences of @{term "ID"}.
  Although @{thm ID_def} by definition, do not use the conventional @{term "id"} instead of @{term ID}, because @{term "id CEQ('a :: ceq)"} immediately simplifies to @{term "CEQ('a :: ceq)"}.
\<close>
(*<*)end(*>*)

subsection \<open>Ordering\<close>
text_raw \<open>\label{subsection:ccompare}\<close>

(*<*)context fixes dummy :: "'a :: {ccompare, ceq}" begin(*>*)
text \<open>
  LC takes the order for storing elements in search trees from the type class @{class ccompare} rather than @{class compare}, because we cannot instantiate @{class compare} for some types (e.g., @{typ "'a set"} as @{term "(\<subseteq>)"} is not linear).
  Similar to @{term "CEQ('a)"} in class @{term ceq}, the class @{class ccompare} specifies an optional comparator @{term [source] "CCOMPARE('a) :: (('a \<Rightarrow> 'a \<Rightarrow> order)) option" }.
  If you cannot or do not want to implement a comparator on your type, you can default to @{term "None"}.
  In that case, you will not be able to use your type as elements of sets or as keys in maps implemented by search trees.

  If the type is a data type or instantiates @{class compare} and we wish to use that comparator also for the search tree, instantiation is again canonical:
  For our data type @{typ expr}, derive does everything!
\<close>
(*<*)end(*>*)
(*<*)(*>*)
derive ccompare expr
(*<*)(*>*)

text \<open>
  In general, the pattern for type constructors without parameters looks as follows:
\<close>
axiomatization where simple_tycon_compare: "OFCLASS(simple_tycon, compare_class)"
instance simple_tycon :: compare by (rule simple_tycon_compare)

derive (compare) ccompare simple_tycon


text \<open>
  For polymorphic types like @{typ "'a expr'"}, we should not do everything manually:
  First, we must define a comparator that takes the comparator on the type variable @{typ "'a"} as a parameter.
  This is necessary to maintain the separation between Isabelle/HOL's type classes (like @{class compare}) and LC's.
  Such a comparator is again easily defined by derive.
\<close>

derive ccompare expr'

thm ccompare_expr'_def comparator_expr'_simps

subsection \<open>Heuristics for picking an implementation\<close>
text_raw \<open>\label{subsection:set_impl} \label{subsection:mapping_impl}\<close>
(*<*)context fixes dummy :: "'a :: {ceq, ccompare, set_impl, mapping_impl}" begin(*>*)
text \<open>
  Now, we have defined the necessary operations on @{typ expr} and @{typ "'a expr'"} to store them in a set 
  or use them as the keys in a map.
  But before we can actually do so, we also have to say which data structure to use.
  The type classes @{class set_impl} and @{class mapping_impl} are used for this.

  They define the overloaded operations @{term [source] "SET_IMPL('a) :: ('a, set_impl) phantom" } and @{term [source] "MAPPING_IMPL('a) :: ('a, mapping_impl) phantom"}, respectively.
  The phantom type @{typ "('a, 'b) phantom"} from theory @{theory "HOL-Library.Phantom_Type"} is isomorphic to @{typ "'b"}, but formally depends on @{typ "'a"}.
  This way, the type class operations meet the requirement that their type contains exactly one type variable.
  The Haskell and ML compiler will get rid of the extra type constructor again.

  For sets, you can choose between @{term set_Collect} (characteristic function @{term P} like in @{term "{x. P x}"}), @{term set_DList} (distinct list), @{term set_RBT} (red-black tree), and @{term set_Monad} (list with duplicates).
  Additionally, you can define @{term "set_impl"} as @{term "set_Choose"} which picks the implementation based on the available operations (RBT if @{term "CCOMPARE('a)"} provides a linear order, else distinct lists if @{term "CEQ('a)"} provides equality testing, and lists with duplicates otherwise).
  @{term "set_Choose"} is the safest choice because it picks only a data structure when the required operations are actually available.
  If @{term set_impl} picks a specific implementation, Isabelle does not ensure that all required operations are indeed available.

  For maps, the choices are @{term "mapping_Assoc_List"} (associative list without duplicates), @{term "mapping_RBT"} (red-black tree), and @{term "mapping_Mapping"} (closures with function update).
  Again, there is also the @{term "mapping_Choose"} heuristics.
  
  For simple cases, \<open>derive\<close> can be used again (even if the type is not a data type).
  Consider, e.g., the following instantiations:
  @{typ "expr set"} uses RBTs, @{typ "(expr, _) mapping"} and @{typ "'a expr' set"} use the heuristics, and @{typ "('a expr', _) mapping"} uses the same implementation as @{typ "('a, _) mapping"}.
\<close>
(*<*)end(*>*)

derive (rbt) set_impl expr
derive (choose) mapping_impl expr
derive (choose) set_impl expr'

text \<open>
  More complex cases such as taking the implementation preference of a type parameter must be done manually.
\<close>

instantiation expr' :: (mapping_impl) mapping_impl begin
definition
  "MAPPING_IMPL('a expr') = 
   Phantom('a expr') (of_phantom MAPPING_IMPL('a))"
instance ..
end

(*<*)
locale mynamespace begin
definition empty where "empty = Mapping.empty" 
declare (in -) mynamespace.empty_def [code]
(*>*)
text \<open>
  To see the effect of the different configurations, consider the following examples where @{term [names_short] "empty"} refers to @{term "Mapping.empty"}.
  For that, we must disable pretty printing for sets as follows:
\<close>
declare (*<*)(in -) (*>*)pretty_sets[code_post del]
text \<open>
  \begin{center}
    \small
    \begin{tabular}{ll}
      \toprule
      \isamarkuptrue\isacommand{value}\isamarkupfalse\ {\isacharbrackleft}code{\isacharbrackright}
      &
      \textbf{result}
      \\
      \midrule
      @{term [source] "{} :: expr set"}
      &
      @{value [names_short] "{} :: expr set"}
      \\
      @{term [source] "empty :: (expr, unit) mapping"}
      &
      @{value [names_short] "empty :: (expr, unit) mapping"}
      \\
      \midrule
      @{term [source] "{} :: string expr' set"}
     &
      @{value [names_short] "{} :: string expr' set"}
      \\
      @{term [source] "{} :: (nat \<Rightarrow> nat) expr' set"}
      &
      @{value [names_short] "{} :: (nat \<Rightarrow> nat) expr' set"}
      \\
      @{term [source] "{} :: bool expr' set"}
      &
      @{value [names_short] "{} :: bool expr' set"}
      \\
      @{term [source] "empty :: (bool expr', unit) mapping"}
      &
      @{value [names_short] "empty :: (bool expr', unit) mapping"}
      \\
      \bottomrule
    \end{tabular}
  \end{center}
  
  For @{typ expr}, @{term mapping_Choose} picks RBTs, because @{term "CCOMPARE(expr)"} provides a comparison operation for @{typ "expr"}.
  For @{typ "'a expr'"}, the effect of @{term set_Choose} is more pronounced:
  @{term "CCOMPARE(string)"} is not @{term "None"}, so neither is @{term "CCOMPARE(string expr')"}, and @{term set_Choose} picks RBTs.
  As @{typ "nat \<Rightarrow> nat"} neither provides equality tests (@{class ceq}) nor comparisons (@{class ccompare}), neither does @{typ "(nat \<Rightarrow> nat) expr'"}, so we use lists with duplicates.
  The last two examples show the difference between inheriting a choice and choosing freshly:
  By default, @{typ bool} prefers distinct (associative) lists over RBTs, because there are just two elements.
  As @{typ "bool expr'"} enherits the choice for maps from @{typ bool}, an associative list implements @{term [source] "empty :: (bool expr', unit) mapping"}.
  For sets, in contrast, @{term "SET_IMPL('a expr')"} discards @{typ 'a}'s preferences and picks RBTs, because there is a comparison operation.

  Finally, let's enable pretty-printing for sets again:
\<close>
declare (*<*)(in -) (*>*)pretty_sets [code_post]
(*<*)
  (* The following value commands ensure that the code generator executes @{value ...} above,
     I could not find a way to specify [code] to @{value}. *)
  value [code] "{} :: expr set"
  value [code] "empty :: (expr, unit) mapping"
  value [code] "{} :: string expr' set"
  value [code] "{} :: (nat \<Rightarrow> nat) expr' set"
  value [code] "{} :: bool expr' set"
  value [code] "empty :: (bool expr', unit) mapping"
(*>*)   
(*<*)end(*>*)

subsection \<open>Set comprehensions\<close>
text_raw \<open>\label{subsection:cenum}\<close>

(*<*)context fixes dummy :: "'a :: cenum" begin(*>*)
text \<open>
  If you use the default code generator setup that comes with Isabelle, set comprehensions @{term [source] "{x. P x} :: 'a set"} are only executable if the type @{typ 'a} has sort @{class enum}.
  Internally, Isabelle's code generator transforms set comprehensions into an explicit list of elements which it obtains from the list @{term enum} of all of @{typ "'a"}'s elements.
  Thus, the type must be an instance of @{class enum}, i.e., finite in particular.
  For example, @{term "{c. CHR ''A'' \<le> c \<and> c \<le> CHR ''D''}"} evaluates to @{term "set ''ABCD''"}, the set of the characters A, B, C, and D.

  For compatibility, LC also implements such an enumeration strategy, but avoids the finiteness restriction.
  The type class @{class cenum} mimicks @{class enum}, but its single parameter @{term [source] "cEnum :: ('a list \<times> (('a \<Rightarrow> bool) \<Rightarrow> bool) \<times> (('a \<Rightarrow> bool) \<Rightarrow> bool)) option"} combines all of @{class enum}'s parameters, namely a list of all elements, a universal and an existential quantifier.
  \<open>option\<close> ensures that every type can be an instance as @{term "CENUM('a)"} can always default to @{term None}.
  
  For types that define @{term "CENUM('a)"}, set comprehensions evaluate to a list of their elements.
  Otherwise, set comprehensions are represented as a closure.
  This means that if the generated code contains at least one set comprehension, all element types of a set must instantiate @{class cenum}.
  Infinite types default to @{term None}, and enumerations for finite types are canoncial, see @{theory Containers.Collection_Enum} for examples.
\<close>
(*<*)end(*>*)

instantiation expr :: cenum begin
definition "CENUM(expr) = None"
instance by(intro_classes)(simp_all add: cEnum_expr_def)
end

derive (no) cenum expr'
derive compare_order expr

text_raw \<open>\par\medskip \isastyletext For example,\<close>
value "({b. b = True}, {x. compare x (Lit 0) = Lt})"
text_raw \<open>
  \isastyletext{}
  yields @{value "({b. b = True}, {x. compare x (Lit 0) = Lt})"}
\<close>

text \<open>
  LC keeps complements of such enumerated set comprehensions, i.e., @{term "- {b. b = True}"} evaluates to @{value "- {b. b = True}"}.
  If you want that the complement operation actually computes the elements of the complements, you have to replace the code equations for @{term uminus} as follows:
\<close>
declare Set_uminus_code[code del] Set_uminus_cenum[code]
(*<*)value "- {b. b = True}"(*>*)
text \<open>
  Then, @{term "- {b. b = True}"} becomes @{value "- {b. b = True}"}, but this applies to all complement invocations.
  For example, @{term [source] "UNIV :: bool set"} becomes @{value "UNIV :: bool set"}.
\<close>
(*<*)declare Set_uminus_cenum[code del] Set_uminus_code[code](*>*)

subsection \<open>Nested sets\<close>
text_raw \<open>\label{subsection:finite_UNIV} \label{subsection:card_UNIV} \label{subsection:cproper_interval}\<close>

(*<*)context fixes dummy :: "'a :: {card_UNIV, cproper_interval}" begin(*>*)
text \<open>
  To deal with nested sets such as @{typ "expr set set"}, the element type must provide three operations from three type classes:
  \begin{itemize}
  \item @{class finite_UNIV} from theory @{theory "HOL-Library.Cardinality"} defines the constant @{term [source] "finite_UNIV :: ('a, bool) phantom"} which designates whether the type is finite.
  \item @{class card_UNIV} from theory @{theory "HOL-Library.Cardinality"} defines the constant @{term [source] "card_UNIV :: ('a, nat) phantom"} which returns @{term "CARD('a)"}, i.e., the number of values in @{typ 'a}.
    If @{typ "'a"} is infinite, @{term "CARD('a) = 0"}.
  \item @{class cproper_interval} from theory @{theory Containers.Collection_Order} defines the function @{term [source] "cproper_interval :: 'a option \<Rightarrow> 'a option \<Rightarrow> bool"}.
    If the type @{typ "'a"} is finite and @{term "CCOMPARE('a)"} yields a linear order on @{typ "'a"}, then @{term "cproper_interval x y"} returns whether the open interval between @{term "x"} and @{term "y"} is non-empty.
    The bound @{term "None"} denotes unboundedness.
  \end{itemize}

  Note that the type class @{class finite_UNIV} must not be confused with the type class @{class finite}.
  @{class finite_UNIV} allows the generated code to examine whether a type is finite whereas @{class finite} requires that the type in fact is finite.
\<close>
(*<*)end(*>*)

text \<open>
  For datatypes, the theory @{theory Containers.Card_Datatype} defines some machinery to assist in proving that the type is (in)finite and has a given number of elements -- see @{file \<open>Examples/Card_Datatype_Ex.thy\<close>} for examples.
  With this, it is easy to instantiate @{class card_UNIV} for our running examples:
\<close>

lemma inj_expr [simp]: "inj Lit" "inj Var" "inj Add" "inj (Add e)"
by(simp_all add: fun_eq_iff inj_on_def)

lemma infinite_UNIV_expr: "\<not> finite (UNIV :: expr set)"
  including card_datatype
proof -
  have "rangeIt (Lit 0) (Add (Lit 0)) \<subseteq> UNIV" by simp
  from finite_subset[OF this] show ?thesis by auto
qed

instantiation expr :: card_UNIV begin
definition "finite_UNIV = Phantom(expr) False"
definition "card_UNIV = Phantom(expr) 0"
instance
  by intro_classes
     (simp_all add: finite_UNIV_expr_def card_UNIV_expr_def infinite_UNIV_expr)
end

lemma inj_expr' [simp]: "inj Lit'" "inj Var'" "inj Add'" "inj (Add' e)"
by(simp_all add: fun_eq_iff inj_on_def)

lemma infinite_UNIV_expr': "\<not> finite (UNIV :: 'a expr' set)"
  including card_datatype
proof -
  have "rangeIt (Lit' 0) (Add' (Lit' 0)) \<subseteq> UNIV" by simp
  from finite_subset[OF this] show ?thesis by auto
qed

instantiation expr' :: (type) card_UNIV begin
definition "finite_UNIV = Phantom('a expr') False"
definition "card_UNIV = Phantom('a expr') 0"
instance
  by intro_classes
     (simp_all add: finite_UNIV_expr'_def card_UNIV_expr'_def infinite_UNIV_expr')
end

text \<open>
  As @{typ expr} and @{typ "'a expr'"} are infinite, instantiating @{class cproper_interval} is trivial,
  because @{class cproper_interval} only makes assumptions about its parameters for finite types.
  Nevertheless, it is important to actually define @{term cproper_interval}, because the
  code generator requires a code equation.
\<close>

instantiation expr :: cproper_interval begin
definition cproper_interval_expr :: "expr proper_interval" 
  where "cproper_interval_expr _ _ = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_expr)
end

instantiation expr' :: (ccompare) cproper_interval begin
definition cproper_interval_expr' :: "'a expr' proper_interval" 
  where "cproper_interval_expr' _ _ = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_expr')
end

subsubsection \<open>Instantiation of @{class proper_interval}\<close>

text \<open>
  To illustrate what to do with finite types, we instantiate @{class proper_interval} for @{typ expr}.
  Like @{class ccompare} relates to @{class compare}, the class @{class cproper_interval} has a counterpart @{class proper_interval} without the finiteness assumption.
  Here, we first have to gather the simplification rules of the comparator from the derive
  invocation, especially, how the strict order of the comparator, @{term lt_of_comp}, can be defined.
  
  Since the order on lists is not yet shown to be consistent with the comparators that are used
  for lists, this part of the userguide is currently not available.
  
\<close>
(*
instantiation expr :: proper_interval begin

lemma less_expr_conv: "(<) = lt_of_comp comparator_expr" "(\<le>) = le_of_comp comparator_expr"
  using less_expr_def less_eq_expr_def unfolding compare_expr_def by auto

lemma lt_of_comp_expr: "lt_of_comp comparator_expr e1 e2 = (
  case e1 of 
    Var x1 \<Rightarrow> 
      (case e2 of 
        Var x2 \<Rightarrow> lt_of_comp (comparator_list comparator_of) x1 x2  
      | Lit _ \<Rightarrow> True
      | Add _ _ \<Rightarrow> True)
  | Lit i1 \<Rightarrow>
      (case e2 of
        Var _ \<Rightarrow> False
      | Lit i2 \<Rightarrow> lt_of_comp comparator_of i1 i2
      | Add _ _ \<Rightarrow> True)
  | Add a1 b1 \<Rightarrow>
      (case e2 of
        Var _ \<Rightarrow> False
      | Lit _ \<Rightarrow> False
      | Add a2 b2 \<Rightarrow> lt_of_comp comparator_expr a1 a2 
          \<or> le_of_comp comparator_expr a1 a2 \<and> lt_of_comp comparator_expr b1 b2) 
    )"
  by (simp add: lt_of_comp_def le_of_comp_def comp_lex_code split: expr.split order.split)
    
fun proper_interval_expr :: "expr option \<Rightarrow> expr option \<Rightarrow> bool"
where
  "proper_interval_expr None (Some (Var x)) \<longleftrightarrow> proper_interval None (Some x)"
| "proper_interval_expr (Some (Var x)) (Some (Var y)) \<longleftrightarrow> proper_interval (Some x) (Some y)"
| "proper_interval_expr (Some (Lit i)) (Some (Lit j)) \<longleftrightarrow> proper_interval (Some i) (Some j)"
| "proper_interval_expr (Some (Lit i)) (Some (Var x)) \<longleftrightarrow> False"
| "proper_interval_expr (Some (Add e1 e2)) (Some (Lit i)) \<longleftrightarrow> False"
| "proper_interval_expr (Some (Add e1 e2)) (Some (Var x)) \<longleftrightarrow> False"
| "proper_interval_expr (Some (Add e1 e2)) (Some (Add e1' e2')) \<longleftrightarrow> 
    (case compare e1 e1' of Lt \<Rightarrow> True | Eq \<Rightarrow> proper_interval_expr (Some e2) (Some e2') | Gt \<Rightarrow> False)"
| "proper_interval_expr _ _ \<longleftrightarrow> True"

instance
proof(intro_classes)
  fix x y :: expr
  show "proper_interval None (Some y) = (\<exists>z. z < y)"
    unfolding less_expr_conv
    by (cases y)(auto simp add: lt_of_comp_expr  intro: exI[where x="''''"])

  { fix x y have "x < Add x y" unfolding less_expr_conv 
      by(induct x arbitrary: y)(simp_all add: lt_of_comp_expr) }
  note le_Add = this
  thus "proper_interval (Some x) None = (\<exists>z. x < z)"
    by(simp add: less_expr_def exI[where x="Add x y"])

  note [simp] = less_expr_conv lt_of_comp_expr

  show "proper_interval (Some x) (Some y) = (\<exists>z. x < z \<and> z < y)"
  proof(induct "Some x" "Some y" arbitrary: x y rule: proper_interval_expr.induct)
    case 2
    show ?case by(auto simp add: proper_interval_list_aux_correct)
  next
    case (3 i j)
    show ?case by(auto intro: exI[where x="Lit (i + 1)"])
  next
    case (7 e1 e2 e1' e2')
    thus ?case by(auto intro: le_Add simp add: le_less)
  next
    case ("8_2" i e1 e2)
    show ?case by(auto intro: exI[where x="Lit (i + 1)"])
  next
    case ("8_5" x i) show ?case
      by(auto intro: exI[where x="Var (x @ [undefined])"] simp add: less_append_same_iff)
  next
    case ("8_6" x e1 e2) show ?case
      by(auto intro: exI[where x="Lit 0"])
  next
    case ("8_7" i e1 e2) show ?case
      by(auto intro: exI[where x="Lit (i + 1)"])
  next
    case ("8_10" x i) show ?case
      by(auto intro: exI[where x="Lit (i - 1)"])
  next
    case ("8_12" x e1 e2) show ?case
      by(auto intro: exI[where x="Lit 0"])
  next
    case ("8_13" i e1 e2) show ?case
      by(auto intro: exI[where x="Lit (i + 1)"])
  qed auto
qed simp
end
*)
(*<*)
value "{{Lit 1}}"
value "{{{Lit 1}}}"
value "{{{{Lit 1}}}}"
(*>*)

section \<open>New implementations for containers\<close>
text_raw \<open>\label{section:new:implementation}\<close>

(*<*)
typedecl 'v trie_raw
(*>*)

text \<open>
  This section explains how to add a new implementation for a container type.
  If you do so, please consider to add your implementation to this AFP entry.
\<close>

subsection \<open>Model and verify the data structure\<close>
text_raw \<open>\label{subsection:implement:data:structure}\<close>
text \<open>
  First, you of course have to define the data structure and verify that it has the required properties.
  As our running example, we use a trie to implement @{typ "('a, 'b) mapping"}.
  A trie is a binary tree whose the nodes store the values, the keys are the paths from the root to the given node.
  We use lists of @{typ bool}ans for the keys where the @{typ bool}ean indicates whether we should go to the left or right child.

  For brevity, we skip this step and rather assume that the type @{typ "'v trie_raw"} of tries has following operations and properties:
\<close>
type_synonym trie_key = "bool list"
axiomatization
  trie_empty :: "'v trie_raw" and
  trie_update :: "trie_key \<Rightarrow> 'v \<Rightarrow> 'v trie_raw \<Rightarrow> 'v trie_raw" and
  trie_lookup :: "'v trie_raw \<Rightarrow> trie_key \<Rightarrow> 'v option" and
  trie_keys :: "'v trie_raw \<Rightarrow> trie_key set"
where trie_lookup_empty: "trie_lookup trie_empty = Map.empty"
  and trie_lookup_update: 
    "trie_lookup (trie_update k v t) = (trie_lookup t)(k \<mapsto> v)"
  and trie_keys_dom_lookup: "trie_keys t = dom (trie_lookup t)"

text \<open>
  This is only a minimal example.
  A full-fledged implementation has to provide more operations and -- for efficiency -- should use more than just @{typ bool}eans for the keys.
\<close>

(*<*) (* Implement trie by free term algebra *)
code_datatype trie_empty trie_update
lemmas [code] = trie_lookup_empty trie_lookup_update

lemma trie_keys_empty [code]: "trie_keys trie_empty = {}"
by(simp add: trie_keys_dom_lookup trie_lookup_empty)

lemma trie_keys_update [code]:
  "trie_keys (trie_update k v t) = insert k (trie_keys t)"
by(simp add: trie_keys_dom_lookup trie_lookup_update)
(*>*)

subsection \<open>Generalise the data structure\<close>
text_raw \<open>\label{subsection:introduce:type:class}\<close>
text \<open>
  As @{typ "('k, 'v) mapping"} store keys of arbitrary type @{typ "'k"}, not just @{typ "trie_key"}, we cannot use @{typ "'v trie_raw"} directly.
  Instead, we must first convert arbitrary types @{typ "'k"} into @{typ "trie_key"}.
  Of course, this is not always possbile, but we only have to make sure that we pick tries as implementation only if the types do.
  This is similar to red-black trees which require an order.
  Hence, we introduce a type class to convert arbitrary keys into trie keys.
  We make the conversions optional such that every type can instantiate the type class, just as LC does for @{class ceq} and @{class ccompare}.
\<close>
type_synonym 'a cbl = "(('a \<Rightarrow> bool list) \<times> (bool list \<Rightarrow> 'a)) option"
class cbl =
  fixes cbl :: "'a cbl"
  assumes inj_to_bl: "ID cbl = Some (to_bl, from_bl) \<Longrightarrow> inj to_bl"
  and to_bl_inverse: "ID cbl = Some (to_bl, from_bl) \<Longrightarrow> from_bl (to_bl a) = a"
begin
abbreviation from_bl where "from_bl \<equiv> snd (the (ID cbl))"
abbreviation to_bl where "to_bl \<equiv> fst (the (ID cbl))"
end

text \<open>
  It is best to immediately provide the instances for as many types as possible.
  Here, we only present two examples: @{typ unit} provides conversion functions, @{typ "'a \<Rightarrow> 'b"} does not.
\<close>
instantiation unit :: cbl begin
definition "cbl = Some (\<lambda>_. [], \<lambda>_. ())"
instance by(intro_classes)(auto simp add: cbl_unit_def ID_Some intro: injI)
end

instantiation "fun" :: (type, type) cbl begin
definition "cbl = (None :: ('a \<Rightarrow> 'b) cbl)"
instance by intro_classes(simp_all add: cbl_fun_def ID_None)
end

subsection \<open>Hide the invariants of the data structure\<close>
text_raw \<open>\label{subsection:hide:invariants}\<close>
text \<open>
  Many data structures have invariants on which the operations rely.
  You must hide such invariants in a \isamarkuptrue\isacommand{typedef}\isamarkupfalse{} before connecting to the container, because the code generator cannot handle explicit invariants.
  The type must be inhabited even if the types of the elements do not provide the required operations.
  The easiest way is often to ignore all invariants in that case.

  In our example, we require that all keys in the trie represent encoded values.
\<close>
typedef (overloaded) ('k :: cbl, 'v) trie = 
  "{t :: 'v trie_raw. 
    trie_keys t \<subseteq> range (to_bl :: 'k \<Rightarrow> trie_key) \<or> ID (cbl :: 'k cbl) = None}"
proof
  show "trie_empty \<in> ?trie"
    by(simp add: trie_keys_dom_lookup trie_lookup_empty)
qed

text \<open>
  Next, transfer the operations to the new type.
  The transfer package does a good job here.
\<close>

setup_lifting type_definition_trie \<comment> \<open>also sets up code generation\<close>

lift_definition empty :: "('k :: cbl, 'v) trie" 
  is trie_empty
  by(simp add: trie_keys_empty)

lift_definition lookup :: "('k :: cbl, 'v) trie \<Rightarrow> 'k \<Rightarrow> 'v option"
  is "\<lambda>t. trie_lookup t \<circ> to_bl" .

lift_definition update :: "'k \<Rightarrow> 'v \<Rightarrow> ('k :: cbl, 'v) trie \<Rightarrow> ('k, 'v) trie"
  is "trie_update \<circ> to_bl"
  by(auto simp add: trie_keys_dom_lookup trie_lookup_update)

lift_definition keys :: "('k :: cbl, 'v) trie \<Rightarrow> 'k set"
  is "\<lambda>t. from_bl ` trie_keys t" .

text \<open>
  And now we go for the properties.
  Note that some properties hold only if the type class operations are actually provided, i.e., @{term "cbl \<noteq> None"} in our example.
\<close>

lemma lookup_empty: "lookup empty = Map.empty"
by transfer(simp add: trie_lookup_empty fun_eq_iff)

context
  fixes t :: "('k :: cbl, 'v) trie"
  assumes ID_cbl: "ID (cbl :: 'k cbl) \<noteq> None"
begin

lemma lookup_update: "lookup (update k v t) = (lookup t)(k \<mapsto> v)"
using ID_cbl
by transfer(auto simp add: trie_lookup_update fun_eq_iff dest: inj_to_bl[THEN injD])

lemma keys_conv_dom_lookup: "keys t = dom (lookup t)"
using ID_cbl
by transfer(force simp add: trie_keys_dom_lookup to_bl_inverse intro: rev_image_eqI)

end

subsection \<open>Connecting to the container\<close>
text_raw \<open>\label{subsection:connect:container}\<close>
text \<open>
  Connecting to the container (@{typ "('a, 'b) mapping"} in our example) takes three steps:
  \begin{enumerate}
  \item Define a new pseudo-constructor
  \item Implement the container operations for the new type
  \item Configure the heuristics to automatically pick an implementation
  \item Test thoroughly
  \end{enumerate}
  Thorough testing is particularly important, because Isabelle does not check whether you have implemented all your operations, whether you have configured your heuristics sensibly, nor whether your implementation always terminates.
\<close>

subsubsection \<open>Define a new pseudo-constructor\<close>

text \<open>
  Define a function that returns the abstract container view for a data structure value, and declare it as a datatype constructor for code generation with \isamarkuptrue\isacommand{code{\isacharunderscore}datatype}\isamarkupfalse.
  Unfortunately, you have to repeat all existing pseudo-constructors, because there is no way to extract the current set of pseudo-constructors from the code generator.
  We call them pseudo-constructors, because they do not behave like datatype constructors in the logic.
  For example, ours are neither injective nor disjoint.
\<close>

definition Trie_Mapping :: "('k :: cbl, 'v) trie \<Rightarrow> ('k, 'v) mapping" 
where [simp, code del]: "Trie_Mapping t = Mapping.Mapping (lookup t)"

code_datatype Assoc_List_Mapping RBT_Mapping Mapping Trie_Mapping

subsubsection \<open>Implement the operations\<close>

text \<open>
  Next, you have to prove and declare code equations that implement the container operations for the new implementation.
  Typically, these just dispatch to the operations on the type from \S\ref{subsection:hide:invariants}.
  Some operations depend on the type class operations from \S\ref{subsection:introduce:type:class} being defined; then, the code equation must check that the operations are indeed defined.
  If not, there is usually no way to implement the operation, so the code should raise an exception.
  Logically, we use the function @{term "Code.abort"} of type @{typ "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"} with definition @{term "\<lambda>_ f. f ()"}, but the generated code raises an exception \texttt{Fail} with the given message (the unit closure avoids non-termination in strict languages).
  This function gets the exception message and the unit-closure of the equation's left-hand side as argument, because it is then trivial to prove equality.

  Again, we only show a small set of operations; a realistic implementation should cover as many as possible.
\<close>
context fixes t :: "('k :: cbl, 'v) trie" begin

lemma lookup_Trie_Mapping [code]:
  "Mapping.lookup (Trie_Mapping t) = lookup t"
  \<comment> \<open>Lookup does not need the check on @{term cbl},
        because we have defined the pseudo-constructor @{term Trie_Mapping} in terms of @{term "lookup"}\<close>
by simp(transfer, simp)

lemma update_Trie_Mapping [code]:
  "Mapping.update k v (Trie_Mapping t) = 
  (case ID cbl :: 'k cbl of
     None \<Rightarrow> Code.abort (STR ''update Trie_Mapping: cbl = None'') (\<lambda>_. Mapping.update k v (Trie_Mapping t))
   | Some _ \<Rightarrow> Trie_Mapping (update k v t))"
by(simp split: option.split add: lookup_update Mapping.update.abs_eq)

lemma keys_Trie_Mapping [code]:
  "Mapping.keys (Trie_Mapping t) =
  (case ID cbl :: 'k cbl of
     None \<Rightarrow> Code.abort (STR ''keys Trie_Mapping: cbl = None'') (\<lambda>_. Mapping.keys (Trie_Mapping t))
   | Some _ \<Rightarrow> keys t)"
by(simp add: Mapping.keys.abs_eq keys_conv_dom_lookup split: option.split)

end

text \<open>
  These equations do not replace the existing equations for the other constructors, but they do take precedence over them.
  If there is already a generic implementation for an operation @{term "foo"}, say @{term "foo A = gen_foo A"}, and you prove a specialised equation @{term "foo (Trie_Mapping t) = trie_foo t"}, then when you call @{term "foo"} on some @{term "Trie_Mapping t"}, your equation will kick in.
  LC exploits this sequentiality especially for binary operators on sets like @{term "(\<inter>)"}, where there are generic implementations and faster specialised ones.
\<close>

subsubsection \<open>Configure the heuristics\<close>

text \<open>
  Finally, you should setup the heuristics that automatically picks a container implementation based on the types of the elements (\S\ref{subsection:set_impl}).

  The heuristics uses a type with a single value, e.g., @{typ mapping_impl} with value @{term Mapping_IMPL}, but there is one pseudo-constructor for each container implementation in the generated code.
  All these pseudo-constructors are the same in the logic, but they are different in the generated code.
  Hence, the generated code can distinguish them, but we do not have to commit to anything in the logic.
  This allows to reconfigure and extend the heuristic at any time.

  First, define and declare a new pseudo-constructor for the heuristics.
  Again, be sure to redeclare all previous pseudo-constructors.
\<close>
definition mapping_Trie :: mapping_impl 
where [simp]: "mapping_Trie = Mapping_IMPL"

code_datatype 
  mapping_Choose mapping_Assoc_List mapping_RBT mapping_Mapping mapping_Trie

text \<open>
  Then, adjust the implementation of the automatic choice.
  For every initial value of the container (such as the empty map or the empty set), there is one new constant (e.g., @{term mapping_empty_choose} and @{term set_empty_choose}) equivalent to it.
  Its code equation, however, checks the available operations from the type classes and picks an appropriate implementation.
  
  For example, the following prefers red-black trees over tries, but tries over associative lists:
\<close>

lemma mapping_empty_choose_code [code]:
  "(mapping_empty_choose :: ('a :: {ccompare, cbl}, 'b) mapping) =
   (case ID CCOMPARE('a) of Some _  \<Rightarrow> RBT_Mapping RBT_Mapping2.empty
    | None \<Rightarrow>
      case ID (cbl :: 'a cbl) of Some _ \<Rightarrow> Trie_Mapping empty 
      | None \<Rightarrow> Assoc_List_Mapping DAList.empty)"
by(auto split: option.split simp add: DAList.lookup_empty[abs_def] Mapping.empty_def lookup_empty)

text \<open>
  There is also a second function for every such initial value that dispatches on the pseudo-constructors for @{typ mapping_impl}.
  This function is used to pick the right implementation for types that specify a preference.
\<close>
lemma mapping_empty_code [code]:
  "mapping_empty mapping_Trie = Trie_Mapping empty"
by(simp add: lookup_empty Mapping.empty_def)

text \<open>
  For @{typ "('k, 'v) mapping"}, LC also has a function @{term "mapping_impl_choose2"} which is given two preferences and returns one (for @{typ "'a set"}, it is called @{term "set_impl_choose2"}).
  Polymorphic type constructors like @{typ "'a + 'b"} use it to pick an implementation based on the preferences of @{typ "'a"} and @{typ "'b"}.
  By default, it returns @{term mapping_Choose}, i.e., ignore the preferences.
  You should add a code equation like the following that overrides this choice if both preferences are your new data structure:
\<close>

lemma mapping_impl_choose2_Trie [code]:
  "mapping_impl_choose2 mapping_Trie mapping_Trie = mapping_Trie"
by(simp add: mapping_Trie_def)

text \<open>
  If your new data structure is better than the existing ones for some element type, you should reconfigure the type's preferene.
  As all preferences are logically equal, you can prove (and declare) the appropriate code equation.
  For example, the following prefers tries for keys of type @{typ "unit"}:
\<close>

lemma mapping_impl_unit_Trie [code]:
  "MAPPING_IMPL(unit) = Phantom(unit) mapping_Trie"
by(simp add: mapping_impl_unit_def)

value "Mapping.empty :: (unit, int) mapping"

text \<open>
  You can also use your new pseudo-constructor with \<open>derive\<close> in instantiations, just give its name as option:
\<close>
derive (mapping_Trie) mapping_impl simple_tycon

section \<open>Changing the configuration\<close>

text \<open>
  As containers are connected to data structures only by refinement in the code generator, this can always be adapted later on.
  You can add new data structures as explained in \S\ref{section:new:implementation}.
  If you want to drop one, you redeclare the remaining pseudo-constructors with \isamarkuptrue\isacommand{code{\isacharunderscore}datatype}\isamarkupfalse{} and delete all code equations that pattern-match on the obsolete pseudo-constructors.
  The command \isamarkuptrue\isacommand{code{\isacharunderscore}thms}\isamarkupfalse{} will tell you which constants have such code equations.
  You can also freely adapt the heuristics for picking implementations as described in \S\ref{subsection:connect:container}.

  One thing, however, you cannot change afterwards, namely the decision whether an element type supports an operation and if so how it does, because this decision is visible in the logic.
\<close>

section \<open>New containers types\<close>

text \<open>
  We hope that the above explanations and the examples with sets and maps suffice to show what you need to do if you add a new container type, e.g., priority queues.
  There are three steps:
  \begin{enumerate}
  \item \textbf{Introduce a type constructor for the container.}
    \\
    Your new container type must not be a composite type, like @{typ "'a \<Rightarrow> 'b option"} for maps, because refinement for code generation only works with a single type constructor.
    Neither should you reuse a type constructor that is used already in other contexts, e.g., do not use @{typ "'a list"} to model queues.

    Introduce a new type constructor if necessary (e.g., @{typ "('a, 'b) mapping"} for maps) -- if your container type already has its own type constructor, everything is fine.

  \item \textbf{Implement the data structures} 
    \\
    and connect them to the container type as described in \S\ref{section:new:implementation}.

  \item \textbf{Define a heuristics for picking an implementation.}
    \\
    See \cite{Lochbihler2013ITP} for an explanation.
  \end{enumerate}
\<close>

section \<open>Troubleshooting\<close>

text \<open>
  This section describes some difficulties in using LC that we have come across, provides some background for them, and discusses how to overcome them.
  If you experience other difficulties, please contact the author.
\<close>

subsection \<open>Nesting of mappings\<close>

text \<open>
  Mappings can be arbitrarily nested on the value side, e.g., @{typ "('a, ('b, 'c) mapping) mapping"}.
  However, @{typ "('a, 'b) mapping"} cannot currently be the key of a mapping, i.e., code generation fails for @{typ "(('a, 'b) mapping, 'c) mapping"}.
  Simiarly, you cannot have a set of mappings like @{typ "('a, 'b) mapping set"} at the moment.
  There are no issues to make this work, we have just not seen the need for it.
  If you need to generate code for such types, please get in touch with the author.
\<close>

subsection \<open>Wellsortedness errors\<close>
text_raw \<open>\label{subsection:well:sortedness}\<close>

text \<open>
  LC uses its own hierarchy of type classes which is distinct from Isabelle/HOL's.
  This ensures that every type can be made an instance of LC's type classes.
  Consequently, you must instantiate these classes for your own types.
  The following lists where you can find information about the classes and examples how to instantiate them:
  \begin{center}
    \begin{tabular}{lll}
      \textbf{type class} & \textbf{user guide} & \textbf{theory}
      \\
      @{class card_UNIV} & \S\ref{subsection:card_UNIV} & @{theory "HOL-Library.Cardinality"} 
      %@{term "Cardinality.card_UNIV_class"}
      \\
      @{class cenum} & \S\ref{subsection:cenum} & @{theory Containers.Collection_Enum}
      %@{term "Collection_Enum.cenum_class"}
      \\
      @{class ceq} & \S\ref{subsection:ceq} & @{theory Containers.Collection_Eq}
      %@{term "Collection_Eq.ceq_class"}
      \\
      @{class ccompare} & \S\ref{subsection:ccompare} & @{theory Containers.Collection_Order}
      %@{term "Collection_Order.ccompare_class"}
      \\
      @{class cproper_interval} & \S\ref{subsection:cproper_interval} & @{theory Containers.Collection_Order}
      %@{term "Collection_Order.cproper_interval_class"}
      \\
      @{class finite_UNIV} & \S\ref{subsection:finite_UNIV} & @{theory "HOL-Library.Cardinality"}
      %@{term "Cardinality.finite_UNIV_class"}
      \\
      @{class mapping_impl} & \S\ref{subsection:mapping_impl} & @{theory Containers.Mapping_Impl}
      %@{term "Mapping_Impl.mapping_impl_class"}
      \\
      @{class set_impl} & \S\ref{subsection:set_impl} & @{theory Containers.Set_Impl}
      %@{term "Set_Impl.set_impl_class"}
      \\
    \end{tabular}
  \end{center}

  The type classes @{class card_UNIV} and @{class cproper_interval} are only required to implement the operations on set complements.
  If your code does not need complements, you can manually delete the code equations involving @{const "Complement"}, the theorem list @{thm [source] set_complement_code} collects them.
  It is also recommended that you remove the pseudo-constructor @{const Complement} from the code generator.
  Note that some set operations like @{term "A - B"} and @{const UNIV} have no code equations any more.
\<close>
declare set_complement_code[code del]
code_datatype Collect_set DList_set RBT_set Set_Monad
(*<*)
datatype minimal_sorts = Minimal_Sorts bool
derive (eq) ceq minimal_sorts
derive (no) ccompare minimal_sorts
derive (monad) set_impl minimal_sorts
derive (no) cenum minimal_sorts
value "{Minimal_Sorts True} \<union> {} \<inter> Minimal_Sorts ` {True, False}"
(*>*)

subsection \<open>Exception raised at run-time\<close>
text_raw \<open>\label{subsection:set_impl_unsupported_operation}\<close>

text \<open>
  Not all combinations of data and container implementation are possible.
  For example, you cannot implement a set of functions with a RBT, because there is no order on @{typ "'a \<Rightarrow> 'b"}.
  If you try, the code will raise an exception \texttt{Fail} (with an exception message) or \texttt{Match}.
  They can occur in three cases:

  \begin{enumerate}
  \item
    You have misconfigured the heuristics that picks implementations (\S\ref{subsection:set_impl}), or you have manually picked an implementation that requires an operation that the element type does not provide.
    Printing a stack trace for the exception may help you in locating the error.

  \item You are trying to invoke an operation on a set complement which cannot be implemented on a complement representation, e.g., @{term "(`)"}.
    If the element type is enumerable, provide an instance of @{class cenum} and choose to represent complements of sets of enumerable types by the elements rather than the elements of the complement (see \S\ref{subsection:cenum} for how to do this).

  \item You use set comprehensions on types which do not provide an enumeration (i.e., they are represented as closures) or you chose to represent a map as a closure.

    A lot of operations are not implementable for closures, in particular those that return some element of the container

    Inspect the code equations with \isacommand{code{\isacharunderscore}thms} and look for calls to @{term "Collect_set"} and @{term "Mapping"} which are LC's constructor for sets and maps as closures.

    Note that the code generator preprocesses set comprehensions like @{term "{i < 4|i :: int. i > 2}"} to @{term "(\<lambda>i :: int. i < 4) ` {i. i > 2}"}, so this is a set comprehension over @{typ int} rather than @{typ bool}.
  \end{enumerate}
\<close>

(*<*)
definition test_set_impl_unsupported_operation1 :: "unit \<Rightarrow> (int \<Rightarrow> int) set"
where "test_set_impl_unsupported_operation1 _ = RBT_set RBT_Set2.empty \<union> {}"

definition test_set_impl_unsupported_operation2 :: "unit \<Rightarrow> bool set"
where "test_set_impl_unsupported_operation2 _ = {i < 4 | i :: int. i > 2}"

definition test_mapping_impl_unsupported_operation :: "unit \<Rightarrow> bool"
where 
  "test_mapping_impl_unsupported_operation _ = 
   Mapping.is_empty (RBT_Mapping (RBT_Mapping2.empty) :: (Enum.finite_4, unit) mapping)"

ML_val \<open>
fun test_fail s f =
  let
    fun error s' = Fail ("exception Fail \"" ^ s ^ "\" expected, but got " ^ s')
  in
    (f (); raise (error "no exception") )
    handle
      Fail s' => if s = s' then () else raise (error s')
  end;

test_fail "union RBT_set Set_Monad: ccompare = None" @{code test_set_impl_unsupported_operation1};
test_fail "image Collect_set" @{code test_set_impl_unsupported_operation2};
test_fail "is_empty RBT_Mapping: ccompare = None" @{code test_mapping_impl_unsupported_operation};
\<close>
(*>*)

subsection \<open>LC slows down my code\<close>

text \<open>
  Normally, this will not happen, because LC's data structures are more efficient than Isabelle's list-based implementations.
  However, in some rare cases, you can experience a slowdown:
\<close>
(*<*)
definition tiny_set :: "nat set"
where tiny_set_code: "tiny_set = {1, 2}"
(*>*)
text_raw \<open>
  \isastyletext
  \begin{enumerate}
  \item \textbf{Your containers contain just a few elements.}
    \\
    In that case, the overhead of the heuristics to pick an implementation outweighs the benefits of efficient implementations.
    You should identify the tiny containers and disable the heuristics locally.
    You do so by replacing the initial value like @{term "{}"} and @{term "Mapping.empty"} with low-overhead constructors like @{term "Set_Monad"} and @{term "Mapping"}.
    For example, if @{thm [source] tiny_set_code}: @{thm tiny_set_code} is your code equation with a tiny set,
    the following changes the code equation to directly use the list-based representation, i.e., disables the heuristics:
    \par
\<close>
lemma empty_Set_Monad: "{} = Set_Monad []" by simp
declare tiny_set_code[code del, unfolded empty_Set_Monad, code]
text_raw \<open>
    \isastyletext
    \par
     If you want to globally disable the heuristics, you can also declare an equation like @{thm [source] empty_Set_Monad} as [code].

  \item \textbf{The element type contains many type constructors and some type variables.}
    \\
    LC heavily relies on type classes, and type classes are implemented as dictionaries if the compiler cannot statically resolve them, i.e., if there are type variables.
    For type constructors with type variables (like @{typ "'a * 'b"}), LC's definitions of the type class parameters recursively calls itself on the type variables, i.e., @{typ "'a"} and @{typ "'b"}.
    If the element type is polymorphic, the compiler cannot precompute these recursive calls and therefore they have to be constructed repeatedly at run time.
    If you wrap your complicated type in a new type constructor, you can define optimised equations for the type class parameters.
  \end{enumerate}
\<close>

(*<*)
end
(*>*)
