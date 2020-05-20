(*<*)
theory Preliminaries
imports Abbrevs
begin


record foorecord = fld\<^sub>1 :: nat fld\<^sub>2 ::nat
datatype foodatatype = Foo
notation (latex output)
Foo ("\<^latex>\<open>\\constructor{Foo}\<close>")

(* TODO:
setup {*add_constructor_syntax "latex" "Preliminaries.foodatatype" *}
*)
(*>*)
section \<open>Preliminaries \label{sec:preliminaries}\<close>
text \<open>
The formalization presented in this papaer is mechanized and checked within the generic interactive theorem prover \emph{Isabelle}\cite{Paulson:IGTP94}. 
Isabelle is called generic as it provides a framework to formalize various \emph{object logics} declared via natural deduction style inference rules.
The object logic that we employ for our formalization is the higher order logic of \emph{Isabelle/HOL}\cite{Nipkow:IHOL02}. 

This article is written using Isabelle's document generation facilities, which guarantees a close correspondence between the presentation and the actual theory files.
We distinguish formal entities typographically from other text. 
We use a sans serif font for types and constants (including functions and predicates), \eg @{term "map"}, a slanted serif font for free variables, \eg @{term "x"}, and a slanted sans serif font for bound variables, \eg @{term "Bind x. x"}.
Small capitals are used for data type constructors, \eg @{term[names_short] "Foo"}, and type variables have a leading tick, \eg  @{typ "'a"}. HOL keywords are typeset in type-writer font, \eg \holkeyword{let}. %We also take the freedom to borrow C notation, \eg @{term "UnsgndT"} when presenting C0.

To group common premises and to support modular reasoning Isabelle provides \emph{locales}\cite{Ballarin:TYPES03-34,Ballarin:MKM06-31}. 
A locale provides a name for a context of fixed parameters and premises, together with an elaborate infrastructure to define new locales by inheriting and extending other locales, prove theorems within locales and interpret (instantiate) locales. In our formalization we employ this infrastructure to separate the memory system from the programming language semantics. 

The logical and mathematical notions follow the standard notational conventions with a bias towards functional programming. 
We only present the more unconventional parts here. 
We prefer curried function application, \eg @{term "f a b"} instead of @{term [mode=uncurry] "f a b"}.
In this setting the latter becomes a function application to \emph{one} argument, which happens to be a pair.

Isabelle/HOL provides a library of standard types like Booleans, natural numbers, integers, total functions, pairs, lists, and sets. Moreover, there are packages to define new data types and records. 
Isabelle allows polymorphic types, \eg @{typ "'a list"} is the list type with type variable @{typ "'a"}. 
In HOL all functions are total, \eg @{typ "nat \<Rightarrow> nat"} is a total function on natural numbers. 
A function update is @{thm fun_upd_def[of f y v]}.
To formalize partial functions the type @{typ "'a option"} is used. 
It is a data type with two constructors, one to inject values of the base type, \eg @{term "Some x"}, and the additional element @{term "None"}. 
A base value can be projected with the function @{term "the"}, which is defined by the sole equation @{thm option.sel [of x]}. 
Since HOL is a total logic the term @{term "the None"} is still a well-defined yet un(der)specified value. 
Partial functions are usually represented by the type \<open>\<^latex>\<open>\tfreeify{\<close>'a\<^latex>\<open>}\<close> \<Rightarrow> \<^latex>\<open>\tfreeify{\<close>'b\<^latex>\<open>}\<close> option\<close>, abbreviated as @{typ  "'a \<rightharpoonup> 'b"}. 
They are commonly used as \emph{maps}. 
%With @{term "map_of xs"} we construct a map from an association list, \ie a list of key~/~value pairs. 
We denote the domain of map  @{term "m"} by @{term "dom m"}. % not used: and to its range by @{term "ran m"}. 
A map update is written as @{term "m(a := Some v)"}.
%With @{term "m\<^sub>1 ++ m\<^sub>2"} we add the map @{term "m\<^sub>2"} to map @{term "m\<^sub>1"}, where entries of @{term "m\<^sub>1"} are overwritten if necessary. 
We can restrict the domain of a map @{term "m"} to a set @{term "A"} by @{term "m |` A"}. 
%Subsumption of maps is defined as @{thm "map_le_def" [of m\<^sub>1 m\<^sub>2]} and composition of maps as @{thm "map_comp_def" [of m\<^sub>1 m\<^sub>2]}.

%\paragraph{Lists.}
The syntax and the operations for lists are similar to functional programming languages like ML or Haskell. 
The empty list is @{term "[]"}, with @{term "x#xs"} the element @{term "x"} is `consed' to the list @{term "xs"}.%, the head of list @{term "xs"} is @{term "hd xs"} and the remainder, its tail, is @{term "tl xs"}. 
With @{term "xs@ys"} list @{term "ys"} is appended to list @{term "xs"}.
With the term @{term "map f xs"} the function @{term "f"} is applied to all elements in @{term "xs"}. 
The length of a list is @{term "length xs"}, the @{term n}-th element of a list can be selected with @{term "xs!n"} and can be updated via @{term "xs[n:=v]"}. With @{term "dropWhile P xs"} the prefix for which all elements satisfy predicate @{term "P"} are dropped from list @{term "xs"}.
%With @{term "set xs"} we obtain the set of elements in list @{term "xs"}.
%Filtering those elements from a list for which predicate @{term "P"} holds is achieved by @{term [eta_contract=false] "[x\<in>xs. P x]"}.
%With @{term "replicate n e"} we denote a list that consists of @{term n} elements @{term e}.

%\paragraph{Sets.}
Sets come along with the standard operations like union, \ie @{term "A \<union> B"}, membership, \ie @{term "x \<in> A"} and set inversion, \ie @{term "- A"}.

%intersection, \ie @{term "A \<inter> B"} and 
%The set image @{term "f ` A"} yields a new set by applying function @{term "f"} to every element in set @{term "A"}.




%\paragraph{Records.}
%A record is constructed by assigning all of its fields, \eg @{term "\<lparr>fld\<^sub>1 = v\<^sub>1, fld\<^sub>2 = v\<^sub>2\<rparr>"}.
%Field @{term [names_short]"fld\<^sub>1"} of record @{term "r"} is selected by @{term[names_short] "fld\<^sub>1 r"} and updated with a value @{term "x"} via @{term[names_short] "r\<lparr>fld\<^sub>1 := x\<rparr>"}. 

%\paragraph{Tuples.}
%The first and second component of a pair can be accessed with the functions @{const fst} and @{const snd}. 
Tuples with more than two components are pairs nested to the right.

\<close>
(*<*)
end
(*>*)
