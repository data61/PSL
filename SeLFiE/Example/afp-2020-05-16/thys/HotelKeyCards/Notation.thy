(*  Title:      Notation for hotel key card system
    Author:     Tobias Nipkow, TU Muenchen
*)

(*<*)
theory Notation
imports "HOL-Library.LaTeXsugar"
begin

abbreviation
 "SomeFloor" ("(\<lfloor>_\<rfloor>)") where "\<lfloor>x\<rfloor> \<equiv> Some x"
(*>*)

subsection\<open>Notation\<close>

text\<open>
HOL conforms largely to everyday mathematical notation.
This section introduces further non-standard notation and in particular
a few basic data types with their primitive operations.
\sloppy
\begin{description}

\item[Types] The type of truth values is called @{typ bool}.  The
space of total functions is denoted by \<open>\<Rightarrow>\<close>. Type variables
start with a quote, as in @{typ"'a"}, @{typ"'b"} etc. The notation
$t$~\<open>::\<close>~$\tau$ means that term $t$ has type $\tau$.

\item[Functions] can be updated at \<open>x\<close> with new value \<open>y\<close>,
written @{term"f(x:=y)"}.  The range of a function is @{term"range f"},
@{prop"inj f"} means \<open>f\<close> is injective.

\item[Pairs] come with the two projection functions
\<open>fst :: 'a \<times> 'b \<Rightarrow> 'a\<close> and \<open>snd :: 'a \<times> 'b \<Rightarrow> 'b\<close>.

\item[Sets] have type @{typ"'a set"}.

\item[Lists] (type @{typ"'a list"}) come with the empty list
@{term"[]"}, the infix constructor \<open>\<cdot>\<close>, the infix \<open>@\<close>
that appends two lists, and the conversion function @{term set} from
lists to sets.  Variable names ending in ``s'' usually stand for
lists.

\item[Records] are constructed like this \<open>\<lparr>f\<^sub>1 = v\<^sub>1, \<dots>\<rparr>\<close>
and updated like this \mbox{\<open>r\<lparr>f\<^sub>i := v\<^sub>i, \<dots>\<rparr>\<close>},
where the \<open>f\<^sub>i\<close> are the field names,
the \<open>v\<^sub>i\<close> the values and \<open>r\<close> is a record.

\end{description}\fussy
Datatype \<open>option\<close> is defined like this
\begin{center}
\isacommand{datatype} \<open>'a option = None | Some 'a\<close>
\end{center}
and adjoins a new element @{term None} to a type @{typ 'a}. For
succinctness we write @{term"Some a"} instead of @{term[source]"Some a"}.

Note that \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> A\<close>
abbreviates \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> A\<close>, which is the same as
``If \<open>A\<^sub>1\<close> and \dots\ and \<open>A\<^sub>n\<close> then \<open>A\<close>''.
\<close>

(*<*)
end
(*>*)
