(*  Title:       Jive Data and Store Model
    Author:      Nicole Rauch <rauch at informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>TypeIds\<close>

theory TypeIds imports Main begin

text \<open>\label{java_typeid_definitions}
This theory contains the program specific names of abstract and concrete classes and 
interfaces. It has to 
be generated for each program we want to verify. 
The following classes are an example taken from the program given in Sect. 
\ref{example-program}.
They are complemented by the classes that are known to exist in each Java program 
implicitly,
namely \texttt{Object}, \texttt{Exception}, \texttt{ClassCastException} and 
\texttt{NullPointerException}.
The example program does not contain any abstract classes, but since we cannot 
formalize datatypes without
constructors, we have to insert a dummy class which we call \texttt{Dummy}.

The datatype CTypeId must contain a constructor called \texttt{Object} because subsequent
proofs in the Subtype theory rely on it.
\<close>

datatype CTypeId = CounterImpl | UndoCounter 
                 | Object | Exception | ClassCastException | NullPointerException
  \<comment> \<open>The last line contains the classes that exist in every program by default.\<close>
datatype ITypeId = Counter
datatype ATypeId = Dummy
  \<comment> \<open>we cannot have an empty type.\<close>

text \<open>
Why do we need different datatypes for the different type identifiers?
Because we want to be able to distinguish the different identifier kinds.
This has a practical reason: If we formalize objects as "ObjectId $\times$ TypeId"
and if we quantify over all objects, we get a lot of objects that do not
exist, namely all objects that bear an interface type identifier or 
abstract class identifier. This is not very helpful. Therefore, we separate
the three identifier kinds from each other.
\<close>




end
