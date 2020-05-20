(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>  and  
                 Nicole Rauch <rauch at informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>The Direct Subtype Relation of Java Types\<close>

theory DirectSubtypes
imports "../Isabelle/JavaType"
begin

text \<open>
In this theory, we formalize the direct subtype relations of the Java types (as defined
in Sec. \ref{java_typeid_definitions}) that appear in the program to be verified. Thus, this
theory has to be generated for each program.
\label{direct_subtype_relations}
\<close>

text \<open>We have the following type hierarchy:
\begin{center}
\includegraphics[width=13cm]{TypeHierarchy}
\end{center}
We need to describe all direct subtype relations of this  type hierarchy.
As you can see in the picture, all unnecessary direct subtype relations can be
ignored, e.g. the subclass relation between CounterImpl and Object, because it is 
added
transitively by the widening relation of types (see Sec. \ref{widening_subtypes}).
\<close>

text \<open>
We have to specify the direct subtype relation between
\begin{itemize}
\item each ``leaf'' class or interface and its subtype \texttt{NullT}
\item each ``root'' class or interface and its supertype \texttt{Object}
\item each two types that are direct subtypes as specified in the code by
\texttt{extends} or \texttt{implements}
\item each array type of a primitive type and its subtype \texttt{NullT}
\item each array type of a primitive type and its supertype \texttt{Object}
\item each array type of a ``leaf'' class or interface and its subtype \texttt{NullT}
\item the array type \texttt{Object[]} and its supertype \texttt{Object}
\item two array types if their element types are in a subtype hierarchy
\end{itemize}
\<close>

definition direct_subtype :: "(Javatype * Javatype) set" where
"direct_subtype =
{ (NullT, AClassT Dummy),
  (NullT, CClassT UndoCounter), 
  (NullT, CClassT NullPointerException),
  (NullT, CClassT ClassCastException),

  (AClassT Dummy, CClassT Object),
  (InterfaceT Counter, CClassT Object),
  (CClassT Exception, CClassT Object), 

  (CClassT UndoCounter, CClassT CounterImpl), 
  (CClassT CounterImpl, InterfaceT Counter),
  (CClassT NullPointerException, CClassT Exception),
  (CClassT ClassCastException, CClassT Exception),

  (NullT, ArrT BoolAT),
  (NullT, ArrT IntgAT),
  (NullT, ArrT ShortAT),
  (NullT, ArrT ByteAT),
  (ArrT BoolAT,  CClassT Object),
  (ArrT IntgAT,  CClassT Object),
  (ArrT ShortAT, CClassT Object),
  (ArrT ByteAT,  CClassT Object),

  (NullT, ArrT (AClassAT Dummy)),
  (NullT, ArrT (CClassAT UndoCounter)),
  (NullT, ArrT (CClassAT NullPointerException)),
  (NullT, ArrT (CClassAT ClassCastException)),

  (ArrT (CClassAT Object),      CClassT Object),

  (ArrT (AClassAT Dummy),       ArrT (CClassAT Object)),
  (ArrT (CClassAT CounterImpl), ArrT (InterfaceAT Counter)), 
  (ArrT (InterfaceAT Counter),  ArrT (CClassAT Object)),
  (ArrT (CClassAT Exception),   ArrT (CClassAT Object)), 
  (ArrT (CClassAT UndoCounter), ArrT (CClassAT CounterImpl)), 
  (ArrT (CClassAT NullPointerException), ArrT (CClassAT Exception)),
  (ArrT (CClassAT ClassCastException),   ArrT (CClassAT Exception))
}"

text \<open>This lemma is used later in the Simplifier.\<close>

lemma direct_subtype:
  "(NullT, AClassT Dummy) \<in> direct_subtype"
  "(NullT, CClassT UndoCounter) \<in> direct_subtype" 
  "(NullT, CClassT NullPointerException) \<in> direct_subtype"
  "(NullT, CClassT ClassCastException) \<in> direct_subtype"

  "(AClassT Dummy, CClassT Object) \<in> direct_subtype"
  "(InterfaceT Counter, CClassT Object) \<in> direct_subtype"
  "(CClassT Exception, CClassT Object) \<in> direct_subtype" 

  "(CClassT UndoCounter, CClassT CounterImpl) \<in> direct_subtype" 
  "(CClassT CounterImpl, InterfaceT Counter) \<in> direct_subtype"
  "(CClassT NullPointerException, CClassT Exception) \<in> direct_subtype"
  "(CClassT ClassCastException, CClassT Exception) \<in> direct_subtype"

  "(NullT, ArrT BoolAT) \<in> direct_subtype"
  "(NullT, ArrT IntgAT) \<in> direct_subtype"
  "(NullT, ArrT ShortAT) \<in> direct_subtype"
  "(NullT, ArrT ByteAT) \<in> direct_subtype"
  "(ArrT BoolAT,  CClassT Object) \<in> direct_subtype"
  "(ArrT IntgAT,  CClassT Object) \<in> direct_subtype"
  "(ArrT ShortAT, CClassT Object) \<in> direct_subtype"
  "(ArrT ByteAT,  CClassT Object) \<in> direct_subtype"

  "(NullT, ArrT (AClassAT Dummy)) \<in> direct_subtype"
  "(NullT, ArrT (CClassAT UndoCounter)) \<in> direct_subtype"
  "(NullT, ArrT (CClassAT NullPointerException)) \<in> direct_subtype"
  "(NullT, ArrT (CClassAT ClassCastException)) \<in> direct_subtype"

  "(ArrT (CClassAT Object),      CClassT Object) \<in> direct_subtype"

  "(ArrT (AClassAT Dummy),       ArrT (CClassAT Object)) \<in> direct_subtype"
  "(ArrT (CClassAT CounterImpl), ArrT (InterfaceAT Counter)) \<in> direct_subtype" 
  "(ArrT (InterfaceAT Counter),  ArrT (CClassAT Object)) \<in> direct_subtype"
  "(ArrT (CClassAT Exception),   ArrT (CClassAT Object)) \<in> direct_subtype" 
  "(ArrT (CClassAT UndoCounter), ArrT (CClassAT CounterImpl)) \<in> direct_subtype" 
  "(ArrT (CClassAT NullPointerException), ArrT (CClassAT Exception)) \<in> direct_subtype"
  "(ArrT (CClassAT ClassCastException),   ArrT (CClassAT Exception)) \<in> direct_subtype"
  by (simp_all add: direct_subtype_def)

end
