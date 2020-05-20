(*  Title:      JinjaThreads/Common/SystemClasses.thy
    Author:     Gerwin Klein, Andreas Lochbihler

    Based on the Jinja theory Common/SystemClasses.thy by Gerwin Klein
*)

section \<open>System Classes\<close>

theory SystemClasses
imports
  Exceptions
begin

text \<open>
  This theory provides definitions for the \<open>Object\<close> class,
  and the system exceptions.

  Inline SystemClasses definition because they are polymorphic values that violate ML's value restriction.
\<close>

text \<open>
  Object has actually superclass, but we set it to the empty string for code generation.
  Any other class name (like @{term undefined}) would do as well except for code generation.
\<close>
definition ObjectC :: "'m cdecl"
where [code_unfold]: 
  "ObjectC = 
  (Object, (STR '''',[],
    [(wait,[],Void,Native), 
     (notify,[],Void,Native),
     (notifyAll,[],Void,Native),
     (hashcode,[],Integer,Native),
     (clone,[],Class Object,Native),
     (print,[Integer],Void,Native),
     (currentThread,[],Class Thread,Native),
     (interrupted,[],Boolean,Native),
     (yield,[],Void,Native)
    ]))"

definition ThrowableC :: "'m cdecl"
where [code_unfold]: "ThrowableC \<equiv> (Throwable, (Object, [], []))"

definition NullPointerC :: "'m cdecl"
where [code_unfold]: "NullPointerC \<equiv> (NullPointer, (Throwable,[],[]))"

definition ClassCastC :: "'m cdecl"
where [code_unfold]: "ClassCastC \<equiv> (ClassCast, (Throwable,[],[]))"

definition OutOfMemoryC :: "'m cdecl"
where [code_unfold]: "OutOfMemoryC \<equiv> (OutOfMemory, (Throwable,[],[]))"

definition ArrayIndexOutOfBoundsC :: "'m cdecl"
where [code_unfold]: "ArrayIndexOutOfBoundsC \<equiv> (ArrayIndexOutOfBounds, (Throwable,[],[]))"

definition ArrayStoreC :: "'m cdecl"
where [code_unfold]: "ArrayStoreC \<equiv> (ArrayStore, (Throwable, [], []))"

definition NegativeArraySizeC :: "'m cdecl"
where [code_unfold]: "NegativeArraySizeC \<equiv> (NegativeArraySize, (Throwable,[],[]))"

definition ArithmeticExceptionC :: "'m cdecl"
where [code_unfold]: "ArithmeticExceptionC \<equiv> (ArithmeticException, (Throwable,[],[]))"

definition IllegalMonitorStateC :: "'m cdecl"
where [code_unfold]: "IllegalMonitorStateC \<equiv> (IllegalMonitorState, (Throwable,[],[]))"

definition IllegalThreadStateC :: "'m cdecl"
where [code_unfold]: "IllegalThreadStateC \<equiv> (IllegalThreadState, (Throwable,[],[]))"

definition InterruptedExceptionC :: "'m cdecl"
where [code_unfold]: "InterruptedExceptionC \<equiv> (InterruptedException, (Throwable,[],[]))"

definition SystemClasses :: "'m cdecl list"
where [code_unfold]: 
  "SystemClasses \<equiv> 
  [ObjectC, ThrowableC, NullPointerC, ClassCastC, OutOfMemoryC,
   ArrayIndexOutOfBoundsC, ArrayStoreC, NegativeArraySizeC,
   ArithmeticExceptionC,
   IllegalMonitorStateC, IllegalThreadStateC, InterruptedExceptionC]"

end
