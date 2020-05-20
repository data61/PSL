(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>, 2003
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>Attributes\<close>

theory Attributes
imports "../Isabelle/Subtype"
begin

text \<open>This theory has to be generated as well for each program under 
verification. It defines the attributes of the classes and various functions
on them.
\<close>

datatype AttId = CounterImpl'value | UndoCounter'save
  | Dummy'dummy | Counter'dummy

text \<open>The last two entries are only added to demonstrate what is to happen with attributes of
abstract classes and interfaces.\<close>

text  \<open>It would be nice if attribute names were generated in a way that keeps them short, so that the proof
state does not get unreadable because of fancy long names. The generation of 
attribute names that is performed by the
Jive tool should only add the definition class if necessary, i.e.~if there 
 would be a name clash otherwise. For the example above, the class names are not 
necessary. One must be careful, though, not to generate names that might clash with names of free variables
that are used subsequently.
\<close>

text \<open>The domain type of an attribute is the definition class (or interface)
of the attribute.\<close>
definition dtype:: "AttId \<Rightarrow> Javatype" where
"dtype f = (case f of 
              CounterImpl'value \<Rightarrow> CClassT CounterImpl
            | UndoCounter'save \<Rightarrow> CClassT UndoCounter
            | Dummy'dummy \<Rightarrow> AClassT Dummy
            | Counter'dummy \<Rightarrow> InterfaceT Counter)"

lemma dtype_simps [simp]:
"dtype CounterImpl'value = CClassT CounterImpl" 
"dtype UndoCounter'save = CClassT UndoCounter"
"dtype Dummy'dummy = AClassT Dummy"
"dtype Counter'dummy = InterfaceT Counter"
  by (simp_all add: dtype_def dtype_def dtype_def)

text \<open>For convenience, we add some functions that directly apply the selectors of 
  the datatype @{typ Javatype}.
\<close>
  
definition cDTypeId :: "AttId \<Rightarrow> CTypeId" where
"cDTypeId f = (case f of 
              CounterImpl'value \<Rightarrow> CounterImpl
            | UndoCounter'save \<Rightarrow> UndoCounter
            | Dummy'dummy \<Rightarrow> undefined
            | Counter'dummy \<Rightarrow> undefined )"

definition aDTypeId:: "AttId \<Rightarrow> ATypeId" where
"aDTypeId f = (case f of 
              CounterImpl'value \<Rightarrow> undefined
            | UndoCounter'save \<Rightarrow> undefined
            | Dummy'dummy \<Rightarrow> Dummy
            | Counter'dummy \<Rightarrow> undefined )"

definition iDTypeId:: "AttId \<Rightarrow> ITypeId" where
"iDTypeId f = (case f of 
              CounterImpl'value \<Rightarrow> undefined
            | UndoCounter'save \<Rightarrow> undefined
            | Dummy'dummy \<Rightarrow> undefined
            | Counter'dummy \<Rightarrow> Counter )"

lemma DTypeId_simps [simp]:
"cDTypeId CounterImpl'value = CounterImpl" 
"cDTypeId UndoCounter'save = UndoCounter"
"aDTypeId Dummy'dummy = Dummy"
"iDTypeId Counter'dummy = Counter"
  by (simp_all add: cDTypeId_def aDTypeId_def iDTypeId_def)


text \<open>The range type of an attribute is the type of the value stored in that
attribute.
\<close>
definition rtype:: "AttId \<Rightarrow> Javatype" where
"rtype f = (case f of 
              CounterImpl'value \<Rightarrow> IntgT
            | UndoCounter'save \<Rightarrow> IntgT
            | Dummy'dummy \<Rightarrow> NullT
            | Counter'dummy \<Rightarrow> NullT)"

lemma rtype_simps [simp]:
"rtype CounterImpl'value  = IntgT"
"rtype UndoCounter'save  = IntgT"
"rtype Dummy'dummy = NullT"
"rtype Counter'dummy = NullT"
  by (simp_all add: rtype_def rtype_def rtype_def)

text \<open>With the datatype \<open>CAttId\<close> we describe the possible locations 
in memory for
instance fields. We rule out the impossible combinations of class names and
field names. For example, a \<open>CounterImpl\<close> cannot have a \<open>save\<close> 
field. A store model which provides locations for all possible combinations
of the Cartesian product of class name and field name works out fine as 
well, because we cannot express modification of such ``wrong'' 
locations in a Java program. So we can only prove useful properties about 
reasonable combinations.
The only drawback in such a model is that we cannot prove a property like 
\<open>not_treach_ref_impl_not_reach\<close> in theory StoreProperties. 
If the store provides locations for
every combination of class name and field name, we cannot rule out 
reachability of certain pointer chains that go through ``wrong'' locations. 
That is why we decided to introduce the new type \<open>CAttId\<close>.

  While \<open>AttId\<close> describes which fields 
are declared in which classes and interfaces,
  \<open>CAttId\<close> describes which objects of which classes may contain which 
fields at run-time. Thus,
  \<open>CAttId\<close> makes the inheritance of fields visible in the formalization.

There is only one such datatype because only objects of concrete classes can be 
created at run-time,
thus only instance fields of concrete classes can occupy memory.\<close>

  datatype CAttId = CounterImpl'CounterImpl'value | UndoCounter'CounterImpl'value
  | UndoCounter'UndoCounter'save 
  | CounterImpl'Counter'dummy | UndoCounter'Counter'dummy


text \<open>Function \<open>catt\<close> builds a \<open>CAttId\<close> from a class name
and a field name. In case of the illegal combinations we just return
\<open>undefined\<close>. We can also filter out static fields in 
\<open>catt\<close>.\<close>
  
definition catt:: "CTypeId \<Rightarrow> AttId \<Rightarrow> CAttId" where
"catt C f =
  (case C of
     CounterImpl \<Rightarrow> (case f of 
                CounterImpl'value \<Rightarrow> CounterImpl'CounterImpl'value
              | UndoCounter'save \<Rightarrow> undefined
              | Dummy'dummy \<Rightarrow> undefined
              | Counter'dummy \<Rightarrow> CounterImpl'Counter'dummy)
   | UndoCounter \<Rightarrow> (case f of 
                     CounterImpl'value \<Rightarrow> UndoCounter'CounterImpl'value
                   | UndoCounter'save \<Rightarrow> UndoCounter'UndoCounter'save
                   | Dummy'dummy \<Rightarrow> undefined
                   | Counter'dummy \<Rightarrow> UndoCounter'Counter'dummy)
   | Object \<Rightarrow> undefined
   | Exception \<Rightarrow> undefined
   | ClassCastException \<Rightarrow> undefined
   | NullPointerException \<Rightarrow> undefined
)"


lemma catt_simps [simp]:
"catt CounterImpl CounterImpl'value = CounterImpl'CounterImpl'value"
"catt UndoCounter CounterImpl'value = UndoCounter'CounterImpl'value"
"catt UndoCounter UndoCounter'save = UndoCounter'UndoCounter'save"
"catt CounterImpl Counter'dummy = CounterImpl'Counter'dummy"
"catt UndoCounter Counter'dummy = UndoCounter'Counter'dummy"
  by (simp_all add: catt_def)

text \<open>Selection of the class name of the type of the object in which the field lives.
  The field can only be located in a concrete class.\<close>
  
definition cls:: "CAttId \<Rightarrow> CTypeId" where
"cls cf = (case cf of
             CounterImpl'CounterImpl'value  \<Rightarrow> CounterImpl
           | UndoCounter'CounterImpl'value  \<Rightarrow> UndoCounter
           | UndoCounter'UndoCounter'save  \<Rightarrow> UndoCounter
  | CounterImpl'Counter'dummy \<Rightarrow> CounterImpl
  | UndoCounter'Counter'dummy \<Rightarrow> UndoCounter
)"

lemma cls_simps [simp]:
"cls CounterImpl'CounterImpl'value = CounterImpl"
"cls UndoCounter'CounterImpl'value = UndoCounter"
"cls UndoCounter'UndoCounter'save = UndoCounter"
"cls CounterImpl'Counter'dummy = CounterImpl"
"cls UndoCounter'Counter'dummy = UndoCounter"
  by (simp_all add: cls_def)

text \<open>Selection of the field name.\<close>
definition att:: "CAttId \<Rightarrow> AttId" where
"att cf = (case cf of
             CounterImpl'CounterImpl'value  \<Rightarrow> CounterImpl'value
           | UndoCounter'CounterImpl'value  \<Rightarrow> CounterImpl'value
           | UndoCounter'UndoCounter'save  \<Rightarrow> UndoCounter'save
           | CounterImpl'Counter'dummy \<Rightarrow> Counter'dummy
           | UndoCounter'Counter'dummy \<Rightarrow> Counter'dummy
)"

lemma att_simps [simp]:
"att CounterImpl'CounterImpl'value = CounterImpl'value"
"att UndoCounter'CounterImpl'value = CounterImpl'value"
"att UndoCounter'UndoCounter'save = UndoCounter'save"
"att CounterImpl'Counter'dummy = Counter'dummy"
"att UndoCounter'Counter'dummy = Counter'dummy"
  by (simp_all add: att_def)

end
