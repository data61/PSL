(*  Title:      Jinja/Common/Value.thy
    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Jinja Values\<close>

theory Value imports TypeRel begin

type_synonym addr = nat

datatype val
  = Unit        \<comment> \<open>dummy result value of void expressions\<close>
  | Null        \<comment> \<open>null reference\<close>
  | Bool bool   \<comment> \<open>Boolean value\<close>
  | Intg int    \<comment> \<open>integer value\<close> 
  | Addr addr   \<comment> \<open>addresses of objects in the heap\<close>

primrec the_Intg :: "val \<Rightarrow> int" where
  "the_Intg (Intg i) = i"

primrec the_Addr :: "val \<Rightarrow> addr" where
  "the_Addr (Addr a) = a"

primrec default_val :: "ty \<Rightarrow> val"   \<comment> \<open>default value for all types\<close> where
  "default_val Void      = Unit"
| "default_val Boolean   = Bool False"
| "default_val Integer   = Intg 0"
| "default_val NT        = Null"
| "default_val (Class C) = Null"

end
