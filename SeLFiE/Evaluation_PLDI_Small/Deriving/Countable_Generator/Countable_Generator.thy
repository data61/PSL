(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section \<open>Countable Datatypes\<close>

theory Countable_Generator
imports 
  "HOL-Library.Countable"
  "../Derive_Manager"
begin

text \<open>
Brian Huffman and Alexander Krauss (old datatype), and Jasmin Blanchette (BNF datatype) 
have developed tactics which automatically can prove that a datatype is countable.
We just make this tactic available in the derive-manager so that
one can conveniently write \texttt{derive countable some-datatype}.
\<close>

subsection "Installing the tactic"

text \<open>
There is nothing more to do, then to write some boiler-plate ML-code
for class-instantiation.
\<close>

setup \<open>
  let 
    fun derive dtyp_name _ thy = 
      let
        val base_name = Long_Name.base_name dtyp_name
        val _ = writeln ("proving that datatype " ^ base_name ^ " is countable")
        val sort = @{sort countable}
        val vs = 
          let val i = BNF_LFP_Compat.the_spec thy dtyp_name |> #1 
          in map (fn (n,_) => (n, sort)) i end
        val thy' = Class.instantiation ([dtyp_name],vs,sort) thy
          |> Class.prove_instantiation_exit (fn ctxt => countable_tac ctxt 1)
        val _ = writeln ("registered " ^ base_name ^ " in class countable")
      in thy' end
  in 
    Derive_Manager.register_derive "countable" "register datatypes is class countable" derive
  end
\<close>

end
