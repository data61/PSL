(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
subsection \<open>Defining Hash-Functions for Common Types\<close>

theory Hash_Instances
imports
  Hash_Generator
begin

text \<open>For all of the following types, we register hashcode-functions.
  @{type int}, @{type integer}, @{type nat}, @{type char}, @{type bool}, @{type unit}, @{type sum}, @{type option}, @{type list},
  and @{type prod}. For types without type parameters, we use plain @{const "hashcode"}, and for the 
  others we use generated ones.\<close>

derive (hashcode) hash_code int integer bool char unit nat

derive hash_code prod sum option list 

text \<open>There is no need to \<open>derive hashable prod sum option list\<close> since all of these types 
  are already instances of class @{class hashable}. Still the above command is necessary to register
  these types in the generator.\<close>

end
