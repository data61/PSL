(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
subsection \<open>Defining Equality-Functions for Common Types\<close>

theory Equality_Instances
imports
  Equality_Generator
begin

text \<open>For all of the following types, we register equality-functions.
  @{type int}, @{type integer}, @{type nat}, @{type char}, @{type bool}, @{type unit}, @{type sum}, @{type option}, @{type list},
  and @{type prod}. For types without type parameters, we use plain @{term "(=)"}, and for the 
  others we use generated ones. These functions will be essential, when the generator is later on
  invoked on types, which in their definition use one these types.\<close>

derive (eq) equality int integer nat char bool unit
derive equality sum list prod option

end
