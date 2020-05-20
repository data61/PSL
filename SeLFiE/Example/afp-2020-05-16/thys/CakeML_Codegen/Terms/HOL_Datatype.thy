section \<open>Reflecting HOL datatype definitions\<close>

theory HOL_Datatype
imports
  Terms_Extras
  "HOL-Library.Datatype_Records"
  "HOL-Library.Finite_Map"
  "Higher_Order_Terms.Name"
begin

datatype "typ" =
  TVar name |
  TApp name "typ list"

datatype_compat "typ"

context begin

qualified definition tapp_0 where
"tapp_0 tc = TApp tc []"

qualified definition tapp_1 where
"tapp_1 tc t1 = TApp tc [t1]"

qualified definition tapp_2 where
"tapp_2 tc t1 t2 = TApp tc [t1, t2]"

end

quickcheck_generator "typ"
  constructors:
    TVar,
    HOL_Datatype.tapp_0,
    HOL_Datatype.tapp_1,
    HOL_Datatype.tapp_2

datatype_record dt_def =
  tparams :: "name list"
  constructors :: "(name, typ list) fmap"

ML_file "hol_datatype.ML"

end