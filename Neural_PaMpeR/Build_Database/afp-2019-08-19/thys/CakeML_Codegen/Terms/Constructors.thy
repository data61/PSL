section \<open>Constructor information\<close>

theory Constructors
imports
  Terms_Extras
  HOL_Datatype
begin

type_synonym C_info = "(name, dt_def) fmap"

locale constructors =
  fixes C_info :: C_info
begin

definition flat_C_info :: "(string \<times> nat \<times> string) list" where
"flat_C_info = do {
  (tname, Cs) \<leftarrow> sorted_list_of_fmap C_info;
  (C, params) \<leftarrow> sorted_list_of_fmap (constructors Cs);
  [(as_string C, (length params, as_string tname))]
}"

definition all_tdefs :: "name fset" where
"all_tdefs = fmdom C_info"

definition C :: "name fset" where
"C = ffUnion (fmdom |`| constructors |`| fmran C_info)"

definition all_constructors :: "name list" where
"all_constructors =
  concat (map (\<lambda>(_, Cs). map fst (sorted_list_of_fmap (constructors Cs))) (sorted_list_of_fmap C_info))"

(* FIXME nice to have *)
(*
lemma all_constructors_alt_def: "all_constructors = map (Name \<circ> fst) flat_C_info"
unfolding all_constructors_def flat_C_info_def
*)

end

declare constructors.C_def[code]
declare constructors.flat_C_info_def[code]
declare constructors.all_constructors_def[code]

export_code
  constructors.C constructors.flat_C_info constructors.all_constructors
  checking Scala

end
