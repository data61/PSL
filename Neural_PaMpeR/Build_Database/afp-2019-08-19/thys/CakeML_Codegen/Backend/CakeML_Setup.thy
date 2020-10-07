section \<open>Basic CakeML setup\<close>

theory CakeML_Setup
imports
  "../CupCakeML/CupCake_Semantics"
  CakeML.CakeML_Code
  "../Terms/Consts"
begin

global_interpretation name: rekey Name
  rewrites "inv Name = as_string"
proof -
  have "bij Name"
    by (metis bijI' name.exhaust name.inject)
  show "rekey Name"
    by standard fact

  show "inv Name = as_string"
    by (metis inv_equality name.exhaust_sel name.sel)
qed

global_interpretation name_as_string: rekey as_string
  by (rule name.inv)

hide_const (open) Lem_string.concat
hide_const (open) sem_env.c
hide_const (open) sem_env.v

definition empty_locn :: locn where
"empty_locn = \<lparr> row = 0, col = 0, offset = 0 \<rparr>"

definition empty_locs :: locs where
"empty_locs = (empty_locn, empty_locn)"

definition empty_state :: "unit SemanticPrimitives.state" where
"empty_state = \<lparr> clock = 0, refs = [], ffi = empty_ffi_state, defined_types = {}, defined_mods = {} \<rparr>"

fun fmap_of_ns :: "('b, string, 'a) namespace \<Rightarrow> (name, 'a) fmap" where
"fmap_of_ns (Bind xs _) = fmap_of_list (map (map_prod Name id) xs)"

lemma fmlookup_ns[simp]: "fmlookup (fmap_of_ns ns) k = cupcake_nsLookup ns (as_string k)"
by (cases ns) (simp add: fmlookup_of_list map_prod_def name.map_of_rekey option.map_ident)

lemma fmap_of_nsBind[simp]: "fmap_of_ns (nsBind (as_string k) v0 ns) = fmupd k v0 (fmap_of_ns ns)"
by (cases ns) auto

lemma fmap_of_nsAppend[simp]: "fmap_of_ns (nsAppend ns1 ns2) = fmap_of_ns ns2 ++\<^sub>f fmap_of_ns ns1"
by (cases ns1; cases ns2) simp

lemma fmap_of_alist_to_ns[simp]: "fmap_of_ns (alist_to_ns xs) = fmap_of_list (map (map_prod Name id) xs)"
unfolding alist_to_ns_def by simp

lemma fmap_of_nsEmpty[simp]: "fmap_of_ns nsEmpty = fmempty"
  unfolding nsEmpty_def by simp

context begin

private lemma build_rec_env_fmap0:
  "fmap_of_ns (foldr (\<lambda>(f, x, e). nsBind f (Recclosure env\<^sub>\<Lambda> funs' f)) funs env) =
    fmap_of_ns env ++\<^sub>f fmap_of_list (map (\<lambda>(f, _). (Name f, Recclosure env\<^sub>\<Lambda> funs' f)) funs)"
apply (induction funs arbitrary: env)
 apply auto
by (metis (no_types, lifting) fmap_of_nsBind name.sel)

definition cake_mk_rec_env where
"cake_mk_rec_env funs env = fmap_of_list (map (\<lambda>(f, _). (Name f, Recclosure env funs f)) funs)"

lemma build_rec_env_fmap:
  "fmap_of_ns (build_rec_env funs env\<^sub>\<Lambda> env) = fmap_of_ns env ++\<^sub>f cake_mk_rec_env funs env\<^sub>\<Lambda>"
unfolding build_rec_env_def cake_mk_rec_env_def
by (rule build_rec_env_fmap0)

end

section \<open>Constructors according to CakeML\<close>

definition cake_tctor :: "string \<Rightarrow> tctor" where
"cake_tctor name = (if name = ''fun'' then Ast.TC_fn else Ast.TC_name (Short name))"

primrec typ_to_t :: "typ \<Rightarrow> Ast.t" where
"typ_to_t (TVar name) = Ast.Tvar (as_string name)" |
"typ_to_t (TApp name args) = Ast.Tapp (map typ_to_t args) (cake_tctor (as_string name))"

context constructors begin

definition as_static_cenv :: c_ns where
"as_static_cenv = Bind (rev (map (map_prod id (map_prod id (TypeId \<circ> Short))) flat_C_info)) []"

lemma as_static_cenv_cakeml_static_env: "cakeml_static_env as_static_cenv"
unfolding cakeml_static_env_def as_static_cenv_def
  by (auto simp: list.pred_map split: prod.splits)

sublocale cake_static_env?: cakeml_static_env as_static_cenv
by (rule as_static_cenv_cakeml_static_env)

definition as_cake_type_def :: Ast.type_def where
"as_cake_type_def =
  map (\<lambda>(name, dt_def). (map as_string (tparams dt_def), as_string name,
      map (\<lambda>(C, params). (as_string C, map typ_to_t params))
        (sorted_list_of_fmap (constructors dt_def))))
    (sorted_list_of_fmap C_info)"

definition cake_dt_prelude :: Ast.dec where
"cake_dt_prelude = Ast.Dtype empty_locs as_cake_type_def"

definition cake_all_types :: "tid_or_exn set" where
"cake_all_types = (TypeId \<circ> Short \<circ> as_string) ` fset all_tdefs"

definition empty_state_with_types :: "unit SemanticPrimitives.state" where
"empty_state_with_types =
  \<lparr> clock = 0, refs = [], ffi = empty_ffi_state, defined_types = cake_all_types, defined_mods = {} \<rparr>"

lemma empty_state_with_types_alt_def:
  "empty_state_with_types = empty_state \<lparr> defined_types := cake_all_types \<rparr>"
unfolding empty_state_with_types_def empty_state_def
(* FIXME update_f (make_t ) lemma missing *)
by (auto simp: datatype_record_update)

end

subsection \<open>Running the generated type declarations through the semantics\<close>

context constants begin

context begin

(* FIXME slightly different shape than empty_state_with_types_alt_def *)
private lemma state_types_update:
  "update_defined_types (\<lambda>_. cake_all_types \<union> defined_types empty_state) empty_state =
    empty_state_with_types"
unfolding empty_state_with_types_def empty_state_def
(* FIXME update_f (make_t ) lemma missing *)
by (simp add: datatype_record_update)

private lemma env_types_update: "build_tdefs [] as_cake_type_def = as_static_cenv"
unfolding as_cake_type_def_def as_static_cenv_def build_tdefs_def alist_to_ns_def flat_C_info_def
apply (auto simp: List.bind_def map_concat)
apply (rule arg_cong[where f = concat])
by (auto simp: map_concat comp_def split_beta)

private lemmas evaluate_type =
  evaluate_dec.dtype1[
    where new_tdecs = cake_all_types and s = empty_state and mn = "[]" and tds = as_cake_type_def,
    unfolded state_types_update env_types_update,
    folded empty_sem_env_def]

private lemma type_defs_to_new_tdecs:
  "type_defs_to_new_tdecs [] as_cake_type_def =
    set (map (\<lambda>name. TypeId (Short (as_string name))) (sorted_list_of_fset (fmdom C_info)))"
unfolding cake_all_types_def type_defs_to_new_tdecs_def as_cake_type_def_def all_tdefs_def
by (simp add: case_prod_twice sorted_list_of_fmap_def)

private lemma cakeml_convoluted1: "foldr (\<lambda>(n, ts). (#) n) ys xs = map fst ys @ xs" (* thanks Scott *)
by (induction ys arbitrary: xs) auto

private lemma cakeml_convoluted2: "foldr (\<lambda>x y. f x @ y) xs ys = concat (map f xs) @ ys" (* thanks again *)
by (induction xs arbitrary: ys) auto

private lemma check_dup_ctors_alt_def: "check_dup_ctors tds \<longleftrightarrow> distinct (tds \<bind> (\<lambda>(_, _, cons). map fst cons))"
unfolding check_dup_ctors_def
apply simp
apply (rule arg_cong[where f = distinct])
apply (subst foldr_cong[OF refl refl, where g = "\<lambda>x a. map fst (snd (snd x)) @ a"])
subgoal
  apply (subst split_beta)
  apply (subst split_beta)
  by (rule cakeml_convoluted1)
subgoal
  apply (subst cakeml_convoluted2)
  apply auto
  unfolding List.bind_def
  apply (rule arg_cong[where f = concat])
  by auto
done

lemma evaluate_dec_prelude:
  "evaluate_dec t [] env empty_state cake_dt_prelude (empty_state_with_types, Rval empty_sem_env)"
unfolding cake_dt_prelude_def
proof (rule evaluate_type, intro conjI)
  show "check_dup_ctors as_cake_type_def"
    using distinct_ctr'
    unfolding check_dup_ctors_alt_def List.bind_def as_cake_type_def_def all_constructors_def
    by (auto simp: comp_def split_beta map_concat)
next
  show "allDistinct (map (\<lambda>x. case x of (tvs, tn, ctors) \<Rightarrow> tn) as_cake_type_def)"
    unfolding all_distinct_alt_def as_cake_type_def_def
    apply (auto simp: comp_def case_prod_twice)
    apply (rule name_as_string.fst_distinct)
    unfolding sorted_list_of_fmap_def
    by (auto simp: comp_def)
next
  show "cake_all_types = type_defs_to_new_tdecs [] as_cake_type_def"
    unfolding cake_all_types_def type_defs_to_new_tdecs all_tdefs_def
    by simp
next
  show "disjnt cake_all_types (defined_types empty_state)"
    unfolding empty_state_def disjnt_def by simp
qed

end

end

text \<open>Computability\<close>

declare constructors.as_static_cenv_def[code]
declare constructors.as_cake_type_def_def[code]
declare constructors.cake_dt_prelude_def[code]

export_code constructors.as_static_cenv constructors.cake_dt_prelude
  checking Scala

end