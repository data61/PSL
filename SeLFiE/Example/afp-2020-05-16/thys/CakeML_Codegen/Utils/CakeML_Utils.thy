theory CakeML_Utils
imports
  "HOL-Library.Finite_Map"
  "CakeML.Semantic_Extras"
begin

type_synonym v_ns = "(modN, varN, v) namespace"
type_synonym c_ns = "(modN, conN, (nat * tid_or_exn)) namespace"
type_synonym all_env = "v sem_env"

abbreviation cake_linear_clauses :: "(Ast.pat \<times> exp) list \<Rightarrow> bool" where
"cake_linear_clauses \<equiv> list_all (\<lambda>(pat, _). allDistinct (pat_bindings pat []))"

hide_const Lem_string.concat

(* needed for the function package *)
lemma [measure_function]: "is_measure (size_sem_env size)"
by rule

declare all_distinct_alt_def[simp]

fun if_rval where
"if_rval f (Rval v0) \<longleftrightarrow> f v0" |
"if_rval _ _ \<longleftrightarrow> True"

lemma if_rvalI: "(\<And>v. r = Rval v \<Longrightarrow> P v) \<Longrightarrow> if_rval P r"
by (cases r) auto

fun if_match where
"if_match f (Match env) \<longleftrightarrow> f env" |
"if_match _ _ \<longleftrightarrow> True"

fun sequence_result :: "('a, 'b) result list \<Rightarrow> ('a list, 'b) result" where
"sequence_result [] = Rval []" |
"sequence_result (Rerr err # rs) = Rerr err" |
"sequence_result (Rval v0 # rs) = map_result (\<lambda>vs. v0 # vs) id (sequence_result rs)"

lemma sequence_result_rvalD[dest]:
  assumes "sequence_result rs = Rval vs"
  shows "rs = map Rval vs"
using assms
proof (induction rs arbitrary: vs)
  case (Cons r rs)
  then obtain v0 vs0 where "r = Rval v0" "vs = v0 # vs0" "sequence_result rs = Rval vs0"
    by (cases r; cases "sequence_result rs") auto
  with Cons show ?case
    by auto
qed simp

lemma sequence_result_Rval[simp]: "sequence_result (map Rval rs) = Rval rs"
  by (induction rs) auto


(* FIXME move to CakeML entry *)

context begin

qualified definition tapp_0 where
"tapp_0 tc = Tapp [] tc"

qualified definition tapp_1 where
"tapp_1 tc t1 = Tapp [t1] tc"

qualified definition tapp_2 where
"tapp_2 tc t1 t2 = Tapp [t1, t2] tc"

end

quickcheck_generator Ast.t
  constructors:
    Ast.Tvar,
    Ast.Tvar_db,
    CakeML_Utils.tapp_0,
    CakeML_Utils.tapp_1,
    CakeML_Utils.tapp_2

end