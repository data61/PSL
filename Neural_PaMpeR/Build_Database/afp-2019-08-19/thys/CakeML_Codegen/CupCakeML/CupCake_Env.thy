section \<open>CupCake environments\<close>

theory CupCake_Env
imports "../Utils/CakeML_Utils"
begin

fun cake_no_abs :: "v \<Rightarrow> bool" where
"cake_no_abs (Conv _ vs) \<longleftrightarrow> list_all cake_no_abs vs" |
"cake_no_abs _ \<longleftrightarrow> False"

fun is_cupcake_pat :: "Ast.pat \<Rightarrow> bool" where
"is_cupcake_pat (Ast.Pvar _) \<longleftrightarrow> True" |
"is_cupcake_pat (Ast.Pcon (Some (Short _)) xs) \<longleftrightarrow> list_all is_cupcake_pat xs" |
"is_cupcake_pat _ \<longleftrightarrow> False"

fun is_cupcake_exp :: "exp \<Rightarrow> bool" where
"is_cupcake_exp (Ast.Var (Short _)) \<longleftrightarrow> True" |
"is_cupcake_exp (Ast.App oper es) \<longleftrightarrow> oper = Ast.Opapp \<and> list_all is_cupcake_exp es" |
"is_cupcake_exp (Ast.Con (Some (Short _)) es) \<longleftrightarrow> list_all is_cupcake_exp es" |
"is_cupcake_exp (Ast.Fun _ e) \<longleftrightarrow> is_cupcake_exp e" |
"is_cupcake_exp (Ast.Mat e cs) \<longleftrightarrow> is_cupcake_exp e \<and> list_all (\<lambda>(p, e). is_cupcake_pat p \<and> is_cupcake_exp e) cs \<and> cake_linear_clauses cs" |
"is_cupcake_exp _ \<longleftrightarrow> False"

abbreviation cupcake_clauses :: "(Ast.pat \<times> exp) list \<Rightarrow> bool" where
"cupcake_clauses \<equiv> list_all (\<lambda>(p, e). is_cupcake_pat p \<and> is_cupcake_exp e)"

fun cupcake_c_ns :: "c_ns \<Rightarrow> bool" where
"cupcake_c_ns (Bind cs mods) \<longleftrightarrow>
  mods = [] \<and> list_all (\<lambda>(_, _, tid). case tid of TypeId (Short _) \<Rightarrow> True | _ \<Rightarrow> False) cs"

locale cakeml_static_env =
  fixes static_cenv :: c_ns
  assumes static_cenv: "cupcake_c_ns static_cenv"
begin

definition empty_sem_env :: "v sem_env" where
"empty_sem_env = \<lparr> sem_env.v = nsEmpty, sem_env.c = static_cenv \<rparr>"

lemma v_of_empty_sem_env[simp]: "sem_env.v empty_sem_env = nsEmpty"
unfolding empty_sem_env_def by simp

lemma c_of_empty_sem_env[simp]: "c empty_sem_env = static_cenv"
unfolding empty_sem_env_def by simp

fun is_cupcake_value :: "SemanticPrimitives.v \<Rightarrow> bool"
and is_cupcake_all_env :: "all_env \<Rightarrow> bool" where
"is_cupcake_value (Conv (Some (_, TypeId (Short _))) vs) \<longleftrightarrow> list_all is_cupcake_value vs" |
"is_cupcake_value (Closure env _ e) \<longleftrightarrow> is_cupcake_exp e \<and> is_cupcake_all_env env" |
"is_cupcake_value (Recclosure env es _) \<longleftrightarrow> list_all (\<lambda>(_, _, e). is_cupcake_exp e) es \<and> is_cupcake_all_env env" |
"is_cupcake_value _ \<longleftrightarrow> False" |
"is_cupcake_all_env \<lparr> sem_env.v = Bind v0 [], sem_env.c = c0 \<rparr> \<longleftrightarrow> c0 = static_cenv \<and> list_all (is_cupcake_value \<circ> snd) v0" |
"is_cupcake_all_env _ \<longleftrightarrow> False"

lemma is_cupcake_all_envE:
  assumes "is_cupcake_all_env env"
  obtains v c where "env = \<lparr> sem_env.v = Bind v [], sem_env.c = c \<rparr>" "c = static_cenv" "list_all (is_cupcake_value \<circ> snd) v"
using assms
by (auto elim!: is_cupcake_all_env.elims)

fun is_cupcake_ns :: "v_ns \<Rightarrow> bool" where
"is_cupcake_ns (Bind v0 []) \<longleftrightarrow> list_all (is_cupcake_value \<circ> snd) v0" |
"is_cupcake_ns _ \<longleftrightarrow> False"

lemma is_cupcake_nsE:
  assumes "is_cupcake_ns ns"
  obtains v where "ns = Bind v []" "list_all (is_cupcake_value \<circ> snd) v"
using assms by (rule is_cupcake_ns.elims)

lemma is_cupcake_all_envD:
  assumes "is_cupcake_all_env env"
  shows "is_cupcake_ns (sem_env.v env)" "cupcake_c_ns (c env)"
using assms static_cenv by (auto elim!: is_cupcake_all_envE)

lemma is_cupcake_all_envI:
  assumes "is_cupcake_ns (sem_env.v env)" "sem_env.c env = static_cenv"
  shows "is_cupcake_all_env env"
using assms static_cenv
apply (cases env)
apply simp
subgoal for v c
  apply (cases v)
  apply simp
  subgoal for x1 x2
    by (cases x2) auto
  done
done

end

end