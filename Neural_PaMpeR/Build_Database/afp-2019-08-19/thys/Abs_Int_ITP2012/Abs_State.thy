(* Author: Tobias Nipkow *)

section "Abstract State with Computable Ordering"

theory Abs_State
imports Abs_Int0
  "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
  (* Library import merely to allow string lists to be sorted for output *)
begin

text\<open>A concrete type of state with computable \<open>\<sqsubseteq>\<close>:\<close>

datatype 'a st = FunDom "vname \<Rightarrow> 'a" "vname list"

fun "fun" where "fun (FunDom f xs) = f"
fun dom where "dom (FunDom f xs) = xs"

definition [simp]: "inter_list xs ys = [x\<leftarrow>xs. x \<in> set ys]"

definition "show_st S = [(x,fun S x). x \<leftarrow> sort(dom S)]"

definition "show_acom = map_acom (map_option show_st)"
definition "show_acom_opt = map_option show_acom"

definition "lookup F x = (if x : set(dom F) then fun F x else \<top>)"

definition "update F x y =
  FunDom ((fun F)(x:=y)) (if x \<in> set(dom F) then dom F else x # dom F)"

lemma lookup_update: "lookup (update S x y) = (lookup S)(x:=y)"
by(rule ext)(auto simp: lookup_def update_def)

definition "\<gamma>_st \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(lookup F x)}"

instantiation st :: (SL_top) SL_top
begin

definition "le_st F G = (\<forall>x \<in> set(dom G). lookup F x \<sqsubseteq> fun G x)"

definition
"join_st F G =
 FunDom (\<lambda>x. fun F x \<squnion> fun G x) (inter_list (dom F) (dom G))"

definition "\<top> = FunDom (\<lambda>x. \<top>) []"

instance
proof (standard, goal_cases)
  case 2 thus ?case
    apply(auto simp: le_st_def)
    by (metis lookup_def preord_class.le_trans top)
qed (auto simp: le_st_def lookup_def join_st_def Top_st_def)

end

lemma mono_lookup: "F \<sqsubseteq> F' \<Longrightarrow> lookup F x \<sqsubseteq> lookup F' x"
by(auto simp add: lookup_def le_st_def)

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> update S x a \<sqsubseteq> update S' x a'"
by(auto simp add: le_st_def lookup_def update_def)

locale Gamma = Val_abs where \<gamma>=\<gamma> for \<gamma> :: "'av::SL_top \<Rightarrow> val set"
begin

abbreviation \<gamma>\<^sub>f :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^sub>f == \<gamma>_st \<gamma>"

abbreviation \<gamma>\<^sub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^sub>o == \<gamma>_option \<gamma>\<^sub>f"

abbreviation \<gamma>\<^sub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^sub>c == map_acom \<gamma>\<^sub>o"

lemma gamma_f_Top[simp]: "\<gamma>\<^sub>f Top = UNIV"
by(auto simp: Top_st_def \<gamma>_st_def lookup_def)

lemma gamma_o_Top[simp]: "\<gamma>\<^sub>o Top = UNIV"
by (simp add: Top_option_def)

(* FIXME (maybe also le \<rightarrow> sqle?) *)

lemma mono_gamma_f: "f \<sqsubseteq> g \<Longrightarrow> \<gamma>\<^sub>f f \<subseteq> \<gamma>\<^sub>f g"
apply(simp add:\<gamma>_st_def subset_iff lookup_def le_st_def split: if_splits)
by (metis UNIV_I mono_gamma gamma_Top subsetD)

lemma mono_gamma_o:
  "sa \<sqsubseteq> sa' \<Longrightarrow> \<gamma>\<^sub>o sa \<subseteq> \<gamma>\<^sub>o sa'"
by(induction sa sa' rule: le_option.induct)(simp_all add: mono_gamma_f)

lemma mono_gamma_c: "ca \<sqsubseteq> ca' \<Longrightarrow> \<gamma>\<^sub>c ca \<le> \<gamma>\<^sub>c ca'"
by (induction ca ca' rule: le_acom.induct) (simp_all add:mono_gamma_o)

lemma in_gamma_option_iff:
  "x : \<gamma>_option r u \<longleftrightarrow> (\<exists>u'. u = Some u' \<and> x : r u')"
by (cases u) auto

end

end
