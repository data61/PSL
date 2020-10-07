theory Predicate_Formulas
imports
  "HOL-Library.Countable"
  "HOL-Library.Infinite_Set"
  "HOL-Eisbach.Eisbach"
  Abstract_Formula
begin

text \<open>This theory contains an example instantiation of @{term Abstract_Formulas} with an 
formula type with local constants. It is a rather ad-hoc type that may not be very useful to
work with, though.\<close>

type_synonym var = nat
type_synonym lconst = nat

text \<open>
We support higher order variables, in order to express \<open>\<forall>x.?P x\<close>. But we stay first order,
i.e. the parameters of such a variables will only be instantiated with ground terms.
\<close>

datatype form =
    Var (var:var) (params: "form list")
  | LC (var:lconst)
  | Op (name:string) (params: "form list")
  | Quant (name:string) (var:nat) (body: form)

type_synonym schema = "var list \<times> form"

type_synonym subst = "(nat \<times> schema) list"

fun fv :: "form \<Rightarrow> var set" where
   "fv (Var v xs) = insert v (Union (fv ` set xs))"
 | "fv (LC v) = {}"
 | "fv (Op n xs) = Union (fv ` set xs)"
 | "fv (Quant n v f) = fv f - {v}"

definition fresh_for :: "var set \<Rightarrow> var" where
  "fresh_for V = (SOME n. n \<notin> V)"

lemma fresh_for_fresh: "finite V \<Longrightarrow> fresh_for V \<notin> V"
  unfolding fresh_for_def
  apply (rule someI2_ex)
   using infinite_nat_iff_unbounded_le
   apply auto
  done

text \<open>Free variables\<close>

fun fv_schema :: "schema \<Rightarrow> var set" where
  "fv_schema (ps,f) = fv f - set ps"

definition fv_subst :: "subst \<Rightarrow> var set" where
  "fv_subst s = \<Union>(fv_schema ` ran (map_of s))"

definition fv_subst1 where
  "fv_subst1 s = \<Union>(fv ` snd ` set s)"

lemma fv_subst_Nil[simp]: "fv_subst1 [] = {}"
  unfolding fv_subst1_def by auto

text \<open>Local constants, separate from free variables.\<close>

fun lc :: "form \<Rightarrow> lconst set" where
   "lc (Var v xs) = Union (lc ` set xs)"
 | "lc (LC c) = {c}"
 | "lc (Op n xs) = Union (lc ` set xs)"
 | "lc (Quant n v f) = lc f"

fun lc_schema :: "schema \<Rightarrow> lconst set" where
  "lc_schema (ps,f) = lc f"

definition lc_subst1 where
  "lc_subst1 s = \<Union>(lc ` snd ` set s)"

fun lc_subst :: "subst \<Rightarrow> lconst set" where
  "lc_subst s = \<Union>(lc_schema ` snd ` set s)"

fun map_lc :: "(lconst \<Rightarrow> lconst) \<Rightarrow> form \<Rightarrow> form" where
  "map_lc f (Var v xs) = Var v (map (map_lc f) xs)"
| "map_lc f (LC n) = LC (f n)"
| "map_lc f (Op n xs) = Op n (map (map_lc f) xs)"
| "map_lc f (Quant n v f') = Quant n v (map_lc f f')"

lemma fv_map_lc[simp]: "fv (map_lc p f) = fv f"
  by (induction f) auto

lemma lc_map_lc[simp]: "lc (map_lc p f) = p ` lc f"
  by (induction f) auto

lemma map_lc_map_lc[simp]: "map_lc p1 (map_lc p2 f) = map_lc (p1 \<circ> p2) f"
  by (induction f) auto

fun map_lc_subst1 :: "(lconst \<Rightarrow> lconst) \<Rightarrow> (var \<times> form) list \<Rightarrow> (var \<times> form) list" where
  "map_lc_subst1 f s = map (apsnd (map_lc f)) s"

fun map_lc_subst :: "(lconst \<Rightarrow> lconst) \<Rightarrow> subst \<Rightarrow> subst" where
  "map_lc_subst f s = map (apsnd (apsnd (map_lc f))) s"

lemma map_lc_noop[simp]: "lc f = {} \<Longrightarrow> map_lc p f = f"
  by (induction f) (auto simp add: map_idI)

lemma map_lc_cong[cong]: "(\<And>x. x \<in> lc f \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> map_lc f1 f = map_lc f2 f"
  by (induction f) auto

lemma [simp]: "fv_subst1 (map (apsnd (map_lc p)) s) = fv_subst1 s"
  unfolding fv_subst1_def
  by auto

lemma map_lc_subst_cong[cong]:
  assumes "(\<And>x. x \<in> lc_subst s \<Longrightarrow> f1 x = f2 x)"
  shows "map_lc_subst f1 s = map_lc_subst f2 s"
  by (force intro!: map_lc_cong assms)

text \<open>In order to make the termination checker happy, we define substitution in two stages: One
that substitutes only ground terms for variables, and the real one that can substitute schematic
terms (or lambda expression, if you want).\<close>


fun subst1 :: "(var \<times> form) list \<Rightarrow> form \<Rightarrow> form" where
    "subst1 s (Var v []) = (case map_of s v of Some f \<Rightarrow> f | None \<Rightarrow> Var v [])"
  | "subst1 s (Var v xs) = Var v xs"
  | "subst1 s (LC n) = LC n"
  | "subst1 s (Op n xs) = Op n (map (subst1 s) xs)"
  | "subst1 s (Quant n v f) =
      (if v \<in> fv_subst1 s then
      (let v' = fresh_for (fv_subst1 s)
      in Quant n v' (subst1 ((v, Var v' [])#s) f))
      else Quant n v (subst1 s f))"

lemma subst1_Nil[simp]: "subst1 [] f = f"
  by (induction "[]::(var \<times> form) list" f  rule:subst1.induct) 
     (auto simp add: map_idI split: option.splits)
 
lemma lc_subst1: "lc (subst1 s f) \<subseteq> lc f \<union> \<Union>(lc ` snd ` set s)"
  by (induction s f rule: subst1.induct)
     (auto split: option.split dest: map_of_SomeD simp add: Let_def)

lemma apsnd_def': "apsnd f = (\<lambda>(k, v). (k, f v))"
  by auto

lemma map_of_map_apsnd:
  "map_of (map (apsnd f) xs) = map_option f \<circ> map_of xs"
  unfolding apsnd_def' by (rule map_of_map)

lemma map_lc_subst1[simp]: "map_lc p (subst1 s f) = subst1 (map_lc_subst1 p s) (map_lc p f)"
  apply (induction s f rule: subst1.induct)
  apply (auto split: option.splits simp add: map_of_map_apsnd Let_def)
  apply (subst subst1.simps, auto split: option.splits)[1]
  apply (subst subst1.simps, auto split: option.splits)[1]
  apply (subst subst1.simps, auto split: option.splits)[1]
  apply (subst subst1.simps, auto split: option.splits)[1]
  apply (subst subst1.simps, auto split: option.splits, simp only: Let_def map_lc.simps)[1]
  apply (subst subst1.simps, auto split: option.splits)
  done 


fun subst' :: "subst \<Rightarrow> form \<Rightarrow> form" where
    "subst' s (Var v xs) =
      (case map_of s v of None \<Rightarrow> (Var v (map (subst' s) xs))
                 | Some (ps,rhs) \<Rightarrow>
                     if length ps = length xs
                     then subst1 (zip ps (map (subst' s) xs)) rhs
                     else (Var v (map (subst' s) xs)))"
  | "subst' s (LC n) = LC n"
  | "subst' s (Op n xs) = Op n (map (subst' s) xs)"
  | "subst' s (Quant n v f) =
      (if v \<in> fv_subst s then
      (let v' = fresh_for (fv_subst s)
       in Quant n v' (subst' ((v,([], Var v' []))#s) f))
      else Quant n v (subst' s f))"

lemma subst'_Nil[simp]: "subst' [] f = f"
  by (induction f) (auto simp add: map_idI fv_subst_def)

lemma lc_subst': "lc (subst' s f) \<subseteq> lc f \<union> lc_subst s"
  apply (induction s f rule: subst'.induct)
     apply (auto split: option.splits dest: map_of_SomeD  dest!: subsetD[OF lc_subst1] simp add: fv_subst_def)
   apply (fastforce dest!: set_zip_rightD)+
  done

lemma ran_map_option_comp[simp]:
  "ran (map_option f \<circ> m) = f ` ran m"
unfolding comp_def by (rule ran_map_option)

lemma fv_schema_apsnd_map_lc[simp]:
  "fv_schema (apsnd (map_lc p) a) = fv_schema a"
by (cases a) auto

lemma fv_subst_map_apsnd_map_lc[simp]:
  "fv_subst (map (apsnd (apsnd (map_lc p))) s) = fv_subst s"
unfolding fv_subst_def 
by (auto simp add: map_of_map_apsnd)

lemma map_apsnd_zip[simp]: "map (apsnd f) (zip a b) = zip a (map f b)"
  by (simp add: apsnd_def' zip_map2)

lemma map_lc_subst'[simp]: "map_lc p (subst' s f) = subst' (map_lc_subst p s) (map_lc p f)"
  apply (induction s f rule: subst'.induct)
     apply (auto split: option.splits dest: map_of_SomeD simp add: map_of_map_apsnd Let_def)
        apply (solves \<open>(subst subst'.simps, auto split: option.splits)[1]\<close>)
       apply (solves \<open>(subst subst'.simps, auto split: option.splits cong: map_cong)[1]\<close>)
      apply (solves \<open>(subst subst'.simps, auto split: option.splits)[1]\<close>)
     apply (solves \<open>(subst subst'.simps, auto split: option.splits)[1]\<close>)
    apply (solves \<open>(subst subst'.simps, auto split: option.splits)[1]\<close>)
   apply (solves \<open>(subst subst'.simps, auto split: option.splits, simp only: Let_def map_lc.simps)[1]\<close>)
  apply (solves \<open>(subst subst'.simps, auto split: option.splits)[1]\<close>)
done

text \<open>Since subst' happily renames quantified variables, we have a simple wrapper that
ensures that the substitution is minimal, and is empty if \<open>f\<close> is closed. This is 
a hack to support lemma  \<open>subst_noop\<close>. \<close>

fun subst :: "subst \<Rightarrow> form \<Rightarrow> form" where
  "subst s f = subst' (filter (\<lambda> (v,s). v \<in> fv f) s) f"

lemma subst_Nil[simp]: "subst [] f = f"
  by auto

lemma subst_noop[simp]: "fv f = {} \<Longrightarrow> subst s f = f"
  by simp

lemma lc_subst: "lc (subst s f) \<subseteq> lc f \<union> lc_subst s"
  by (auto dest: subsetD[OF lc_subst'])

lemma lc_subst_map_lc_subst[simp]: "lc_subst (map_lc_subst p s) = p ` lc_subst s"
  by force

lemma map_lc_subst[simp]: "map_lc p (subst s f) = subst (map_lc_subst p s) (map_lc p f)"
  unfolding subst.simps
  by (auto simp add: filter_map intro!: arg_cong[OF filter_cong] )

fun closed :: "form \<Rightarrow> bool" where
  "closed f \<longleftrightarrow> fv f = {} \<and> lc f = {}"

interpretation predicate: Abstract_Formulas
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  apply unfold_locales
  apply (solves fastforce)
  apply (solves fastforce)
  apply (solves fastforce)
  apply (solves fastforce)
  apply (solves fastforce)
  apply (solves \<open>rule lc_subst\<close>)
  apply (solves fastforce)
  apply (solves fastforce)
  apply (solves fastforce)
  apply (solves \<open>metis map_lc_subst_cong\<close>)
  apply (solves \<open>rule lc_subst_map_lc_subst\<close>)
  apply (solves simp)
  apply (solves \<open>rule exI[where x = "[]"], simp\<close>)
  apply (solves \<open>rename_tac f, rule_tac x = "[(0, ([],f))]" in exI, simp\<close>)
  done

declare predicate.subst_lconsts_empty_subst [simp del]

end
