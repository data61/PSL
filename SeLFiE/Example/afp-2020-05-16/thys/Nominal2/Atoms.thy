(*  Title:      Atoms
    Authors:    Brian Huffman, Christian Urban

    Instantiations of concrete atoms 
*)

theory Atoms
imports Nominal2_Base
begin



section \<open>@{const nat_of} is an example of a function 
  without finite support\<close>


lemma not_fresh_nat_of:
  shows "\<not> a \<sharp> nat_of"
unfolding fresh_def supp_def
proof (clarsimp)
  assume "finite {b. (a \<rightleftharpoons> b) \<bullet> nat_of \<noteq> nat_of}"
  hence "finite ({a} \<union> {b. (a \<rightleftharpoons> b) \<bullet> nat_of \<noteq> nat_of})"
    by simp
  then obtain b where
    b1: "b \<noteq> a" and
    b2: "sort_of b = sort_of a" and
    b3: "(a \<rightleftharpoons> b) \<bullet> nat_of = nat_of"
    by (rule obtain_atom) auto
  have "nat_of a = (a \<rightleftharpoons> b) \<bullet> (nat_of a)" by (simp add: permute_nat_def)
  also have "\<dots> = ((a \<rightleftharpoons> b) \<bullet> nat_of) ((a \<rightleftharpoons> b) \<bullet> a)" by (simp add: permute_fun_app_eq)
  also have "\<dots> = nat_of ((a \<rightleftharpoons> b) \<bullet> a)" using b3 by simp
  also have "\<dots> = nat_of b" using b2 by simp
  finally have "nat_of a = nat_of b" by simp
  with b2 have "a = b" by (simp add: atom_components_eq_iff)
  with b1 show "False" by simp
qed

lemma supp_nat_of:
  shows "supp nat_of = UNIV"
  using not_fresh_nat_of [unfolded fresh_def] by auto


section \<open>Manual instantiation of class \<open>at\<close>.\<close>

typedef name = "{a. sort_of a = Sort ''name'' []}"
by (rule exists_eq_simple_sort)

instantiation name :: at
begin

definition
  "p \<bullet> a = Abs_name (p \<bullet> Rep_name a)"

definition
  "atom a = Rep_name a"

instance
apply (rule at_class)
apply (rule type_definition_name)
apply (rule atom_name_def)
apply (rule permute_name_def)
done

end

lemma sort_of_atom_name: 
  shows "sort_of (atom (a::name)) = Sort ''name'' []"
  by (simp add: atom_name_def Rep_name[simplified])

text \<open>Custom syntax for concrete atoms of type at\<close>

term "a:::name"


section \<open>Automatic instantiation of class \<open>at\<close>.\<close>

atom_decl name2

lemma 
  "sort_of (atom (a::name2)) \<noteq> sort_of (atom (b::name))"
by (simp add: sort_of_atom_name)


text \<open>example swappings\<close>
lemma
  fixes a b::"atom"
  assumes "sort_of a = sort_of b"
  shows "(a \<rightleftharpoons> b) \<bullet> (a, b) = (b, a)"
using assms
by simp

lemma
  fixes a b::"name2"
  shows "(a \<leftrightarrow> b) \<bullet> (a, b) = (b, a)"
by simp

section \<open>An example for multiple-sort atoms\<close>

datatype ty =
  TVar string
| Fun ty ty ("_ \<rightarrow> _")

primrec
  sort_of_ty::"ty \<Rightarrow> atom_sort"
where
  "sort_of_ty (TVar s) = Sort ''TVar'' [Sort s []]"
| "sort_of_ty (Fun ty1 ty2) = Sort ''Fun'' [sort_of_ty ty1, sort_of_ty ty2]"

lemma sort_of_ty_eq_iff:
  shows "sort_of_ty x = sort_of_ty y \<longleftrightarrow> x = y"
apply(induct x arbitrary: y)
apply(case_tac [!] y)
apply(simp_all)
done

declare sort_of_ty.simps [simp del]

typedef var = "{a. sort_of a \<in> range sort_of_ty}"
  by (rule_tac x="Atom (sort_of_ty x) y" in exI, simp)

instantiation var :: at_base
begin

definition
  "p \<bullet> a = Abs_var (p \<bullet> Rep_var a)"

definition
  "atom a = Rep_var a"

instance
apply (rule at_base_class)
apply (rule type_definition_var)
apply (rule atom_var_def)
apply (rule permute_var_def)
done

end

text \<open>Constructor for variables.\<close>

definition
  Var :: "nat \<Rightarrow> ty \<Rightarrow> var"
where
  "Var x t = Abs_var (Atom (sort_of_ty t) x)"

lemma Var_eq_iff [simp]:
  shows "Var x s = Var y t \<longleftrightarrow> x = y \<and> s = t"
  unfolding Var_def
  by (auto simp add: Abs_var_inject sort_of_ty_eq_iff)

lemma sort_of_atom_var [simp]:
  "sort_of (atom (Var n ty)) = sort_of_ty ty"
  unfolding atom_var_def Var_def
  by (simp add: Abs_var_inverse)

lemma 
  assumes "\<alpha> \<noteq> \<beta>" 
  shows "(Var x \<alpha> \<leftrightarrow> Var y \<alpha>) \<bullet> (Var x \<alpha>, Var x \<beta>) = (Var y \<alpha>, Var x \<beta>)"
  using assms by simp

text \<open>Projecting out the type component of a variable.\<close>

definition
  ty_of :: "var \<Rightarrow> ty"
where
  "ty_of x = inv sort_of_ty (sort_of (atom x))"

text \<open>
  Functions @{term Var}/@{term ty_of} satisfy many of the same
  properties as @{term Atom}/@{term sort_of}.
\<close>

lemma ty_of_Var [simp]:
  shows "ty_of (Var x t) = t"
  unfolding ty_of_def
  unfolding sort_of_atom_var
  apply (rule inv_f_f)
  apply (simp add: inj_on_def sort_of_ty_eq_iff)
  done

lemma ty_of_permute [simp]:
  shows "ty_of (p \<bullet> x) = ty_of x"
  unfolding ty_of_def
  unfolding atom_eqvt [symmetric]
  by (simp only: sort_of_permute)


section \<open>Tests with subtyping and automatic coercions\<close>

declare [[coercion_enabled]]

atom_decl var1
atom_decl var2

declare [[coercion "atom::var1\<Rightarrow>atom"]]

declare [[coercion "atom::var2\<Rightarrow>atom"]]

lemma
  fixes a::"var1" and b::"var2"
  shows "a \<sharp> t \<and> b \<sharp> t"
oops


(* does not yet work: it needs image as
   coercion map *)

lemma
  fixes as::"var1 set"
  shows "atom ` as \<sharp>* t"

oops

end
