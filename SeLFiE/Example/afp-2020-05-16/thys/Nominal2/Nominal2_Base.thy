(*  Title:      Nominal2_Base
    Authors:    Christian Urban, Brian Huffman, Cezary Kaliszyk

    Basic definitions and lemma infrastructure for
    Nominal Isabelle.
*)
theory Nominal2_Base
imports "HOL-Library.Infinite_Set"
        "HOL-Library.Multiset"
        "HOL-Library.FSet"
        FinFun.FinFun
keywords
  "atom_decl" "equivariance" :: thy_decl
begin

declare [[typedef_overloaded]]


section \<open>Atoms and Sorts\<close>

text \<open>A simple implementation for \<open>atom_sorts\<close> is strings.\<close>
(* types atom_sort = string *)

text \<open>To deal with Church-like binding we use trees of
  strings as sorts.\<close>

datatype atom_sort = Sort "string" "atom_sort list"

datatype atom = Atom atom_sort nat


text \<open>Basic projection function.\<close>

primrec
  sort_of :: "atom \<Rightarrow> atom_sort"
where
  "sort_of (Atom s n) = s"

primrec
  nat_of :: "atom \<Rightarrow> nat"
where
  "nat_of (Atom s n) = n"


text \<open>There are infinitely many atoms of each sort.\<close>
lemma INFM_sort_of_eq:
  shows "INFM a. sort_of a = s"
proof -
  have "INFM i. sort_of (Atom s i) = s" by simp
  moreover have "inj (Atom s)" by (simp add: inj_on_def)
  ultimately show "INFM a. sort_of a = s" by (rule INFM_inj)
qed

lemma infinite_sort_of_eq:
  shows "infinite {a. sort_of a = s}"
  using INFM_sort_of_eq unfolding INFM_iff_infinite .

lemma atom_infinite [simp]:
  shows "infinite (UNIV :: atom set)"
  using subset_UNIV infinite_sort_of_eq
  by (rule infinite_super)

lemma obtain_atom:
  fixes X :: "atom set"
  assumes X: "finite X"
  obtains a where "a \<notin> X" "sort_of a = s"
proof -
  from X have "MOST a. a \<notin> X"
    unfolding MOST_iff_cofinite by simp
  with INFM_sort_of_eq
  have "INFM a. sort_of a = s \<and> a \<notin> X"
    by (rule INFM_conjI)
  then obtain a where "a \<notin> X" "sort_of a = s"
    by (auto elim: INFM_E)
  then show ?thesis ..
qed

lemma atom_components_eq_iff:
  fixes a b :: atom
  shows "a = b \<longleftrightarrow> sort_of a = sort_of b \<and> nat_of a = nat_of b"
  by (induct a, induct b, simp)


section \<open>Sort-Respecting Permutations\<close>

definition
  "perm \<equiv> {f. bij f \<and> finite {a. f a \<noteq> a} \<and> (\<forall>a. sort_of (f a) = sort_of a)}"

typedef perm = "perm"
proof
  show "id \<in> perm" unfolding perm_def by simp
qed

lemma permI:
  assumes "bij f" and "MOST x. f x = x" and "\<And>a. sort_of (f a) = sort_of a"
  shows "f \<in> perm"
  using assms unfolding perm_def MOST_iff_cofinite by simp

lemma perm_is_bij: "f \<in> perm \<Longrightarrow> bij f"
  unfolding perm_def by simp

lemma perm_is_finite: "f \<in> perm \<Longrightarrow> finite {a. f a \<noteq> a}"
  unfolding perm_def by simp

lemma perm_is_sort_respecting: "f \<in> perm \<Longrightarrow> sort_of (f a) = sort_of a"
  unfolding perm_def by simp

lemma perm_MOST: "f \<in> perm \<Longrightarrow> MOST x. f x = x"
  unfolding perm_def MOST_iff_cofinite by simp

lemma perm_id: "id \<in> perm"
  unfolding perm_def by simp

lemma perm_comp:
  assumes f: "f \<in> perm" and g: "g \<in> perm"
  shows "(f \<circ> g) \<in> perm"
apply (rule permI)
apply (rule bij_comp)
apply (rule perm_is_bij [OF g])
apply (rule perm_is_bij [OF f])
apply (rule MOST_rev_mp [OF perm_MOST [OF g]])
apply (rule MOST_rev_mp [OF perm_MOST [OF f]])
apply (simp)
apply (simp add: perm_is_sort_respecting [OF f])
apply (simp add: perm_is_sort_respecting [OF g])
done

lemma perm_inv:
  assumes f: "f \<in> perm"
  shows "(inv f) \<in> perm"
apply (rule permI)
apply (rule bij_imp_bij_inv)
apply (rule perm_is_bij [OF f])
apply (rule MOST_mono [OF perm_MOST [OF f]])
apply (erule subst, rule inv_f_f)
apply (rule bij_is_inj [OF perm_is_bij [OF f]])
apply (rule perm_is_sort_respecting [OF f, THEN sym, THEN trans])
apply (simp add: surj_f_inv_f [OF bij_is_surj [OF perm_is_bij [OF f]]])
done

lemma bij_Rep_perm: "bij (Rep_perm p)"
  using Rep_perm [of p] unfolding perm_def by simp

lemma finite_Rep_perm: "finite {a. Rep_perm p a \<noteq> a}"
  using Rep_perm [of p] unfolding perm_def by simp

lemma sort_of_Rep_perm: "sort_of (Rep_perm p a) = sort_of a"
  using Rep_perm [of p] unfolding perm_def by simp

lemma Rep_perm_ext:
  "Rep_perm p1 = Rep_perm p2 \<Longrightarrow> p1 = p2"
  by (simp add: fun_eq_iff Rep_perm_inject [symmetric])

instance perm :: size ..


subsection \<open>Permutations form a (multiplicative) group\<close>

instantiation perm :: group_add
begin

definition
  "0 = Abs_perm id"

definition
  "- p = Abs_perm (inv (Rep_perm p))"

definition
  "p + q = Abs_perm (Rep_perm p \<circ> Rep_perm q)"

definition
  "(p1::perm) - p2 = p1 + - p2"

lemma Rep_perm_0: "Rep_perm 0 = id"
  unfolding zero_perm_def
  by (simp add: Abs_perm_inverse perm_id)

lemma Rep_perm_add:
  "Rep_perm (p1 + p2) = Rep_perm p1 \<circ> Rep_perm p2"
  unfolding plus_perm_def
  by (simp add: Abs_perm_inverse perm_comp Rep_perm)

lemma Rep_perm_uminus:
  "Rep_perm (- p) = inv (Rep_perm p)"
  unfolding uminus_perm_def
  by (simp add: Abs_perm_inverse perm_inv Rep_perm)

instance
apply standard
unfolding Rep_perm_inject [symmetric]
unfolding minus_perm_def
unfolding Rep_perm_add
unfolding Rep_perm_uminus
unfolding Rep_perm_0
by (simp_all add: o_assoc inv_o_cancel [OF bij_is_inj [OF bij_Rep_perm]])

end


section \<open>Implementation of swappings\<close>

definition
  swap :: "atom \<Rightarrow> atom \<Rightarrow> perm" ("'(_ \<rightleftharpoons> _')")
where
  "(a \<rightleftharpoons> b) =
    Abs_perm (if sort_of a = sort_of b
              then (\<lambda>c. if a = c then b else if b = c then a else c)
              else id)"

lemma Rep_perm_swap:
  "Rep_perm (a \<rightleftharpoons> b) =
    (if sort_of a = sort_of b
     then (\<lambda>c. if a = c then b else if b = c then a else c)
     else id)"
unfolding swap_def
apply (rule Abs_perm_inverse)
apply (rule permI)
apply (auto simp: bij_def inj_on_def surj_def)[1]
apply (rule MOST_rev_mp [OF MOST_neq(1) [of a]])
apply (rule MOST_rev_mp [OF MOST_neq(1) [of b]])
apply (simp)
apply (simp)
done

lemmas Rep_perm_simps =
  Rep_perm_0
  Rep_perm_add
  Rep_perm_uminus
  Rep_perm_swap

lemma swap_different_sorts [simp]:
  "sort_of a \<noteq> sort_of b \<Longrightarrow> (a \<rightleftharpoons> b) = 0"
  by (rule Rep_perm_ext) (simp add: Rep_perm_simps)

lemma swap_cancel:
  shows "(a \<rightleftharpoons> b) + (a \<rightleftharpoons> b) = 0"
  and   "(a \<rightleftharpoons> b) + (b \<rightleftharpoons> a) = 0"
  by (rule_tac [!] Rep_perm_ext)
     (simp_all add: Rep_perm_simps fun_eq_iff)

lemma swap_self [simp]:
  "(a \<rightleftharpoons> a) = 0"
  by (rule Rep_perm_ext, simp add: Rep_perm_simps fun_eq_iff)

lemma minus_swap [simp]:
  "- (a \<rightleftharpoons> b) = (a \<rightleftharpoons> b)"
  by (rule minus_unique [OF swap_cancel(1)])

lemma swap_commute:
  "(a \<rightleftharpoons> b) = (b \<rightleftharpoons> a)"
  by (rule Rep_perm_ext)
     (simp add: Rep_perm_swap fun_eq_iff)

lemma swap_triple:
  assumes "a \<noteq> b" and "c \<noteq> b"
  assumes "sort_of a = sort_of b" "sort_of b = sort_of c"
  shows "(a \<rightleftharpoons> c) + (b \<rightleftharpoons> c) + (a \<rightleftharpoons> c) = (a \<rightleftharpoons> b)"
  using assms
  by (rule_tac Rep_perm_ext)
     (auto simp: Rep_perm_simps fun_eq_iff)


section \<open>Permutation Types\<close>

text \<open>
  Infix syntax for \<open>permute\<close> has higher precedence than
  addition, but lower than unary minus.
\<close>

class pt =
  fixes permute :: "perm \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<bullet> _" [76, 75] 75)
  assumes permute_zero [simp]: "0 \<bullet> x = x"
  assumes permute_plus [simp]: "(p + q) \<bullet> x = p \<bullet> (q \<bullet> x)"
begin

lemma permute_diff [simp]:
  shows "(p - q) \<bullet> x = p \<bullet> - q \<bullet> x"
  using permute_plus [of p "- q" x] by simp

lemma permute_minus_cancel [simp]:
  shows "p \<bullet> - p \<bullet> x = x"
  and   "- p \<bullet> p \<bullet> x = x"
  unfolding permute_plus [symmetric] by simp_all

lemma permute_swap_cancel [simp]:
  shows "(a \<rightleftharpoons> b) \<bullet> (a \<rightleftharpoons> b) \<bullet> x = x"
  unfolding permute_plus [symmetric]
  by (simp add: swap_cancel)

lemma permute_swap_cancel2 [simp]:
  shows "(a \<rightleftharpoons> b) \<bullet> (b \<rightleftharpoons> a) \<bullet> x = x"
  unfolding permute_plus [symmetric]
  by (simp add: swap_commute)

lemma inj_permute [simp]:
  shows "inj (permute p)"
  by (rule inj_on_inverseI)
     (rule permute_minus_cancel)

lemma surj_permute [simp]:
  shows "surj (permute p)"
  by (rule surjI, rule permute_minus_cancel)

lemma bij_permute [simp]:
  shows "bij (permute p)"
  by (rule bijI [OF inj_permute surj_permute])

lemma inv_permute:
  shows "inv (permute p) = permute (- p)"
  by (rule inv_equality) (simp_all)

lemma permute_minus:
  shows "permute (- p) = inv (permute p)"
  by (simp add: inv_permute)

lemma permute_eq_iff [simp]:
  shows "p \<bullet> x = p \<bullet> y \<longleftrightarrow> x = y"
  by (rule inj_permute [THEN inj_eq])

end

subsection \<open>Permutations for atoms\<close>

instantiation atom :: pt
begin

definition
  "p \<bullet> a = (Rep_perm p) a"

instance
apply standard
apply(simp_all add: permute_atom_def Rep_perm_simps)
done

end

lemma sort_of_permute [simp]:
  shows "sort_of (p \<bullet> a) = sort_of a"
  unfolding permute_atom_def by (rule sort_of_Rep_perm)

lemma swap_atom:
  shows "(a \<rightleftharpoons> b) \<bullet> c =
           (if sort_of a = sort_of b
            then (if c = a then b else if c = b then a else c) else c)"
  unfolding permute_atom_def
  by (simp add: Rep_perm_swap)

lemma swap_atom_simps [simp]:
  "sort_of a = sort_of b \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> a = b"
  "sort_of a = sort_of b \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> b = a"
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> c = c"
  unfolding swap_atom by simp_all

lemma perm_eq_iff:
  fixes p q :: "perm"
  shows "p = q \<longleftrightarrow> (\<forall>a::atom. p \<bullet> a = q \<bullet> a)"
  unfolding permute_atom_def
  by (metis Rep_perm_ext ext)

subsection \<open>Permutations for permutations\<close>

instantiation perm :: pt
begin

definition
  "p \<bullet> q = p + q - p"

instance
apply standard
apply (simp add: permute_perm_def)
apply (simp add: permute_perm_def algebra_simps)
done

end

lemma permute_self:
  shows "p \<bullet> p = p"
  unfolding permute_perm_def
  by (simp add: add.assoc)

lemma pemute_minus_self:
  shows "- p \<bullet> p = p"
  unfolding permute_perm_def
  by (simp add: add.assoc)


subsection \<open>Permutations for functions\<close>

instantiation "fun" :: (pt, pt) pt
begin

definition
  "p \<bullet> f = (\<lambda>x. p \<bullet> (f (- p \<bullet> x)))"

instance
apply standard
apply (simp add: permute_fun_def)
apply (simp add: permute_fun_def minus_add)
done

end

lemma permute_fun_app_eq:
  shows "p \<bullet> (f x) = (p \<bullet> f) (p \<bullet> x)"
  unfolding permute_fun_def by simp

lemma permute_fun_comp:
  shows "p \<bullet> f  = (permute p) o f o (permute (-p))"
by (simp add: comp_def permute_fun_def)

subsection \<open>Permutations for booleans\<close>

instantiation bool :: pt
begin

definition "p \<bullet> (b::bool) = b"

instance
apply standard
apply(simp_all add: permute_bool_def)
done

end

lemma permute_boolE:
  fixes P::"bool"
  shows "p \<bullet> P \<Longrightarrow> P"
  by (simp add: permute_bool_def)

lemma permute_boolI:
  fixes P::"bool"
  shows "P \<Longrightarrow> p \<bullet> P"
  by(simp add: permute_bool_def)

subsection \<open>Permutations for sets\<close>

instantiation "set" :: (pt) pt
begin

definition
  "p \<bullet> X = {p \<bullet> x | x. x \<in> X}"

instance
apply standard
apply (auto simp: permute_set_def)
done

end

lemma permute_set_eq:
 shows "p \<bullet> X = {x. - p \<bullet> x \<in> X}"
unfolding permute_set_def
by (auto) (metis permute_minus_cancel(1))

lemma permute_set_eq_image:
  shows "p \<bullet> X = permute p ` X"
  unfolding permute_set_def by auto

lemma permute_set_eq_vimage:
  shows "p \<bullet> X = permute (- p) -` X"
  unfolding permute_set_eq vimage_def
  by simp

lemma permute_finite [simp]:
  shows "finite (p \<bullet> X) = finite X"
  unfolding permute_set_eq_vimage
  using bij_permute by (rule finite_vimage_iff)

lemma swap_set_not_in:
  assumes a: "a \<notin> S" "b \<notin> S"
  shows "(a \<rightleftharpoons> b) \<bullet> S = S"
  unfolding permute_set_def
  using a by (auto simp: swap_atom)

lemma swap_set_in:
  assumes a: "a \<in> S" "b \<notin> S" "sort_of a = sort_of b"
  shows "(a \<rightleftharpoons> b) \<bullet> S \<noteq> S"
  unfolding permute_set_def
  using a by (auto simp: swap_atom)

lemma swap_set_in_eq:
  assumes a: "a \<in> S" "b \<notin> S" "sort_of a = sort_of b"
  shows "(a \<rightleftharpoons> b) \<bullet> S = (S - {a}) \<union> {b}"
  unfolding permute_set_def
  using a by (auto simp: swap_atom)

lemma swap_set_both_in:
  assumes a: "a \<in> S" "b \<in> S"
  shows "(a \<rightleftharpoons> b) \<bullet> S = S"
  unfolding permute_set_def
  using a by (auto simp: swap_atom)

lemma mem_permute_iff:
  shows "(p \<bullet> x) \<in> (p \<bullet> X) \<longleftrightarrow> x \<in> X"
  unfolding permute_set_def
  by auto

lemma empty_eqvt:
  shows "p \<bullet> {} = {}"
  unfolding permute_set_def
  by (simp)

lemma insert_eqvt:
  shows "p \<bullet> (insert x A) = insert (p \<bullet> x) (p \<bullet> A)"
  unfolding permute_set_eq_image image_insert ..


subsection \<open>Permutations for @{typ unit}\<close>

instantiation unit :: pt
begin

definition "p \<bullet> (u::unit) = u"

instance
  by standard (simp_all add: permute_unit_def)

end


subsection \<open>Permutations for products\<close>

instantiation prod :: (pt, pt) pt
begin

primrec
  permute_prod
where
  Pair_eqvt: "p \<bullet> (x, y) = (p \<bullet> x, p \<bullet> y)"

instance
  by standard auto

end

subsection \<open>Permutations for sums\<close>

instantiation sum :: (pt, pt) pt
begin

primrec
  permute_sum
where
  Inl_eqvt: "p \<bullet> (Inl x) = Inl (p \<bullet> x)"
| Inr_eqvt: "p \<bullet> (Inr y) = Inr (p \<bullet> y)"

instance
  by standard (case_tac [!] x, simp_all)

end

subsection \<open>Permutations for @{typ "'a list"}\<close>

instantiation list :: (pt) pt
begin

primrec
  permute_list
where
  Nil_eqvt:  "p \<bullet> [] = []"
| Cons_eqvt: "p \<bullet> (x # xs) = p \<bullet> x # p \<bullet> xs"

instance
  by standard (induct_tac [!] x, simp_all)

end

lemma set_eqvt:
  shows "p \<bullet> (set xs) = set (p \<bullet> xs)"
  by (induct xs) (simp_all add: empty_eqvt insert_eqvt)



subsection \<open>Permutations for @{typ "'a option"}\<close>

instantiation option :: (pt) pt
begin

primrec
  permute_option
where
  None_eqvt: "p \<bullet> None = None"
| Some_eqvt: "p \<bullet> (Some x) = Some (p \<bullet> x)"

instance
  by standard (induct_tac [!] x, simp_all)

end

subsection \<open>Permutations for @{typ "'a multiset"}\<close>

instantiation multiset :: (pt) pt
begin

definition
  "p \<bullet> M = {# p \<bullet> x. x :# M #}"

instance
proof
  fix M :: "'a multiset" and p q :: "perm"
  show "0 \<bullet> M = M"
    unfolding permute_multiset_def
    by (induct_tac M) (simp_all)
  show "(p + q) \<bullet> M = p \<bullet> q \<bullet> M"
    unfolding permute_multiset_def
    by (induct_tac M) (simp_all)
qed

end

lemma permute_multiset [simp]:
  fixes M N::"('a::pt) multiset"
  shows "(p \<bullet> {#}) = ({#} ::('a::pt) multiset)"
  and   "(p \<bullet> add_mset x M) = add_mset (p \<bullet> x) (p \<bullet> M)"
  and   "(p \<bullet> (M + N)) = (p \<bullet> M) + (p \<bullet> N)"
  unfolding permute_multiset_def
  by (simp_all)


subsection \<open>Permutations for @{typ "'a fset"}\<close>

instantiation fset :: (pt) pt
begin

context includes fset.lifting begin
lift_definition
  "permute_fset" :: "perm \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
is "permute :: perm \<Rightarrow> 'a set \<Rightarrow> 'a set" by simp
end

context includes fset.lifting begin
instance
proof
  fix x :: "'a fset" and p q :: "perm"
  show "0 \<bullet> x = x" by transfer simp
  show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x"  by transfer simp
qed
end

end

context includes fset.lifting
begin
lemma permute_fset [simp]:
  fixes S::"('a::pt) fset"
  shows "(p \<bullet> {||}) = ({||} ::('a::pt) fset)"
  and   "(p \<bullet> finsert x S) = finsert (p \<bullet> x) (p \<bullet> S)"
  apply (transfer, simp add: empty_eqvt)
  apply (transfer, simp add: insert_eqvt)
  done

lemma fset_eqvt:
  shows "p \<bullet> (fset S) = fset (p \<bullet> S)"
  by transfer simp
end


subsection \<open>Permutations for @{typ "('a, 'b) finfun"}\<close>

instantiation finfun :: (pt, pt) pt
begin

lift_definition
  permute_finfun :: "perm \<Rightarrow> ('a, 'b) finfun \<Rightarrow> ('a, 'b) finfun"
is
  "permute :: perm \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  apply(simp add: permute_fun_comp)
  apply(rule finfun_right_compose)
  apply(rule finfun_left_compose)
  apply(assumption)
  apply(simp)
  done

instance
apply standard
apply(transfer)
apply(simp)
apply(transfer)
apply(simp)
done

end


subsection \<open>Permutations for @{typ char}, @{typ nat}, and @{typ int}\<close>

instantiation char :: pt
begin

definition "p \<bullet> (c::char) = c"

instance
  by standard (simp_all add: permute_char_def)

end

instantiation nat :: pt
begin

definition "p \<bullet> (n::nat) = n"

instance
  by standard (simp_all add: permute_nat_def)

end

instantiation int :: pt
begin

definition "p \<bullet> (i::int) = i"

instance
  by standard (simp_all add: permute_int_def)

end


section \<open>Pure types\<close>

text \<open>Pure types will have always empty support.\<close>

class pure = pt +
  assumes permute_pure: "p \<bullet> x = x"

text \<open>Types @{typ unit} and @{typ bool} are pure.\<close>

instance unit :: pure
proof qed (rule permute_unit_def)

instance bool :: pure
proof qed (rule permute_bool_def)


text \<open>Other type constructors preserve purity.\<close>

instance "fun" :: (pure, pure) pure
  by standard (simp add: permute_fun_def permute_pure)

instance set :: (pure) pure
  by standard (simp add: permute_set_def permute_pure)

instance prod :: (pure, pure) pure
  by standard (induct_tac x, simp add: permute_pure)

instance sum :: (pure, pure) pure
  by standard (induct_tac x, simp_all add: permute_pure)

instance list :: (pure) pure
  by standard (induct_tac x, simp_all add: permute_pure)

instance option :: (pure) pure
  by standard (induct_tac x, simp_all add: permute_pure)


subsection \<open>Types @{typ char}, @{typ nat}, and @{typ int}\<close>

instance char :: pure
proof qed (rule permute_char_def)

instance nat :: pure
proof qed (rule permute_nat_def)

instance int :: pure
proof qed (rule permute_int_def)


section \<open>Infrastructure for Equivariance and \<open>Perm_simp\<close>\<close>

subsection \<open>Basic functions about permutations\<close>

ML_file \<open>nominal_basics.ML\<close>


subsection \<open>Eqvt infrastructure\<close>

text \<open>Setup of the theorem attributes \<open>eqvt\<close> and \<open>eqvt_raw\<close>.\<close>

ML_file \<open>nominal_thmdecls.ML\<close>


lemmas [eqvt] =
  (* pt types *)
  permute_prod.simps
  permute_list.simps
  permute_option.simps
  permute_sum.simps

  (* sets *)
  empty_eqvt insert_eqvt set_eqvt

  (* fsets *)
  permute_fset fset_eqvt

  (* multisets *)
  permute_multiset

subsection \<open>\<open>perm_simp\<close> infrastructure\<close>

definition
  "unpermute p = permute (- p)"

lemma eqvt_apply:
  fixes f :: "'a::pt \<Rightarrow> 'b::pt"
  and x :: "'a::pt"
  shows "p \<bullet> (f x) \<equiv> (p \<bullet> f) (p \<bullet> x)"
  unfolding permute_fun_def by simp

lemma eqvt_lambda:
  fixes f :: "'a::pt \<Rightarrow> 'b::pt"
  shows "p \<bullet> f \<equiv> (\<lambda>x. p \<bullet> (f (unpermute p x)))"
  unfolding permute_fun_def unpermute_def by simp

lemma eqvt_bound:
  shows "p \<bullet> unpermute p x \<equiv> x"
  unfolding unpermute_def by simp

text \<open>provides \<open>perm_simp\<close> methods\<close>

ML_file \<open>nominal_permeq.ML\<close>

method_setup perm_simp =
 \<open>Nominal_Permeq.args_parser >> Nominal_Permeq.perm_simp_meth\<close>
 \<open>pushes permutations inside.\<close>

method_setup perm_strict_simp =
 \<open>Nominal_Permeq.args_parser >> Nominal_Permeq.perm_strict_simp_meth\<close>
 \<open>pushes permutations inside, raises an error if it cannot solve all permutations.\<close>

simproc_setup perm_simproc ("p \<bullet> t") = \<open>fn _ => fn ctxt => fn ctrm =>
  case Thm.term_of (Thm.dest_arg ctrm) of
    Free _ => NONE
  | Var _ => NONE
  | Const (@{const_name permute}, _) $ _ $ _ => NONE
  | _ =>
      let
        val thm = Nominal_Permeq.eqvt_conv ctxt Nominal_Permeq.eqvt_strict_config ctrm
          handle ERROR _ => Thm.reflexive ctrm
      in
        if Thm.is_reflexive thm then NONE else SOME(thm)
      end
\<close>


subsubsection \<open>Equivariance for permutations and swapping\<close>

lemma permute_eqvt:
  shows "p \<bullet> (q \<bullet> x) = (p \<bullet> q) \<bullet> (p \<bullet> x)"
  unfolding permute_perm_def by simp

(* the normal version of this lemma would cause loops *)
lemma permute_eqvt_raw [eqvt_raw]:
  shows "p \<bullet> permute \<equiv> permute"
apply(simp add: fun_eq_iff permute_fun_def)
apply(subst permute_eqvt)
apply(simp)
done

lemma zero_perm_eqvt [eqvt]:
  shows "p \<bullet> (0::perm) = 0"
  unfolding permute_perm_def by simp

lemma add_perm_eqvt [eqvt]:
  fixes p p1 p2 :: perm
  shows "p \<bullet> (p1 + p2) = p \<bullet> p1 + p \<bullet> p2"
  unfolding permute_perm_def
  by (simp add: perm_eq_iff)

lemma swap_eqvt [eqvt]:
  shows "p \<bullet> (a \<rightleftharpoons> b) = (p \<bullet> a \<rightleftharpoons> p \<bullet> b)"
  unfolding permute_perm_def
  by (auto simp: swap_atom perm_eq_iff)

lemma uminus_eqvt [eqvt]:
  fixes p q::"perm"
  shows "p \<bullet> (- q) = - (p \<bullet> q)"
  unfolding permute_perm_def
  by (simp add: diff_add_eq_diff_diff_swap)


subsubsection \<open>Equivariance of Logical Operators\<close>

lemma eq_eqvt [eqvt]:
  shows "p \<bullet> (x = y) \<longleftrightarrow> (p \<bullet> x) = (p \<bullet> y)"
  unfolding permute_eq_iff permute_bool_def ..

lemma Not_eqvt [eqvt]:
  shows "p \<bullet> (\<not> A) \<longleftrightarrow> \<not> (p \<bullet> A)"
  by (simp add: permute_bool_def)

lemma conj_eqvt [eqvt]:
  shows "p \<bullet> (A \<and> B) \<longleftrightarrow> (p \<bullet> A) \<and> (p \<bullet> B)"
  by (simp add: permute_bool_def)

lemma imp_eqvt [eqvt]:
  shows "p \<bullet> (A \<longrightarrow> B) \<longleftrightarrow> (p \<bullet> A) \<longrightarrow> (p \<bullet> B)"
  by (simp add: permute_bool_def)

declare imp_eqvt[folded HOL.induct_implies_def, eqvt]

lemma all_eqvt [eqvt]:
  shows "p \<bullet> (\<forall>x. P x) = (\<forall>x. (p \<bullet> P) x)"
  unfolding All_def
  by (perm_simp) (rule refl)

declare all_eqvt[folded HOL.induct_forall_def, eqvt]

lemma ex_eqvt [eqvt]:
  shows "p \<bullet> (\<exists>x. P x) = (\<exists>x. (p \<bullet> P) x)"
  unfolding Ex_def
  by (perm_simp) (rule refl)

lemma ex1_eqvt [eqvt]:
  shows "p \<bullet> (\<exists>!x. P x) = (\<exists>!x. (p \<bullet> P) x)"
  unfolding Ex1_def
  by (perm_simp) (rule refl)

lemma if_eqvt [eqvt]:
  shows "p \<bullet> (if b then x else y) = (if p \<bullet> b then p \<bullet> x else p \<bullet> y)"
  by (simp add: permute_fun_def permute_bool_def)

lemma True_eqvt [eqvt]:
  shows "p \<bullet> True = True"
  unfolding permute_bool_def ..

lemma False_eqvt [eqvt]:
  shows "p \<bullet> False = False"
  unfolding permute_bool_def ..

lemma disj_eqvt [eqvt]:
  shows "p \<bullet> (A \<or> B) \<longleftrightarrow> (p \<bullet> A) \<or> (p \<bullet> B)"
  by (simp add: permute_bool_def)

lemma all_eqvt2:
  shows "p \<bullet> (\<forall>x. P x) = (\<forall>x. p \<bullet> P (- p \<bullet> x))"
  by (perm_simp add: permute_minus_cancel) (rule refl)

lemma ex_eqvt2:
  shows "p \<bullet> (\<exists>x. P x) = (\<exists>x. p \<bullet> P (- p \<bullet> x))"
  by (perm_simp add: permute_minus_cancel) (rule refl)

lemma ex1_eqvt2:
  shows "p \<bullet> (\<exists>!x. P x) = (\<exists>!x. p \<bullet> P (- p \<bullet> x))"
  by (perm_simp add: permute_minus_cancel) (rule refl)

lemma the_eqvt:
  assumes unique: "\<exists>!x. P x"
  shows "(p \<bullet> (THE x. P x)) = (THE x. (p \<bullet> P) x)"
  apply(rule the1_equality [symmetric])
  apply(rule_tac p="-p" in permute_boolE)
  apply(perm_simp add: permute_minus_cancel)
  apply(rule unique)
  apply(rule_tac p="-p" in permute_boolE)
  apply(perm_simp add: permute_minus_cancel)
  apply(rule theI'[OF unique])
  done

lemma the_eqvt2:
  assumes unique: "\<exists>!x. P x"
  shows "(p \<bullet> (THE x. P x)) = (THE x. p \<bullet> P (- p \<bullet> x))"
  apply(rule the1_equality [symmetric])
  apply(simp only: ex1_eqvt2[symmetric])
  apply(simp add: permute_bool_def unique)
  apply(simp add: permute_bool_def)
  apply(rule theI'[OF unique])
  done

subsubsection \<open>Equivariance of Set operators\<close>

lemma mem_eqvt [eqvt]:
  shows "p \<bullet> (x \<in> A) \<longleftrightarrow> (p \<bullet> x) \<in> (p \<bullet> A)"
  unfolding permute_bool_def permute_set_def
  by (auto)

lemma Collect_eqvt [eqvt]:
  shows "p \<bullet> {x. P x} = {x. (p \<bullet> P) x}"
  unfolding permute_set_eq permute_fun_def
  by (auto simp: permute_bool_def)

lemma Bex_eqvt [eqvt]:
  shows "p \<bullet> (\<exists>x \<in> S. P x) = (\<exists>x \<in> (p \<bullet> S). (p \<bullet> P) x)"
  unfolding Bex_def by simp

lemma Ball_eqvt [eqvt]:
  shows "p \<bullet> (\<forall>x \<in> S. P x) = (\<forall>x \<in> (p \<bullet> S). (p \<bullet> P) x)"
  unfolding Ball_def by simp

lemma image_eqvt [eqvt]:
  shows "p \<bullet> (f ` A) = (p \<bullet> f) ` (p \<bullet> A)"
  unfolding image_def by simp

lemma Image_eqvt [eqvt]:
  shows "p \<bullet> (R `` A) = (p \<bullet> R) `` (p \<bullet> A)"
  unfolding Image_def by simp

lemma UNIV_eqvt [eqvt]:
  shows "p \<bullet> UNIV = UNIV"
  unfolding UNIV_def
  by (perm_simp) (rule refl)

lemma inter_eqvt [eqvt]:
  shows "p \<bullet> (A \<inter> B) = (p \<bullet> A) \<inter> (p \<bullet> B)"
  unfolding Int_def by simp

lemma Inter_eqvt [eqvt]:
  shows "p \<bullet> \<Inter>S = \<Inter>(p \<bullet> S)"
  unfolding Inter_eq by simp

lemma union_eqvt [eqvt]:
  shows "p \<bullet> (A \<union> B) = (p \<bullet> A) \<union> (p \<bullet> B)"
  unfolding Un_def by simp

lemma Union_eqvt [eqvt]:
  shows "p \<bullet> \<Union>A = \<Union>(p \<bullet> A)"
  unfolding Union_eq
  by perm_simp rule

lemma Diff_eqvt [eqvt]:
  fixes A B :: "'a::pt set"
  shows "p \<bullet> (A - B) = (p \<bullet> A) - (p \<bullet> B)"
  unfolding set_diff_eq by simp

lemma Compl_eqvt [eqvt]:
  fixes A :: "'a::pt set"
  shows "p \<bullet> (- A) = - (p \<bullet> A)"
  unfolding Compl_eq_Diff_UNIV by simp

lemma subset_eqvt [eqvt]:
  shows "p \<bullet> (S \<subseteq> T) \<longleftrightarrow> (p \<bullet> S) \<subseteq> (p \<bullet> T)"
  unfolding subset_eq by simp

lemma psubset_eqvt [eqvt]:
  shows "p \<bullet> (S \<subset> T) \<longleftrightarrow> (p \<bullet> S) \<subset> (p \<bullet> T)"
  unfolding psubset_eq by simp

lemma vimage_eqvt [eqvt]:
  shows "p \<bullet> (f -` A) = (p \<bullet> f) -` (p \<bullet> A)"
  unfolding vimage_def by simp

lemma foldr_eqvt[eqvt]:
  "p \<bullet> foldr f xs = foldr (p \<bullet> f) (p \<bullet> xs)"
  apply(induct xs)
  apply(simp_all)
  apply(perm_simp exclude: foldr)
  apply(simp)
  done

(* FIXME: eqvt attribute *)
lemma Sigma_eqvt:
  shows "(p \<bullet> (X \<times> Y)) = (p \<bullet> X) \<times> (p \<bullet> Y)"
unfolding Sigma_def
by (perm_simp) (rule refl)

text \<open>
  In order to prove that lfp is equivariant we need two
  auxiliary classes which specify that (<=) and
  Inf are equivariant. Instances for bool and fun are
  given.
\<close>

class le_eqvt = order +
  assumes le_eqvt [eqvt]: "p \<bullet> (x \<le> y) = ((p \<bullet> x) \<le> (p \<bullet> (y::('a::{pt, order}))))"

class inf_eqvt = Inf +
  assumes inf_eqvt [eqvt]: "p \<bullet> (Inf X) = Inf (p \<bullet> (X::('a::{pt, complete_lattice}) set))"

instantiation bool :: le_eqvt
begin

instance
apply standard
unfolding le_bool_def
apply(perm_simp)
apply(rule refl)
done

end

instantiation "fun" :: (pt, le_eqvt) le_eqvt
begin

instance
apply standard
unfolding le_fun_def
apply(perm_simp)
apply(rule refl)
done

end

instantiation bool :: inf_eqvt
begin

instance
apply standard
unfolding Inf_bool_def
apply(perm_simp)
apply(rule refl)
done

end

instantiation "fun" :: (pt, inf_eqvt) inf_eqvt
begin

instance
apply standard
unfolding Inf_fun_def
apply(perm_simp)
apply(rule refl)
done

end

lemma lfp_eqvt [eqvt]:
  fixes F::"('a \<Rightarrow> 'b) \<Rightarrow> ('a::pt \<Rightarrow> 'b::{inf_eqvt, le_eqvt})"
  shows "p \<bullet> (lfp F) = lfp (p \<bullet> F)"
unfolding lfp_def
by simp

lemma finite_eqvt [eqvt]:
  shows "p \<bullet> finite A = finite (p \<bullet> A)"
unfolding finite_def
by simp

lemma fun_upd_eqvt[eqvt]:
  shows "p \<bullet> (f(x := y)) = (p \<bullet> f)((p \<bullet> x) := (p \<bullet> y))"
unfolding fun_upd_def
by simp

lemma comp_eqvt [eqvt]:
  shows "p \<bullet> (f \<circ> g) = (p \<bullet> f) \<circ> (p \<bullet> g)"
unfolding comp_def
by simp

subsubsection \<open>Equivariance for product operations\<close>

lemma fst_eqvt [eqvt]:
  shows "p \<bullet> (fst x) = fst (p \<bullet> x)"
  by (cases x) simp

lemma snd_eqvt [eqvt]:
  shows "p \<bullet> (snd x) = snd (p \<bullet> x)"
  by (cases x) simp

lemma split_eqvt [eqvt]:
  shows "p \<bullet> (case_prod P x) = case_prod (p \<bullet> P) (p \<bullet> x)"
  unfolding split_def
  by simp


subsubsection \<open>Equivariance for list operations\<close>

lemma append_eqvt [eqvt]:
  shows "p \<bullet> (xs @ ys) = (p \<bullet> xs) @ (p \<bullet> ys)"
  by (induct xs) auto

lemma rev_eqvt [eqvt]:
  shows "p \<bullet> (rev xs) = rev (p \<bullet> xs)"
  by (induct xs) (simp_all add: append_eqvt)

lemma map_eqvt [eqvt]:
  shows "p \<bullet> (map f xs) = map (p \<bullet> f) (p \<bullet> xs)"
  by (induct xs) (simp_all)

lemma removeAll_eqvt [eqvt]:
  shows "p \<bullet> (removeAll x xs) = removeAll (p \<bullet> x) (p \<bullet> xs)"
  by (induct xs) (auto)

lemma filter_eqvt [eqvt]:
  shows "p \<bullet> (filter f xs) = filter (p \<bullet> f) (p \<bullet> xs)"
apply(induct xs)
apply(simp)
apply(simp only: filter.simps permute_list.simps if_eqvt)
apply(simp only: permute_fun_app_eq)
done

lemma distinct_eqvt [eqvt]:
  shows "p \<bullet> (distinct xs) = distinct (p \<bullet> xs)"
apply(induct xs)
apply(simp add: permute_bool_def)
apply(simp add: conj_eqvt Not_eqvt mem_eqvt set_eqvt)
done

lemma length_eqvt [eqvt]:
  shows "p \<bullet> (length xs) = length (p \<bullet> xs)"
by (induct xs) (simp_all add: permute_pure)


subsubsection \<open>Equivariance for @{typ "'a option"}\<close>

lemma map_option_eqvt[eqvt]:
  shows "p \<bullet> (map_option f x) = map_option (p \<bullet> f) (p \<bullet> x)"
  by (cases x) (simp_all)


subsubsection \<open>Equivariance for @{typ "'a fset"}\<close>

context includes fset.lifting begin
lemma in_fset_eqvt [eqvt]:
  shows "(p \<bullet> (x |\<in>| S)) = ((p \<bullet> x) |\<in>| (p \<bullet> S))"
  by transfer simp

lemma union_fset_eqvt [eqvt]:
  shows "(p \<bullet> (S |\<union>| T)) = ((p \<bullet> S) |\<union>| (p \<bullet> T))"
  by (induct S) (simp_all)

lemma inter_fset_eqvt [eqvt]:
  shows "(p \<bullet> (S |\<inter>| T)) = ((p \<bullet> S) |\<inter>| (p \<bullet> T))"
  by transfer simp

lemma subset_fset_eqvt [eqvt]:
  shows "(p \<bullet> (S |\<subseteq>| T)) = ((p \<bullet> S) |\<subseteq>| (p \<bullet> T))"
  by transfer simp

lemma map_fset_eqvt [eqvt]:
  shows "p \<bullet> (f |`| S) = (p \<bullet> f) |`| (p \<bullet> S)"
  by transfer simp
end

subsubsection \<open>Equivariance for @{typ "('a, 'b) finfun"}\<close>

lemma finfun_update_eqvt [eqvt]:
  shows "(p \<bullet> (finfun_update f a b)) = finfun_update (p \<bullet> f) (p \<bullet> a) (p \<bullet> b)"
by (transfer) (simp)

lemma finfun_const_eqvt [eqvt]:
  shows "(p \<bullet> (finfun_const b)) = finfun_const (p \<bullet> b)"
by (transfer) (simp)

lemma finfun_apply_eqvt [eqvt]:
  shows "(p \<bullet> (finfun_apply f b)) = finfun_apply (p \<bullet> f) (p \<bullet> b)"
by (transfer) (simp)


section \<open>Supp, Freshness and Supports\<close>

context pt
begin

definition
  supp :: "'a \<Rightarrow> atom set"
where
  "supp x = {a. infinite {b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x}}"

definition
  fresh :: "atom \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<sharp> _" [55, 55] 55)
where
  "a \<sharp> x \<equiv> a \<notin> supp x"

end

lemma supp_conv_fresh:
  shows "supp x = {a. \<not> a \<sharp> x}"
  unfolding fresh_def by simp

lemma swap_rel_trans:
  assumes "sort_of a = sort_of b"
  assumes "sort_of b = sort_of c"
  assumes "(a \<rightleftharpoons> c) \<bullet> x = x"
  assumes "(b \<rightleftharpoons> c) \<bullet> x = x"
  shows "(a \<rightleftharpoons> b) \<bullet> x = x"
proof (cases)
  assume "a = b \<or> c = b"
  with assms show "(a \<rightleftharpoons> b) \<bullet> x = x" by auto
next
  assume *: "\<not> (a = b \<or> c = b)"
  have "((a \<rightleftharpoons> c) + (b \<rightleftharpoons> c) + (a \<rightleftharpoons> c)) \<bullet> x = x"
    using assms by simp
  also have "(a \<rightleftharpoons> c) + (b \<rightleftharpoons> c) + (a \<rightleftharpoons> c) = (a \<rightleftharpoons> b)"
    using assms * by (simp add: swap_triple)
  finally show "(a \<rightleftharpoons> b) \<bullet> x = x" .
qed

lemma swap_fresh_fresh:
  assumes a: "a \<sharp> x"
  and     b: "b \<sharp> x"
  shows "(a \<rightleftharpoons> b) \<bullet> x = x"
proof (cases)
  assume asm: "sort_of a = sort_of b"
  have "finite {c. (a \<rightleftharpoons> c) \<bullet> x \<noteq> x}" "finite {c. (b \<rightleftharpoons> c) \<bullet> x \<noteq> x}"
    using a b unfolding fresh_def supp_def by simp_all
  then have "finite ({c. (a \<rightleftharpoons> c) \<bullet> x \<noteq> x} \<union> {c. (b \<rightleftharpoons> c) \<bullet> x \<noteq> x})" by simp
  then obtain c
    where "(a \<rightleftharpoons> c) \<bullet> x = x" "(b \<rightleftharpoons> c) \<bullet> x = x" "sort_of c = sort_of b"
    by (rule obtain_atom) (auto)
  then show "(a \<rightleftharpoons> b) \<bullet> x = x" using asm by (rule_tac swap_rel_trans) (simp_all)
next
  assume "sort_of a \<noteq> sort_of b"
  then show "(a \<rightleftharpoons> b) \<bullet> x = x" by simp
qed


subsection \<open>supp and fresh are equivariant\<close>


lemma supp_eqvt [eqvt]:
  shows "p \<bullet> (supp x) = supp (p \<bullet> x)"
  unfolding supp_def by simp

lemma fresh_eqvt [eqvt]:
  shows "p \<bullet> (a \<sharp> x) = (p \<bullet> a) \<sharp> (p \<bullet> x)"
  unfolding fresh_def by simp

lemma fresh_permute_iff:
  shows "(p \<bullet> a) \<sharp> (p \<bullet> x) \<longleftrightarrow> a \<sharp> x"
  by (simp only: fresh_eqvt[symmetric] permute_bool_def)

lemma fresh_permute_left:
  shows "a \<sharp> p \<bullet> x \<longleftrightarrow> - p \<bullet> a \<sharp> x"
proof
  assume "a \<sharp> p \<bullet> x"
  then have "- p \<bullet> a \<sharp> - p \<bullet> p \<bullet> x" by (simp only: fresh_permute_iff)
  then show "- p \<bullet> a \<sharp> x" by simp
next
  assume "- p \<bullet> a \<sharp> x"
  then have "p \<bullet> - p \<bullet> a \<sharp> p \<bullet> x" by (simp only: fresh_permute_iff)
  then show "a \<sharp> p \<bullet> x" by simp
qed


section \<open>supports\<close>

definition
  supports :: "atom set \<Rightarrow> 'a::pt \<Rightarrow> bool" (infixl "supports" 80)
where
  "S supports x \<equiv> \<forall>a b. (a \<notin> S \<and> b \<notin> S \<longrightarrow> (a \<rightleftharpoons> b) \<bullet> x = x)"

lemma supp_is_subset:
  fixes S :: "atom set"
  and   x :: "'a::pt"
  assumes a1: "S supports x"
  and     a2: "finite S"
  shows "(supp x) \<subseteq> S"
proof (rule ccontr)
  assume "\<not> (supp x \<subseteq> S)"
  then obtain a where b1: "a \<in> supp x" and b2: "a \<notin> S" by auto
  from a1 b2 have "\<forall>b. b \<notin> S \<longrightarrow> (a \<rightleftharpoons> b) \<bullet> x = x" unfolding supports_def by auto
  then have "{b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x} \<subseteq> S" by auto
  with a2 have "finite {b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x}" by (simp add: finite_subset)
  then have "a \<notin> (supp x)" unfolding supp_def by simp
  with b1 show False by simp
qed

lemma supports_finite:
  fixes S :: "atom set"
  and   x :: "'a::pt"
  assumes a1: "S supports x"
  and     a2: "finite S"
  shows "finite (supp x)"
proof -
  have "(supp x) \<subseteq> S" using a1 a2 by (rule supp_is_subset)
  then show "finite (supp x)" using a2 by (simp add: finite_subset)
qed

lemma supp_supports:
  fixes x :: "'a::pt"
  shows "(supp x) supports x"
unfolding supports_def
proof (intro strip)
  fix a b
  assume "a \<notin> (supp x) \<and> b \<notin> (supp x)"
  then have "a \<sharp> x" and "b \<sharp> x" by (simp_all add: fresh_def)
  then show "(a \<rightleftharpoons> b) \<bullet> x = x" by (simp add: swap_fresh_fresh)
qed

lemma supports_fresh:
  fixes x :: "'a::pt"
  assumes a1: "S supports x"
  and     a2: "finite S"
  and     a3: "a \<notin> S"
  shows "a \<sharp> x"
unfolding fresh_def
proof -
  have "(supp x) \<subseteq> S" using a1 a2 by (rule supp_is_subset)
  then show "a \<notin> (supp x)" using a3 by auto
qed

lemma supp_is_least_supports:
  fixes S :: "atom set"
  and   x :: "'a::pt"
  assumes  a1: "S supports x"
  and      a2: "finite S"
  and      a3: "\<And>S'. finite S' \<Longrightarrow> (S' supports x) \<Longrightarrow> S \<subseteq> S'"
  shows "(supp x) = S"
proof (rule equalityI)
  show "(supp x) \<subseteq> S" using a1 a2 by (rule supp_is_subset)
  with a2 have fin: "finite (supp x)" by (rule rev_finite_subset)
  have "(supp x) supports x" by (rule supp_supports)
  with fin a3 show "S \<subseteq> supp x" by blast
qed


lemma subsetCI:
  shows "(\<And>x. x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> False) \<Longrightarrow> A \<subseteq> B"
  by auto

lemma finite_supp_unique:
  assumes a1: "S supports x"
  assumes a2: "finite S"
  assumes a3: "\<And>a b. \<lbrakk>a \<in> S; b \<notin> S; sort_of a = sort_of b\<rbrakk> \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> x \<noteq> x"
  shows "(supp x) = S"
  using a1 a2
proof (rule supp_is_least_supports)
  fix S'
  assume "finite S'" and "S' supports x"
  show "S \<subseteq> S'"
  proof (rule subsetCI)
    fix a
    assume "a \<in> S" and "a \<notin> S'"
    have "finite (S \<union> S')"
      using \<open>finite S\<close> \<open>finite S'\<close> by simp
    then obtain b where "b \<notin> S \<union> S'" and "sort_of b = sort_of a"
      by (rule obtain_atom)
    then have "b \<notin> S" and "b \<notin> S'"  and "sort_of a = sort_of b"
      by simp_all
    then have "(a \<rightleftharpoons> b) \<bullet> x = x"
      using \<open>a \<notin> S'\<close> \<open>S' supports x\<close> by (simp add: supports_def)
    moreover have "(a \<rightleftharpoons> b) \<bullet> x \<noteq> x"
      using \<open>a \<in> S\<close> \<open>b \<notin> S\<close> \<open>sort_of a = sort_of b\<close>
      by (rule a3)
    ultimately show "False" by simp
  qed
qed

section \<open>Support w.r.t. relations\<close>

text \<open>
  This definition is used for unquotient types, where
  alpha-equivalence does not coincide with equality.
\<close>

definition
  "supp_rel R x = {a. infinite {b. \<not>(R ((a \<rightleftharpoons> b) \<bullet> x) x)}}"



section \<open>Finitely-supported types\<close>

class fs = pt +
  assumes finite_supp: "finite (supp x)"

lemma pure_supp:
  fixes x::"'a::pure"
  shows "supp x = {}"
  unfolding supp_def by (simp add: permute_pure)

lemma pure_fresh:
  fixes x::"'a::pure"
  shows "a \<sharp> x"
  unfolding fresh_def by (simp add: pure_supp)

instance pure < fs
  by standard (simp add: pure_supp)


subsection  \<open>Type @{typ atom} is finitely-supported.\<close>

lemma supp_atom:
  shows "supp a = {a}"
apply (rule finite_supp_unique)
apply (clarsimp simp add: supports_def)
apply simp
apply simp
done

lemma fresh_atom:
  shows "a \<sharp> b \<longleftrightarrow> a \<noteq> b"
  unfolding fresh_def supp_atom by simp

instance atom :: fs
  by standard (simp add: supp_atom)


section \<open>Type @{typ perm} is finitely-supported.\<close>

lemma perm_swap_eq:
  shows "(a \<rightleftharpoons> b) \<bullet> p = p \<longleftrightarrow> (p \<bullet> (a \<rightleftharpoons> b)) = (a \<rightleftharpoons> b)"
unfolding permute_perm_def
by (metis add_diff_cancel minus_perm_def)

lemma supports_perm:
  shows "{a. p \<bullet> a \<noteq> a} supports p"
  unfolding supports_def
  unfolding perm_swap_eq
  by (simp add: swap_eqvt)

lemma finite_perm_lemma:
  shows "finite {a::atom. p \<bullet> a \<noteq> a}"
  using finite_Rep_perm [of p]
  unfolding permute_atom_def .

lemma supp_perm:
  shows "supp p = {a. p \<bullet> a \<noteq> a}"
apply (rule finite_supp_unique)
apply (rule supports_perm)
apply (rule finite_perm_lemma)
apply (simp add: perm_swap_eq swap_eqvt)
apply (auto simp: perm_eq_iff swap_atom)
done

lemma fresh_perm:
  shows "a \<sharp> p \<longleftrightarrow> p \<bullet> a = a"
  unfolding fresh_def
  by (simp add: supp_perm)

lemma supp_swap:
  shows "supp (a \<rightleftharpoons> b) = (if a = b \<or> sort_of a \<noteq> sort_of b then {} else {a, b})"
  by (auto simp: supp_perm swap_atom)

lemma fresh_swap:
  shows "a \<sharp> (b \<rightleftharpoons> c) \<longleftrightarrow> (sort_of b \<noteq> sort_of c) \<or> b = c \<or> (a \<sharp> b \<and> a \<sharp> c)"
  by (simp add: fresh_def supp_swap supp_atom)

lemma fresh_zero_perm:
  shows "a \<sharp> (0::perm)"
  unfolding fresh_perm by simp

lemma supp_zero_perm:
  shows "supp (0::perm) = {}"
  unfolding supp_perm by simp

lemma fresh_plus_perm:
  fixes p q::perm
  assumes "a \<sharp> p" "a \<sharp> q"
  shows "a \<sharp> (p + q)"
  using assms
  unfolding fresh_def
  by (auto simp: supp_perm)

lemma supp_plus_perm:
  fixes p q::perm
  shows "supp (p + q) \<subseteq> supp p \<union> supp q"
  by (auto simp: supp_perm)

lemma fresh_minus_perm:
  fixes p::perm
  shows "a \<sharp> (- p) \<longleftrightarrow> a \<sharp> p"
  unfolding fresh_def
  unfolding supp_perm
  apply(simp)
  apply(metis permute_minus_cancel)
  done

lemma supp_minus_perm:
  fixes p::perm
  shows "supp (- p) = supp p"
  unfolding supp_conv_fresh
  by (simp add: fresh_minus_perm)

lemma plus_perm_eq:
  fixes p q::"perm"
  assumes asm: "supp p \<inter> supp q = {}"
  shows "p + q = q + p"
unfolding perm_eq_iff
proof
  fix a::"atom"
  show "(p + q) \<bullet> a = (q + p) \<bullet> a"
  proof -
    { assume "a \<notin> supp p" "a \<notin> supp q"
      then have "(p + q) \<bullet> a = (q + p) \<bullet> a"
        by (simp add: supp_perm)
    }
    moreover
    { assume a: "a \<in> supp p" "a \<notin> supp q"
      then have "p \<bullet> a \<in> supp p" by (simp add: supp_perm)
      then have "p \<bullet> a \<notin> supp q" using asm by auto
      with a have "(p + q) \<bullet> a = (q + p) \<bullet> a"
        by (simp add: supp_perm)
    }
    moreover
    { assume a: "a \<notin> supp p" "a \<in> supp q"
      then have "q \<bullet> a \<in> supp q" by (simp add: supp_perm)
      then have "q \<bullet> a \<notin> supp p" using asm by auto
      with a have "(p + q) \<bullet> a = (q + p) \<bullet> a"
        by (simp add: supp_perm)
    }
    ultimately show "(p + q) \<bullet> a = (q + p) \<bullet> a"
      using asm by blast
  qed
qed

lemma supp_plus_perm_eq:
  fixes p q::perm
  assumes asm: "supp p \<inter> supp q = {}"
  shows "supp (p + q) = supp p \<union> supp q"
proof -
  { fix a::"atom"
    assume "a \<in> supp p"
    then have "a \<notin> supp q" using asm by auto
    then have "a \<in> supp (p + q)" using \<open>a \<in> supp p\<close>
      by (simp add: supp_perm)
  }
  moreover
  { fix a::"atom"
    assume "a \<in> supp q"
    then have "a \<notin> supp p" using asm by auto
    then have "a \<in> supp (q + p)" using \<open>a \<in> supp q\<close>
      by (simp add: supp_perm)
    then have "a \<in> supp (p + q)" using asm plus_perm_eq
      by metis
  }
  ultimately have "supp p \<union> supp q \<subseteq> supp (p + q)"
    by blast
  then show "supp (p + q) = supp p \<union> supp q" using supp_plus_perm
    by blast
qed

lemma perm_eq_iff2:
  fixes p q :: "perm"
  shows "p = q \<longleftrightarrow> (\<forall>a::atom \<in> supp p \<union> supp q. p \<bullet> a = q \<bullet> a)"
  unfolding perm_eq_iff
  apply(auto)
  apply(case_tac "a \<sharp> p \<and> a \<sharp> q")
  apply(simp add: fresh_perm)
  apply(simp add: fresh_def)
  done


instance perm :: fs
  by standard (simp add: supp_perm finite_perm_lemma)



section \<open>Finite Support instances for other types\<close>


subsection \<open>Type @{typ "'a \<times> 'b"} is finitely-supported.\<close>

lemma supp_Pair:
  shows "supp (x, y) = supp x \<union> supp y"
  by (simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma fresh_Pair:
  shows "a \<sharp> (x, y) \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y"
  by (simp add: fresh_def supp_Pair)

lemma supp_Unit:
  shows "supp () = {}"
  by (simp add: supp_def)

lemma fresh_Unit:
  shows "a \<sharp> ()"
  by (simp add: fresh_def supp_Unit)

instance prod :: (fs, fs) fs
apply standard
apply (case_tac x)
apply (simp add: supp_Pair finite_supp)
done


subsection \<open>Type @{typ "'a + 'b"} is finitely supported\<close>

lemma supp_Inl:
  shows "supp (Inl x) = supp x"
  by (simp add: supp_def)

lemma supp_Inr:
  shows "supp (Inr x) = supp x"
  by (simp add: supp_def)

lemma fresh_Inl:
  shows "a \<sharp> Inl x \<longleftrightarrow> a \<sharp> x"
  by (simp add: fresh_def supp_Inl)

lemma fresh_Inr:
  shows "a \<sharp> Inr y \<longleftrightarrow> a \<sharp> y"
  by (simp add: fresh_def supp_Inr)

instance sum :: (fs, fs) fs
apply standard
apply (case_tac x)
apply (simp_all add: supp_Inl supp_Inr finite_supp)
done


subsection \<open>Type @{typ "'a option"} is finitely supported\<close>

lemma supp_None:
  shows "supp None = {}"
by (simp add: supp_def)

lemma supp_Some:
  shows "supp (Some x) = supp x"
  by (simp add: supp_def)

lemma fresh_None:
  shows "a \<sharp> None"
  by (simp add: fresh_def supp_None)

lemma fresh_Some:
  shows "a \<sharp> Some x \<longleftrightarrow> a \<sharp> x"
  by (simp add: fresh_def supp_Some)

instance option :: (fs) fs
apply standard
apply (induct_tac x)
apply (simp_all add: supp_None supp_Some finite_supp)
done


subsubsection \<open>Type @{typ "'a list"} is finitely supported\<close>

lemma supp_Nil:
  shows "supp [] = {}"
  by (simp add: supp_def)

lemma fresh_Nil:
  shows "a \<sharp> []"
  by (simp add: fresh_def supp_Nil)

lemma supp_Cons:
  shows "supp (x # xs) = supp x \<union> supp xs"
by (simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma fresh_Cons:
  shows "a \<sharp> (x # xs) \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> xs"
  by (simp add: fresh_def supp_Cons)

lemma supp_append:
  shows "supp (xs @ ys) = supp xs \<union> supp ys"
  by (induct xs) (auto simp: supp_Nil supp_Cons)

lemma fresh_append:
  shows "a \<sharp> (xs @ ys) \<longleftrightarrow> a \<sharp> xs \<and> a \<sharp> ys"
  by (induct xs) (simp_all add: fresh_Nil fresh_Cons)

lemma supp_rev:
  shows "supp (rev xs) = supp xs"
  by (induct xs) (auto simp: supp_append supp_Cons supp_Nil)

lemma fresh_rev:
  shows "a \<sharp> rev xs \<longleftrightarrow> a \<sharp> xs"
  by (induct xs) (auto simp: fresh_append fresh_Cons fresh_Nil)

lemma supp_removeAll:
  fixes x::"atom"
  shows "supp (removeAll x xs) = supp xs - {x}"
  by (induct xs)
     (auto simp: supp_Nil supp_Cons supp_atom)

lemma supp_of_atom_list:
  fixes as::"atom list"
  shows "supp as = set as"
by (induct as)
   (simp_all add: supp_Nil supp_Cons supp_atom)

instance list :: (fs) fs
apply standard
apply (induct_tac x)
apply (simp_all add: supp_Nil supp_Cons finite_supp)
done


section \<open>Support and Freshness for Applications\<close>

lemma fresh_conv_MOST:
  shows "a \<sharp> x \<longleftrightarrow> (MOST b. (a \<rightleftharpoons> b) \<bullet> x = x)"
  unfolding fresh_def supp_def
  unfolding MOST_iff_cofinite by simp

lemma fresh_fun_app:
  assumes "a \<sharp> f" and "a \<sharp> x"
  shows "a \<sharp> f x"
  using assms
  unfolding fresh_conv_MOST
  unfolding permute_fun_app_eq
  by (elim MOST_rev_mp) (simp)

lemma supp_fun_app:
  shows "supp (f x) \<subseteq> (supp f) \<union> (supp x)"
  using fresh_fun_app
  unfolding fresh_def
  by auto


subsection \<open>Equivariance Predicate \<open>eqvt\<close> and \<open>eqvt_at\<close>\<close>

definition
  "eqvt f \<equiv> \<forall>p. p \<bullet> f = f"

lemma eqvt_boolI:
  fixes f::"bool"
  shows "eqvt f"
unfolding eqvt_def by (simp add: permute_bool_def)


text \<open>equivariance of a function at a given argument\<close>

definition
 "eqvt_at f x \<equiv> \<forall>p. p \<bullet> (f x) = f (p \<bullet> x)"

lemma eqvtI:
  shows "(\<And>p. p \<bullet> f \<equiv> f) \<Longrightarrow> eqvt f"
unfolding eqvt_def
by simp

lemma eqvt_at_perm:
  assumes "eqvt_at f x"
  shows "eqvt_at f (q \<bullet> x)"
proof -
  { fix p::"perm"
    have "p \<bullet> (f (q \<bullet> x)) = p \<bullet> q \<bullet> (f x)"
      using assms by (simp add: eqvt_at_def)
    also have "\<dots> = (p + q) \<bullet> (f x)" by simp
    also have "\<dots> = f ((p + q) \<bullet> x)"
      using assms by (simp only: eqvt_at_def)
    finally have "p \<bullet> (f (q \<bullet> x)) = f (p \<bullet> q \<bullet> x)" by simp }
  then show "eqvt_at f (q \<bullet> x)" unfolding eqvt_at_def
    by simp
qed

lemma supp_fun_eqvt:
  assumes a: "eqvt f"
  shows "supp f = {}"
  using a
  unfolding eqvt_def
  unfolding supp_def
  by simp

lemma fresh_fun_eqvt:
  assumes a: "eqvt f"
  shows "a \<sharp> f"
  using a
  unfolding fresh_def
  by (simp add: supp_fun_eqvt)

lemma fresh_fun_eqvt_app:
  assumes a: "eqvt f"
  shows "a \<sharp> x \<Longrightarrow> a \<sharp> f x"
proof -
  from a have "supp f = {}" by (simp add: supp_fun_eqvt)
  then show "a \<sharp> x \<Longrightarrow> a \<sharp> f x"
    unfolding fresh_def
    using supp_fun_app by auto
qed

lemma supp_fun_app_eqvt:
  assumes a: "eqvt f"
  shows "supp (f x) \<subseteq> supp x"
  using fresh_fun_eqvt_app[OF a]
  unfolding fresh_def
  by auto

lemma supp_eqvt_at:
  assumes asm: "eqvt_at f x"
  and     fin: "finite (supp x)"
  shows "supp (f x) \<subseteq> supp x"
apply(rule supp_is_subset)
unfolding supports_def
unfolding fresh_def[symmetric]
using asm
apply(simp add: eqvt_at_def)
apply(simp add: swap_fresh_fresh)
apply(rule fin)
done

lemma finite_supp_eqvt_at:
  assumes asm: "eqvt_at f x"
  and     fin: "finite (supp x)"
  shows "finite (supp (f x))"
apply(rule finite_subset)
apply(rule supp_eqvt_at[OF asm fin])
apply(rule fin)
done

lemma fresh_eqvt_at:
  assumes asm: "eqvt_at f x"
  and     fin: "finite (supp x)"
  and     fresh: "a \<sharp> x"
  shows "a \<sharp> f x"
using fresh
unfolding fresh_def
using supp_eqvt_at[OF asm fin]
by auto

text \<open>for handling of freshness of functions\<close>

simproc_setup fresh_fun_simproc ("a \<sharp> (f::'a::pt \<Rightarrow>'b::pt)") = \<open>fn _ => fn ctxt => fn ctrm =>
  let
    val _ $ _ $ f = Thm.term_of ctrm
  in
    case (Term.add_frees f [], Term.add_vars f []) of
      ([], []) => SOME(@{thm fresh_fun_eqvt[simplified eqvt_def, THEN Eq_TrueI]})
    | (x::_, []) =>
      let
        val argx = Free x
        val absf = absfree x f
        val cty_inst =
          [SOME (Thm.ctyp_of ctxt (fastype_of argx)), SOME (Thm.ctyp_of ctxt (fastype_of f))]
        val ctrm_inst = [NONE, SOME (Thm.cterm_of ctxt absf), SOME (Thm.cterm_of ctxt argx)]
        val thm = Thm.instantiate' cty_inst ctrm_inst @{thm fresh_fun_app}
      in
        SOME(thm RS @{thm Eq_TrueI})
      end
    | (_, _) => NONE
  end
\<close>

subsection \<open>helper functions for \<open>nominal_functions\<close>\<close>

lemma THE_defaultI2:
  assumes "\<exists>!x. P x" "\<And>x. P x \<Longrightarrow> Q x"
  shows "Q (THE_default d P)"
by (iprover intro: assms THE_defaultI')

lemma the_default_eqvt:
  assumes unique: "\<exists>!x. P x"
  shows "(p \<bullet> (THE_default d P)) = (THE_default (p \<bullet> d) (p \<bullet> P))"
  apply(rule THE_default1_equality [symmetric])
  apply(rule_tac p="-p" in permute_boolE)
  apply(simp add: ex1_eqvt)
  apply(rule unique)
  apply(rule_tac p="-p" in permute_boolE)
  apply(rule subst[OF permute_fun_app_eq])
  apply(simp)
  apply(rule THE_defaultI'[OF unique])
  done

lemma fundef_ex1_eqvt:
  fixes x::"'a::pt"
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (G x))"
  assumes eqvt: "eqvt G"
  assumes ex1: "\<exists>!y. G x y"
  shows "(p \<bullet> (f x)) = f (p \<bullet> x)"
  apply(simp only: f_def)
  apply(subst the_default_eqvt)
  apply(rule ex1)
  apply(rule THE_default1_equality [symmetric])
  apply(rule_tac p="-p" in permute_boolE)
  apply(perm_simp add: permute_minus_cancel)
  using eqvt[simplified eqvt_def]
  apply(simp)
  apply(rule ex1)
  apply(rule THE_defaultI2)
  apply(rule_tac p="-p" in permute_boolE)
  apply(perm_simp add: permute_minus_cancel)
  apply(rule ex1)
  apply(perm_simp)
  using eqvt[simplified eqvt_def]
  apply(simp)
  done

lemma fundef_ex1_eqvt_at:
  fixes x::"'a::pt"
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (G x))"
  assumes eqvt: "eqvt G"
  assumes ex1: "\<exists>!y. G x y"
  shows "eqvt_at f x"
  unfolding eqvt_at_def
  using assms
  by (auto intro: fundef_ex1_eqvt)

lemma fundef_ex1_prop:
  fixes x::"'a::pt"
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (G x))"
  assumes P_all: "\<And>x y. G x y \<Longrightarrow> P x y"
  assumes ex1: "\<exists>!y. G x y"
  shows "P x (f x)"
  unfolding f_def
  using ex1
  apply(erule_tac ex1E)
  apply(rule THE_defaultI2)
  apply(blast)
  apply(rule P_all)
  apply(assumption)
  done


section \<open>Support of Finite Sets of Finitely Supported Elements\<close>

text \<open>support and freshness for atom sets\<close>

lemma supp_finite_atom_set:
  fixes S::"atom set"
  assumes "finite S"
  shows "supp S = S"
  apply(rule finite_supp_unique)
  apply(simp add: supports_def)
  apply(simp add: swap_set_not_in)
  apply(rule assms)
  apply(simp add: swap_set_in)
done

lemma supp_cofinite_atom_set:
  fixes S::"atom set"
  assumes "finite (UNIV - S)"
  shows "supp S = (UNIV - S)"
  apply(rule finite_supp_unique)
  apply(simp add: supports_def)
  apply(simp add: swap_set_both_in)
  apply(rule assms)
  apply(subst swap_commute)
  apply(simp add: swap_set_in)
done

lemma fresh_finite_atom_set:
  fixes S::"atom set"
  assumes "finite S"
  shows "a \<sharp> S \<longleftrightarrow> a \<notin> S"
  unfolding fresh_def
  by (simp add: supp_finite_atom_set[OF assms])

lemma fresh_minus_atom_set:
  fixes S::"atom set"
  assumes "finite S"
  shows "a \<sharp> S - T \<longleftrightarrow> (a \<notin> T \<longrightarrow> a \<sharp> S)"
  unfolding fresh_def
  by (auto simp: supp_finite_atom_set assms)

lemma Union_supports_set:
  shows "(\<Union>x \<in> S. supp x) supports S"
proof -
  { fix a b
    have "\<forall>x \<in> S. (a \<rightleftharpoons> b) \<bullet> x = x \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> S = S"
      unfolding permute_set_def by force
  }
  then show "(\<Union>x \<in> S. supp x) supports S"
    unfolding supports_def
    by (simp add: fresh_def[symmetric] swap_fresh_fresh)
qed

lemma Union_of_finite_supp_sets:
  fixes S::"('a::fs set)"
  assumes fin: "finite S"
  shows "finite (\<Union>x\<in>S. supp x)"
  using fin by (induct) (auto simp: finite_supp)

lemma Union_included_in_supp:
  fixes S::"('a::fs set)"
  assumes fin: "finite S"
  shows "(\<Union>x\<in>S. supp x) \<subseteq> supp S"
proof -
  have eqvt: "eqvt (\<lambda>S. \<Union>x \<in> S. supp x)"
    unfolding eqvt_def by simp
  have "(\<Union>x\<in>S. supp x) = supp (\<Union>x\<in>S. supp x)"
    by (rule supp_finite_atom_set[symmetric]) (rule Union_of_finite_supp_sets[OF fin])
  also have "\<dots> \<subseteq> supp S" using eqvt
    by (rule supp_fun_app_eqvt)
  finally show "(\<Union>x\<in>S. supp x) \<subseteq> supp S" .
qed

lemma supp_of_finite_sets:
  fixes S::"('a::fs set)"
  assumes fin: "finite S"
  shows "(supp S) = (\<Union>x\<in>S. supp x)"
apply(rule subset_antisym)
apply(rule supp_is_subset)
apply(rule Union_supports_set)
apply(rule Union_of_finite_supp_sets[OF fin])
apply(rule Union_included_in_supp[OF fin])
done

lemma finite_sets_supp:
  fixes S::"('a::fs set)"
  assumes "finite S"
  shows "finite (supp S)"
using assms
by (simp only: supp_of_finite_sets Union_of_finite_supp_sets)

lemma supp_of_finite_union:
  fixes S T::"('a::fs) set"
  assumes fin1: "finite S"
  and     fin2: "finite T"
  shows "supp (S \<union> T) = supp S \<union> supp T"
  using fin1 fin2
  by (simp add: supp_of_finite_sets)

lemma fresh_finite_union:
  fixes S T::"('a::fs) set"
  assumes fin1: "finite S"
  and     fin2: "finite T"
  shows "a \<sharp> (S \<union> T) \<longleftrightarrow> a \<sharp> S \<and> a \<sharp> T"
  unfolding fresh_def
  by (simp add: supp_of_finite_union[OF fin1 fin2])

lemma supp_of_finite_insert:
  fixes S::"('a::fs) set"
  assumes fin:  "finite S"
  shows "supp (insert x S) = supp x \<union> supp S"
  using fin
  by (simp add: supp_of_finite_sets)

lemma fresh_finite_insert:
  fixes S::"('a::fs) set"
  assumes fin:  "finite S"
  shows "a \<sharp> (insert x S) \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> S"
  using fin unfolding fresh_def
  by (simp add: supp_of_finite_insert)

lemma supp_set_empty:
  shows "supp {} = {}"
  unfolding supp_def
  by (simp add: empty_eqvt)

lemma fresh_set_empty:
  shows "a \<sharp> {}"
  by (simp add: fresh_def supp_set_empty)

lemma supp_set:
  fixes xs :: "('a::fs) list"
  shows "supp (set xs) = supp xs"
apply(induct xs)
apply(simp add: supp_set_empty supp_Nil)
apply(simp add: supp_Cons supp_of_finite_insert)
done

lemma fresh_set:
  fixes xs :: "('a::fs) list"
  shows "a \<sharp> (set xs) \<longleftrightarrow> a \<sharp> xs"
unfolding fresh_def
by (simp add: supp_set)


subsection \<open>Type @{typ "'a multiset"} is finitely supported\<close>

lemma set_mset_eqvt [eqvt]:
  shows "p \<bullet> (set_mset M) = set_mset (p \<bullet> M)"
by (induct M) (simp_all add: insert_eqvt empty_eqvt)

lemma supp_set_mset:
  shows "supp (set_mset M) \<subseteq> supp M"
  apply (rule supp_fun_app_eqvt)
  unfolding eqvt_def
  apply(perm_simp)
  apply(simp)
  done

lemma Union_finite_multiset:
  fixes M::"'a::fs multiset"
  shows "finite (\<Union>{supp x | x. x \<in># M})"
proof -
  have "finite (\<Union>(supp ` {x. x \<in># M}))"
    by (induct M) (simp_all add: Collect_imp_eq Collect_neg_eq finite_supp)
  then show "finite (\<Union>{supp x | x. x \<in># M})"
    by (simp only: image_Collect)
qed

lemma Union_supports_multiset:
  shows "\<Union>{supp x | x. x \<in># M} supports M"
proof -
  have sw: "\<And>a b. ((\<And>x. x \<in># M \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> x = x) \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> M = M)"
    unfolding permute_multiset_def by (induct M) simp_all
  have "(\<Union>x\<in>set_mset M. supp x) supports M"
    by (auto intro!: sw swap_fresh_fresh simp add: fresh_def supports_def)
  also have "(\<Union>x\<in>set_mset M. supp x) = (\<Union>{supp x | x. x \<in># M})"
    by auto
  finally show "(\<Union>{supp x | x. x \<in># M}) supports M" .
qed

lemma Union_included_multiset:
  fixes M::"('a::fs multiset)"
  shows "(\<Union>{supp x | x. x \<in># M}) \<subseteq> supp M"
proof -
  have "(\<Union>{supp x | x. x \<in># M}) = (\<Union>x \<in> set_mset M. supp x)" by auto
  also have "... = supp (set_mset M)"
    by (simp add: supp_of_finite_sets)
  also have " ... \<subseteq> supp M" by (rule supp_set_mset)
  finally show "(\<Union>{supp x | x. x \<in># M}) \<subseteq> supp M" .
qed

lemma supp_of_multisets:
  fixes M::"('a::fs multiset)"
  shows "(supp M) = (\<Union>{supp x | x. x \<in># M})"
apply(rule subset_antisym)
apply(rule supp_is_subset)
apply(rule Union_supports_multiset)
apply(rule Union_finite_multiset)
apply(rule Union_included_multiset)
done

lemma multisets_supp_finite:
  fixes M::"('a::fs multiset)"
  shows "finite (supp M)"
by (simp only: supp_of_multisets Union_finite_multiset)

lemma supp_of_multiset_union:
  fixes M N::"('a::fs) multiset"
  shows "supp (M + N) = supp M \<union> supp N"
  by (auto simp: supp_of_multisets)

lemma supp_empty_mset [simp]:
  shows "supp {#} = {}"
  unfolding supp_def
  by simp

instance multiset :: (fs) fs
  by standard (rule multisets_supp_finite)

subsection \<open>Type @{typ "'a fset"} is finitely supported\<close>

lemma supp_fset [simp]:
  shows "supp (fset S) = supp S"
  unfolding supp_def
  by (simp add: fset_eqvt fset_cong)

lemma supp_empty_fset [simp]:
  shows "supp {||} = {}"
  unfolding supp_def
  by simp

lemma fresh_empty_fset:
  shows "a \<sharp> {||}"
unfolding fresh_def
by (simp)

lemma supp_finsert [simp]:
  fixes x::"'a::fs"
  and   S::"'a fset"
  shows "supp (finsert x S) = supp x \<union> supp S"
  apply(subst supp_fset[symmetric])
  apply(simp add: supp_of_finite_insert)
  done

lemma fresh_finsert:
  fixes x::"'a::fs"
  and   S::"'a fset"
  shows "a \<sharp> finsert x S \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> S"
  unfolding fresh_def
  by simp

lemma fset_finite_supp:
  fixes S::"('a::fs) fset"
  shows "finite (supp S)"
  by (induct S) (simp_all add: finite_supp)

lemma supp_union_fset:
  fixes S T::"'a::fs fset"
  shows "supp (S |\<union>| T) = supp S \<union> supp T"
by (induct S) (auto)

lemma fresh_union_fset:
  fixes S T::"'a::fs fset"
  shows "a \<sharp> S |\<union>| T \<longleftrightarrow> a \<sharp> S \<and> a \<sharp> T"
unfolding fresh_def
by (simp add: supp_union_fset)

instance fset :: (fs) fs
  by standard (rule fset_finite_supp)


subsection \<open>Type @{typ "('a, 'b) finfun"} is finitely supported\<close>

lemma fresh_finfun_const:
  shows "a \<sharp> (finfun_const b) \<longleftrightarrow> a \<sharp> b"
  by (simp add: fresh_def supp_def)

lemma fresh_finfun_update:
  shows "\<lbrakk>a \<sharp> f; a \<sharp> x; a \<sharp> y\<rbrakk> \<Longrightarrow> a \<sharp> finfun_update f x y"
  unfolding fresh_conv_MOST
  unfolding finfun_update_eqvt
  by (elim MOST_rev_mp) (simp)

lemma supp_finfun_const:
  shows "supp (finfun_const b) = supp(b)"
  by (simp add: supp_def)

lemma supp_finfun_update:
  shows "supp (finfun_update f x y) \<subseteq> supp(f, x, y)"
using fresh_finfun_update
by (auto simp: fresh_def supp_Pair)

instance finfun :: (fs, fs) fs
  apply standard
  apply(induct_tac x rule: finfun_weak_induct)
  apply(simp add: supp_finfun_const finite_supp)
  apply(rule finite_subset)
  apply(rule supp_finfun_update)
  apply(simp add: supp_Pair finite_supp)
  done


section \<open>Freshness and Fresh-Star\<close>

lemma fresh_Unit_elim:
  shows "(a \<sharp> () \<Longrightarrow> PROP C) \<equiv> PROP C"
  by (simp add: fresh_Unit)

lemma fresh_Pair_elim:
  shows "(a \<sharp> (x, y) \<Longrightarrow> PROP C) \<equiv> (a \<sharp> x \<Longrightarrow> a \<sharp> y \<Longrightarrow> PROP C)"
  by rule (simp_all add: fresh_Pair)

(* this rule needs to be added before the fresh_prodD is *)
(* added to the simplifier with mksimps                  *)
lemma [simp]:
  shows "a \<sharp> x1 \<Longrightarrow> a \<sharp> x2 \<Longrightarrow> a \<sharp> (x1, x2)"
  by (simp add: fresh_Pair)

lemma fresh_PairD:
  shows "a \<sharp> (x, y) \<Longrightarrow> a \<sharp> x"
  and   "a \<sharp> (x, y) \<Longrightarrow> a \<sharp> y"
  by (simp_all add: fresh_Pair)

declaration \<open>fn _ =>
let
  val mksimps_pairs = (@{const_name Nominal2_Base.fresh}, @{thms fresh_PairD}) :: mksimps_pairs
in
  Simplifier.map_ss (fn ss => Simplifier.set_mksimps (mksimps mksimps_pairs) ss)
end
\<close>


text \<open>The fresh-star generalisation of fresh is used in strong
  induction principles.\<close>

definition
  fresh_star :: "atom set \<Rightarrow> 'a::pt \<Rightarrow> bool" ("_ \<sharp>* _" [80,80] 80)
where
  "as \<sharp>* x \<equiv> \<forall>a \<in> as. a \<sharp> x"

lemma fresh_star_supp_conv:
  shows "supp x \<sharp>* y \<Longrightarrow> supp y \<sharp>* x"
by (auto simp: fresh_star_def fresh_def)

lemma fresh_star_perm_set_conv:
  fixes p::"perm"
  assumes fresh: "as \<sharp>* p"
  and     fin: "finite as"
  shows "supp p \<sharp>* as"
apply(rule fresh_star_supp_conv)
apply(simp add: supp_finite_atom_set fin fresh)
done

lemma fresh_star_atom_set_conv:
  assumes fresh: "as \<sharp>* bs"
  and     fin: "finite as" "finite bs"
  shows "bs \<sharp>* as"
using fresh
unfolding fresh_star_def fresh_def
by (auto simp: supp_finite_atom_set fin)

lemma atom_fresh_star_disjoint:
  assumes fin: "finite bs"
  shows "as \<sharp>* bs \<longleftrightarrow> (as \<inter> bs = {})"

unfolding fresh_star_def fresh_def
by (auto simp: supp_finite_atom_set fin)


lemma fresh_star_Pair:
  shows "as \<sharp>* (x, y) = (as \<sharp>* x \<and> as \<sharp>* y)"
  by (auto simp: fresh_star_def fresh_Pair)

lemma fresh_star_list:
  shows "as \<sharp>* (xs @ ys) \<longleftrightarrow> as \<sharp>* xs \<and> as \<sharp>* ys"
  and   "as \<sharp>* (x # xs) \<longleftrightarrow> as \<sharp>* x \<and> as \<sharp>* xs"
  and   "as \<sharp>* []"
by (auto simp: fresh_star_def fresh_Nil fresh_Cons fresh_append)

lemma fresh_star_set:
  fixes xs::"('a::fs) list"
  shows "as \<sharp>* set xs \<longleftrightarrow> as \<sharp>* xs"
unfolding fresh_star_def
by (simp add: fresh_set)

lemma fresh_star_singleton:
  fixes a::"atom"
  shows "as \<sharp>* {a} \<longleftrightarrow> as \<sharp>* a"
  by (simp add: fresh_star_def fresh_finite_insert fresh_set_empty)

lemma fresh_star_fset:
  fixes xs::"('a::fs) list"
  shows "as \<sharp>* fset S \<longleftrightarrow> as \<sharp>* S"
by (simp add: fresh_star_def fresh_def)

lemma fresh_star_Un:
  shows "(as \<union> bs) \<sharp>* x = (as \<sharp>* x \<and> bs \<sharp>* x)"
  by (auto simp: fresh_star_def)

lemma fresh_star_insert:
  shows "(insert a as) \<sharp>* x = (a \<sharp> x \<and> as \<sharp>* x)"
  by (auto simp: fresh_star_def)

lemma fresh_star_Un_elim:
  "((as \<union> bs) \<sharp>* x \<Longrightarrow> PROP C) \<equiv> (as \<sharp>* x \<Longrightarrow> bs \<sharp>* x \<Longrightarrow> PROP C)"
  unfolding fresh_star_def
  apply(rule)
  apply(erule meta_mp)
  apply(auto)
  done

lemma fresh_star_insert_elim:
  "(insert a as \<sharp>* x \<Longrightarrow> PROP C) \<equiv> (a \<sharp> x \<Longrightarrow> as \<sharp>* x \<Longrightarrow> PROP C)"
  unfolding fresh_star_def
  by rule (simp_all add: fresh_star_def)

lemma fresh_star_empty_elim:
  "({} \<sharp>* x \<Longrightarrow> PROP C) \<equiv> PROP C"
  by (simp add: fresh_star_def)

lemma fresh_star_Unit_elim:
  shows "(a \<sharp>* () \<Longrightarrow> PROP C) \<equiv> PROP C"
  by (simp add: fresh_star_def fresh_Unit)

lemma fresh_star_Pair_elim:
  shows "(a \<sharp>* (x, y) \<Longrightarrow> PROP C) \<equiv> (a \<sharp>* x \<Longrightarrow> a \<sharp>* y \<Longrightarrow> PROP C)"
  by (rule, simp_all add: fresh_star_Pair)

lemma fresh_star_zero:
  shows "as \<sharp>* (0::perm)"
  unfolding fresh_star_def
  by (simp add: fresh_zero_perm)

lemma fresh_star_plus:
  fixes p q::perm
  shows "\<lbrakk>a \<sharp>* p;  a \<sharp>* q\<rbrakk> \<Longrightarrow> a \<sharp>* (p + q)"
  unfolding fresh_star_def
  by (simp add: fresh_plus_perm)

lemma fresh_star_permute_iff:
  shows "(p \<bullet> a) \<sharp>* (p \<bullet> x) \<longleftrightarrow> a \<sharp>* x"
  unfolding fresh_star_def
  by (metis mem_permute_iff permute_minus_cancel(1) fresh_permute_iff)

lemma fresh_star_eqvt [eqvt]:
  shows "p \<bullet> (as \<sharp>* x) \<longleftrightarrow> (p \<bullet> as) \<sharp>* (p \<bullet> x)"
unfolding fresh_star_def by simp


section \<open>Induction principle for permutations\<close>

lemma smaller_supp:
  assumes a: "a \<in> supp p"
  shows "supp ((p \<bullet> a \<rightleftharpoons> a) + p) \<subset> supp p"
proof -
  have "supp ((p \<bullet> a \<rightleftharpoons> a) + p) \<subseteq> supp p"
    unfolding supp_perm by (auto simp: swap_atom)
  moreover
  have "a \<notin> supp ((p \<bullet> a \<rightleftharpoons> a) + p)" by (simp add: supp_perm)
  then have "supp ((p \<bullet> a \<rightleftharpoons> a) + p) \<noteq> supp p" using a by auto
  ultimately
  show "supp ((p \<bullet> a \<rightleftharpoons> a) + p) \<subset> supp p" by auto
qed


lemma perm_struct_induct[consumes 1, case_names zero swap]:
  assumes S: "supp p \<subseteq> S"
  and zero: "P 0"
  and swap: "\<And>p a b. \<lbrakk>P p; supp p \<subseteq> S; a \<in> S; b \<in> S; a \<noteq> b; sort_of a = sort_of b\<rbrakk> \<Longrightarrow> P ((a \<rightleftharpoons> b) + p)"
  shows "P p"
proof -
  have "finite (supp p)" by (simp add: finite_supp)
  then show "P p" using S
  proof(induct A\<equiv>"supp p" arbitrary: p rule: finite_psubset_induct)
    case (psubset p)
    then have ih: "\<And>q. supp q \<subset> supp p \<Longrightarrow> P q" by auto
    have as: "supp p \<subseteq> S" by fact
    { assume "supp p = {}"
      then have "p = 0" by (simp add: supp_perm perm_eq_iff)
      then have "P p" using zero by simp
    }
    moreover
    { assume "supp p \<noteq> {}"
      then obtain a where a0: "a \<in> supp p" by blast
      then have a1: "p \<bullet> a \<in> S" "a \<in> S" "sort_of (p \<bullet> a) = sort_of a" "p \<bullet> a \<noteq> a"
        using as by (auto simp: supp_atom supp_perm swap_atom)
      let ?q = "(p \<bullet> a \<rightleftharpoons> a) + p"
      have a2: "supp ?q \<subset> supp p" using a0 smaller_supp by simp
      then have "P ?q" using ih by simp
      moreover
      have "supp ?q \<subseteq> S" using as a2 by simp
      ultimately  have "P ((p \<bullet> a \<rightleftharpoons> a) + ?q)" using as a1 swap by simp
      moreover
      have "p = (p \<bullet> a \<rightleftharpoons> a) + ?q" by (simp add: perm_eq_iff)
      ultimately have "P p" by simp
    }
    ultimately show "P p" by blast
  qed
qed

lemma perm_simple_struct_induct[case_names zero swap]:
  assumes zero: "P 0"
  and     swap: "\<And>p a b. \<lbrakk>P p; a \<noteq> b; sort_of a = sort_of b\<rbrakk> \<Longrightarrow> P ((a \<rightleftharpoons> b) + p)"
  shows "P p"
by (rule_tac S="supp p" in perm_struct_induct)
   (auto intro: zero swap)

lemma perm_struct_induct2[consumes 1, case_names zero swap plus]:
  assumes S: "supp p \<subseteq> S"
  assumes zero: "P 0"
  assumes swap: "\<And>a b. \<lbrakk>sort_of a = sort_of b; a \<noteq> b; a \<in> S; b \<in> S\<rbrakk> \<Longrightarrow> P (a \<rightleftharpoons> b)"
  assumes plus: "\<And>p1 p2. \<lbrakk>P p1; P p2; supp p1 \<subseteq> S; supp p2 \<subseteq> S\<rbrakk> \<Longrightarrow> P (p1 + p2)"
  shows "P p"
using S
by (induct p rule: perm_struct_induct)
   (auto intro: zero plus swap simp add: supp_swap)

lemma perm_simple_struct_induct2[case_names zero swap plus]:
  assumes zero: "P 0"
  assumes swap: "\<And>a b. \<lbrakk>sort_of a = sort_of b; a \<noteq> b\<rbrakk> \<Longrightarrow> P (a \<rightleftharpoons> b)"
  assumes plus: "\<And>p1 p2. \<lbrakk>P p1; P p2\<rbrakk> \<Longrightarrow> P (p1 + p2)"
  shows "P p"
by (rule_tac S="supp p" in perm_struct_induct2)
   (auto intro: zero swap plus)

lemma supp_perm_singleton:
  fixes p::"perm"
  shows "supp p \<subseteq> {b} \<longleftrightarrow> p = 0"
proof -
  { assume "supp p \<subseteq> {b}"
    then have "p = 0"
      by (induct p rule: perm_struct_induct) (simp_all)
  }
  then show "supp p \<subseteq> {b} \<longleftrightarrow> p = 0" by (auto simp: supp_zero_perm)
qed

lemma supp_perm_pair:
  fixes p::"perm"
  shows "supp p \<subseteq> {a, b} \<longleftrightarrow> p = 0 \<or> p = (b \<rightleftharpoons> a)"
proof -
  { assume "supp p \<subseteq> {a, b}"
    then have "p = 0 \<or> p = (b \<rightleftharpoons> a)"
      apply (induct p rule: perm_struct_induct)
      apply (auto simp: swap_cancel supp_zero_perm supp_swap)
      apply (simp add: swap_commute)
      done
  }
  then show "supp p \<subseteq> {a, b} \<longleftrightarrow> p = 0 \<or> p = (b \<rightleftharpoons> a)"
    by (auto simp: supp_zero_perm supp_swap split: if_splits)
qed

lemma supp_perm_eq:
  assumes "(supp x) \<sharp>* p"
  shows "p \<bullet> x = x"
proof -
  from assms have "supp p \<subseteq> {a. a \<sharp> x}"
    unfolding supp_perm fresh_star_def fresh_def by auto
  then show "p \<bullet> x = x"
  proof (induct p rule: perm_struct_induct)
    case zero
    show "0 \<bullet> x = x" by simp
  next
    case (swap p a b)
    then have "a \<sharp> x" "b \<sharp> x" "p \<bullet> x = x" by simp_all
    then show "((a \<rightleftharpoons> b) + p) \<bullet> x = x" by (simp add: swap_fresh_fresh)
  qed
qed

text \<open>same lemma as above, but proved with a different induction principle\<close>
lemma supp_perm_eq_test:
  assumes "(supp x) \<sharp>* p"
  shows "p \<bullet> x = x"
proof -
  from assms have "supp p \<subseteq> {a. a \<sharp> x}"
    unfolding supp_perm fresh_star_def fresh_def by auto
  then show "p \<bullet> x = x"
  proof (induct p rule: perm_struct_induct2)
    case zero
    show "0 \<bullet> x = x" by simp
  next
    case (swap a b)
    then have "a \<sharp> x" "b \<sharp> x" by simp_all
    then show "(a \<rightleftharpoons> b) \<bullet> x = x" by (simp add: swap_fresh_fresh)
  next
    case (plus p1 p2)
    have "p1 \<bullet> x = x" "p2 \<bullet> x = x" by fact+
    then show "(p1 + p2) \<bullet> x = x" by simp
  qed
qed

lemma perm_supp_eq:
  assumes a: "(supp p) \<sharp>* x"
  shows "p \<bullet> x = x"
proof -
  from assms have "supp p \<subseteq> {a. a \<sharp> x}"
    unfolding supp_perm fresh_star_def fresh_def by auto
  then show "p \<bullet> x = x"
  proof (induct p rule: perm_struct_induct2)
    case zero
    show "0 \<bullet> x = x" by simp
  next
    case (swap a b)
    then have "a \<sharp> x" "b \<sharp> x" by simp_all
    then show "(a \<rightleftharpoons> b) \<bullet> x = x" by (simp add: swap_fresh_fresh)
  next
    case (plus p1 p2)
    have "p1 \<bullet> x = x" "p2 \<bullet> x = x" by fact+
    then show "(p1 + p2) \<bullet> x = x" by simp
  qed
qed

lemma supp_perm_perm_eq:
  assumes a: "\<forall>a \<in> supp x. p \<bullet> a = q \<bullet> a"
  shows "p \<bullet> x = q \<bullet> x"
proof -
  from a have "\<forall>a \<in> supp x. (-q + p) \<bullet> a = a" by simp
  then have "\<forall>a \<in> supp x. a \<notin> supp (-q + p)"
    unfolding supp_perm by simp
  then have "supp x \<sharp>* (-q + p)"
    unfolding fresh_star_def fresh_def by simp
  then have "(-q + p) \<bullet> x = x" by (simp only: supp_perm_eq)
  then show "p \<bullet> x = q \<bullet> x"
    by (metis permute_minus_cancel permute_plus)
qed

text \<open>disagreement set\<close>

definition
  dset :: "perm \<Rightarrow> perm \<Rightarrow> atom set"
where
  "dset p q = {a::atom. p \<bullet> a \<noteq> q \<bullet> a}"

lemma ds_fresh:
  assumes "dset p q \<sharp>* x"
  shows "p \<bullet> x = q \<bullet> x"
using assms
unfolding dset_def fresh_star_def fresh_def
by (auto intro: supp_perm_perm_eq)

lemma atom_set_perm_eq:
  assumes a: "as \<sharp>* p"
  shows "p \<bullet> as = as"
proof -
  from a have "supp p \<subseteq> {a. a \<notin> as}"
    unfolding supp_perm fresh_star_def fresh_def by auto
  then show "p \<bullet> as = as"
  proof (induct p rule: perm_struct_induct)
    case zero
    show "0 \<bullet> as = as" by simp
  next
    case (swap p a b)
    then have "a \<notin> as" "b \<notin> as" "p \<bullet> as = as" by simp_all
    then show "((a \<rightleftharpoons> b) + p) \<bullet> as = as" by (simp add: swap_set_not_in)
  qed
qed

section \<open>Avoiding of atom sets\<close>

text \<open>
  For every set of atoms, there is another set of atoms
  avoiding a finitely supported c and there is a permutation
  which 'translates' between both sets.
\<close>

lemma at_set_avoiding_aux:
  fixes Xs::"atom set"
  and   As::"atom set"
  assumes b: "Xs \<subseteq> As"
  and     c: "finite As"
  shows "\<exists>p. (p \<bullet> Xs) \<inter> As = {} \<and> (supp p) = (Xs \<union> (p \<bullet> Xs))"
proof -
  from b c have "finite Xs" by (rule finite_subset)
  then show ?thesis using b
  proof (induct rule: finite_subset_induct)
    case empty
    have "0 \<bullet> {} \<inter> As = {}" by simp
    moreover
    have "supp (0::perm) = {} \<union> 0 \<bullet> {}" by (simp add: supp_zero_perm)
    ultimately show ?case by blast
  next
    case (insert x Xs)
    then obtain p where
      p1: "(p \<bullet> Xs) \<inter> As = {}" and
      p2: "supp p = (Xs \<union> (p \<bullet> Xs))" by blast
    from \<open>x \<in> As\<close> p1 have "x \<notin> p \<bullet> Xs" by fast
    with \<open>x \<notin> Xs\<close> p2 have "x \<notin> supp p" by fast
    hence px: "p \<bullet> x = x" unfolding supp_perm by simp
    have "finite (As \<union> p \<bullet> Xs \<union> supp p)"
      using \<open>finite As\<close> \<open>finite Xs\<close>
      by (simp add: permute_set_eq_image finite_supp)
    then obtain y where "y \<notin> (As \<union> p \<bullet> Xs \<union> supp p)" "sort_of y = sort_of x"
      by (rule obtain_atom)
    hence y: "y \<notin> As" "y \<notin> p \<bullet> Xs" "y \<notin> supp p" "sort_of y = sort_of x"
      by simp_all
    hence py: "p \<bullet> y = y" "x \<noteq> y" using \<open>x \<in> As\<close>
      by (auto simp: supp_perm)
    let ?q = "(x \<rightleftharpoons> y) + p"
    have q: "?q \<bullet> insert x Xs = insert y (p \<bullet> Xs)"
      unfolding insert_eqvt
      using \<open>p \<bullet> x = x\<close> \<open>sort_of y = sort_of x\<close>
      using \<open>x \<notin> p \<bullet> Xs\<close> \<open>y \<notin> p \<bullet> Xs\<close>
      by (simp add: swap_atom swap_set_not_in)
    have "?q \<bullet> insert x Xs \<inter> As = {}"
      using \<open>y \<notin> As\<close> \<open>p \<bullet> Xs \<inter> As = {}\<close>
      unfolding q by simp
    moreover
    have "supp (x \<rightleftharpoons> y) \<inter> supp p = {}" using px py \<open>sort_of y = sort_of x\<close>
      unfolding supp_swap by (simp add: supp_perm)
    then have "supp ?q = (supp (x \<rightleftharpoons> y) \<union> supp p)"
      by (simp add: supp_plus_perm_eq)
    then have "supp ?q = insert x Xs \<union> ?q \<bullet> insert x Xs"
      using p2 \<open>sort_of y = sort_of x\<close> \<open>x \<noteq> y\<close> unfolding q supp_swap
      by auto
    ultimately show ?case by blast
  qed
qed

lemma at_set_avoiding:
  assumes a: "finite Xs"
  and     b: "finite (supp c)"
  obtains p::"perm" where "(p \<bullet> Xs)\<sharp>*c" and "(supp p) = (Xs \<union> (p \<bullet> Xs))"
  using a b at_set_avoiding_aux [where Xs="Xs" and As="Xs \<union> supp c"]
  unfolding fresh_star_def fresh_def by blast

lemma at_set_avoiding1:
  assumes "finite xs"
  and     "finite (supp c)"
  shows "\<exists>p. (p \<bullet> xs) \<sharp>* c"
using assms
apply(erule_tac c="c" in at_set_avoiding)
apply(auto)
done

lemma at_set_avoiding2:
  assumes "finite xs"
  and     "finite (supp c)" "finite (supp x)"
  and     "xs \<sharp>* x"
  shows "\<exists>p. (p \<bullet> xs) \<sharp>* c \<and> supp x \<sharp>* p"
using assms
apply(erule_tac c="(c, x)" in at_set_avoiding)
apply(simp add: supp_Pair)
apply(rule_tac x="p" in exI)
apply(simp add: fresh_star_Pair)
apply(rule fresh_star_supp_conv)
apply(auto simp: fresh_star_def)
done

lemma at_set_avoiding3:
  assumes "finite xs"
  and     "finite (supp c)" "finite (supp x)"
  and     "xs \<sharp>* x"
  shows "\<exists>p. (p \<bullet> xs) \<sharp>* c \<and> supp x \<sharp>* p \<and> supp p = xs \<union> (p \<bullet> xs)"
using assms
apply(erule_tac c="(c, x)" in at_set_avoiding)
apply(simp add: supp_Pair)
apply(rule_tac x="p" in exI)
apply(simp add: fresh_star_Pair)
apply(rule fresh_star_supp_conv)
apply(auto simp: fresh_star_def)
done

lemma at_set_avoiding2_atom:
  assumes "finite (supp c)" "finite (supp x)"
  and     b: "a \<sharp> x"
  shows "\<exists>p. (p \<bullet> a) \<sharp> c \<and> supp x \<sharp>* p"
proof -
  have a: "{a} \<sharp>* x" unfolding fresh_star_def by (simp add: b)
  obtain p where p1: "(p \<bullet> {a}) \<sharp>* c" and p2: "supp x \<sharp>* p"
    using at_set_avoiding2[of "{a}" "c" "x"] assms a by blast
  have c: "(p \<bullet> a) \<sharp> c" using p1
    unfolding fresh_star_def Ball_def
    by(erule_tac x="p \<bullet> a" in allE) (simp add: permute_set_def)
  hence "p \<bullet> a \<sharp> c \<and> supp x \<sharp>* p" using p2 by blast
  then show "\<exists>p. (p \<bullet> a) \<sharp> c \<and> supp x \<sharp>* p" by blast
qed


section \<open>Renaming permutations\<close>

lemma set_renaming_perm:
  assumes b: "finite bs"
  shows "\<exists>q. (\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> bs \<union> (p \<bullet> bs)"
using b
proof (induct)
  case empty
  have "(\<forall>b \<in> {}. 0 \<bullet> b = p \<bullet> b) \<and> supp (0::perm) \<subseteq> {} \<union> p \<bullet> {}"
    by (simp add: permute_set_def supp_perm)
  then show "\<exists>q. (\<forall>b \<in> {}. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> {} \<union> p \<bullet> {}" by blast
next
  case (insert a bs)
  then have " \<exists>q. (\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> bs \<union> p \<bullet> bs" by simp
  then obtain q where *: "\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b" and **: "supp q \<subseteq> bs \<union> p \<bullet> bs"
    by (metis empty_subsetI insert(3) supp_swap)
  { assume 1: "q \<bullet> a = p \<bullet> a"
    have "\<forall>b \<in> (insert a bs). q \<bullet> b = p \<bullet> b" using 1 * by simp
    moreover
    have "supp q \<subseteq> insert a bs \<union> p \<bullet> insert a bs"
      using ** by (auto simp: insert_eqvt)
    ultimately
    have "\<exists>q. (\<forall>b \<in> insert a bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> insert a bs \<union> p \<bullet> insert a bs" by blast
  }
  moreover
  { assume 2: "q \<bullet> a \<noteq> p \<bullet> a"
    define q' where "q' = ((q \<bullet> a) \<rightleftharpoons> (p \<bullet> a)) + q"
    have "\<forall>b \<in> insert a bs. q' \<bullet> b = p \<bullet> b" using 2 * \<open>a \<notin> bs\<close> unfolding q'_def
      by (auto simp: swap_atom)
    moreover
    { have "{q \<bullet> a, p \<bullet> a} \<subseteq> insert a bs \<union> p \<bullet> insert a bs"
        using **
        apply (auto simp: supp_perm insert_eqvt)
        apply (subgoal_tac "q \<bullet> a \<in> bs \<union> p \<bullet> bs")
        apply(auto)[1]
        apply(subgoal_tac "q \<bullet> a \<in> {a. q \<bullet> a \<noteq> a}")
        apply(blast)
        apply(simp)
        done
      then have "supp (q \<bullet> a \<rightleftharpoons> p \<bullet> a) \<subseteq> insert a bs \<union> p \<bullet> insert a bs"
        unfolding supp_swap by auto
      moreover
      have "supp q \<subseteq> insert a bs \<union> p \<bullet> insert a bs"
        using ** by (auto simp: insert_eqvt)
      ultimately
      have "supp q' \<subseteq> insert a bs \<union> p \<bullet> insert a bs"
        unfolding q'_def using supp_plus_perm by blast
    }
    ultimately
    have "\<exists>q. (\<forall>b \<in> insert a bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> insert a bs \<union> p \<bullet> insert a bs" by blast
  }
  ultimately show "\<exists>q. (\<forall>b \<in> insert a bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> insert a bs \<union> p \<bullet> insert a bs"
    by blast
qed

lemma set_renaming_perm2:
  shows "\<exists>q. (\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> bs \<union> (p \<bullet> bs)"
proof -
  have "finite (bs \<inter> supp p)" by (simp add: finite_supp)
  then obtain q
    where *: "\<forall>b \<in> bs \<inter> supp p. q \<bullet> b = p \<bullet> b" and **: "supp q \<subseteq> (bs \<inter> supp p) \<union> (p \<bullet> (bs \<inter> supp p))"
    using set_renaming_perm by blast
  from ** have "supp q \<subseteq> bs \<union> (p \<bullet> bs)" by (auto simp: inter_eqvt)
  moreover
  have "\<forall>b \<in> bs - supp p. q \<bullet> b = p \<bullet> b"
    apply(auto)
    apply(subgoal_tac "b \<notin> supp q")
    apply(simp add: fresh_def[symmetric])
    apply(simp add: fresh_perm)
    apply(clarify)
    apply(rotate_tac 2)
    apply(drule subsetD[OF **])
    apply(simp add: inter_eqvt supp_eqvt permute_self)
    done
  ultimately have "(\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> bs \<union> (p \<bullet> bs)" using * by auto
  then show "\<exists>q. (\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> bs \<union> (p \<bullet> bs)" by blast
qed

lemma list_renaming_perm:
  shows "\<exists>q. (\<forall>b \<in> set bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> set bs \<union> (p \<bullet> set bs)"
proof (induct bs)
  case (Cons a bs)
  then have " \<exists>q. (\<forall>b \<in> set bs. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> set bs \<union> p \<bullet> (set bs)"  by simp
  then obtain q where *: "\<forall>b \<in> set bs. q \<bullet> b = p \<bullet> b" and **: "supp q \<subseteq> set bs \<union> p \<bullet> (set bs)"
    by (blast)
  { assume 1: "a \<in> set bs"
    have "q \<bullet> a = p \<bullet> a" using * 1 by (induct bs) (auto)
    then have "\<forall>b \<in> set (a # bs). q \<bullet> b = p \<bullet> b" using * by simp
    moreover
    have "supp q \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))" using ** by (auto simp: insert_eqvt)
    ultimately
    have "\<exists>q. (\<forall>b \<in> set (a # bs). q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))" by blast
  }
  moreover
  { assume 2: "a \<notin> set bs"
    define q' where "q' = ((q \<bullet> a) \<rightleftharpoons> (p \<bullet> a)) + q"
    have "\<forall>b \<in> set (a # bs). q' \<bullet> b = p \<bullet> b"
      unfolding q'_def using 2 * \<open>a \<notin> set bs\<close> by (auto simp: swap_atom)
    moreover
    { have "{q \<bullet> a, p \<bullet> a} \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))"
        using **
        apply (auto simp: supp_perm insert_eqvt)
        apply (subgoal_tac "q \<bullet> a \<in> set bs \<union> p \<bullet> set bs")
        apply(auto)[1]
        apply(subgoal_tac "q \<bullet> a \<in> {a. q \<bullet> a \<noteq> a}")
        apply(blast)
        apply(simp)
        done
      then have "supp (q \<bullet> a \<rightleftharpoons> p \<bullet> a) \<subseteq> set (a # bs) \<union> p \<bullet> set (a # bs)"
        unfolding supp_swap by auto
      moreover
      have "supp q \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))"
        using ** by (auto simp: insert_eqvt)
      ultimately
      have "supp q' \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))"
        unfolding q'_def using supp_plus_perm by blast
    }
    ultimately
    have "\<exists>q. (\<forall>b \<in> set (a # bs).  q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))" by blast
  }
  ultimately show "\<exists>q. (\<forall>b \<in> set (a # bs). q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> set (a # bs) \<union> p \<bullet> (set (a # bs))"
    by blast
next
 case Nil
  have "(\<forall>b \<in> set []. 0 \<bullet> b = p \<bullet> b) \<and> supp (0::perm) \<subseteq> set [] \<union> p \<bullet> set []"
    by (simp add: supp_zero_perm)
  then show "\<exists>q. (\<forall>b \<in> set []. q \<bullet> b = p \<bullet> b) \<and> supp q \<subseteq> set [] \<union> p \<bullet> (set [])" by blast
qed


section \<open>Concrete Atoms Types\<close>

text \<open>
  Class \<open>at_base\<close> allows types containing multiple sorts of atoms.
  Class \<open>at\<close> only allows types with a single sort.
\<close>

class at_base = pt +
  fixes atom :: "'a \<Rightarrow> atom"
  assumes atom_eq_iff [simp]: "atom a = atom b \<longleftrightarrow> a = b"
  assumes atom_eqvt: "p \<bullet> (atom a) = atom (p \<bullet> a)"

declare atom_eqvt [eqvt]

class at = at_base +
  assumes sort_of_atom_eq [simp]: "sort_of (atom a) = sort_of (atom b)"

lemma sort_ineq [simp]:
  assumes "sort_of (atom a) \<noteq> sort_of (atom b)"
  shows "atom a \<noteq> atom b"
using assms by metis

lemma supp_at_base:
  fixes a::"'a::at_base"
  shows "supp a = {atom a}"
  by (simp add: supp_atom [symmetric] supp_def atom_eqvt)

lemma fresh_at_base:
  shows  "sort_of a \<noteq> sort_of (atom b) \<Longrightarrow> a \<sharp> b"
  and "a \<sharp> b \<longleftrightarrow> a \<noteq> atom b"
  unfolding fresh_def
  apply(simp_all add: supp_at_base)
  apply(metis)
  done

(* solves the freshness only if the inequality can be shown by the
   simproc below *)
lemma fresh_ineq_at_base [simp]:
  shows "a \<noteq> atom b \<Longrightarrow> a \<sharp> b"
  by (simp add: fresh_at_base)


lemma fresh_atom_at_base [simp]:
  fixes b::"'a::at_base"
  shows "a \<sharp> atom b \<longleftrightarrow> a \<sharp> b"
  by (simp add: fresh_def supp_at_base supp_atom)

lemma fresh_star_atom_at_base:
  fixes b::"'a::at_base"
  shows "as \<sharp>* atom b \<longleftrightarrow> as \<sharp>* b"
  by (simp add: fresh_star_def fresh_atom_at_base)

lemma if_fresh_at_base [simp]:
  shows "atom a \<sharp> x \<Longrightarrow> P (if a = x then t else s) = P s"
  and   "atom a \<sharp> x \<Longrightarrow> P (if x = a then t else s) = P s"
by (simp_all add: fresh_at_base)


simproc_setup fresh_ineq ("x \<noteq> (y::'a::at_base)") = \<open>fn _ => fn ctxt => fn ctrm =>
  case Thm.term_of ctrm of @{term "HOL.Not"} $ (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) =>
    let
      fun first_is_neg lhs rhs [] = NONE
        | first_is_neg lhs rhs (thm::thms) =
          (case Thm.prop_of thm of
             _ $ (@{term "HOL.Not"} $ (Const (@{const_name HOL.eq}, _) $ l $ r)) =>
               (if l = lhs andalso r = rhs then SOME(thm)
                else if r = lhs andalso l = rhs then SOME(thm RS @{thm not_sym})
                else first_is_neg lhs rhs thms)
        | _ => first_is_neg lhs rhs thms)

      val simp_thms = @{thms fresh_Pair fresh_at_base atom_eq_iff}
      val prems = Simplifier.prems_of ctxt
         |> filter (fn thm => case Thm.prop_of thm of
            _ $ (Const (@{const_name fresh}, ty) $ (_ $ a) $ b) =>
            (let
               val atms = a :: HOLogic.strip_tuple b
             in
               member ((=)) atms lhs andalso member ((=)) atms rhs
             end)
            | _ => false)
         |> map (simplify (put_simpset HOL_basic_ss ctxt addsimps simp_thms))
         |> map (HOLogic.conj_elims ctxt)
         |> flat
    in
      case first_is_neg lhs rhs prems of
        SOME(thm) => SOME(thm RS @{thm Eq_TrueI})
      | NONE => NONE
    end
  | _ => NONE
\<close>


instance at_base < fs
proof qed (simp add: supp_at_base)

lemma at_base_infinite [simp]:
  shows "infinite (UNIV :: 'a::at_base set)" (is "infinite ?U")
proof
  obtain a :: 'a where "True" by auto
  assume "finite ?U"
  hence "finite (atom ` ?U)"
    by (rule finite_imageI)
  then obtain b where b: "b \<notin> atom ` ?U" "sort_of b = sort_of (atom a)"
    by (rule obtain_atom)
  from b(2) have "b = atom ((atom a \<rightleftharpoons> b) \<bullet> a)"
    unfolding atom_eqvt [symmetric]
    by (simp add: swap_atom)
  hence "b \<in> atom ` ?U" by simp
  with b(1) show "False" by simp
qed

lemma swap_at_base_simps [simp]:
  fixes x y::"'a::at_base"
  shows "sort_of (atom x) = sort_of (atom y) \<Longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> x = y"
  and   "sort_of (atom x) = sort_of (atom y) \<Longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> y = x"
  and   "atom x \<noteq> a \<Longrightarrow> atom x \<noteq> b \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> x = x"
  unfolding atom_eq_iff [symmetric]
  unfolding atom_eqvt [symmetric]
  by simp_all

lemma obtain_at_base:
  assumes X: "finite X"
  obtains a::"'a::at_base" where "atom a \<notin> X"
proof -
  have "inj (atom :: 'a \<Rightarrow> atom)"
    by (simp add: inj_on_def)
  with X have "finite (atom -` X :: 'a set)"
    by (rule finite_vimageI)
  with at_base_infinite have "atom -` X \<noteq> (UNIV :: 'a set)"
    by auto
  then obtain a :: 'a where "atom a \<notin> X"
    by auto
  thus ?thesis ..
qed

lemma obtain_fresh':
  assumes fin: "finite (supp x)"
  obtains a::"'a::at_base" where "atom a \<sharp> x"
using obtain_at_base[where X="supp x"]
by (auto simp: fresh_def fin)

lemma obtain_fresh:
  fixes x::"'b::fs"
  obtains a::"'a::at_base" where "atom a \<sharp> x"
  by (rule obtain_fresh') (auto simp: finite_supp)

lemma supp_finite_set_at_base:
  assumes a: "finite S"
  shows "supp S = atom ` S"
apply(simp add: supp_of_finite_sets[OF a])
apply(simp add: supp_at_base)
apply(auto)
done

(* FIXME
lemma supp_cofinite_set_at_base:
  assumes a: "finite (UNIV - S)"
  shows "supp S = atom ` (UNIV - S)"
apply(rule finite_supp_unique)
*)

lemma fresh_finite_set_at_base:
  fixes a::"'a::at_base"
  assumes a: "finite S"
  shows "atom a \<sharp> S \<longleftrightarrow> a \<notin> S"
  unfolding fresh_def
  apply(simp add: supp_finite_set_at_base[OF a])
  apply(subst inj_image_mem_iff)
  apply(simp add: inj_on_def)
  apply(simp)
  done

lemma fresh_at_base_permute_iff [simp]:
  fixes a::"'a::at_base"
  shows "atom (p \<bullet> a) \<sharp> p \<bullet> x \<longleftrightarrow> atom a \<sharp> x"
  unfolding atom_eqvt[symmetric]
  by (simp only: fresh_permute_iff)

lemma fresh_at_base_permI:
  shows "atom a \<sharp> p \<Longrightarrow> p \<bullet> a = a"
by (simp add: fresh_def supp_perm)


section \<open>Infrastructure for concrete atom types\<close>

definition
  flip :: "'a::at_base \<Rightarrow> 'a \<Rightarrow> perm" ("'(_ \<leftrightarrow> _')")
where
  "(a \<leftrightarrow> b) = (atom a \<rightleftharpoons> atom b)"

lemma flip_fresh_fresh:
  assumes "atom a \<sharp> x" "atom b \<sharp> x"
  shows "(a \<leftrightarrow> b) \<bullet> x = x"
using assms
by (simp add: flip_def swap_fresh_fresh)

lemma flip_self [simp]: "(a \<leftrightarrow> a) = 0"
  unfolding flip_def by (rule swap_self)

lemma flip_commute: "(a \<leftrightarrow> b) = (b \<leftrightarrow> a)"
  unfolding flip_def by (rule swap_commute)

lemma minus_flip [simp]: "- (a \<leftrightarrow> b) = (a \<leftrightarrow> b)"
  unfolding flip_def by (rule minus_swap)

lemma add_flip_cancel: "(a \<leftrightarrow> b) + (a \<leftrightarrow> b) = 0"
  unfolding flip_def by (rule swap_cancel)

lemma permute_flip_cancel [simp]: "(a \<leftrightarrow> b) \<bullet> (a \<leftrightarrow> b) \<bullet> x = x"
  unfolding permute_plus [symmetric] add_flip_cancel by simp

lemma permute_flip_cancel2 [simp]: "(a \<leftrightarrow> b) \<bullet> (b \<leftrightarrow> a) \<bullet> x = x"
  by (simp add: flip_commute)

lemma flip_eqvt [eqvt]:
  shows "p \<bullet> (a \<leftrightarrow> b) = (p \<bullet> a \<leftrightarrow> p \<bullet> b)"
  unfolding flip_def
  by (simp add: swap_eqvt atom_eqvt)

lemma flip_at_base_simps [simp]:
  shows "sort_of (atom a) = sort_of (atom b) \<Longrightarrow> (a \<leftrightarrow> b) \<bullet> a = b"
  and   "sort_of (atom a) = sort_of (atom b) \<Longrightarrow> (a \<leftrightarrow> b) \<bullet> b = a"
  and   "\<lbrakk>a \<noteq> c; b \<noteq> c\<rbrakk> \<Longrightarrow> (a \<leftrightarrow> b) \<bullet> c = c"
  and   "sort_of (atom a) \<noteq> sort_of (atom b) \<Longrightarrow> (a \<leftrightarrow> b) \<bullet> x = x"
  unfolding flip_def
  unfolding atom_eq_iff [symmetric]
  unfolding atom_eqvt [symmetric]
  by simp_all

text \<open>the following two lemmas do not hold for \<open>at_base\<close>,
  only for single sort atoms from at\<close>

lemma flip_triple:
  fixes a b c::"'a::at"
  assumes "a \<noteq> b" and "c \<noteq> b"
  shows "(a \<leftrightarrow> c) + (b \<leftrightarrow> c) + (a \<leftrightarrow> c) = (a \<leftrightarrow> b)"
  unfolding flip_def
  by (rule swap_triple) (simp_all add: assms)

lemma permute_flip_at:
  fixes a b c::"'a::at"
  shows "(a \<leftrightarrow> b) \<bullet> c = (if c = a then b else if c = b then a else c)"
  unfolding flip_def
  apply (rule atom_eq_iff [THEN iffD1])
  apply (subst atom_eqvt [symmetric])
  apply (simp add: swap_atom)
  done

lemma flip_at_simps [simp]:
  fixes a b::"'a::at"
  shows "(a \<leftrightarrow> b) \<bullet> a = b"
  and   "(a \<leftrightarrow> b) \<bullet> b = a"
  unfolding permute_flip_at by simp_all


subsection \<open>Syntax for coercing at-elements to the atom-type\<close>

syntax
  "_atom_constrain" :: "logic \<Rightarrow> type \<Rightarrow> logic" ("_:::_" [4, 0] 3)

translations
  "_atom_constrain a t" => "CONST atom (_constrain a t)"


subsection \<open>A lemma for proving instances of class \<open>at\<close>.\<close>

setup \<open>Sign.add_const_constraint (@{const_name "permute"}, NONE)\<close>
setup \<open>Sign.add_const_constraint (@{const_name "atom"}, NONE)\<close>

text \<open>
  New atom types are defined as subtypes of @{typ atom}.
\<close>

lemma exists_eq_simple_sort:
  shows "\<exists>a. a \<in> {a. sort_of a = s}"
  by (rule_tac x="Atom s 0" in exI, simp)

lemma exists_eq_sort:
  shows "\<exists>a. a \<in> {a. sort_of a \<in> range sort_fun}"
  by (rule_tac x="Atom (sort_fun x) y" in exI, simp)

lemma at_base_class:
  fixes sort_fun :: "'b \<Rightarrow> atom_sort"
  fixes Rep :: "'a \<Rightarrow> atom" and Abs :: "atom \<Rightarrow> 'a"
  assumes type: "type_definition Rep Abs {a. sort_of a \<in> range sort_fun}"
  assumes atom_def: "\<And>a. atom a = Rep a"
  assumes permute_def: "\<And>p a. p \<bullet> a = Abs (p \<bullet> Rep a)"
  shows "OFCLASS('a, at_base_class)"
proof
  interpret type_definition Rep Abs "{a. sort_of a \<in> range sort_fun}" by (rule type)
  have sort_of_Rep: "\<And>a. sort_of (Rep a) \<in> range sort_fun" using Rep by simp
  fix a b :: 'a and p p1 p2 :: perm
  show "0 \<bullet> a = a"
    unfolding permute_def by (simp add: Rep_inverse)
  show "(p1 + p2) \<bullet> a = p1 \<bullet> p2 \<bullet> a"
    unfolding permute_def by (simp add: Abs_inverse sort_of_Rep)
  show "atom a = atom b \<longleftrightarrow> a = b"
    unfolding atom_def by (simp add: Rep_inject)
  show "p \<bullet> atom a = atom (p \<bullet> a)"
    unfolding permute_def atom_def by (simp add: Abs_inverse sort_of_Rep)
qed

(*
lemma at_class:
  fixes s :: atom_sort
  fixes Rep :: "'a \<Rightarrow> atom" and Abs :: "atom \<Rightarrow> 'a"
  assumes type: "type_definition Rep Abs {a. sort_of a \<in> range (\<lambda>x::unit. s)}"
  assumes atom_def: "\<And>a. atom a = Rep a"
  assumes permute_def: "\<And>p a. p \<bullet> a = Abs (p \<bullet> Rep a)"
  shows "OFCLASS('a, at_class)"
proof
  interpret type_definition Rep Abs "{a. sort_of a \<in> range (\<lambda>x::unit. s)}" by (rule type)
  have sort_of_Rep: "\<And>a. sort_of (Rep a) = s" using Rep by (simp add: image_def)
  fix a b :: 'a and p p1 p2 :: perm
  show "0 \<bullet> a = a"
    unfolding permute_def by (simp add: Rep_inverse)
  show "(p1 + p2) \<bullet> a = p1 \<bullet> p2 \<bullet> a"
    unfolding permute_def by (simp add: Abs_inverse sort_of_Rep)
  show "sort_of (atom a) = sort_of (atom b)"
    unfolding atom_def by (simp add: sort_of_Rep)
  show "atom a = atom b \<longleftrightarrow> a = b"
    unfolding atom_def by (simp add: Rep_inject)
  show "p \<bullet> atom a = atom (p \<bullet> a)"
    unfolding permute_def atom_def by (simp add: Abs_inverse sort_of_Rep)
qed
*)

lemma at_class:
  fixes s :: atom_sort
  fixes Rep :: "'a \<Rightarrow> atom" and Abs :: "atom \<Rightarrow> 'a"
  assumes type: "type_definition Rep Abs {a. sort_of a = s}"
  assumes atom_def: "\<And>a. atom a = Rep a"
  assumes permute_def: "\<And>p a. p \<bullet> a = Abs (p \<bullet> Rep a)"
  shows "OFCLASS('a, at_class)"
proof
  interpret type_definition Rep Abs "{a. sort_of a = s}" by (rule type)
  have sort_of_Rep: "\<And>a. sort_of (Rep a) = s" using Rep by (simp add: image_def)
  fix a b :: 'a and p p1 p2 :: perm
  show "0 \<bullet> a = a"
    unfolding permute_def by (simp add: Rep_inverse)
  show "(p1 + p2) \<bullet> a = p1 \<bullet> p2 \<bullet> a"
    unfolding permute_def by (simp add: Abs_inverse sort_of_Rep)
  show "sort_of (atom a) = sort_of (atom b)"
    unfolding atom_def by (simp add: sort_of_Rep)
  show "atom a = atom b \<longleftrightarrow> a = b"
    unfolding atom_def by (simp add: Rep_inject)
  show "p \<bullet> atom a = atom (p \<bullet> a)"
    unfolding permute_def atom_def by (simp add: Abs_inverse sort_of_Rep)
qed

lemma at_class_sort:
  fixes s :: atom_sort
  fixes Rep :: "'a \<Rightarrow> atom" and Abs :: "atom \<Rightarrow> 'a"
  fixes a::"'a"
  assumes type: "type_definition Rep Abs {a. sort_of a = s}"
  assumes atom_def: "\<And>a. atom a = Rep a"
  shows "sort_of (atom a) = s"
  using atom_def type
  unfolding type_definition_def by simp


setup \<open>Sign.add_const_constraint
  (@{const_name "permute"}, SOME @{typ "perm \<Rightarrow> 'a::pt \<Rightarrow> 'a"})\<close>
setup \<open>Sign.add_const_constraint
  (@{const_name "atom"}, SOME @{typ "'a::at_base \<Rightarrow> atom"})\<close>


section \<open>Library functions for the nominal infrastructure\<close>

ML_file \<open>nominal_library.ML\<close>


section \<open>The freshness lemma according to Andy Pitts\<close>

lemma freshness_lemma:
  fixes h :: "'a::at \<Rightarrow> 'b::pt"
  assumes a: "\<exists>a. atom a \<sharp> (h, h a)"
  shows  "\<exists>x. \<forall>a. atom a \<sharp> h \<longrightarrow> h a = x"
proof -
  from a obtain b where a1: "atom b \<sharp> h" and a2: "atom b \<sharp> h b"
    by (auto simp: fresh_Pair)
  show "\<exists>x. \<forall>a. atom a \<sharp> h \<longrightarrow> h a = x"
  proof (intro exI allI impI)
    fix a :: 'a
    assume a3: "atom a \<sharp> h"
    show "h a = h b"
    proof (cases "a = b")
      assume "a = b"
      thus "h a = h b" by simp
    next
      assume "a \<noteq> b"
      hence "atom a \<sharp> b" by (simp add: fresh_at_base)
      with a3 have "atom a \<sharp> h b"
        by (rule fresh_fun_app)
      with a2 have d1: "(atom b \<rightleftharpoons> atom a) \<bullet> (h b) = (h b)"
        by (rule swap_fresh_fresh)
      from a1 a3 have d2: "(atom b \<rightleftharpoons> atom a) \<bullet> h = h"
        by (rule swap_fresh_fresh)
      from d1 have "h b = (atom b \<rightleftharpoons> atom a) \<bullet> (h b)" by simp
      also have "\<dots> = ((atom b \<rightleftharpoons> atom a) \<bullet> h) ((atom b \<rightleftharpoons> atom a) \<bullet> b)"
        by (rule permute_fun_app_eq)
      also have "\<dots> = h a"
        using d2 by simp
      finally show "h a = h b"  by simp
    qed
  qed
qed

lemma freshness_lemma_unique:
  fixes h :: "'a::at \<Rightarrow> 'b::pt"
  assumes a: "\<exists>a. atom a \<sharp> (h, h a)"
  shows "\<exists>!x. \<forall>a. atom a \<sharp> h \<longrightarrow> h a = x"
proof (rule ex_ex1I)
  from a show "\<exists>x. \<forall>a. atom a \<sharp> h \<longrightarrow> h a = x"
    by (rule freshness_lemma)
next
  fix x y
  assume x: "\<forall>a. atom a \<sharp> h \<longrightarrow> h a = x"
  assume y: "\<forall>a. atom a \<sharp> h \<longrightarrow> h a = y"
  from a x y show "x = y"
    by (auto simp: fresh_Pair)
qed

text \<open>packaging the freshness lemma into a function\<close>

definition
  Fresh :: "('a::at \<Rightarrow> 'b::pt) \<Rightarrow> 'b"
where
  "Fresh h = (THE x. \<forall>a. atom a \<sharp> h \<longrightarrow> h a = x)"

lemma Fresh_apply:
  fixes h :: "'a::at \<Rightarrow> 'b::pt"
  assumes a: "\<exists>a. atom a \<sharp> (h, h a)"
  assumes b: "atom a \<sharp> h"
  shows "Fresh h = h a"
unfolding Fresh_def
proof (rule the_equality)
  show "\<forall>a'. atom a' \<sharp> h \<longrightarrow> h a' = h a"
  proof (intro strip)
    fix a':: 'a
    assume c: "atom a' \<sharp> h"
    from a have "\<exists>x. \<forall>a. atom a \<sharp> h \<longrightarrow> h a = x" by (rule freshness_lemma)
    with b c show "h a' = h a" by auto
  qed
next
  fix fr :: 'b
  assume "\<forall>a. atom a \<sharp> h \<longrightarrow> h a = fr"
  with b show "fr = h a" by auto
qed

lemma Fresh_apply':
  fixes h :: "'a::at \<Rightarrow> 'b::pt"
  assumes a: "atom a \<sharp> h" "atom a \<sharp> h a"
  shows "Fresh h = h a"
  apply (rule Fresh_apply)
  apply (auto simp: fresh_Pair intro: a)
  done

simproc_setup Fresh_simproc ("Fresh (h::'a::at \<Rightarrow> 'b::pt)") = \<open>fn _ => fn ctxt => fn ctrm =>
  let
     val _ $ h = Thm.term_of ctrm

     val cfresh = @{const_name fresh}
     val catom  = @{const_name atom}

     val atoms = Simplifier.prems_of ctxt
      |> map_filter (fn thm => case Thm.prop_of thm of
           _ $ (Const (cfresh, _) $ (Const (catom, _) $ atm) $ _) => SOME (atm) | _ => NONE)
      |> distinct ((=))

     fun get_thm atm =
       let
         val goal1 = HOLogic.mk_Trueprop (mk_fresh (mk_atom atm) h)
         val goal2 = HOLogic.mk_Trueprop (mk_fresh (mk_atom atm) (h $ atm))

         val thm1 = Goal.prove ctxt [] [] goal1 (K (asm_simp_tac ctxt 1))
         val thm2 = Goal.prove ctxt [] [] goal2 (K (asm_simp_tac ctxt 1))
       in
         SOME (@{thm Fresh_apply'} OF [thm1, thm2] RS eq_reflection)
       end handle ERROR _ => NONE
  in
    get_first get_thm atoms
  end
\<close>


lemma Fresh_eqvt:
  fixes h :: "'a::at \<Rightarrow> 'b::pt"
  assumes a: "\<exists>a. atom a \<sharp> (h, h a)"
  shows "p \<bullet> (Fresh h) = Fresh (p \<bullet> h)"
proof -
  from a obtain a::"'a::at" where fr: "atom a \<sharp> h" "atom a \<sharp> h a"
    by (metis fresh_Pair)
  then have fr_p: "atom (p \<bullet> a) \<sharp> (p \<bullet> h)" "atom (p \<bullet> a) \<sharp> (p \<bullet> h) (p \<bullet> a)"
    by (metis atom_eqvt fresh_permute_iff eqvt_apply)+
  have "p \<bullet> (Fresh h) = p \<bullet> (h a)" using fr by simp
  also have "... = (p \<bullet> h) (p \<bullet> a)" by simp
  also have "... = Fresh (p \<bullet> h)" using fr_p by simp
  finally show "p \<bullet> (Fresh h) = Fresh (p \<bullet> h)" .
qed

lemma Fresh_supports:
  fixes h :: "'a::at \<Rightarrow> 'b::pt"
  assumes a: "\<exists>a. atom a \<sharp> (h, h a)"
  shows "(supp h) supports (Fresh h)"
  apply (simp add: supports_def fresh_def [symmetric])
  apply (simp add: Fresh_eqvt [OF a] swap_fresh_fresh)
  done

notation Fresh (binder "FRESH " 10)

lemma FRESH_f_iff:
  fixes P :: "'a::at \<Rightarrow> 'b::pure"
  fixes f :: "'b \<Rightarrow> 'c::pure"
  assumes P: "finite (supp P)"
  shows "(FRESH x. f (P x)) = f (FRESH x. P x)"
proof -
  obtain a::'a where "atom a \<sharp> P" using P by (rule obtain_fresh')
  then show "(FRESH x. f (P x)) = f (FRESH x. P x)"
    by (simp add: pure_fresh)
qed

lemma FRESH_binop_iff:
  fixes P :: "'a::at \<Rightarrow> 'b::pure"
  fixes Q :: "'a::at \<Rightarrow> 'c::pure"
  fixes binop :: "'b \<Rightarrow> 'c \<Rightarrow> 'd::pure"
  assumes P: "finite (supp P)"
  and     Q: "finite (supp Q)"
  shows "(FRESH x. binop (P x) (Q x)) = binop (FRESH x. P x) (FRESH x. Q x)"
proof -
  from assms have "finite (supp (P, Q))" by (simp add: supp_Pair)
  then obtain a::'a where "atom a \<sharp> (P, Q)" by (rule obtain_fresh')
  then show ?thesis
    by (simp add: pure_fresh)
qed

lemma FRESH_conj_iff:
  fixes P Q :: "'a::at \<Rightarrow> bool"
  assumes P: "finite (supp P)" and Q: "finite (supp Q)"
  shows "(FRESH x. P x \<and> Q x) \<longleftrightarrow> (FRESH x. P x) \<and> (FRESH x. Q x)"
using P Q by (rule FRESH_binop_iff)

lemma FRESH_disj_iff:
  fixes P Q :: "'a::at \<Rightarrow> bool"
  assumes P: "finite (supp P)" and Q: "finite (supp Q)"
  shows "(FRESH x. P x \<or> Q x) \<longleftrightarrow> (FRESH x. P x) \<or> (FRESH x. Q x)"
using P Q by (rule FRESH_binop_iff)


section \<open>Automation for creating concrete atom types\<close>

text \<open>At the moment only single-sort concrete atoms are supported.\<close>

ML_file \<open>nominal_atoms.ML\<close>


section \<open>Automatic equivariance procedure for inductive definitions\<close>

ML_file \<open>nominal_eqvt.ML\<close>

end
