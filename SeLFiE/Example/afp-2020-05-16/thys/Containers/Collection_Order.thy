(* Title:      Containers/Collection_Order.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)

theory Collection_Order
imports
  Set_Linorder
  Containers_Generator
  Deriving.Compare_Instances
begin

chapter \<open>Light-weight containers\<close>
text_raw \<open>\label{chapter:light-weight:containers}\<close>

section \<open>A linear order for code generation\<close>

subsection \<open>Optional comparators\<close>

class ccompare =
  fixes ccompare :: "'a comparator option"
  assumes ccompare: "\<And> comp. ccompare = Some comp \<Longrightarrow> comparator comp"
begin
abbreviation ccomp :: "'a comparator" where "ccomp \<equiv> the (ID ccompare)"
abbreviation cless :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "cless \<equiv> lt_of_comp (the (ID ccompare))"
abbreviation cless_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "cless_eq \<equiv> le_of_comp (the (ID ccompare))"
end

lemma (in ccompare) ID_ccompare': 
  "\<And>c. ID ccompare = Some c \<Longrightarrow> comparator c"
  unfolding ID_def id_apply using ccompare by simp 

lemma (in ccompare) ID_ccompare: 
  "\<And>c. ID ccompare = Some c \<Longrightarrow> class.linorder (le_of_comp c) (lt_of_comp c)"
  by (rule comparator.linorder[OF ID_ccompare'])
  
syntax "_CCOMPARE" :: "type => logic"  ("(1CCOMPARE/(1'(_')))")

parse_translation \<open>
let
  fun ccompare_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "ccompare"} $
       (Syntax.const @{type_syntax option} $ 
         (Syntax.const @{type_syntax fun} $ ty $ 
           (Syntax.const @{type_syntax fun} $ ty $ Syntax.const @{type_syntax order}))))
    | ccompare_tr ts = raise TERM ("ccompare_tr", ts);
in [(@{syntax_const "_CCOMPARE"}, K ccompare_tr)] end
\<close>

definition is_ccompare :: "'a :: ccompare itself \<Rightarrow> bool"
where "is_ccompare _ \<longleftrightarrow> ID CCOMPARE('a) \<noteq> None"

context ccompare
begin
lemma cless_eq_conv_cless: 
  fixes a b :: "'a"
  assumes "ID CCOMPARE('a) \<noteq> None"
  shows "cless_eq a b \<longleftrightarrow> cless a b \<or> a = b"
proof -
  from assms interpret linorder cless_eq "cless :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
    by(clarsimp simp add: ID_ccompare)
  show ?thesis by(rule le_less)
qed
end

subsection \<open>Generator for the @{class ccompare}--class\<close>

text \<open>
This generator registers itself at the derive-manager for the class
@{class ccompare}. To be more precise, one can choose whether one does not want to
support a comparator by passing parameter "no", one wants to register an arbitrary type which
is already in class @{class compare} using parameter "compare", or
one wants to generate a new comparator by passing no parameter.
In the last case, one demands that the type is a datatype
and that all non-recursive types of that datatype already provide a comparator,
which can usually be achieved via "derive comparator type" or "derive compare type".


\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (no) corder}
\item \texttt{instantiation datatype :: (type,\ldots,type) corder}
\item \texttt{instantiation datatype :: (compare,\ldots,compare) (compare) corder}
\end{itemize}

If the parameter "no" is not used, then the corresponding
@{const is_ccompare}-theorem is automatically generated and attributed with 
\texttt{[simp, code-post]}.
\<close>


text \<open>
To create a new comparator, we just invoke the functionality provided by the generator.
The only difference is the boilerplate-code, which for the generator has to perform
the class instantiation for a comparator, whereas here we have to invoke the methods to 
satisfy the corresponding locale for comparators.
\<close>

text \<open>
This generator can be used for arbitrary types, not just datatypes. 
When passing no parameters, we get same limitation as for the order generator.
\<close>

lemma corder_intro: "class.linorder le lt \<Longrightarrow> a = Some (le, lt)\<Longrightarrow> a = Some (le',lt') \<Longrightarrow>
  class.linorder le' lt'" by auto

lemma comparator_subst: "c1 = c2 \<Longrightarrow> comparator c1 \<Longrightarrow> comparator c2" by blast
  
lemma (in compare) compare_subst: "\<And> comp. compare = comp \<Longrightarrow> comparator comp"
  using comparator_compare by blast  

ML_file \<open>ccompare_generator.ML\<close>

subsection \<open>Instantiations for HOL types\<close>

derive (linorder) compare_order 
  Enum.finite_1 Enum.finite_2 Enum.finite_3 natural String.literal
derive (compare) ccompare 
  unit bool nat int Enum.finite_1 Enum.finite_2 Enum.finite_3 integer natural char String.literal
derive (no) ccompare Enum.finite_4 Enum.finite_5

derive ccompare sum list option prod

derive (no) ccompare "fun"

lemma is_ccompare_fun [simp]: "\<not> is_ccompare TYPE('a \<Rightarrow> 'b)"
by(simp add: is_ccompare_def ccompare_fun_def ID_None)

instantiation set :: (ccompare) ccompare begin
definition "CCOMPARE('a set) = 
  map_option (\<lambda> c. comp_of_ords (ord.set_less_eq (le_of_comp c)) (ord.set_less (le_of_comp c))) (ID CCOMPARE('a))"
instance by(intro_classes)(auto simp add: ccompare_set_def intro: comp_of_ords linorder.set_less_eq_linorder ID_ccompare)
end

lemma is_ccompare_set [simp, code_post]:
  "is_ccompare TYPE('a set) \<longleftrightarrow> is_ccompare TYPE('a :: ccompare)"
by(simp add: is_ccompare_def ccompare_set_def ID_def)


definition cless_eq_set :: "'a :: ccompare set \<Rightarrow> 'a set \<Rightarrow> bool" 
where [simp, code del]: "cless_eq_set = le_of_comp (the (ID CCOMPARE('a set)))"

definition cless_set :: "'a :: ccompare set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del]: "cless_set = lt_of_comp (the (ID CCOMPARE('a set)))"

lemma ccompare_set_code [code]:
  "CCOMPARE('a :: ccompare set) = 
    (case ID CCOMPARE('a) of None \<Rightarrow> None | Some _ \<Rightarrow> Some (comp_of_ords cless_eq_set cless_set))"
  by (clarsimp simp add: ccompare_set_def ID_Some split: option.split)

derive (no) ccompare Predicate.pred

subsection \<open>Proper intervals\<close>

class cproper_interval = ccompare + 
  fixes cproper_interval :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  assumes cproper_interval: 
  "\<lbrakk> ID CCOMPARE('a) \<noteq> None; finite (UNIV :: 'a set) \<rbrakk>
  \<Longrightarrow> class.proper_interval cless cproper_interval"
begin

lemma ID_ccompare_interval: 
  "\<lbrakk> ID CCOMPARE('a) = Some c; finite (UNIV :: 'a set) \<rbrakk>
  \<Longrightarrow> class.linorder_proper_interval (le_of_comp c) (lt_of_comp c) cproper_interval"
using cproper_interval
by(simp add: ID_ccompare class.linorder_proper_interval_def)

end

instantiation unit :: cproper_interval begin
definition "cproper_interval = (proper_interval :: unit proper_interval)"
instance by intro_classes (simp add: compare_order_class.ord_defs cproper_interval_unit_def ccompare_unit_def ID_Some proper_interval_class.axioms)
end

instantiation bool :: cproper_interval begin
definition "cproper_interval = (proper_interval :: bool proper_interval)"
instance by(intro_classes)
  (simp add: cproper_interval_bool_def ord_defs ccompare_bool_def ID_Some proper_interval_class.axioms)
end

instantiation nat :: cproper_interval begin
definition "cproper_interval = (proper_interval :: nat proper_interval)"
instance by intro_classes simp
end

instantiation int :: cproper_interval begin
definition "cproper_interval = (proper_interval :: int proper_interval)"
instance by intro_classes 
  (simp add: cproper_interval_int_def ord_defs ccompare_int_def ID_Some proper_interval_class.axioms)
end

instantiation integer :: cproper_interval begin
definition "cproper_interval = (proper_interval :: integer proper_interval)"
instance by intro_classes 
  (simp add: cproper_interval_integer_def ord_defs ccompare_integer_def ID_Some proper_interval_class.axioms)
end

instantiation natural :: cproper_interval begin
definition "cproper_interval = (proper_interval :: natural proper_interval)"
instance by intro_classes (simp add: cproper_interval_natural_def ord_defs ccompare_natural_def ID_Some proper_interval_class.axioms)
end

instantiation char :: cproper_interval begin
definition "cproper_interval = (proper_interval :: char proper_interval)"
instance by intro_classes (simp add: cproper_interval_char_def ord_defs ccompare_char_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_1 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: Enum.finite_1 proper_interval)"
instance by intro_classes (simp add: cproper_interval_finite_1_def ord_defs ccompare_finite_1_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_2 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: Enum.finite_2 proper_interval)"
instance by intro_classes (simp add: cproper_interval_finite_2_def ord_defs ccompare_finite_2_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_3 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: Enum.finite_3 proper_interval)"
instance by intro_classes (simp add: cproper_interval_finite_3_def ord_defs ccompare_finite_3_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_4 :: cproper_interval begin
definition "(cproper_interval :: Enum.finite_4 proper_interval) _ _ = undefined"
instance by intro_classes(simp add: ord_defs ccompare_finite_4_def ID_None)
end

instantiation Enum.finite_5 :: cproper_interval begin
definition "(cproper_interval :: Enum.finite_5 proper_interval) _ _ = undefined"
instance by intro_classes(simp add: ord_defs ccompare_finite_5_def ID_None)
end

lemma lt_of_comp_sum: "lt_of_comp (comparator_sum ca cb) sx sy = (
  case sx of Inl x \<Rightarrow> (case sy of Inl y \<Rightarrow> lt_of_comp ca x y | Inr y \<Rightarrow> True)
   | Inr x \<Rightarrow> (case sy of Inl y \<Rightarrow> False | Inr y \<Rightarrow> lt_of_comp cb x y))" 
    by (simp add: lt_of_comp_def le_of_comp_def split: sum.split)

instantiation sum :: (cproper_interval, cproper_interval) cproper_interval begin
fun cproper_interval_sum :: "('a + 'b) proper_interval" where
  "cproper_interval_sum None None \<longleftrightarrow> True"
| "cproper_interval_sum None (Some (Inl x)) \<longleftrightarrow> cproper_interval None (Some x)"
| "cproper_interval_sum None (Some (Inr y)) \<longleftrightarrow> True"
| "cproper_interval_sum (Some (Inl x)) None \<longleftrightarrow> True"
| "cproper_interval_sum (Some (Inl x)) (Some (Inl y)) \<longleftrightarrow> cproper_interval (Some x) (Some y)"
| "cproper_interval_sum (Some (Inl x)) (Some (Inr y)) \<longleftrightarrow> cproper_interval (Some x) None \<or> cproper_interval None (Some y)"
| "cproper_interval_sum (Some (Inr y)) None \<longleftrightarrow> cproper_interval (Some y) None"
| "cproper_interval_sum (Some (Inr y)) (Some (Inl x)) \<longleftrightarrow> False"
| "cproper_interval_sum (Some (Inr x)) (Some (Inr y)) \<longleftrightarrow> cproper_interval (Some x) (Some y)"
instance
proof
  assume "ID CCOMPARE('a + 'b) \<noteq> None" "finite (UNIV :: ('a + 'b) set)"
  then obtain c_a c_b
    where A: "ID CCOMPARE('a) = Some c_a" "finite (UNIV :: 'a set)"
    and B: "ID CCOMPARE('b) = Some c_b" "finite (UNIV :: 'b set)" 
    by(fastforce simp add: ccompare_sum_def ID_Some ID_None split: option.split_asm)
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] 
    lt_of_comp_sum ccompare_sum_def ID_Some
    and [split] = sum.split
  show "class.proper_interval cless (cproper_interval :: ('a + 'b) proper_interval)"
  proof
    fix y :: "'a + 'b"
    show "cproper_interval None (Some y) = (\<exists>z. cless z y)"
      using A B by(cases y)(auto, case_tac z, auto)

    fix x :: "'a + 'b"
    show "cproper_interval (Some x) None = (\<exists>z. cless x z)"
      using A B by(cases x)(auto, case_tac z, auto)

    show "cproper_interval (Some x) (Some y) = (\<exists>z. cless x z \<and> cless z y)"
      using A B by(cases x)(case_tac [!] y, auto, case_tac [!] z, auto)
  qed simp
qed
end


lemma lt_of_comp_less_prod: "lt_of_comp (comparator_prod c_a c_b) =
  less_prod (le_of_comp c_a) (lt_of_comp c_a) (lt_of_comp c_b)"
  unfolding less_prod_def
  by (intro ext, auto simp: lt_of_comp_def le_of_comp_def split: order.split_asm prod.split)

lemma lt_of_comp_prod: "lt_of_comp (comparator_prod c_a c_b) (x1,x2) (y1,y2) = 
  (lt_of_comp c_a x1 y1 \<or> le_of_comp c_a x1 y1 \<and> lt_of_comp c_b x2 y2)"
  unfolding lt_of_comp_less_prod less_prod_def by simp

instantiation prod :: (cproper_interval, cproper_interval) cproper_interval begin
fun cproper_interval_prod :: "('a \<times> 'b) proper_interval" where
  "cproper_interval_prod None None \<longleftrightarrow> True"
| "cproper_interval_prod None (Some (y1, y2)) \<longleftrightarrow> cproper_interval None (Some y1) \<or> cproper_interval None (Some y2)"
| "cproper_interval_prod (Some (x1, x2)) None \<longleftrightarrow> cproper_interval (Some x1) None \<or> cproper_interval (Some x2) None"
| "cproper_interval_prod (Some (x1, x2)) (Some (y1, y2)) \<longleftrightarrow> 
   cproper_interval (Some x1) (Some y1) \<or> 
   cless x1 y1 \<and> (cproper_interval (Some x2) None \<or> cproper_interval None (Some y2)) \<or>
   \<not> cless y1 x1 \<and> cproper_interval (Some x2) (Some y2)"
instance
proof
  assume "ID CCOMPARE('a \<times> 'b) \<noteq> None" "finite (UNIV :: ('a \<times> 'b) set)"
  then obtain c_a c_b 
    where A: "ID CCOMPARE('a) = Some c_a" "finite (UNIV :: 'a set)"
    and B: "ID CCOMPARE('b) = Some c_b" "finite (UNIV :: 'b set)"
    by(fastforce simp add: ccompare_prod_def ID_Some ID_None finite_prod split: option.split_asm)
  interpret a: linorder "le_of_comp c_a" "lt_of_comp c_a" by(rule ID_ccompare)(rule A)
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] 
    ccompare_prod_def lt_of_comp_prod ID_Some
  show "class.proper_interval cless (cproper_interval :: ('a \<times> 'b) proper_interval)" using A B
    by (unfold_locales, auto 4 4)
qed
end


instantiation list :: (ccompare) cproper_interval begin
definition cproper_interval_list :: "'a list proper_interval"
where "cproper_interval_list xso yso = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_listI)
end

lemma infinite_UNIV_literal:
  "infinite (UNIV :: String.literal set)"
  by (fact infinite_literal)

instantiation String.literal :: cproper_interval begin
definition cproper_interval_literal :: "String.literal proper_interval"
where "cproper_interval_literal xso yso = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_literal)
end

lemma lt_of_comp_option: "lt_of_comp (comparator_option c) sx sy = (
  case sx of None \<Rightarrow> (case sy of None \<Rightarrow> False | Some y \<Rightarrow> True)
   | Some x \<Rightarrow> (case sy of None \<Rightarrow> False | Some y \<Rightarrow> lt_of_comp c x y))" 
    by (simp add: lt_of_comp_def le_of_comp_def split: option.split)


instantiation option :: (cproper_interval) cproper_interval begin
fun cproper_interval_option :: "'a option proper_interval" where
  "cproper_interval_option None None \<longleftrightarrow> True"
| "cproper_interval_option None (Some x) \<longleftrightarrow> x \<noteq> None"
| "cproper_interval_option (Some x) None \<longleftrightarrow> cproper_interval x None"
| "cproper_interval_option (Some x) (Some None) \<longleftrightarrow> False"
| "cproper_interval_option (Some x) (Some (Some y)) \<longleftrightarrow> cproper_interval x (Some y)"
instance
proof
  assume "ID CCOMPARE('a option) \<noteq> None" "finite (UNIV :: 'a option set)"
  then obtain c_a
    where A: "ID CCOMPARE('a) = Some c_a" "finite (UNIV :: 'a set)"
    by(auto simp add: ccompare_option_def ID_def split: option.split_asm)
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] 
    ccompare_option_def lt_of_comp_option ID_Some
  show "class.proper_interval cless (cproper_interval :: 'a option proper_interval)" using A
  proof(unfold_locales)
    fix x y :: "'a option"
    show "cproper_interval (Some x) None = (\<exists>z. cless x z)" using A
      by(cases x)(auto split: option.split intro: exI[where x="Some undefined"])

    show "cproper_interval (Some x) (Some y) = (\<exists>z. cless x z \<and> cless z y)" using A
      by(cases x y rule: option.exhaust[case_product option.exhaust])(auto cong: option.case_cong split: option.split)
  qed(auto split: option.splits)
qed
end


instantiation set :: (cproper_interval) cproper_interval begin
fun cproper_interval_set :: "'a set proper_interval" where
  [code]: "cproper_interval_set None None \<longleftrightarrow> True"
| [code]: "cproper_interval_set None (Some B) \<longleftrightarrow> (B \<noteq> {})"
| [code]: "cproper_interval_set (Some A) None \<longleftrightarrow> (A \<noteq> UNIV)"
| cproper_interval_set_Some_Some [code del]: \<comment> \<open>Refine for concrete implementations\<close>
  "cproper_interval_set (Some A) (Some B) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> (\<exists>C. cless A C \<and> cless C B)"
instance
proof
  assume "ID CCOMPARE('a set) \<noteq> None" "finite (UNIV :: 'a set set)"
  then obtain c_a
    where A: "ID CCOMPARE('a) = Some c_a" "finite (UNIV :: 'a set)"
    by(auto simp add: ccompare_set_def ID_def Finite_Set.finite_set)
  interpret a: linorder "le_of_comp c_a" "lt_of_comp c_a" by(rule ID_ccompare)(rule A) 
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] ccompare_set_def 
    ID_Some lt_of_comp_of_ords
  show "class.proper_interval cless (cproper_interval :: 'a set proper_interval)" using A
    by (unfold_locales, auto)
qed


lemma Complement_cproper_interval_set_Complement:
  fixes A B :: "'a set"
  assumes corder: "ID CCOMPARE('a) \<noteq> None"
  shows "cproper_interval (Some (- A)) (Some (- B)) = cproper_interval (Some B) (Some A)"
using assms
by(clarsimp simp add: ccompare_set_def ID_Some lt_of_comp_of_ords) (metis double_complement linorder.Compl_set_less_Compl[OF ID_ccompare])

end


instantiation "fun" :: (type, type) cproper_interval begin
text \<open>No interval checks on functions needed because we have not defined an order on them.\<close>
definition "cproper_interval = (undefined :: ('a \<Rightarrow> 'b) proper_interval)"
instance by(intro_classes)(simp add: ccompare_fun_def ID_None)
end

end
