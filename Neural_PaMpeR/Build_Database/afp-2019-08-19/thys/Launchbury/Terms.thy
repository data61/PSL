theory Terms
  imports "Nominal-Utils" Vars  "AList-Utils-Nominal"
begin

subsubsection \<open>Expressions\<close>

text \<open>
This is the main data type of the development; our minimal lambda calculus with recursive let-bindings.
It is created using the nominal\_datatype command, which creates alpha-equivalence classes.

The package does not support nested recursion, so the bindings of the let cannot simply be of type
\<open>(var, exp) list\<close>. Instead, the definition of lists have to be inlined here, as the custom type
\<open>assn\<close>. Later we create conversion functions between these two types, define a properly typed \<open>let\<close> 
and redo the various lemmas in terms of that, so that afterwards, the type \<open>assn\<close> is no longer
referenced.
\<close>

nominal_datatype exp =
  Var var
| App exp var
| LetA as::assn body::exp binds "bn as" in body as
| Lam x::var body::exp binds x in body  ("Lam [_]. _" [100, 100] 100)
| Bool bool
| IfThenElse exp exp exp  ("((_)/ ? (_)/ : (_))" [0, 0, 10] 10)
and assn =
  ANil | ACons var exp assn
binder
  bn :: "assn \<Rightarrow> atom list"
where "bn ANil = []" | "bn (ACons x t as) = (atom x) # (bn as)"

notation (latex output) Terms.Var ("_")
notation (latex output) Terms.App ("_ _")
notation (latex output) Terms.Lam ("\<lambda>_. _"  [100, 100] 100)

type_synonym heap = "(var \<times> exp) list"

lemma exp_assn_size_eqvt[eqvt]: "p \<bullet> (size :: exp \<Rightarrow> nat) = size"
  by (metis exp_assn.size_eqvt(1) fun_eqvtI permute_pure)

subsubsection \<open>Rewriting in terms of heaps\<close>

text \<open>
We now work towards using @{type heap} instead of @{type assn}. All this
could be skipped if Nominal supported nested recursion.
\<close>

text \<open>
Conversion from @{typ assn} to @{typ heap}.
\<close>

nominal_function asToHeap :: "assn \<Rightarrow> heap" 
 where ANilToHeap: "asToHeap ANil = []"
 | AConsToHeap: "asToHeap (ACons v e as) = (v, e) # asToHeap as"
unfolding eqvt_def asToHeap_graph_aux_def
apply rule
apply simp
apply rule
apply(case_tac x rule: exp_assn.exhaust(2))
apply auto
done
nominal_termination(eqvt) by lexicographic_order

lemma asToHeap_eqvt: "eqvt asToHeap"
  unfolding eqvt_def
  by (auto simp add: permute_fun_def asToHeap.eqvt)

text \<open>The other direction.\<close>

fun heapToAssn :: "heap \<Rightarrow> assn"
  where "heapToAssn [] = ANil" 
  | "heapToAssn ((v,e)#\<Gamma>) = ACons v e (heapToAssn \<Gamma>)"

declare heapToAssn.simps[simp del]

lemma heapToAssn_eqvt[simp,eqvt]: "p \<bullet> heapToAssn \<Gamma> =  heapToAssn (p \<bullet> \<Gamma>)"
  by (induct \<Gamma> rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps)

lemma bn_heapToAssn: "bn (heapToAssn \<Gamma>) = map (\<lambda>x. atom (fst x)) \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps exp_assn.bn_defs)

lemma set_bn_to_atom_domA:
  "set (bn as) = atom ` domA (asToHeap as)"
   by (induct as rule: asToHeap.induct)
      (auto simp add: exp_assn.bn_defs)

text \<open>
They are inverse to each other.
\<close>

lemma heapToAssn_asToHeap[simp]:
  "heapToAssn (asToHeap as) = as"
  by (induct  rule: exp_assn.inducts(2)[of "\<lambda> _ . True"])
     (auto simp add: heapToAssn.simps)

lemma asToHeap_heapToAssn[simp]:
  "asToHeap (heapToAssn as) = as"
  by (induct rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps)

lemma heapToAssn_inject[simp]:
  "heapToAssn x = heapToAssn y \<longleftrightarrow> x = y"
  by (metis asToHeap_heapToAssn)

text \<open>
They are transparent to various notions from the Nominal package.
\<close>

lemma supp_heapToAssn: "supp (heapToAssn \<Gamma>) = supp \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (simp_all add: heapToAssn.simps  exp_assn.supp supp_Nil supp_Cons supp_Pair sup_assoc)

lemma supp_asToHeap: "supp (asToHeap as) = supp as"
   by (induct as rule: asToHeap.induct)
      (simp_all add:  exp_assn.supp supp_Nil supp_Cons supp_Pair sup_assoc)

lemma fv_asToHeap: "fv (asToHeap \<Gamma>) = fv \<Gamma>"
  unfolding fv_def by (auto simp add: supp_asToHeap)

lemma fv_heapToAssn: "fv (heapToAssn \<Gamma>) = fv \<Gamma>"
  unfolding fv_def by (auto simp add: supp_heapToAssn)

lemma [simp]: "size (heapToAssn \<Gamma>) = size_list (\<lambda> (v,e) . size e) \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (simp_all add: heapToAssn.simps)

lemma Lam_eq_same_var[simp]: "Lam [y]. e = Lam [y]. e' \<longleftrightarrow>  e = e'"
  by auto (metis fresh_PairD(2) obtain_fresh)

text \<open>Now we define the Let constructor in the form that we actually want.\<close>

hide_const HOL.Let
definition Let :: "heap \<Rightarrow> exp \<Rightarrow> exp"
  where "Let \<Gamma> e = LetA (heapToAssn \<Gamma>) e"

notation (latex output) Let ("\<^latex>\<open>\\textrm{\\textsf{let}}\<close> _ \<^latex>\<open>\\textrm{\\textsf{in}}\<close> _")

abbreviation
  LetBe :: "var\<Rightarrow>exp\<Rightarrow>exp\<Rightarrow>exp" ("let _ be _ in _ " [100,100,100] 100)
where
  "let x be t1 in t2 \<equiv> Let [(x,t1)] t2"

text \<open>
We rewrite all (relevant) lemmas about @{term LetA} in terms of @{term Let}.
\<close>

lemma size_Let[simp]: "size (Let \<Gamma> e) = size_list (\<lambda>p. size (snd p)) \<Gamma> + size e + Suc 0"
  unfolding Let_def by (auto simp add: split_beta')

lemma Let_distinct[simp]:
  "Var v \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Var v"
  "App e v \<noteq> Let \<Gamma> e'"
  "Lam [v]. e' \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Lam [v]. e'"
  "Let \<Gamma> e' \<noteq> App e v"
  "Bool b \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Bool b"
  "(scrut ? e1 : e2) \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> (scrut ? e1 : e2)"
  unfolding Let_def by simp_all

lemma Let_perm_simps[simp,eqvt]:
  "p \<bullet> Let \<Gamma> e = Let (p \<bullet> \<Gamma>) (p \<bullet> e)"
  unfolding Let_def by simp

lemma Let_supp:
  "supp (Let \<Gamma> e) = (supp e \<union> supp \<Gamma>) - atom ` (domA \<Gamma>)"
  unfolding Let_def by (simp add: exp_assn.supp supp_heapToAssn bn_heapToAssn domA_def image_image)

lemma Let_fresh[simp]:
  "a \<sharp> Let \<Gamma> e = (a \<sharp> e \<and> a \<sharp> \<Gamma> \<or> a \<in> atom ` domA \<Gamma>)"
  unfolding fresh_def by (auto simp add: Let_supp)

lemma Abs_eq_cong:
  assumes "\<And> p. (p \<bullet> x = x') \<longleftrightarrow> (p \<bullet> y = y')"
  assumes "supp y = supp x"
  assumes "supp y' = supp x'"
  shows "([a]lst. x = [a']lst. x') \<longleftrightarrow> ([a]lst. y = [a']lst. y')"
  by (simp add: Abs_eq_iff alpha_lst assms)

lemma Let_eq_iff[simp]:
  "(Let \<Gamma> e = Let \<Gamma>' e') = ([map (\<lambda>x. atom (fst x)) \<Gamma> ]lst. (e, \<Gamma>) = [map (\<lambda>x. atom (fst x)) \<Gamma>']lst. (e',\<Gamma>'))"
  unfolding Let_def 
  apply (simp add: bn_heapToAssn)
  apply (rule Abs_eq_cong)
  apply (simp_all add: supp_Pair supp_heapToAssn)
  done

lemma exp_strong_exhaust:
  fixes c :: "'a :: fs"
  assumes "\<And>var. y = Var var \<Longrightarrow> P"
  assumes "\<And>exp var. y = App exp var \<Longrightarrow> P"
  assumes "\<And>\<Gamma> exp. atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> y = Let \<Gamma> exp \<Longrightarrow> P"
  assumes "\<And>var exp. {atom var} \<sharp>* c \<Longrightarrow> y = Lam [var]. exp \<Longrightarrow> P"
  assumes "\<And> b. (y = Bool b) \<Longrightarrow> P"
  assumes "\<And> scrut e1 e2. y = (scrut ? e1 : e2) \<Longrightarrow> P"
  shows P
  apply (rule  exp_assn.strong_exhaust(1)[where y = y and c = c])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3) set_bn_to_atom_domA Let_def heapToAssn_asToHeap)
  apply (metis assms(4))
  apply (metis assms(5))
  apply (metis assms(6))
  done

text \<open>
And finally the induction rules with @{term Let}.
\<close>

lemma exp_heap_induct[case_names Var App Let Lam Bool IfThenElse Nil Cons]:
  assumes "\<And>b var. P1 (Var var)"
  assumes "\<And>exp var. P1 exp \<Longrightarrow> P1 (App exp var)"
  assumes "\<And>\<Gamma> exp. P2 \<Gamma> \<Longrightarrow> P1 exp \<Longrightarrow> P1 (Let \<Gamma> exp)"
  assumes "\<And>var exp. P1 exp \<Longrightarrow> P1 (Lam [var]. exp)"
  assumes "\<And> b. P1 (Bool b)"
  assumes "\<And> scrut e1 e2. P1 scrut \<Longrightarrow> P1 e1 \<Longrightarrow> P1 e2 \<Longrightarrow> P1 (scrut ? e1 : e2)"
  assumes "P2 []"
  assumes "\<And>var exp \<Gamma>. P1 exp \<Longrightarrow> P2 \<Gamma> \<Longrightarrow> P2 ((var, exp)#\<Gamma>)"
  shows "P1 e" and "P2 \<Gamma>"
proof-
  have "P1 e" and "P2 (asToHeap (heapToAssn \<Gamma>))"
    apply (induct rule: exp_assn.inducts[of P1 "\<lambda> assn. P2 (asToHeap assn)"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply (metis assms(3) Let_def heapToAssn_asToHeap )
    apply (metis assms(4))
    apply (metis assms(5))
    apply (metis assms(6))
    apply (metis assms(7) asToHeap.simps(1))
    apply (metis assms(8) asToHeap.simps(2))
    done
  thus "P1 e" and "P2 \<Gamma>" unfolding asToHeap_heapToAssn.
qed

lemma exp_heap_strong_induct[case_names Var App Let Lam Bool IfThenElse Nil Cons]:
  assumes "\<And>var c. P1 c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P1 c exp) \<Longrightarrow> P1 c (App exp var)"
  assumes "\<And>\<Gamma> exp c. atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c. P2 c \<Gamma>) \<Longrightarrow> (\<And>c. P1 c exp) \<Longrightarrow> P1 c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P1 c exp) \<Longrightarrow> P1 c (Lam [var]. exp)"
  assumes "\<And> b c. P1 c (Bool b)"
  assumes "\<And> scrut e1 e2 c. (\<And> c. P1 c scrut) \<Longrightarrow> (\<And> c. P1 c e1) \<Longrightarrow> (\<And> c. P1 c e2) \<Longrightarrow> P1 c (scrut ? e1 : e2)"
  assumes "\<And>c. P2 c []"
  assumes "\<And>var exp \<Gamma> c. (\<And>c. P1 c exp) \<Longrightarrow> (\<And>c. P2 c \<Gamma>) \<Longrightarrow> P2 c ((var,exp)#\<Gamma>)"
  fixes c :: "'a :: fs"
  shows "P1 c e" and "P2 c \<Gamma>"
proof-
  have "P1 c e" and "P2 c (asToHeap (heapToAssn \<Gamma>))"
    apply (induct rule: exp_assn.strong_induct[of P1 "\<lambda> c assn. P2 c (asToHeap assn)"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply (metis assms(3) set_bn_to_atom_domA Let_def heapToAssn_asToHeap )
    apply (metis assms(4))
    apply (metis assms(5))
    apply (metis assms(6))
    apply (metis assms(7) asToHeap.simps(1))
    apply (metis assms(8) asToHeap.simps(2))
    done
  thus "P1 c e" and "P2 c \<Gamma>" unfolding asToHeap_heapToAssn.
qed

subsubsection \<open>Nice induction rules\<close>

text \<open>
These rules can be used instead of the original induction rules, which require a separate
goal for @{typ assn}.
\<close>

lemma exp_induct[case_names Var App Let Lam Bool IfThenElse]:
  assumes "\<And>var. P (Var var)"
  assumes "\<And>exp var. P exp \<Longrightarrow> P (App exp var)"
  assumes "\<And>\<Gamma> exp. (\<And> x. x \<in> domA \<Gamma> \<Longrightarrow>  P (the (map_of \<Gamma> x))) \<Longrightarrow> P exp \<Longrightarrow> P (Let \<Gamma> exp)"
  assumes "\<And>var exp.  P exp \<Longrightarrow> P (Lam [var]. exp)"
  assumes "\<And> b. P (Bool b)"
  assumes "\<And> scrut e1 e2. P scrut \<Longrightarrow> P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (scrut ? e1 : e2)"
  shows "P exp"
  apply (rule exp_heap_induct[of P "\<lambda> \<Gamma>. (\<forall>x \<in> domA \<Gamma>. P (the (map_of \<Gamma> x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply (metis assms(5))
  apply (metis assms(6))
  apply auto
  done

lemma  exp_strong_induct_set[case_names Var App Let Lam Bool IfThenElse]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>\<Gamma> exp c.
    atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c x e. (x,e) \<in> set \<Gamma> \<Longrightarrow>  P c e) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  assumes "\<And>b c. P c (Bool b)"
  assumes "\<And>scrut e1 e2 c. (\<And> c. P c scrut) \<Longrightarrow> (\<And> c. P c e1) \<Longrightarrow> (\<And> c. P c e2) \<Longrightarrow> P c (scrut ? e1 : e2)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_heap_strong_induct(1)[of P "\<lambda> c \<Gamma>. (\<forall>(x,e) \<in> set \<Gamma>. P c e)"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3) split_conv)
  apply (metis assms(4))
  apply (metis assms(5))
  apply (metis assms(6))
  apply auto
  done


lemma  exp_strong_induct[case_names Var App Let Lam Bool IfThenElse]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>\<Gamma> exp c.
    atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c x. x \<in> domA \<Gamma> \<Longrightarrow>  P c (the (map_of \<Gamma> x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  assumes "\<And>b c. P c (Bool b)"
  assumes "\<And> scrut e1 e2 c. (\<And> c. P c scrut) \<Longrightarrow> (\<And> c. P c e1) \<Longrightarrow> (\<And> c. P c e2) \<Longrightarrow> P c (scrut ? e1 : e2)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_heap_strong_induct(1)[of P "\<lambda> c \<Gamma>. (\<forall>x \<in> domA \<Gamma>. P c (the (map_of \<Gamma> x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply (metis assms(5))
  apply (metis assms(6))
  apply auto
  done

subsubsection \<open>Testing alpha equivalence\<close>
              
lemma alpha_test:
  shows "Lam [x]. (Var x) = Lam [y]. (Var y)"
  by (simp add: Abs1_eq_iff fresh_at_base pure_fresh)

lemma alpha_test2:
  shows "let x be (Var x) in (Var x) = let y be (Var y) in (Var y)"
  by (simp add: fresh_Cons fresh_Nil Abs1_eq_iff fresh_Pair add: fresh_at_base pure_fresh)

lemma alpha_test3:
  shows "
    Let [(x, Var y), (y, Var x)] (Var x)
    =
    Let [(y, Var x), (x, Var y)] (Var y)" (is "Let ?la ?lb = _")
  by (simp add: bn_heapToAssn Abs1_eq_iff fresh_Pair fresh_at_base
                Abs_swap2[of "atom x" "(?lb, [(x, Var y), (y, Var x)])" "[atom x, atom y]" "atom y"])

subsubsection \<open>Free variables\<close>

lemma fv_supp_exp: "supp e = atom ` (fv (e::exp) :: var set)" and fv_supp_as: "supp as = atom ` (fv (as::assn) :: var set)"
  by (induction e and as rule:exp_assn.inducts)
     (auto simp add: fv_def exp_assn.supp supp_at_base pure_supp)

lemma fv_supp_heap: "supp (\<Gamma>::heap) = atom ` (fv \<Gamma> :: var set)"
  by (metis fv_def fv_supp_as supp_heapToAssn)

lemma fv_Lam[simp]: "fv (Lam [x]. e) = fv e - {x}"
  unfolding fv_def by (auto simp add: exp_assn.supp)
lemma fv_Var[simp]: "fv (Var x) = {x}"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base pure_supp)
lemma fv_App[simp]: "fv (App e x) = insert x (fv e)"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)
lemma fv_Let[simp]: "fv (Let \<Gamma> e) = (fv \<Gamma> \<union> fv e) - domA \<Gamma>"
  unfolding fv_def by (auto simp add: Let_supp exp_assn.supp supp_at_base set_bn_to_atom_domA)
lemma fv_Bool[simp]: "fv (Bool b) = {}"
  unfolding fv_def by (auto simp add: exp_assn.supp pure_supp)
lemma fv_IfThenElse[simp]: "fv (scrut ? e1 : e2)  = fv scrut \<union> fv e1 \<union> fv e2"
  unfolding fv_def by (auto simp add: exp_assn.supp)


lemma fv_delete_heap:
  assumes "map_of \<Gamma> x = Some e"
  shows "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> (fv (\<Gamma>, Var x) :: var set)"
proof-
  have "fv (delete x \<Gamma>) \<subseteq> fv \<Gamma>" by (metis fv_delete_subset)
  moreover
  have "(x,e) \<in> set \<Gamma>" by (metis assms map_of_SomeD)
  hence "fv e \<subseteq> fv \<Gamma>" by (metis assms domA_from_set map_of_fv_subset option.sel)
  moreover
  have "x \<in> fv (Var x)" by simp
  ultimately show ?thesis by auto
qed

subsubsection \<open>Lemmas helping with nominal definitions\<close>

lemma eqvt_lam_case:
  assumes "Lam [x]. e = Lam [x']. e'"
  assumes "\<And> \<pi> . supp (-\<pi>) \<sharp>* (fv (Lam [x]. e) :: var set) \<Longrightarrow>
                 supp \<pi> \<sharp>* (Lam [x]. e) \<Longrightarrow>
        F (\<pi> \<bullet> e) (\<pi> \<bullet> x) (Lam [x]. e) = F e x (Lam [x]. e)"
  shows "F e x (Lam [x]. e) = F e' x' (Lam [x']. e')"
proof-

  from assms(1)
  have "[[atom x]]lst. (e, x) = [[atom x']]lst. (e', x')" by auto
  then obtain p
    where "(supp (e, x) - {atom x}) \<sharp>* p"
    and [simp]: "p \<bullet> x = x'"
    and [simp]: "p \<bullet> e = e'"
    unfolding  Abs_eq_iff(3) alpha_lst.simps by auto

  from \<open>_ \<sharp>* p\<close>
  have *: "supp (-p) \<sharp>* (fv (Lam [x]. e) :: var set)"
    by (auto simp add: fresh_star_def fresh_def supp_finite_set_at_base supp_Pair fv_supp_exp fv_supp_heap supp_minus_perm)

  from \<open>_ \<sharp>* p\<close>
  have **: "supp p \<sharp>* Lam [x]. e"
    by (auto simp add: fresh_star_def fresh_def supp_Pair fv_supp_exp)

  have "F e x (Lam [x]. e) =  F (p \<bullet> e) (p \<bullet> x) (Lam [x]. e)" by (rule assms(2)[OF * **, symmetric])
  also have "\<dots> = F e' x' (Lam [x']. e')" by (simp add: assms(1))
  finally show ?thesis.
qed

(* Nice idea, but doesn't work well with extra arguments to the function

lemma eqvt_lam_case_eqvt:
  assumes "Lam [x]. e = Lam [x']. e'"
  assumes F_eqvt: "\<And> \<pi> e'. \<pi> \<bullet> F e x e' = F (\<pi> \<bullet> e) (\<pi> \<bullet> x) (\<pi> \<bullet> e')"
  assumes F_supp: "atom x \<sharp> F e x (Lam [x]. e)"
  shows "F e x (Lam [x]. e) = F e' x' (Lam [x']. e')"
using assms(1)
proof(rule eqvt_lam_case)
  have "eqvt F" unfolding eqvt_def by (rule, perm_simp, rule) so rry
  hence "supp (F e x (Lam [x]. e)) \<subseteq> supp e \<union> supp x \<union> supp (Lam [x]. e)" by (rule supp_fun_app_eqvt3)    
  with F_supp[unfolded fresh_def]
  have *: "supp (F e x (Lam [x]. e)) \<subseteq> supp (Lam [x]. e)" by (auto simp add: exp_assn.supp supp_at_base)

  fix \<pi> :: perm
  assume "supp \<pi> \<sharp>* Lam [x]. e" with *
  have "supp \<pi> \<sharp>* F e x (Lam [x]. e)" by (auto simp add: fresh_star_def fresh_def)
  hence "F e x (Lam [x]. e) = \<pi> \<bullet> (F e x (Lam [x]. e))" by (metis perm_supp_eq)
  also have "\<dots> =  F (\<pi> \<bullet> e) (\<pi> \<bullet> x) (\<pi> \<bullet> (Lam [x]. e))" by (simp add: F_eqvt)
  also have "\<pi> \<bullet> (Lam [x]. e) = (Lam [x]. e)" using `supp \<pi> \<sharp>* Lam [x]. e` by (metis perm_supp_eq)
  finally show "F (\<pi> \<bullet> e) (\<pi> \<bullet> x) (Lam [x]. e) = F e x (Lam [x]. e)"..
qed
*)

lemma eqvt_let_case:
  assumes "Let as body = Let as' body'"
  assumes "\<And> \<pi> .
    supp (-\<pi>) \<sharp>* (fv (Let as body) :: var set) \<Longrightarrow>
    supp \<pi> \<sharp>* Let as body \<Longrightarrow>
    F (\<pi> \<bullet> as) (\<pi> \<bullet> body) (Let as body) = F as body (Let as body)"
  shows "F as body (Let as body) = F as' body' (Let as' body')"
proof-
  from assms(1)
  have "[map (\<lambda> p. atom (fst p)) as]lst. (body, as) = [map (\<lambda> p. atom (fst p)) as']lst. (body', as')" by auto
  then obtain p
    where "(supp (body, as) - atom ` domA as) \<sharp>* p"
    and [simp]: "p \<bullet> body = body'"
    and [simp]: "p \<bullet> as = as'"
    unfolding  Abs_eq_iff(3) alpha_lst.simps by (auto simp add: domA_def image_image)

  from \<open>_ \<sharp>* p\<close>
  have *: "supp (-p) \<sharp>* (fv (Terms.Let as body) :: var set)"
    by (auto simp add: fresh_star_def fresh_def supp_finite_set_at_base supp_Pair fv_supp_exp fv_supp_heap supp_minus_perm)

  from \<open>_ \<sharp>* p\<close>
  have **: "supp p \<sharp>* Terms.Let as body"
    by (auto simp add: fresh_star_def fresh_def supp_Pair fv_supp_exp fv_supp_heap )

  have "F as body (Let as body) =  F (p \<bullet> as) (p \<bullet> body) (Let as body)" by (rule assms(2)[OF * **, symmetric])
  also have "\<dots> = F as' body' (Let as' body')" by (simp add: assms(1))
  finally show ?thesis.
qed

subsubsection \<open>A smart constructor for lets\<close>

text \<open>
Certian program transformations might change the bound variables, possibly making it an empty list.
This smart constructor avoids the empty let in the resulting expression. Semantically, it should
not make a difference. 
\<close>

definition SmartLet :: "heap => exp => exp"
  where "SmartLet \<Gamma> e = (if \<Gamma> = [] then e else Let \<Gamma> e)"

lemma SmartLet_eqvt[eqvt]: "\<pi> \<bullet> (SmartLet \<Gamma> e) = SmartLet (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding SmartLet_def by perm_simp rule

lemma SmartLet_supp:
  "supp (SmartLet \<Gamma> e) = (supp e \<union> supp \<Gamma>) - atom ` (domA \<Gamma>)"
  unfolding SmartLet_def using Let_supp by (auto simp add: supp_Nil)

lemma fv_SmartLet[simp]: "fv (SmartLet \<Gamma> e) = (fv \<Gamma> \<union> fv e) - domA \<Gamma>"
  unfolding SmartLet_def by auto

subsubsection \<open>A predicate for value expressions\<close>

nominal_function isLam :: "exp \<Rightarrow> bool" where
  "isLam (Var x) = False" |
  "isLam (Lam [x]. e) = True" |
  "isLam (App e x) = False" |
  "isLam (Let as e) = False" |
  "isLam (Bool b) = False" |
  "isLam (scrut ? e1 : e2) = False"
  unfolding isLam_graph_aux_def eqvt_def
  apply simp
  apply simp
  apply (metis exp_strong_exhaust)
  apply auto
  done
nominal_termination (eqvt) by lexicographic_order

lemma isLam_Lam: "isLam (Lam [x]. e)" by simp

lemma isLam_obtain_fresh:
  assumes "isLam z"
  obtains y e'
  where "z = (Lam [y]. e')" and "atom y \<sharp> (c::'a::fs)"
using assms by (nominal_induct z avoiding: c rule:exp_strong_induct) auto

nominal_function isVal :: "exp \<Rightarrow> bool" where
  "isVal (Var x) = False" |
  "isVal (Lam [x]. e) = True" |
  "isVal (App e x) = False" |
  "isVal (Let as e) = False" |
  "isVal (Bool b) = True" |
  "isVal (scrut ? e1 : e2) = False"
  unfolding isVal_graph_aux_def eqvt_def
  apply simp
  apply simp
  apply (metis exp_strong_exhaust)
  apply auto
  done
nominal_termination (eqvt) by lexicographic_order

lemma isVal_Lam: "isVal (Lam [x]. e)" by simp
lemma isVal_Bool: "isVal (Bool b)" by simp


subsubsection \<open>The notion of thunks\<close>
(*
fun thunks :: "heap \<Rightarrow> var set" where
  "thunks [] = {}"
  | "thunks ((x,e)#\<Gamma>) = (if isLam e then {} else {x}) \<union> thunks \<Gamma>"
*)

definition thunks :: "heap \<Rightarrow> var set" where
  "thunks \<Gamma> = {x . case map_of \<Gamma> x of Some e \<Rightarrow> \<not> isVal e | None \<Rightarrow> False}"

lemma thunks_Nil[simp]: "thunks [] = {}" by (auto simp add: thunks_def)

lemma thunks_domA: "thunks \<Gamma> \<subseteq> domA \<Gamma>"
  by (induction \<Gamma> ) (auto simp add: thunks_def)

lemma thunks_Cons: "thunks ((x,e)#\<Gamma>) = (if isVal e then thunks \<Gamma> - {x} else insert x (thunks \<Gamma>))"
  by (auto simp add: thunks_def )

lemma thunks_append[simp]: "thunks (\<Delta>@\<Gamma>) = thunks \<Delta> \<union> (thunks \<Gamma> - domA \<Delta>)"
  by (induction \<Delta>) (auto simp add: thunks_def )

lemma thunks_delete[simp]: "thunks (delete x \<Gamma>) = thunks \<Gamma> - {x}"
  by (induction \<Gamma>) (auto simp add: thunks_def )

lemma thunksI[intro]: "map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isVal e \<Longrightarrow> x \<in> thunks \<Gamma>"
  by (induction \<Gamma>) (auto simp add: thunks_def )

lemma thunksE[intro]: "x \<in> thunks \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isVal e"
  by (induction \<Gamma>) (auto simp add: thunks_def )

lemma thunks_cong: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> thunks \<Gamma> = thunks \<Delta>"
  by (simp add: thunks_def)

lemma thunks_eqvt[eqvt]:
  "\<pi> \<bullet> thunks \<Gamma> = thunks (\<pi> \<bullet> \<Gamma>)"
    unfolding thunks_def
    by perm_simp rule

subsubsection \<open>Non-recursive Let bindings\<close>

definition nonrec :: "heap \<Rightarrow> bool" where
  "nonrec \<Gamma> = (\<exists> x e. \<Gamma> = [(x,e)] \<and> x \<notin> fv e)"


lemma nonrecE:
  assumes "nonrec \<Gamma>"
  obtains x e where "\<Gamma> = [(x,e)]" and "x \<notin> fv e"
  using assms
  unfolding nonrec_def
  by blast

lemma nonrec_eqvt[eqvt]:
  "nonrec \<Gamma> \<Longrightarrow> nonrec (\<pi> \<bullet> \<Gamma>)"
  apply (erule nonrecE)
  apply (auto simp add: nonrec_def fv_def fresh_def )
  apply (metis fresh_at_base_permute_iff fresh_def)
  done

lemma exp_induct_rec[case_names Var App Let Let_nonrec Lam Bool IfThenElse]:
  assumes "\<And>var. P (Var var)"
  assumes "\<And>exp var. P exp \<Longrightarrow> P (App exp var)"
  assumes "\<And>\<Gamma> exp. \<not> nonrec \<Gamma> \<Longrightarrow> (\<And> x. x \<in> domA \<Gamma> \<Longrightarrow>  P (the (map_of \<Gamma> x))) \<Longrightarrow> P exp \<Longrightarrow> P (Let \<Gamma> exp)"
  assumes "\<And>x e exp. x \<notin> fv e \<Longrightarrow> P e \<Longrightarrow> P exp \<Longrightarrow> P (let x be e in exp)"
  assumes "\<And>var exp.  P exp \<Longrightarrow> P (Lam [var]. exp)"
  assumes "\<And>b. P (Bool b)"
  assumes "\<And> scrut e1 e2. P scrut \<Longrightarrow> P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (scrut ? e1 : e2)"
  shows "P exp"
  apply (rule exp_induct[of P])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (case_tac "nonrec \<Gamma>")
  apply (erule nonrecE)
  apply simp
  apply (metis assms(4))
  apply (metis assms(3))
  apply (metis assms(5))
  apply (metis assms(6))
  apply (metis assms(7))
  done

lemma  exp_strong_induct_rec[case_names Var App Let Let_nonrec Lam Bool IfThenElse]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>\<Gamma> exp c.
    atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> \<not> nonrec \<Gamma> \<Longrightarrow> (\<And>c x. x \<in> domA \<Gamma> \<Longrightarrow>  P c (the (map_of \<Gamma> x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Let \<Gamma> exp)"
  assumes "\<And>x e exp c. {atom x} \<sharp>* c \<Longrightarrow> x \<notin> fv e \<Longrightarrow> (\<And> c. P c e) \<Longrightarrow> (\<And> c. P c exp) \<Longrightarrow> P c (let x be e in exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  assumes "\<And>b c. P c (Bool b)"
  assumes "\<And> scrut e1 e2 c. (\<And> c. P c scrut) \<Longrightarrow> (\<And> c. P c e1) \<Longrightarrow> (\<And> c. P c e2) \<Longrightarrow> P c (scrut ? e1 : e2)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_strong_induct[of P])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (case_tac "nonrec \<Gamma>")
  apply (erule nonrecE)
  apply simp
  apply (metis assms(4))
  apply (metis assms(3))
  apply (metis assms(5))
  apply (metis assms(6))
  apply (metis assms(7))
  done

lemma  exp_strong_induct_rec_set[case_names Var App Let Let_nonrec Lam Bool IfThenElse]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>\<Gamma> exp c.
    atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> \<not> nonrec \<Gamma> \<Longrightarrow> (\<And>c x e. (x,e) \<in> set \<Gamma> \<Longrightarrow>  P c e) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Let \<Gamma> exp)"
  assumes "\<And>x e exp c. {atom x} \<sharp>* c \<Longrightarrow> x \<notin> fv e \<Longrightarrow> (\<And> c. P c e) \<Longrightarrow> (\<And> c. P c exp) \<Longrightarrow> P c (let x be e in exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  assumes "\<And>b c. P c (Bool b)"
  assumes "\<And> scrut e1 e2 c. (\<And> c. P c scrut) \<Longrightarrow> (\<And> c. P c e1) \<Longrightarrow> (\<And> c. P c e2) \<Longrightarrow> P c (scrut ? e1 : e2)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_strong_induct_set(1)[of P])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (case_tac "nonrec \<Gamma>")
  apply (erule nonrecE)
  apply simp
  apply (metis assms(4))
  apply (metis assms(3))
  apply (metis assms(5))
  apply (metis assms(6))
  apply (metis assms(7))
  done



subsubsection \<open>Renaming a lambda-bound variable\<close>

lemma change_Lam_Variable:
  assumes "y' \<noteq> y \<Longrightarrow> atom y' \<sharp> (e,  y)"
  shows   "Lam [y]. e =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)"
proof(cases "y' = y")
  case True thus ?thesis by simp
next
  case False
  from assms[OF this]
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e) = Lam [y]. e"
    by -(rule flip_fresh_fresh, (simp add: fresh_Pair)+)
  moreover
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e) = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)"
    by simp
  ultimately
  show "Lam [y]. e =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)" by (simp add: fresh_Pair)
qed


end
