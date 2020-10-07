(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>, 2003
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>Widening the Direct Subtype Relation\<close>

theory Subtype
imports "../Isa_Counter/DirectSubtypes"
begin

text \<open>
In this theory, we define the widening subtype relation of types and prove 
that it is a partial order.
\<close>

subsection \<open>Auxiliary lemmas\<close>

text \<open>These general lemmas are not especially related to Jive. 
They capture
some useful properties of general relations. 
\<close>
lemma distinct_rtrancl_into_trancl:
  assumes neq_x_y: "x\<noteq>y"
  assumes x_y_rtrancl: "(x,y) \<in> r\<^sup>*"
  shows "(x,y) \<in> r\<^sup>+"
  using x_y_rtrancl neq_x_y
proof (induct)
  assume "x\<noteq>x" thus "(x, x) \<in> r\<^sup>+" by simp
next
  fix y z
  assume x_y_rtrancl: "(x, y) \<in> r\<^sup>*" 
  assume y_z_r: "(y, z) \<in> r" 
  assume "x \<noteq> y \<Longrightarrow> (x, y) \<in> r\<^sup>+" 
  assume "x \<noteq> z"
  from x_y_rtrancl
  show "(x, z) \<in> r\<^sup>+"
  proof (cases)
    assume "x=y"
    with y_z_r have "(x,z) \<in> r" by simp
    thus "(x,z) \<in>  r\<^sup>+"..
  next
    fix w
    assume "(x, w) \<in> r\<^sup>*"
    moreover assume "(w, y) \<in> r"
    ultimately have "(x,y) \<in> r\<^sup>+"
      by (rule rtrancl_into_trancl1)
    from this y_z_r
    show "(x, z) \<in> r\<^sup>+"..
  qed
qed

lemma acyclic_imp_antisym_rtrancl: "acyclic r \<Longrightarrow> antisym (r\<^sup>*)"
proof (clarsimp simp only: acyclic_def antisym_def)
  fix x y
  assume acyclic: "\<forall>x. (x, x) \<notin> r\<^sup>+"
  assume x_y: "(x, y) \<in> r\<^sup>*" 
  assume y_x: "(y, x) \<in> r\<^sup>*"
  show "x=y"
  proof (cases "x=y")
    case True thus ?thesis .
  next
    case False
    from False x_y have "(x, y) \<in> r\<^sup>+"
      by (rule distinct_rtrancl_into_trancl)
    also
    from False y_x have "(y, x) \<in> r\<^sup>+"
      by (fastforce intro: distinct_rtrancl_into_trancl)
    finally have "(x,x) \<in> r\<^sup>+".
    with acyclic show ?thesis by simp
  qed
qed

lemma acyclic_trancl_rtrancl: 
  assumes acyclic: "acyclic r"
  shows "(x,y) \<in> r\<^sup>+ = ((x,y) \<in> r\<^sup>* \<and> x\<noteq>y)"
proof
  assume x_y_trancl: "(x,y) \<in> r\<^sup>+"
  show "(x,y) \<in> r\<^sup>* \<and> x\<noteq>y"
  proof
    from x_y_trancl show "(x,y) \<in> r\<^sup>*"..
  next
    from x_y_trancl acyclic show "x\<noteq>y" by (auto simp add: acyclic_def)
  qed
next
  assume "(x,y) \<in> r\<^sup>* \<and> x\<noteq>y"
  thus "(x,y) \<in> r\<^sup>+"
    by (auto intro: distinct_rtrancl_into_trancl)
qed


subsection \<open>The Widening (Subtype) Relation of Javatypes\<close>


text \<open>\label{widening_subtypes}
In this section we widen the direct subtype relations specified in Sec. 
\ref{direct_subtype_relations}.
It is done by a calculation of the transitive closure of the 
direct subtype relation. 
\<close>

text \<open>This is the concrete syntax that expresses the subtype relations 
between all types. 
\label{subtype_relations_concrete_syntax}\<close>

abbreviation
  direct_subtype_syntax :: "Javatype \<Rightarrow> Javatype \<Rightarrow> bool" ("_ \<prec>1 _" [71,71] 70)
where \<comment> \<open>direct subtype relation\<close>
  "A \<prec>1 B == (A,B) \<in> direct_subtype"

abbreviation
  widen_syntax :: "Javatype \<Rightarrow> Javatype \<Rightarrow> bool" ("_ \<preceq> _" [71,71] 70)
where \<comment> \<open>reflexive transitive closure of direct subtype relation\<close>
  "A \<preceq> B == (A,B) \<in> direct_subtype\<^sup>*"

abbreviation
  widen_strict_syntax :: "Javatype \<Rightarrow> Javatype \<Rightarrow> bool" ("_ \<prec> _" [71,71] 70)
where \<comment> \<open>transitive closure of direct subtype relation\<close>
  "A \<prec> B == (A,B) \<in> direct_subtype\<^sup>+"


subsection \<open>The Subtype Relation as Partial Order\<close>

text \<open>We prove the axioms required for partial orders, i.e.\ 
reflexivity, transitivity and antisymmetry, for the widened subtype
relation. The direct subtype relation has been
defined in Sec. \ref{direct_subtype_relations}.
The reflexivity lemma is
added to the Simplifier and to the Classical reasoner (via the
attribute iff), and the transitivity and antisymmetry lemmas
are made known as transitivity rules (via the attribute trans).
This way, these lemmas will be automatically used in subsequent proofs.
\<close>

lemma acyclic_direct_subtype: "acyclic direct_subtype"
proof (clarsimp simp add: acyclic_def)
  fix x show "x \<prec> x \<Longrightarrow> False"
  by (cases x) (fastforce elim: tranclE simp add: direct_subtype_def)+
     (* takes a very long time to calculate *)
qed

lemma antisym_rtrancl_direct_subtype: "antisym (direct_subtype\<^sup>*)"
using acyclic_direct_subtype by (rule acyclic_imp_antisym_rtrancl)

lemma widen_strict_to_widen: "C \<prec> D = (C \<preceq> D \<and> C\<noteq>D)"
using acyclic_direct_subtype by (rule acyclic_trancl_rtrancl)

text \<open>The widening relation on Javatype is reflexive.\<close>

lemma widen_refl [iff]: "X \<preceq> X" ..

text \<open>The widening relation on Javatype is transitive.\<close>

lemma widen_trans [trans] : 
  assumes a_b: "a \<preceq> b"
  shows "\<And> c. b \<preceq> c \<Longrightarrow> a \<preceq> c"
  by (insert a_b, rule rtrancl_trans)

text \<open>The widening relation on Javatype is antisymmetric.\<close>

lemma widen_antisym [trans]: 
  assumes a_b: "a \<preceq> b" 
  assumes b_c: "b \<preceq> a"  
  shows "a = b"
  using a_b b_c antisym_rtrancl_direct_subtype
  by (unfold antisym_def) blast


subsection \<open>Javatype Ordering Properties\<close>

text \<open>The type class @{term ord} allows us to overwrite the two comparison 
operators $<$ and $\leq$.
  These are  the two comparison operators on @{typ Javatype} that we want
to use subsequently.\<close>

text \<open>We can also prove that @{typ Javatype} is in the type class @{term order}. 
For this we
  have to prove reflexivity, transitivity, antisymmetry and that $<$ and $\leq$ are 
defined in such
  a way that @{thm Orderings.order_less_le [no_vars]} holds. This proof can easily 
be achieved by using the
  lemmas proved above and the definition of @{term less_Javatype_def}.
\<close>

instantiation Javatype:: order
begin

definition
  le_Javatype_def:   "A \<le> B \<equiv> A \<preceq> B"

definition
  less_Javatype_def: "A < B \<equiv> A \<le> B \<and> \<not> B \<le> (A::Javatype)"
  
instance proof
  fix x y z:: "Javatype"
  {
    show "x \<le> x"
      by (simp add: le_Javatype_def )
  next
    assume "x \<le> y" "y \<le> z"
    then show "x \<le> z"
      by (unfold le_Javatype_def) (rule rtrancl_trans) 
  next
    assume "x \<le> y" "y \<le> x" 
    then show "x = y"
      apply (unfold le_Javatype_def) 
      apply (rule widen_antisym) 
      apply assumption +
      done
  next
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (simp add: less_Javatype_def)
  }
qed

end


subsection \<open>Enhancing the Simplifier\<close>

lemmas subtype_defs = le_Javatype_def less_Javatype_def
                      direct_subtype_def 
(*
                      direct_subtype
                      direct_subtype[THEN r_into_rtrancl]
*)
lemmas subtype_ok_simps = subtype_defs 
lemmas subtype_wrong_elims = rtranclE

text \<open>During verification we will often have to solve the goal that one type
widens to the other. So we equip the simplifier with a special solver-tactic.
\<close>

lemma widen_asm: "(a::Javatype) \<le> b \<Longrightarrow> a \<le> b"
  by simp

lemmas direct_subtype_widened = direct_subtype[THEN r_into_rtrancl]

ML \<open>
local val ss = simpset_of @{context} in

fun widen_tac ctxt =
  resolve_tac ctxt @{thms widen_asm} THEN'
  simp_tac (put_simpset ss ctxt addsimps @{thms le_Javatype_def}) THEN'
  Method.insert_tac ctxt @{thms direct_subtype_widened} THEN'
  simp_tac (put_simpset (simpset_of @{theory_context Transitive_Closure}) ctxt)

end
\<close>

declaration \<open>fn _ =>
  Simplifier.map_ss (fn ss => ss addSolver (mk_solver "widen" widen_tac))
\<close>


text \<open>In this solver-tactic, we first try the trivial resolution with \<open>widen_asm\<close> to
check if the actual subgaol really is a request to solve a subtyping problem.
If so, we unfold the comparison operator, insert the direct subtype
relations and call the simplifier.
\<close>


subsection \<open>Properties of the Subtype Relation\<close>


text \<open>The class \<open>Object\<close> has to be the root of the class hierarchy, 
i.e.~it is supertype of each concrete class, abstract class, interface
and array type.
  The proof scripts should run on every correctly generated type hierarchy.
\<close>


lemma Object_root: "CClassT C \<le> CClassT Object"
  by (cases C, simp_all)

lemma Object_root_abs: "AClassT C \<le> CClassT Object"
  by (cases C, simp_all)

lemma Object_root_int: "InterfaceT C \<le> CClassT Object"
  by (cases C, simp_all)

lemma Object_root_array: "ArrT C \<le> CClassT Object"
  proof (cases C)
    fix x
    assume c: "C = CClassAT x"
    show "ArrT C \<le> CClassT Object"
      using c by (cases x, simp_all)
  next
    fix x
    assume c: "C = AClassAT x"
    show "ArrT C \<le> CClassT Object"
      using c by (cases x, simp_all)
  next
    fix x
    assume c: "C = InterfaceAT x"
    show "ArrT C \<le> CClassT Object"
      using c by (cases x, simp_all)
  next
    assume c: "C = BoolAT"
    show "ArrT C \<le> CClassT Object"
      using c by simp
  next
    assume c: "C = IntgAT"
    show "ArrT C \<le> CClassT Object"
      using c by simp
  next
    assume c: "C = ShortAT"
    show "ArrT C \<le> CClassT Object"
      using c by simp
  next
    assume c: "C = ByteAT"
    show "ArrT C \<le> CClassT Object"
      using c by simp
qed

text \<open>If another type is (non-strict) supertype of Object, 
then it must be the type Object itself.\<close>

lemma Object_rootD: 
  assumes p: "CClassT Object \<le> c"
  shows "CClassT Object = c"
  using p
  apply (cases c)
  apply (fastforce elim: subtype_wrong_elims simp add: subtype_defs) +
  \<comment> \<open>In this lemma, we only get contradictory cases except for Object itself.\<close>
done

text \<open>The type NullT has to be the leaf of each branch of the class
hierarchy, i.e.~it is subtype of each type.\<close>

lemma NullT_leaf [simp]: "NullT \<le> CClassT C"
  by (cases C, simp_all)

lemma NullT_leaf_abs [simp]: "NullT \<le> AClassT C"
  by (cases C, simp_all)

lemma NullT_leaf_int [simp]: "NullT \<le> InterfaceT C"
  by (cases C, simp_all)

lemma NullT_leaf_array: "NullT \<le> ArrT C"
  proof (cases C)
    fix x
    assume c: "C = CClassAT x"
    show "NullT \<le> ArrT C"
      using c by (cases x, simp_all)
  next
    fix x
    assume c: "C = AClassAT x"
    show "NullT \<le> ArrT C"
      using c by (cases x, simp_all)
  next
    fix x
    assume c: "C = InterfaceAT x"
    show "NullT \<le> ArrT C"
      using c by (cases x, simp_all)
  next
    assume c: "C = BoolAT"
    show "NullT \<le> ArrT C"
      using c by simp
  next
    assume c: "C = IntgAT"
    show "NullT \<le> ArrT C"
      using c by simp
  next
    assume c: "C = ShortAT"
    show "NullT \<le> ArrT C"
      using c by simp
  next
    assume c: "C = ByteAT"
    show "NullT \<le> ArrT C"
      using c by simp
qed

end
