theory Substitution
imports Terms
begin

text \<open>Defining a substitution function on terms turned out to be slightly tricky.\<close>

fun
  subst_var :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" ("_[_::v=_]" [1000,100,100] 1000)
where "x[y ::v= z] = (if x = y then z else x)"

nominal_function  (default "case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)",
                  invariant "\<lambda> a r . (\<forall> \<Gamma> y z . ((a = Inr (\<Gamma>, y, z) \<and> atom ` domA \<Gamma> \<sharp>* (y, z)) \<longrightarrow> map (\<lambda>x . atom (fst x))  (Sum_Type.projr r) = map (\<lambda>x . atom (fst x)) \<Gamma>))")
  subst :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_::=_]" [1000,100,100] 1000)
and
  subst_heap :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> heap" ("_[_::h=_]" [1000,100,100] 1000)
where
   "(Var x)[y ::= z] = Var (x[y ::v= z])"
 | "(App e v)[y ::= z] = App (e[y ::= z]) (v[y ::v= z])"
 | "atom ` domA \<Gamma> \<sharp>* (y,z) \<Longrightarrow>
     (Let \<Gamma> body)[y ::= z] = Let (\<Gamma>[y ::h= z]) (body[y ::= z])" 
 | "atom x \<sharp> (y,z) \<Longrightarrow> (Lam [x].e)[y ::= z] = Lam [x].(e[y::=z])"
 | "(Bool b)[y ::= z] = Bool b"
 | "(scrut ? e1 : e2)[y ::= z] = (scrut[y ::= z] ? e1[y ::= z] : e2[y ::= z])"
 | "[][y ::h= z] = []"
 | "((v,e)# \<Gamma>)[y ::h= z] = (v, e[y ::= z])# (\<Gamma>[y ::h= z])"
proof goal_cases

have eqvt_at_subst: "\<And> e y z . eqvt_at subst_subst_heap_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst a b c) (e, y, z)"
  apply(simp add: eqvt_at_def subst_def)
  apply(rule)
  apply(subst Projl_permute)
  apply(thin_tac _)+
  apply (simp add: subst_subst_heap_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_heap_graph (Inl (e, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_heap_graph.cases)
  apply(assumption)
  apply(rule_tac x="Sum_Type.projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: sum.sel)
  apply(rule_tac x="Sum_Type.projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: sum.sel)
  apply(rule_tac x="Sum_Type.projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: sum.sel)
  apply(rule_tac x="Sum_Type.projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: sum.sel)
  apply(rule_tac x="Sum_Type.projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: sum.sel)
  apply(rule_tac x="Sum_Type.projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: sum.sel)
  apply (metis Inr_not_Inl)
  apply (metis Inr_not_Inl)
  apply(simp)
  apply(perm_simp)
  apply(simp)
done

have eqvt_at_subst_heap: "\<And> \<Gamma> y z . eqvt_at subst_subst_heap_sumC (Inr (\<Gamma>, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_heap a b c) (\<Gamma>, y, z)"
  apply(simp add: eqvt_at_def subst_heap_def)
  apply(rule)
  apply(subst Projr_permute)
  apply(thin_tac _)+
  apply (simp add: subst_subst_heap_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_heap_graph (Inr (\<Gamma>, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_heap_graph.cases)
  apply(assumption)
  apply (metis (mono_tags) Inr_not_Inl)+
  apply(rule_tac x="Sum_Type.projr x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply auto[1]
  apply(simp (no_asm) only: sum.sel)
  
  apply(rule_tac x="Sum_Type.projr x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply auto[1]
  apply(simp (no_asm) only: sum.sel)
  
  apply(simp)
  apply(perm_simp)
  apply(simp)
done

{
(* Equivariance of the graph *)
case 1 thus ?case
  unfolding eqvt_def subst_subst_heap_graph_aux_def
  by simp

(* The invariant *)
next case 2 thus ?case
  by (induct rule: subst_subst_heap_graph.induct)(auto simp add: exp_assn.bn_defs fresh_star_insert)

(* Exhaustiveness *)
next case prems: (3 P x) show ?case
  proof(cases x)
  case (Inl a) thus P
    proof(cases a)
    case (fields a1 a2 a3)
    thus P using Inl prems
      apply (rule_tac y ="a1" and c ="(a2, a3)" in exp_strong_exhaust)
      apply (auto simp add: fresh_star_def)
    done
  qed
  next
  case (Inr a) thus P
    proof (cases a)
    case (fields a1 a2 a3)
    thus P using Inr prems
      by (metis heapToAssn.cases)
  qed
qed

next case (19 e y2 z2 \<Gamma> e2 y z as2) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (drule eqvt_at_subst_heap)+
  apply (simp only: meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff]
    meta_eq_to_obj_eq[OF subst_heap_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (auto simp add: Abs_fresh_iff)
  apply (drule_tac
    c = "(y, z)" and
    as = "(map (\<lambda>x. atom (fst x)) e)" and
    bs = "(map (\<lambda>x. atom (fst x)) e2)" and
    f = "\<lambda> a b c . [a]lst. (subst (fst b) y z, subst_heap (snd b) y z )" in Abs_lst_fcb2)
  apply (simp add: perm_supp_eq fresh_Pair fresh_star_def Abs_fresh_iff)
  apply (metis domA_def image_image image_set)
  apply (metis domA_def image_image image_set)
  apply (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  apply (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  apply (simp add: eqvt_at_def)
  done

next case (25 x2 y2 z2 e2 x y z e) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (simp only: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (simp add: eqvt_at_def)
  apply rule
  apply (erule_tac x = "(x2 \<leftrightarrow> c)" in allE)
  apply (erule_tac x = "(x \<leftrightarrow> c)" in allE)
  apply auto
  done
}
qed(auto)

nominal_termination (eqvt) by lexicographic_order

lemma shows
  True and bn_subst[simp]: "domA (subst_heap \<Gamma> y z) = domA \<Gamma>"
by(induct rule:subst_subst_heap.induct)
  (auto simp add: exp_assn.bn_defs fresh_star_insert)


lemma subst_noop[simp]:
shows "e[y ::= y] = e" and "\<Gamma>[y::h=y]= \<Gamma>"
by(induct e y y and \<Gamma> y y rule:subst_subst_heap.induct)
  (auto simp add:fresh_star_Pair exp_assn.bn_defs)

lemma subst_is_fresh[simp]:
assumes "atom y \<sharp> z"
shows
  "atom y \<sharp> e[y ::= z]"
and
 "atom ` domA \<Gamma> \<sharp>* y \<Longrightarrow> atom y \<sharp> \<Gamma>[y::h=z]"
using assms
by(induct e y z and \<Gamma> y z rule:subst_subst_heap.induct)
  (auto simp add:fresh_at_base fresh_star_Pair fresh_star_insert fresh_Nil fresh_Cons pure_fresh)

lemma
 subst_pres_fresh: "atom x \<sharp> e \<or> x = y \<Longrightarrow> atom x \<sharp> z \<Longrightarrow> atom x \<sharp> e[y ::= z]"
and
 "atom x \<sharp> \<Gamma> \<or> x = y \<Longrightarrow> atom x \<sharp> z \<Longrightarrow> x \<notin> domA \<Gamma> \<Longrightarrow> atom x \<sharp> (\<Gamma>[y ::h= z])"
by(induct e y z and \<Gamma> y z rule:subst_subst_heap.induct)
  (auto simp add:fresh_star_Pair exp_assn.bn_defs fresh_Cons fresh_Nil pure_fresh)

lemma subst_fresh_noop: "atom x \<sharp> e \<Longrightarrow> e[x ::= y] = e"
  and subst_heap_fresh_noop: "atom x \<sharp> \<Gamma> \<Longrightarrow>  \<Gamma>[x ::h= y] = \<Gamma>"
by (nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_def fresh_Pair fresh_at_base fresh_Cons simp del: exp_assn.eq_iff)

lemma supp_subst_eq: "supp (e[y::=x]) = (supp e - {atom y}) \<union> (if atom y \<in> supp e then {atom x} else {})"
  and  "atom ` domA \<Gamma> \<sharp>* y \<Longrightarrow> supp (\<Gamma>[y::h=x]) = (supp \<Gamma> - {atom y}) \<union> (if atom y \<in> supp \<Gamma> then {atom x} else {})"
by (nominal_induct  e  and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
   (auto simp add: fresh_star_def fresh_Pair supp_Nil supp_Cons supp_Pair fresh_Cons exp_assn.supp Let_supp supp_at_base pure_supp simp del: exp_assn.eq_iff)

lemma supp_subst: "supp (e[y::=x]) \<subseteq> (supp e - {atom y}) \<union> {atom x}"
  using supp_subst_eq by auto

lemma fv_subst_eq: "fv (e[y::=x]) = (fv e - {y}) \<union> (if y \<in> fv e then {x} else {})"
  and  "atom ` domA \<Gamma> \<sharp>* y \<Longrightarrow> fv (\<Gamma>[y::h=x]) = (fv \<Gamma> - {y}) \<union> (if y \<in> fv \<Gamma> then {x} else {})"
by (nominal_induct  e  and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
   (auto simp add: fresh_star_def fresh_Pair supp_Nil supp_Cons supp_Pair fresh_Cons exp_assn.supp Let_supp supp_at_base simp del: exp_assn.eq_iff)

lemma fv_subst_subset: "fv (e[y ::= x]) \<subseteq> (fv e - {y}) \<union> {x}"
  using fv_subst_eq by auto

lemma fv_subst_int: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> fv (e[y ::= x]) \<inter> S = fv e \<inter> S"
  by (auto simp add: fv_subst_eq)

lemma fv_subst_int2: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> S \<inter> fv (e[y ::= x]) = S \<inter> fv e"
  by (auto simp add: fv_subst_eq)

lemma subst_swap_same: "atom x \<sharp> e \<Longrightarrow>  (x \<leftrightarrow> y) \<bullet> e = e[y ::=x]"
  and "atom x \<sharp> \<Gamma> \<Longrightarrow> atom `domA \<Gamma> \<sharp>* y \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> \<Gamma> = \<Gamma>[y ::h= x]"
by (nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
   (auto simp add: fresh_star_Pair fresh_star_at_base fresh_Cons pure_fresh permute_pure simp del: exp_assn.eq_iff)

lemma subst_subst_back: "atom x \<sharp> e \<Longrightarrow>  e[y::=x][x::=y] = e" 
  and "atom x \<sharp> \<Gamma> \<Longrightarrow> atom `domA \<Gamma> \<sharp>* y  \<Longrightarrow> \<Gamma>[y::h=x][x::h=y] = \<Gamma>"
by(nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_Pair fresh_star_at_base fresh_star_Cons fresh_Cons  exp_assn.bn_defs simp del: exp_assn.eq_iff)

lemma subst_heap_delete[simp]: "(delete x \<Gamma>)[y ::h= z] = delete x (\<Gamma>[y ::h= z])"
  by (induction \<Gamma>) auto

lemma subst_nil_iff[simp]: "\<Gamma>[x ::h= z] = [] \<longleftrightarrow> \<Gamma> = []"
  by (cases \<Gamma>) auto

lemma subst_SmartLet[simp]:
  "atom ` domA \<Gamma> \<sharp>* (y,z) \<Longrightarrow> (SmartLet \<Gamma> body)[y ::= z] = SmartLet (\<Gamma>[y ::h= z]) (body[y ::= z])"
  unfolding SmartLet_def by auto

lemma subst_let_be[simp]:
  "atom x'  \<sharp> y \<Longrightarrow> atom x' \<sharp> x \<Longrightarrow> (let x' be e in exp )[y::=x] = (let x' be e[y::=x] in exp[y::=x])"
  by (simp add: fresh_star_def fresh_Pair)

lemma isLam_subst[simp]: "isLam e[x::=y] = isLam e"
  by (nominal_induct e avoiding: x y  rule: exp_strong_induct)
     (auto simp add: fresh_star_Pair)

lemma isVal_subst[simp]: "isVal e[x::=y] = isVal e"
  by (nominal_induct e avoiding: x y  rule: exp_strong_induct)
     (auto simp add: fresh_star_Pair)

lemma thunks_subst[simp]:
  "thunks \<Gamma>[y::h=x] = thunks \<Gamma>"
  by (induction \<Gamma>) (auto simp add: thunks_Cons)

lemma map_of_subst:
  "map_of (\<Gamma>[x::h=y]) k = map_option (\<lambda> e . e[x::=y]) (map_of \<Gamma> k)"
by (induction \<Gamma> ) auto

lemma mapCollect_subst[simp]:
  "{e k v | k\<mapsto>v\<in>map_of \<Gamma>[x::h=y]} = {e k v[x::=y] | k\<mapsto>v\<in>map_of \<Gamma>}"
  by (auto simp add: map_of_subst)

lemma subst_eq_Cons:
  "\<Gamma>[x::h=y] = (x', e)#\<Delta> \<longleftrightarrow> (\<exists> e' \<Gamma>'. \<Gamma> = (x',e')#\<Gamma>' \<and> e'[x::=y] = e \<and> \<Gamma>'[x::h=y] = \<Delta>)"
  by (cases \<Gamma>) auto

lemma nonrec_subst:
  "atom ` domA \<Gamma> \<sharp>* x \<Longrightarrow> atom ` domA \<Gamma> \<sharp>* y \<Longrightarrow> nonrec \<Gamma>[x::h=y] \<longleftrightarrow> nonrec \<Gamma>"
  by (auto simp add: nonrec_def  fresh_star_def subst_eq_Cons fv_subst_eq)

end
