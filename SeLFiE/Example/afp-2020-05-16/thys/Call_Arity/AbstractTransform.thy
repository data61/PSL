theory AbstractTransform
imports Launchbury.Terms TransformTools
begin

locale AbstractAnalProp =
  fixes PropApp :: "'a \<Rightarrow> 'a::cont_pt"
  fixes PropLam :: "'a \<Rightarrow> 'a"
  fixes AnalLet :: "heap \<Rightarrow> exp \<Rightarrow> 'a \<Rightarrow> 'b::cont_pt"
  fixes PropLetBody :: "'b \<Rightarrow> 'a"
  fixes PropLetHeap :: "'b\<Rightarrow> var \<Rightarrow> 'a\<^sub>\<bottom>"
  fixes PropIfScrut :: "'a \<Rightarrow> 'a"
  assumes PropApp_eqvt: "\<pi> \<bullet> PropApp \<equiv> PropApp"
  assumes PropLam_eqvt: "\<pi> \<bullet> PropLam \<equiv> PropLam"
  assumes AnalLet_eqvt: "\<pi> \<bullet> AnalLet \<equiv> AnalLet"
  assumes PropLetBody_eqvt: "\<pi> \<bullet> PropLetBody \<equiv> PropLetBody"
  assumes PropLetHeap_eqvt: "\<pi> \<bullet> PropLetHeap \<equiv> PropLetHeap"
  assumes PropIfScrut_eqvt: "\<pi> \<bullet> PropIfScrut \<equiv> PropIfScrut"

locale AbstractAnalPropSubst = AbstractAnalProp +
  assumes AnalLet_subst:  "x \<notin> domA \<Gamma> \<Longrightarrow> y \<notin> domA \<Gamma> \<Longrightarrow> AnalLet (\<Gamma>[x::h=y]) (e[x::=y]) a = AnalLet \<Gamma> e a"

locale AbstractTransform = AbstractAnalProp +
  constrains AnalLet :: "heap \<Rightarrow> exp \<Rightarrow> 'a::pure_cont_pt \<Rightarrow> 'b::cont_pt"
  fixes TransVar :: "'a \<Rightarrow> var \<Rightarrow> exp"
  fixes TransApp :: "'a \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> exp"
  fixes TransLam :: "'a \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp"
  fixes TransLet :: "'b \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> exp"
  assumes TransVar_eqvt: "\<pi> \<bullet> TransVar = TransVar"
  assumes TransApp_eqvt: "\<pi> \<bullet> TransApp = TransApp"
  assumes TransLam_eqvt: "\<pi> \<bullet> TransLam = TransLam"
  assumes TransLet_eqvt: "\<pi> \<bullet> TransLet = TransLet"
  assumes SuppTransLam: "supp (TransLam a v e) \<subseteq> supp e - supp v"
  assumes SuppTransLet: "supp (TransLet b \<Gamma> e) \<subseteq> supp (\<Gamma>, e) - atom ` domA \<Gamma>"
begin
  nominal_function transform where
    "transform a (App e x) = TransApp a (transform (PropApp a) e) x"
  | "transform a (Lam [x]. e) = TransLam a x (transform (PropLam a) e)"
  | "transform a (Var x) = TransVar a x"
  | "transform a (Let \<Gamma> e) = TransLet (AnalLet \<Gamma> e a)
        (map_transform transform (PropLetHeap (AnalLet \<Gamma> e a)) \<Gamma>)
        (transform (PropLetBody (AnalLet \<Gamma> e a)) e)"
  | "transform a (Bool b) = (Bool b)"
  | "transform a (scrut ? e1 : e2)  = (transform (PropIfScrut a) scrut ? transform a e1 : transform a e2)"
proof goal_cases
  case 1
  note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] AnalLet_eqvt[eqvt_raw] TransVar_eqvt[eqvt]  TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]
  show ?case
    unfolding eqvt_def transform_graph_aux_def
    apply rule
    apply perm_simp
    apply (rule refl)
    done
next
  case prems: (3 P x)
  show ?case
  proof (cases x)
    fix a b
    assume "x = (a, b)"
    thus ?case
      using prems
      apply (cases b rule:Terms.exp_strong_exhaust)
      apply auto
      done
  qed
next
  case prems: (10 a x e a' x' e')
  from prems(5)
  have "a' = a" and  "Lam [x]. e = Lam [x']. e'" by simp_all
  from this(2)
  show ?case
  unfolding \<open>a' = a\<close>
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm

    have "supp (TransLam a x (transform_sumC (PropLam a, e))) \<subseteq> supp (Lam [x]. e)"
      apply (rule subset_trans[OF SuppTransLam])
      apply (auto simp add:  exp_assn.supp supp_Pair supp_at_base pure_supp exp_assn.fsupp dest!: subsetD[OF supp_eqvt_at[OF prems(1)], rotated])
      done
    moreover
    assume "supp \<pi> \<sharp>* (Lam [x]. e)" 
    ultimately
    have *: "supp \<pi> \<sharp>* TransLam a x (transform_sumC (PropLam a, e))" by (auto simp add: fresh_star_def fresh_def)

    note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransVar_eqvt[eqvt] TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]

    have "TransLam a (\<pi> \<bullet> x) (transform_sumC (PropLam a, \<pi> \<bullet> e))
        = TransLam a (\<pi> \<bullet> x) (transform_sumC (\<pi> \<bullet>  (PropLam a, e)))"
      by perm_simp rule
    also have "\<dots> = TransLam a (\<pi> \<bullet> x) (\<pi> \<bullet> transform_sumC (PropLam a, e))"
      unfolding eqvt_at_apply'[OF prems(1)] ..
    also have "\<dots> = \<pi> \<bullet> (TransLam a x (transform_sumC (PropLam a, e)))"
      by simp
    also have "\<dots> = TransLam a x (transform_sumC (PropLam a, e))"
      by (rule perm_supp_eq[OF *])
    finally show "TransLam a (\<pi> \<bullet> x) (transform_sumC (PropLam a, \<pi> \<bullet> e)) = TransLam a x (transform_sumC (PropLam a, e))" by simp
  qed
next
  case prems: (19 a as body a' as' body')
  note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw]  AnalLet_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransVar_eqvt[eqvt]  TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]

  from supp_eqvt_at[OF prems(1)]
  have "\<And> x e a. (x, e) \<in> set as \<Longrightarrow> supp (transform_sumC (a, e)) \<subseteq> supp e"
    by (auto simp add: exp_assn.fsupp supp_Pair pure_supp)
  hence supp_map: "\<And>ae. supp (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) ae as) \<subseteq> supp as"
    by (rule supp_map_transform_step)

  from prems(9)
  have "a' = a" and  "Terms.Let as body = Terms.Let as' body'" by simp_all
  from this(2)
  show ?case
  unfolding \<open>a' = a\<close>
  proof (rule eqvt_let_case)
    have "supp (TransLet (AnalLet as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet as body a)) as) (transform_sumC (PropLetBody (AnalLet as body a), body))) \<subseteq> supp (Let as body)"
      by (auto simp add: Let_supp supp_Pair pure_supp exp_assn.fsupp
               dest!: subsetD[OF supp_eqvt_at[OF prems(2)], rotated] subsetD[OF SuppTransLet] subsetD[OF supp_map])
    moreover
    fix \<pi> :: perm
    assume "supp \<pi> \<sharp>* Terms.Let as body"
    ultimately
    have *: "supp \<pi> \<sharp>* TransLet (AnalLet as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet as body a)) as) (transform_sumC (PropLetBody (AnalLet as body a), body))"
      by (auto simp add: fresh_star_def fresh_def)

    have "TransLet (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (map_transform (\<lambda>x0 x1. (\<pi> \<bullet> transform_sumC) (x0, x1)) (PropLetHeap (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a)) (\<pi> \<bullet> as)) ((\<pi> \<bullet> transform_sumC) (PropLetBody (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a), \<pi> \<bullet> body)) = 
        \<pi> \<bullet> TransLet (AnalLet as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet as body a)) as) (transform_sumC (PropLetBody (AnalLet as body a), body))"
       by (simp del: Let_eq_iff Pair_eqvt add:  eqvt_at_apply[OF prems(2)])
    also have "\<dots> = TransLet (AnalLet as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet as body a)) as) (transform_sumC (PropLetBody (AnalLet as body a), body))"
      by (rule perm_supp_eq[OF *])
    also
    have "map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a)) (\<pi> \<bullet> as)
        = map_transform (\<lambda>x xa. (\<pi> \<bullet> transform_sumC) (x, xa)) (PropLetHeap (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a)) (\<pi> \<bullet> as)"
        apply (rule map_transform_fundef_cong[OF _ refl refl])
        apply (subst (asm) set_eqvt[symmetric])
        apply (subst (asm) mem_permute_set)
        apply (auto simp add: permute_self  dest: eqvt_at_apply''[OF prems(1)[where aa = "(- \<pi> \<bullet> a)" for a], where p = \<pi>, symmetric])
        done
    moreover
    have "(\<pi> \<bullet> transform_sumC) (PropLetBody (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a), \<pi> \<bullet> body) = transform_sumC (PropLetBody (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a), \<pi> \<bullet> body)"
      using eqvt_at_apply''[OF prems(2), where p = \<pi>] by perm_simp
    ultimately
    show "TransLet (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a)) (\<pi> \<bullet> as)) (transform_sumC (PropLetBody (AnalLet (\<pi> \<bullet> as) (\<pi> \<bullet> body) a), \<pi> \<bullet> body)) =
          TransLet (AnalLet as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (AnalLet as body a)) as) (transform_sumC (PropLetBody (AnalLet as body a), body))" by metis
    qed
  qed auto
  nominal_termination by lexicographic_order

  lemma supp_transform: "supp (transform a e) \<subseteq> supp e"
  proof-
    note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw]  AnalLet_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransVar_eqvt[eqvt]  TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]
    note transform.eqvt[eqvt]
    show ?thesis
      apply (rule supp_fun_app_eqvt)
      apply (rule eqvtI)
      apply perm_simp
      apply (rule reflexive)
      done
   qed

  lemma fv_transform: "fv (transform a e) \<subseteq> fv e"
    unfolding fv_def by (auto dest: subsetD[OF supp_transform])

end

locale AbstractTransformSubst = AbstractTransform + AbstractAnalPropSubst +
  assumes TransVar_subst: "(TransVar a v)[x ::= y] = (TransVar a v[x ::v= y])"
  assumes TransApp_subst: "(TransApp a e v)[x ::= y] = (TransApp a e[x ::= y] v[x ::v= y])"
  assumes TransLam_subst: "atom v \<sharp> (x,y) \<Longrightarrow> (TransLam a v e)[x ::= y] = (TransLam a v[x ::v= y] e[x ::= y])"
  assumes TransLet_subst: "atom ` domA \<Gamma> \<sharp>* (x,y) \<Longrightarrow> (TransLet b \<Gamma> e)[x ::= y] = (TransLet b \<Gamma>[x ::h= y] e[x ::= y])"
begin
  lemma subst_transform: "(transform a e)[x ::= y] = transform a e[x ::= y]"
  proof (nominal_induct e avoiding: x y arbitrary: a  rule: exp_strong_induct_set)
  case (Let \<Delta> body x y)
    hence *: "x \<notin> domA \<Delta>" "y \<notin> domA \<Delta>" by (auto simp add: fresh_star_def fresh_at_base)
    hence "AnalLet \<Delta>[x::h=y] body[x::=y] a = AnalLet \<Delta> body a" by (rule AnalLet_subst)
    with Let
    show ?case
    apply (auto simp add: fresh_star_Pair TransLet_subst simp del: Let_eq_iff)
    apply (rule fun_cong[OF arg_cong[where f = "TransLet b" for b]])
    apply (rule subst_map_transform)
    apply simp
    done
  qed (simp_all add: TransVar_subst TransApp_subst TransLam_subst)
end


locale AbstractTransformBound = AbstractAnalProp + supp_bounded_transform  +
  constrains PropApp :: "'a \<Rightarrow> 'a::pure_cont_pt"
  constrains PropLetHeap :: "'b::cont_pt \<Rightarrow> var \<Rightarrow> 'a\<^sub>\<bottom>"
  constrains trans :: "'c::cont_pt \<Rightarrow> exp \<Rightarrow> exp"
  fixes PropLetHeapTrans :: "'b\<Rightarrow> var \<Rightarrow> 'c\<^sub>\<bottom>"
  assumes PropLetHeapTrans_eqvt: "\<pi> \<bullet> PropLetHeapTrans = PropLetHeapTrans"
  assumes TransBound_eqvt: "\<pi> \<bullet> trans = trans"
begin
  sublocale AbstractTransform PropApp PropLam AnalLet PropLetBody PropLetHeap PropIfScrut
      "(\<lambda> a. Var)"
      "(\<lambda> a. App)"
      "(\<lambda> a. Terms.Lam)"
      "(\<lambda> b \<Gamma> e . Let (map_transform trans (PropLetHeapTrans b) \<Gamma>) e)"
  proof goal_cases
    case 1
    note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] PropIfScrut_eqvt[eqvt_raw]
        AnalLet_eqvt[eqvt_raw] PropLetHeapTrans_eqvt[eqvt] TransBound_eqvt[eqvt]
    show ?case
      apply standard
      apply ((perm_simp, rule)+)[4]
      apply (auto simp add: exp_assn.supp supp_at_base)[1]
      apply (auto simp add: Let_supp supp_Pair supp_at_base dest: subsetD[OF supp_map_transform])[1]
      done
  qed

  lemma isLam_transform[simp]:
    "isLam (transform a e) \<longleftrightarrow> isLam e"
    by (induction e rule:isLam.induct) auto

  lemma isVal_transform[simp]:
    "isVal (transform a e) \<longleftrightarrow> isVal e"
    by (induction e rule:isLam.induct) auto

end

locale AbstractTransformBoundSubst = AbstractAnalPropSubst + AbstractTransformBound + 
  assumes TransBound_subst: "(trans a e)[x::=y] = trans a e[x::=y]"
begin
  sublocale AbstractTransformSubst PropApp PropLam AnalLet PropLetBody PropLetHeap PropIfScrut
      "(\<lambda> a. Var)"
      "(\<lambda> a. App)"
      "(\<lambda> a. Terms.Lam)"
      "(\<lambda> b \<Gamma> e . Let (map_transform trans (PropLetHeapTrans b) \<Gamma>) e)"
  proof goal_cases
    case 1
    note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] PropIfScrut_eqvt[eqvt_raw]
         TransBound_eqvt[eqvt]
    show ?case
      apply standard
      apply simp_all[3]
      apply (simp del: Let_eq_iff)
      apply (rule arg_cong[where f = "\<lambda> x. Let x y" for y])
      apply (rule subst_map_transform)
      apply (simp add: TransBound_subst)
      done
  qed
end


end
