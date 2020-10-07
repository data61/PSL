section \<open>\isaheader{Implementing Priority Queues by Annotated Lists}\<close>
theory PrioByAnnotatedList
imports 
  "../spec/AnnotatedListSpec"
  "../spec/PrioSpec"
begin

text \<open>
  In this theory, we implement priority queues by annotated lists.

  The implementation is realized as a generic adapter from the
  AnnotatedList to the priority queue interface.

  Priority queues are realized as a sequence of pairs of
  elements and associated priority. The monoids operation
  takes the element with minimum priority.

  The element with minimum priority is extracted from the
  sum over all elements.
  Deleting the element with minimum priority is done by
  splitting the sequence at the point where the minimum priority
  of the elements read so far becomes equal to the minimum priority of 
  all elements.
\<close>

subsection "Definitions"
subsubsection "Monoid"
datatype ('e, 'a) Prio = Infty | Prio 'e 'a

fun p_unwrap :: "('e,'a) Prio \<Rightarrow> ('e \<times> 'a)" where
"p_unwrap (Prio e a) = (e , a)"

fun p_min :: "('e, 'a::linorder) Prio \<Rightarrow> ('e, 'a) Prio \<Rightarrow> ('e, 'a) Prio"  where
  "p_min Infty Infty = Infty"|
  "p_min Infty (Prio e a) = Prio e a"|
  "p_min (Prio e a) Infty = Prio e a"|
  "p_min (Prio e1 a) (Prio e2 b) = (if a \<le> b then Prio e1 a else Prio e2 b)"


lemma p_min_re_neut[simp]: "p_min a Infty = a" by (induct a) auto
lemma p_min_le_neut[simp]: "p_min Infty a = a" by (induct a) auto
lemma p_min_asso: "p_min (p_min a b) c = p_min a (p_min b c)"
  apply(induct a b  rule: p_min.induct )
  apply auto 
  apply (induct c)
  apply auto
  apply (induct c)
  apply auto
  done
lemma lp_mono: "class.monoid_add p_min Infty" 
  by unfold_locales (auto simp add: p_min_asso)

instantiation Prio :: (type,linorder) monoid_add
begin
definition zero_def: "0 == Infty" 
definition plus_def: "a+b == p_min a b"
  
instance by 
  intro_classes 
(auto simp add: p_min_asso zero_def plus_def)
end

fun p_less_eq :: "('e, 'a::linorder) Prio \<Rightarrow> ('e, 'a) Prio \<Rightarrow> bool" where
  "p_less_eq (Prio e a) (Prio f b) = (a \<le> b)"|
  "p_less_eq  _ Infty = True"|
  "p_less_eq Infty (Prio e a) = False"

fun p_less :: "('e, 'a::linorder) Prio \<Rightarrow> ('e, 'a) Prio \<Rightarrow> bool" where
  "p_less (Prio e a) (Prio f b) = (a < b)"|
  "p_less (Prio e a) Infty = True"|
  "p_less Infty _ = False"

lemma p_less_le_not_le : "p_less x y \<longleftrightarrow> p_less_eq x y \<and> \<not> (p_less_eq y x)"
  by (induct x y rule: p_less.induct) auto

lemma p_order_refl : "p_less_eq x x"
  by (induct x) auto

lemma p_le_inf : "p_less_eq Infty x \<Longrightarrow> x = Infty"
  by (induct x) auto

lemma p_order_trans : "\<lbrakk>p_less_eq x y; p_less_eq y z\<rbrakk> \<Longrightarrow> p_less_eq x z"
  apply (induct y z rule: p_less.induct)
  apply auto
  apply (induct x)
  apply auto
  apply (cases x)
  apply auto
  apply(induct x)
  apply (auto simp add: p_le_inf)
  apply (metis p_le_inf p_less_eq.simps(2))
  done

lemma p_linear2 : "p_less_eq x y \<or> p_less_eq y x"
  apply (induct x y rule: p_less_eq.induct)
  apply auto
  done

instantiation Prio :: (type, linorder) preorder
begin
definition plesseq_def: "less_eq = p_less_eq"
definition pless_def: "less = p_less"

instance 
  apply (intro_classes)
  apply (simp only: p_less_le_not_le pless_def plesseq_def)
  apply (simp only: p_order_refl plesseq_def pless_def)
  apply (simp only: plesseq_def)
  apply (metis p_order_trans)
  done

end


subsubsection "Operations"
definition alprio_\<alpha> :: "('s \<Rightarrow> (unit \<times> ('e,'a::linorder) Prio) list) 
  \<Rightarrow> 's \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  where 
  "alprio_\<alpha> \<alpha> al == (mset (map p_unwrap (map snd (\<alpha> al))))"

definition alprio_invar :: "('s \<Rightarrow> (unit \<times> ('c, 'd::linorder) Prio) list) 
  \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where
  "alprio_invar \<alpha> invar al == invar al \<and> (\<forall> x\<in>set (\<alpha> al). snd x\<noteq>Infty)"

definition alprio_empty  where 
  "alprio_empty empt = empt"

definition alprio_isEmpty  where 
  "alprio_isEmpty isEmpty = isEmpty"

definition alprio_insert :: "(unit \<Rightarrow> ('e,'a) Prio \<Rightarrow> 's \<Rightarrow> 's) 
  \<Rightarrow> 'e \<Rightarrow> 'a::linorder \<Rightarrow> 's  \<Rightarrow> 's"  
  where
  "alprio_insert consl e a s = consl () (Prio e a) s"

definition alprio_find :: "('s \<Rightarrow> ('e,'a::linorder) Prio) \<Rightarrow> 's \<Rightarrow> ('e \<times> 'a)" 
where
"alprio_find annot s = p_unwrap (annot s)"

definition alprio_delete :: "((('e,'a::linorder) Prio \<Rightarrow> bool) 
  \<Rightarrow> ('e,'a) Prio \<Rightarrow> 's \<Rightarrow> ('s \<times> (unit \<times> ('e,'a) Prio) \<times> 's)) 
                      \<Rightarrow> ('s \<Rightarrow> ('e,'a) Prio) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" 
  where
  "alprio_delete splits annot app s = (let (l, _ , r) 
    = splits (\<lambda> x. x\<le>(annot s)) Infty s in app l r) "

definition alprio_meld where
  "alprio_meld app = app"

lemmas alprio_defs =
  alprio_invar_def
  alprio_\<alpha>_def
  alprio_empty_def
  alprio_isEmpty_def
  alprio_insert_def
  alprio_find_def
  alprio_delete_def
  alprio_meld_def

subsection "Correctness"

subsubsection "Auxiliary Lemmas"
lemma sum_list_split: "sum_list (l @ (a::'a::monoid_add) # r) = (sum_list l) + a + (sum_list r)"
  by (induct l) (auto simp add: add.assoc)


lemma p_linear: "(x::('e, 'a::linorder) Prio) \<le> y \<or> y \<le> x"
  by (unfold plesseq_def) (simp only: p_linear2)


lemma p_min_mon: "(x::(('e,'a::linorder) Prio)) \<le> y \<Longrightarrow> (z + x) \<le> y"
apply (unfold plus_def plesseq_def)
apply (induct x y rule: p_less_eq.induct)
apply (auto)
apply (induct z)
apply (auto)
done

lemma p_min_mon2: "p_less_eq x y \<Longrightarrow> p_less_eq (p_min z x) y"
apply (induct x y rule: p_less_eq.induct)
apply (auto)
apply (induct z)
apply (auto)
done

lemma ls_min: " \<forall>x \<in> set (xs:: ('e,'a::linorder) Prio list) . sum_list xs \<le> x"
proof (induct xs)
case Nil thus ?case by auto
next
case (Cons a ins) thus ?case
  apply (auto simp add: plus_def plesseq_def)
  apply (cases a)
  apply auto
  apply (cases "sum_list ins")
  apply auto
  apply (case_tac x)
  apply auto
  apply (cases a)
  apply auto
  apply (cases "sum_list ins")
  apply auto
  done
qed    

lemma infadd: "x \<noteq> Infty \<Longrightarrow>x + y \<noteq> Infty"
apply (unfold plus_def)
apply (induct x y rule: p_min.induct)
apply auto
done


lemma prio_selects_one: "a+b = a \<or> a+b=(b::('e,'a::linorder) Prio)"
  apply (simp add: plus_def)
  apply (cases "(a,b)" rule: p_min.cases)
  apply simp_all
  done


lemma sum_list_in_set: "(l::('x \<times> ('e,'a::linorder) Prio) list)\<noteq>[] \<Longrightarrow> 
  sum_list (map snd l) \<in> set (map snd l)"
  apply (induct l)
  apply simp
  apply (case_tac l)
  apply simp
  using prio_selects_one
  apply auto
  apply force
  apply force
  done

lemma p_unwrap_less_sum: "snd (p_unwrap ((Prio e aa) + b)) \<le> aa"
  apply (cases b)
  apply (auto simp add: plus_def)
done

lemma prio_add_alb: "\<not> b \<le> (a::('e,'a::linorder)Prio)  \<Longrightarrow> b + a = a"
  by (auto simp add: plus_def, cases "(a,b)" rule: p_min.cases) (auto simp add: plesseq_def)

lemma prio_add_alb2: " (a::('e,'a::linorder)Prio)  \<le> a + b \<Longrightarrow>  a + b = a"
  by (auto simp add: plus_def, cases "(a,b)" rule: p_min.cases) (auto simp add: plesseq_def)

lemma prio_add_abc:
  assumes "(l::('e,'a::linorder)Prio) + a \<le> c" 
  and "\<not> l \<le> c"
  shows  "\<not> l \<le> a"
proof (rule ccontr)
  assume "\<not> \<not> l \<le> a"
  with assms have "l + a = l"
    apply (auto simp add: plus_def plesseq_def)
    apply (cases "(l,a)" rule: p_less_eq.cases)
    apply auto
    done
  with assms show False by simp
qed

lemma prio_add_abc2:
  assumes "(a::('e,'a::linorder)Prio) \<le> a + b" 
  shows "a \<le> b"
proof (rule ccontr)
  assume ann: "\<not> a \<le> b"
  hence "a + b = b" 
    apply (auto simp add: plus_def plesseq_def)
    apply (cases "(a,b)" rule: p_min.cases)
    apply auto
    done
  thus False using assms ann by simp
qed


subsubsection "Empty"
lemma alprio_empty_correct: 
  assumes "al_empty \<alpha> invar empt"
  shows "prio_empty (alprio_\<alpha> \<alpha>) (alprio_invar \<alpha> invar) (alprio_empty empt)"
proof -
  interpret al_empty \<alpha> invar empt by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold alprio_invar_def)
    apply auto
    apply (unfold alprio_empty_def)
    apply (auto simp add: empty_correct)
    apply (unfold alprio_\<alpha>_def)
    apply auto
    apply (simp only: empty_correct)
    done
qed


subsubsection "Is Empty"

lemma alprio_isEmpty_correct: 
  assumes "al_isEmpty \<alpha> invar isEmpty"
  shows "prio_isEmpty (alprio_\<alpha> \<alpha>) (alprio_invar \<alpha> invar) (alprio_isEmpty isEmpty)"
proof -
  interpret al_isEmpty \<alpha> invar isEmpty by fact
  show ?thesis by (unfold_locales) (auto simp add: alprio_defs isEmpty_correct)
qed


subsubsection "Insert"
lemma alprio_insert_correct: 
  assumes "al_consl \<alpha> invar consl"
  shows "prio_insert (alprio_\<alpha> \<alpha>) (alprio_invar \<alpha> invar) (alprio_insert consl)"
proof -
  interpret al_consl \<alpha> invar consl by fact
  show ?thesis by unfold_locales (auto simp add: alprio_defs consl_correct)
qed


subsubsection "Meld"

lemma alprio_meld_correct: 
  assumes "al_app \<alpha> invar app"
  shows "prio_meld (alprio_\<alpha> \<alpha>) (alprio_invar \<alpha> invar) (alprio_meld app)"
proof -
  interpret al_app \<alpha> invar app by fact
  show ?thesis by unfold_locales (auto simp add: alprio_defs app_correct)
qed

subsubsection "Find"

lemma annot_not_inf :
  assumes "(alprio_invar \<alpha> invar) s" 
  and "(alprio_\<alpha> \<alpha>) s \<noteq> {#}"
  and "al_annot \<alpha> invar annot"
  shows "annot s \<noteq> Infty"
proof -
  interpret al_annot \<alpha> invar annot by fact
  show ?thesis
  proof -
    from assms(1) have invs: "invar s" by (simp add: alprio_defs)
    from assms(2) have sne: "set (\<alpha> s) \<noteq> {}"
    proof (cases "set (\<alpha> s) = {}")
      case True 
      hence "\<alpha> s = []" by simp
      hence "(alprio_\<alpha> \<alpha>) s = {#}" by (simp add: alprio_defs)
      from this assms(2) show ?thesis by simp
    next
      case False thus ?thesis by simp
    qed
    hence "(\<alpha> s) \<noteq> []" by simp
    hence " \<exists>x xs. (\<alpha> s) = x # xs" by (cases "\<alpha> s") auto
    from this obtain x xs where [simp]: "(\<alpha> s) = x # xs" by blast
    from this assms(1) have "snd x \<noteq> Infty" by (auto simp add: alprio_defs)
    hence "sum_list (map snd (\<alpha> s)) \<noteq> Infty" by (auto simp add: infadd)
    thus "annot s \<noteq> Infty" using annot_correct invs by simp
  qed
qed

lemma annot_in_set: 
  assumes "(alprio_invar \<alpha> invar) s" 
  and "(alprio_\<alpha> \<alpha>) s \<noteq> {#}"
  and "al_annot \<alpha> invar annot"
  shows "p_unwrap (annot s) \<in># ((alprio_\<alpha> \<alpha>) s)"         
proof - 
  interpret al_annot \<alpha> invar annot by fact
  from assms(2) have snn: "\<alpha> s \<noteq> []" by (auto simp add: alprio_defs)
  from assms(1) have invs: "invar s" by (simp add: alprio_defs)
  hence ans: "annot s = sum_list (map snd (\<alpha> s))" by (simp add: annot_correct)
  let ?P = "map snd (\<alpha> s)"
  have "annot s \<in> set ?P"
    by (unfold ans) (rule sum_list_in_set[OF snn])
  then show ?thesis
    by (auto intro!: image_eqI simp add: alprio_\<alpha>_def)
qed

lemma  sum_list_less_elems: "\<forall>x\<in>set xs. snd x \<noteq> Infty \<Longrightarrow>
   \<forall>y\<in>set_mset (mset (map p_unwrap (map snd xs))).
              snd (p_unwrap (sum_list (map snd xs))) \<le> snd y"          
    proof (induct xs)
    case Nil thus ?case by simp
    next
    case (Cons a as) thus ?case
      apply auto
      apply (cases "(snd a)" rule: p_unwrap.cases)
      apply auto
      apply (cases "sum_list (map snd as)")
      apply auto
      apply (metis linorder_linear p_min_re_neut 
        p_unwrap.simps plus_def [abs_def] snd_eqD)
      apply (auto simp add: p_unwrap_less_sum)
      apply (unfold plus_def)
      apply (cases "(snd a, sum_list (map snd as))" rule: p_min.cases)
      apply auto
      apply (cases "map snd as")
      apply (auto simp add: infadd)
      done
qed  
  
lemma alprio_find_correct: 
  assumes  "al_annot \<alpha> invar annot"
  shows "prio_find (alprio_\<alpha> \<alpha>) (alprio_invar \<alpha> invar) (alprio_find annot)"
proof -
  interpret al_annot \<alpha> invar annot by fact
  show ?thesis
    apply unfold_locales
    apply (rule conjI)
    apply (insert assms)
    apply (unfold alprio_find_def)
    apply (simp add:annot_in_set)
    apply (unfold alprio_defs)
    apply (simp add: annot_correct)
    apply (auto simp add: sum_list_less_elems)
    done
qed


subsubsection "Delete"

lemma delpred_mon: 
  "\<forall>(a:: ('e, 'a::linorder) Prio) b. ((\<lambda> x. x \<le> y) a 
    \<longrightarrow> (\<lambda> x. x \<le> y) (a + b)) "
proof (intro impI allI) 
  fix a b 
  show "a \<le> y \<Longrightarrow> a + b \<le> y"
    apply (induct a b rule: p_less.induct)
    apply (auto simp add: plus_def)
    apply (metis linorder_linear order_trans 
      p_linear p_min.simps(4) p_min_mon plus_def prio_selects_one)
    apply (metis order_trans p_linear p_min_mon p_min_re_neut plus_def)
    done 
qed

(* alprio_delete erhält die Invariante *)
lemma alpriodel_invar: 
  assumes "alprio_invar \<alpha> invar s"
  and "al_annot \<alpha> invar annot"
  and "alprio_\<alpha> \<alpha> s \<noteq> {#}"
  and "al_splits \<alpha> invar splits"
  and "al_app \<alpha> invar app"
  shows "alprio_invar \<alpha> invar (alprio_delete splits annot app s)"
proof -
  interpret al_splits \<alpha> invar splits by fact
  let ?P = "\<lambda>x. x \<le> annot s"
  obtain l p r where 
    [simp]:"splits ?P Infty s = (l, p, r)" 
    by (cases "splits ?P Infty s")  auto
  obtain e a where 
    "p = (e, a)" 
    by (cases p, blast)
  hence 
    lear:"splits ?P Infty s = (l, (e,a), r)" 
    by simp
  from annot_not_inf[OF assms(1) assms(3) assms(2)] have 
    "annot s \<noteq> Infty" .
  hence 
    sv1: "\<not> Infty \<le> annot s" 
    by (simp add: plesseq_def, cases "annot s", auto)
  from assms(1) have 
    invs: "invar s" 
    unfolding alprio_invar_def by simp
  interpret al_annot \<alpha> invar annot by fact
  from invs have 
    sv2: "Infty + sum_list (map snd (\<alpha> s)) \<le> annot s" 
    by (auto simp add: annot_correct plus_def 
      plesseq_def p_min_le_neut p_order_refl)
  note sp = splits_correct[of s "?P" Infty l e a r]
  note dp = delpred_mon[of "annot s"]
  from sp[OF invs dp sv1 sv2 lear] have 
    invlr: "invar l \<and> invar r" and 
    alr: "\<alpha> s = \<alpha> l @ (e, a) # \<alpha> r" 
    by auto
  interpret al_app \<alpha> invar app by fact
  from invlr app_correct have 
    invapplr: "invar (app l r)" 
    by simp
  from invlr app_correct have 
    sr: "\<alpha> (app l r) = (\<alpha> l) @ (\<alpha> r)" 
    by simp
  from alr have  
    "set (\<alpha> s) \<supseteq> (set (\<alpha> l) Un set (\<alpha> r))" 
    by auto
  with app_correct[of l r] invlr have 
    "set (\<alpha> s) \<supseteq> set (\<alpha> (app l r))" by auto
  with invapplr assms(1) 
  show ?thesis 
    unfolding alprio_defs by auto
qed


lemma sum_list_elem:
  assumes " ins = l @ (a::('e,'a::linorder)Prio) # r"  
  and "\<not> sum_list l \<le> sum_list ins"  
  and "sum_list l + a \<le> sum_list ins "
  shows " a = sum_list ins"
proof -
  have "\<not> sum_list l \<le> a" using assms prio_add_abc by simp
  hence lpa: "sum_list l + a = a" using prio_add_alb by auto
  hence als: "a \<le> sum_list ins" using assms(3) by simp
  have "sum_list ins = a + sum_list r" 
    using lpa sum_list_split[of l a r] assms(1) by auto
  thus ?thesis using prio_add_alb2[of a "sum_list r"] prio_add_abc2 als  
    by auto
qed

lemma alpriodel_right:
  assumes "alprio_invar \<alpha> invar s"
  and "al_annot \<alpha> invar annot"
  and "alprio_\<alpha> \<alpha> s \<noteq> {#}"
  and "al_splits \<alpha> invar splits"
  and "al_app \<alpha> invar app"
  shows "alprio_\<alpha> \<alpha> (alprio_delete splits annot app s) = 
          alprio_\<alpha> \<alpha> s - {#p_unwrap (annot s)#}"
proof -
  interpret al_splits \<alpha> invar splits by fact
  let ?P = "\<lambda>x. x \<le> annot s"
  obtain l p r where 
    [simp]:"splits ?P Infty s = (l, p, r)" 
    by (cases "splits ?P Infty s")  auto
  obtain e a where 
    "p = (e, a)" 
    by (cases p, blast)
  hence 
    lear:"splits ?P Infty s = (l, (e,a), r)" 
    by simp
  from annot_not_inf[OF assms(1) assms(3) assms(2)] have 
    "annot s \<noteq> Infty" .
  hence 
    sv1: "\<not> Infty \<le> annot s" 
    by (simp add: plesseq_def, cases "annot s", auto)
  from assms(1) have 
    invs: "invar s" 
    unfolding alprio_invar_def by simp
  interpret al_annot \<alpha> invar annot by fact
  from invs have 
    sv2: "Infty + sum_list (map snd (\<alpha> s)) \<le> annot s" 
    by (auto simp add: annot_correct plus_def 
      plesseq_def p_min_le_neut p_order_refl)
  note sp = splits_correct[of s "?P" Infty l e a r]
  note dp = delpred_mon[of "annot s"]
  
  from sp[OF invs dp sv1 sv2 lear] have 
    invlr: "invar l \<and> invar r" and 
    alr: "\<alpha> s = \<alpha> l @ (e, a) # \<alpha> r" and
    anlel: "\<not> sum_list (map snd (\<alpha> l)) \<le> annot s" and 
    aneqa: "(sum_list (map snd (\<alpha> l)) + a) \<le> annot s"
    by (auto simp add: plus_def zero_def)
  have mapalr: "map snd (\<alpha> s) = (map snd (\<alpha> l)) @ a # (map snd (\<alpha> r))" 
    using alr by simp
  note lsa = sum_list_elem[of "map snd (\<alpha> s)" "map snd (\<alpha> l)" a "map snd (\<alpha> r)"]
  note lsa2 = lsa[OF mapalr]
  hence a_is_annot: "a = annot s" 
    using annot_correct[OF invs] anlel aneqa by auto
  have "map p_unwrap (map snd (\<alpha> s)) = 
    (map p_unwrap (map snd (\<alpha> l))) @ (p_unwrap a) 
      # (map p_unwrap (map snd (\<alpha> r)))" 
    using alr by simp
  hence alpriolst: "(alprio_\<alpha> \<alpha> s) = (alprio_\<alpha> \<alpha> l) +{# p_unwrap a #}+ (alprio_\<alpha> \<alpha> r)" 
    unfolding alprio_defs
    by (simp add: algebra_simps)
  interpret al_app \<alpha> invar app by fact
  from alpriolst show ?thesis using app_correct[of l r] invlr a_is_annot 
    by (auto simp add: alprio_defs algebra_simps)
qed  

lemma alprio_delete_correct: 
  assumes "al_annot \<alpha> invar annot"
  and "al_splits \<alpha> invar splits"
  and "al_app \<alpha> invar app"
  shows "prio_delete (alprio_\<alpha> \<alpha>) (alprio_invar \<alpha> invar) 
           (alprio_find annot) (alprio_delete splits annot app)"
proof-
  interpret al_annot \<alpha> invar annot by fact
  interpret al_splits \<alpha> invar splits by fact
  interpret al_app \<alpha> invar app by fact
  show ?thesis
    apply intro_locales
    apply (rule alprio_find_correct,simp add: assms) 
    apply unfold_locales
    apply (insert assms)
    apply (simp add: alpriodel_invar)
    apply (simp add: alpriodel_right alprio_find_def)   
    done
qed  

lemmas alprio_correct =
  alprio_empty_correct
  alprio_isEmpty_correct
  alprio_insert_correct
  alprio_delete_correct
  alprio_find_correct
  alprio_meld_correct

locale alprio_defs = StdALDefs ops 
  for ops :: "(unit,('e,'a::linorder) Prio,'s) alist_ops"
begin
  definition [icf_rec_def]: "alprio_ops \<equiv> \<lparr>
    prio_op_\<alpha> = alprio_\<alpha> \<alpha>,
    prio_op_invar = alprio_invar \<alpha> invar,
    prio_op_empty = alprio_empty empty,
    prio_op_isEmpty = alprio_isEmpty isEmpty,
    prio_op_insert = alprio_insert consl,
    prio_op_find = alprio_find annot,
    prio_op_delete = alprio_delete splits annot app,
    prio_op_meld = alprio_meld app
    \<rparr>"
  
end

locale alprio = alprio_defs ops + StdAL ops 
  for ops :: "(unit,('e,'a::linorder) Prio,'s) alist_ops"
begin
  lemma alprio_ops_impl: "StdPrio alprio_ops"
    apply (rule StdPrio.intro)
    apply (simp_all add: icf_rec_unf)
    apply (rule alprio_correct, unfold_locales) []
    apply (rule alprio_correct, unfold_locales) []
    apply (rule alprio_correct, unfold_locales) []
    apply (rule alprio_correct, unfold_locales) []
    apply (rule alprio_correct, unfold_locales) []
    apply (rule alprio_correct, unfold_locales) []
    done
end
    
end
