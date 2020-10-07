section \<open>\isaheader{Implementing Unique Priority Queues by Annotated Lists}\<close>
theory PrioUniqueByAnnotatedList
imports 
  "../spec/AnnotatedListSpec"
  "../spec/PrioUniqueSpec"
begin

text \<open>
  In this theory we use annotated lists to implement unique priority queues 
  with totally ordered elements.

  This theory is written as a generic adapter from the AnnotatedList interface
  to the unique priority queue interface.

  The annotated list stores a sequence of elements annotated with 
  priorities\footnote{Technically, the annotated list elements are of unit-type,
  and the annotations hold both, the priority queue elements and the priorities.
  This is required as we defined annotated lists to only sum up the elements 
  annotations.}

  The monoids operations forms the maximum over the elements and
  the minimum over the priorities. 
  The sequence of pairs is ordered by ascending elements' order. 
  The insertion point for a new element, or the priority of an existing element
  can be found by splitting the
  sequence at the point where the maximum of the elements read so far gets
  bigger than the element to be inserted.

  The minimum priority can be read out as the sum over the whole sequence.
  Finding the element with minimum priority is done by splitting the sequence
  at the point where the minimum priority of the elements read so far becomes
  equal to the minimum priority of the whole sequence.
\<close>

subsection "Definitions"

subsubsection "Monoid"
datatype ('e, 'a) LP = Infty | LP 'e 'a

fun p_unwrap :: "('e,'a) LP \<Rightarrow> ('e \<times> 'a)" where
  "p_unwrap (LP e a) = (e , a)"

fun p_min :: "('e::linorder, 'a::linorder) LP \<Rightarrow> ('e, 'a) LP \<Rightarrow> ('e, 'a) LP"  where
  "p_min Infty Infty = Infty"|
  "p_min Infty (LP e a) = LP e a"|
  "p_min (LP e a) Infty = LP e a"|
  "p_min (LP e1 a) (LP e2 b) = (LP (max e1 e2) (min a b))"

fun e_less_eq :: "'e \<Rightarrow> ('e::linorder, 'a::linorder) LP \<Rightarrow> bool"  where
  "e_less_eq e Infty = False"|
  "e_less_eq e (LP e' _) = (e \<le> e')"


text_raw\<open>\paragraph{Instantiation of classes}\ \\\<close>
lemma p_min_re_neut[simp]: "p_min a Infty = a" by (induct a) auto
lemma p_min_le_neut[simp]: "p_min Infty a = a" by (induct a) auto
lemma p_min_asso: "p_min (p_min a b) c = p_min a (p_min b c)"
  apply(induct a b  rule: p_min.induct )
  apply (auto)
  apply (induct c)
  apply (auto)
apply (metis max.assoc)
apply (metis min.assoc)
  done

lemma lp_mono: "class.monoid_add p_min Infty" by  unfold_locales  (auto simp add: p_min_asso)

instantiation LP :: (linorder,linorder) monoid_add
begin
definition zero_def: "0 == Infty" 
definition plus_def: "a+b == p_min a b"
  
instance by 
  intro_classes 
(auto simp add: p_min_asso zero_def plus_def)
end

fun p_less_eq :: "('e, 'a::linorder) LP \<Rightarrow> ('e, 'a) LP \<Rightarrow> bool" where
  "p_less_eq (LP e a) (LP f b) = (a \<le> b)"|
  "p_less_eq  _ Infty = True"|
  "p_less_eq Infty (LP e a) = False"

fun p_less :: "('e, 'a::linorder) LP \<Rightarrow> ('e, 'a) LP \<Rightarrow> bool" where
  "p_less (LP e a) (LP f b) = (a < b)"|
  "p_less (LP e a) Infty = True"|
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

instantiation LP :: (type, linorder) preorder
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

definition aluprio_\<alpha> :: "('s \<Rightarrow> (unit \<times> ('e::linorder,'a::linorder) LP) list) 
  \<Rightarrow> 's \<Rightarrow> ('e::linorder \<rightharpoonup>  'a::linorder)"
  where 
  "aluprio_\<alpha> \<alpha> ft == (map_of (map p_unwrap (map snd (\<alpha> ft))))"

definition aluprio_invar :: "('s \<Rightarrow> (unit \<times> ('c::linorder, 'd::linorder) LP) list)
  \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where
  "aluprio_invar \<alpha> invar ft == 
     invar ft 
     \<and> (\<forall> x\<in>set (\<alpha> ft). snd x\<noteq>Infty) 
     \<and> sorted (map fst (map p_unwrap (map snd (\<alpha> ft)))) 
     \<and> distinct (map fst (map p_unwrap (map snd (\<alpha> ft)))) "

definition aluprio_empty  where 
  "aluprio_empty empt = empt"

definition aluprio_isEmpty  where 
  "aluprio_isEmpty isEmpty = isEmpty"

definition aluprio_insert :: 
  "((('e::linorder,'a::linorder) LP \<Rightarrow> bool) 
  \<Rightarrow> ('e,'a) LP \<Rightarrow> 's \<Rightarrow> ('s \<times> (unit \<times> ('e,'a) LP) \<times> 's)) 
    \<Rightarrow> ('s \<Rightarrow> ('e,'a) LP) 
      \<Rightarrow> ('s \<Rightarrow> bool)
        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) 
          \<Rightarrow> ('s \<Rightarrow> unit \<Rightarrow> ('e,'a) LP \<Rightarrow> 's)
            \<Rightarrow> 's \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 's" 
  where
  "
  aluprio_insert splits annot isEmpty app consr s e a = 
    (if e_less_eq e (annot s) \<and> \<not> isEmpty s 
    then
      (let (l, (_,lp) , r) = splits (e_less_eq e) Infty s in 
        (if e < fst (p_unwrap lp)
        then 
          app (consr (consr l () (LP e a))  () lp) r
        else 
          app (consr l () (LP e a)) r  ))
    else 
      consr s () (LP e a))
  "

definition aluprio_pop :: "((('e::linorder,'a::linorder) LP \<Rightarrow> bool) \<Rightarrow> ('e,'a) LP
  \<Rightarrow> 's \<Rightarrow> ('s \<times> (unit \<times> ('e,'a) LP) \<times> 's)) 
    \<Rightarrow> ('s \<Rightarrow> ('e,'a) LP) 
      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) 
        \<Rightarrow> 's 
          \<Rightarrow> 'e \<times>'a \<times>'s" 
  where
  "aluprio_pop splits annot app s = 
    (let (l, (_,lp) , r) = splits (\<lambda> x. x \<le> (annot s)) Infty s 
    in 
      (case lp of 
        (LP e a) \<Rightarrow> 
          (e, a, app l r) ))"

definition aluprio_prio :: 
  "((('e::linorder,'a::linorder) LP \<Rightarrow> bool) \<Rightarrow> ('e,'a) LP \<Rightarrow> 's 
  \<Rightarrow> ('s \<times> (unit \<times> ('e,'a) LP) \<times> 's)) 
    \<Rightarrow> ('s \<Rightarrow> ('e,'a) LP) 
      \<Rightarrow> ('s \<Rightarrow> bool)
        \<Rightarrow> 's \<Rightarrow> 'e \<Rightarrow> 'a option" 
  where
  "
  aluprio_prio splits annot isEmpty s e = 
    (if e_less_eq e (annot s) \<and> \<not> isEmpty s 
    then
      (let (l, (_,lp) , r) = splits (e_less_eq e) Infty s in 
        (if e = fst (p_unwrap lp)
        then 
          Some (snd (p_unwrap lp))
        else
          None))
    else 
      None)
  "

lemmas aluprio_defs =
aluprio_invar_def
aluprio_\<alpha>_def
aluprio_empty_def
aluprio_isEmpty_def
aluprio_insert_def
aluprio_pop_def
aluprio_prio_def

subsection "Correctness"

subsubsection "Auxiliary Lemmas"

lemma p_linear: "(x::('e, 'a::linorder) LP) \<le> y \<or> y \<le> x"
  by (unfold plesseq_def) (simp only: p_linear2)


lemma e_less_eq_mon1: "e_less_eq e x \<Longrightarrow> e_less_eq e (x + y)"
  apply (cases x) 
  apply (auto simp add: plus_def) 
  apply (cases y) 
  apply (auto simp add: max.coboundedI1)
  done
lemma e_less_eq_mon2: "e_less_eq e y \<Longrightarrow> e_less_eq e (x + y)"
  apply (cases x) 
  apply (auto simp add: plus_def) 
  apply (cases y) 
  apply (auto simp add: max.coboundedI2)
  done
lemmas e_less_eq_mon = 
  e_less_eq_mon1
  e_less_eq_mon2

lemma p_less_eq_mon:
  "(x::('e::linorder,'a::linorder) LP) \<le> z \<Longrightarrow> (x + y) \<le> z"
  apply(cases y)
  apply(auto simp add: plus_def)
  apply (cases x)
  apply (cases z)
  apply (auto simp add: plesseq_def)
  apply (cases z)
  apply (auto simp add: min.coboundedI1)
  done

lemma p_less_eq_lem1:
  "\<lbrakk>\<not> (x::('e::linorder,'a::linorder) LP) \<le> z;
  (x + y) \<le> z\<rbrakk>
  \<Longrightarrow> y \<le> z "
  apply (cases x,auto simp add: plus_def)
  apply (cases y, auto)
  apply (cases z, auto simp add: plesseq_def)
  apply (metis min_le_iff_disj)
  done
  
lemma infadd: "x \<noteq> Infty \<Longrightarrow>x + y \<noteq> Infty"
  apply (unfold plus_def)
  apply (induct x y rule: p_min.induct)
  apply auto
  done


lemma e_less_eq_sum_list: 
  "\<lbrakk>\<not> e_less_eq e (sum_list xs)\<rbrakk> \<Longrightarrow> \<forall>x \<in> set xs. \<not> e_less_eq e x"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  hence "\<not> e_less_eq e (sum_list xs)" by (auto simp add: e_less_eq_mon)
  hence v1: "\<forall>x\<in>set xs. \<not> e_less_eq e x" using Cons.hyps by simp
  from Cons.prems have "\<not> e_less_eq e a" by (auto simp add: e_less_eq_mon)
  with v1 show "\<forall>x\<in>set (a#xs). \<not> e_less_eq e x" by simp
qed

lemma e_less_eq_p_unwrap: 
  "\<lbrakk>x \<noteq> Infty;\<not> e_less_eq e x\<rbrakk> \<Longrightarrow> fst (p_unwrap x) < e"
  by (cases x) auto

lemma e_less_eq_refl :
  "b \<noteq> Infty \<Longrightarrow> e_less_eq (fst (p_unwrap b)) b"
  by (cases b) auto

lemma e_less_eq_sum_list2:
  assumes 
  "\<forall>x\<in>set (\<alpha>s). snd x \<noteq> Infty"
  "((), b) \<in> set (\<alpha>s)"
  shows "e_less_eq (fst (p_unwrap b)) (sum_list (map snd (\<alpha>s)))"
  apply(insert assms)
  apply (induct "\<alpha>s")
  apply (auto simp add: zero_def e_less_eq_mon e_less_eq_refl) 
  done

lemma e_less_eq_lem1:
  "\<lbrakk>\<not> e_less_eq e a;e_less_eq e (a + b)\<rbrakk> \<Longrightarrow> e_less_eq e b"
  apply (auto simp add: plus_def)
  apply (cases a)
  apply auto
  apply (cases b)
  apply auto
  apply (metis le_max_iff_disj)
  done

lemma p_unwrap_less_sum: "snd (p_unwrap ((LP e aa) + b)) \<le> aa"
  apply (cases b)
  apply (auto simp add: plus_def)
done

lemma  sum_list_less_elems: "\<forall>x\<in>set xs. snd x \<noteq> Infty \<Longrightarrow>
  \<forall>y\<in>set (map snd (map p_unwrap (map snd xs))).
              snd (p_unwrap (sum_list (map snd xs))) \<le> y"          
    proof (induct xs)
    case Nil thus ?case by simp
    next
    case (Cons a as) thus ?case
      apply auto
      apply (cases "(snd a)" rule: p_unwrap.cases)
      apply auto
      apply (cases "sum_list (map snd as)")
      apply auto
      apply (metis linorder_linear p_min_re_neut p_unwrap.simps 
        plus_def[abs_def] snd_eqD)
      apply (auto simp add: p_unwrap_less_sum)
      apply (unfold plus_def)
      apply (cases "(snd a, sum_list (map snd as))" rule: p_min.cases)
      apply auto
      apply (cases "map snd as")
      apply (auto simp add: infadd)
      apply (metis min.coboundedI2 snd_conv)
      done
qed

lemma distinct_sortet_list_app:
  "\<lbrakk>sorted xs; distinct xs; xs = as @ b # cs\<rbrakk>
  \<Longrightarrow> \<forall> x\<in> set cs. b < x"
  by (metis distinct.simps(2) distinct_append 
    linorder_antisym_conv2 sorted.simps(2) sorted_append)

lemma distinct_sorted_list_lem1:
  assumes 
  "sorted xs"
  "sorted ys"
  "distinct xs"
  "distinct ys"
  " \<forall> x \<in> set xs. x < e"
  " \<forall> y \<in> set ys. e < y"
  shows 
  "sorted (xs @ e # ys)"
  "distinct (xs @ e # ys)"
proof -
  from assms (5,6)
  have "\<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y" by force
  thus "sorted (xs @ e # ys)"
    using assms
    by (auto simp add: sorted_append)
  have "set xs \<inter> set ys = {}" using assms (5,6) by force
  thus "distinct (xs @ e # ys)"
    using assms
    by (auto)
qed

lemma distinct_sorted_list_lem2:
  assumes 
  "sorted xs"
  "sorted ys"
  "distinct xs"
  "distinct ys"
  "e < e'"  
  " \<forall> x \<in> set xs. x < e"
  " \<forall> y \<in> set ys. e' < y"
  shows 
  "sorted (xs @ e # e' # ys)"
  "distinct (xs @ e # e' # ys)"
proof -
  have "sorted (e' # ys)"
    "distinct (e' # ys)"
    "\<forall> y \<in> set (e' # ys). e < y"
    using assms(2,4,5,7)
    by (auto)
  thus "sorted (xs @ e # e' # ys)"
  "distinct (xs @ e # e' # ys)"
    using assms(1,3,6) distinct_sorted_list_lem1[of xs "e' # ys" e]  
    by auto
qed

lemma map_of_distinct_upd:
  "x \<notin> set (map fst xs) \<Longrightarrow> [x \<mapsto> y] ++ map_of xs = (map_of xs) (x \<mapsto> y)"
  by (induct xs) (auto simp add: fun_upd_twist)

lemma map_of_distinct_upd2:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ (x,y) # ys) = (map_of (xs @ ys))(x \<mapsto> y)"
  apply(insert assms)
  apply(induct xs)
  apply (auto intro: ext)
  done

lemma map_of_distinct_upd3:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ (x,y) # ys) = (map_of (xs @ (x,y') # ys))(x \<mapsto> y)"
  apply(insert assms)
  apply(induct xs)
  apply (auto intro: ext)
  done

lemma map_of_distinct_upd4:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ ys) = (map_of (xs @ (x,y) # ys))(x := None)"
  apply(insert assms)
  apply(induct xs)

  apply clarsimp
  apply (metis dom_map_of_conv_image_fst fun_upd_None_restrict 
    restrict_complement_singleton_eq restrict_map_self)

  apply (auto simp add: map_of_eq_None_iff) []
  done

lemma map_of_distinct_lookup:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ (x,y) # ys) x = Some y"
proof -
  have "map_of (xs @ (x,y) # ys) = (map_of (xs @ ys)) (x \<mapsto> y)"
    using assms map_of_distinct_upd2 by simp
  thus ?thesis
    by simp
qed

lemma ran_distinct: 
  assumes dist: "distinct (map fst al)" 
  shows "ran (map_of al) = snd ` set al"
using assms proof (induct al)
  case Nil then show ?case by simp
next
  case (Cons kv al)
  then have "ran (map_of al) = snd ` set al" by simp
  moreover from Cons.prems have "map_of al (fst kv) = None"
    by (simp add: map_of_eq_None_iff)
  ultimately show ?case by (simp only: map_of.simps ran_map_upd) simp
qed




subsubsection "Finite"

lemma aluprio_finite_correct: "uprio_finite (aluprio_\<alpha> \<alpha>) (aluprio_invar \<alpha> invar)" 
  by(unfold_locales) (simp add: aluprio_defs finite_dom_map_of)

subsubsection "Empty"
lemma aluprio_empty_correct:
  assumes "al_empty \<alpha> invar empt"
  shows "uprio_empty (aluprio_\<alpha> \<alpha>) (aluprio_invar \<alpha> invar) (aluprio_empty empt)"
proof -
  interpret al_empty \<alpha> invar empt by fact
  show ?thesis
    apply (unfold_locales)
    apply (auto simp add: empty_correct aluprio_defs)
    done
qed

subsubsection "Is Empty"

lemma aluprio_isEmpty_correct: 
  assumes "al_isEmpty \<alpha> invar isEmpty"
  shows "uprio_isEmpty (aluprio_\<alpha> \<alpha>) (aluprio_invar \<alpha> invar) (aluprio_isEmpty isEmpty)"
proof -
  interpret al_isEmpty \<alpha> invar isEmpty by fact
  show ?thesis 
    apply (unfold_locales) 
    apply (auto simp add: aluprio_defs isEmpty_correct)
    done
qed


subsubsection "Insert"

lemma annot_inf: 
  assumes A: "invar s" "\<forall>x\<in>set (\<alpha> s). snd x \<noteq> Infty" "al_annot \<alpha> invar annot"
  shows "annot s = Infty \<longleftrightarrow> \<alpha> s = [] " 
proof -
  from A have invs: "invar s" by (simp add: aluprio_defs)  
  interpret al_annot \<alpha> invar annot by fact
  show "annot s = Infty \<longleftrightarrow> \<alpha> s = []"  
  proof (cases "\<alpha> s = []")
    case True
    hence "map snd (\<alpha> s) = []" by simp
    hence "sum_list (map snd (\<alpha> s)) = Infty"  
      by (auto simp add: zero_def)
    with invs have  "annot s = Infty" by (auto simp add: annot_correct)
    with True show ?thesis by simp
  next
    case False
    hence " \<exists>x xs. (\<alpha> s) = x # xs" by (cases "\<alpha> s") auto
    from this obtain x xs where [simp]: "(\<alpha> s) = x # xs" by blast
    from this assms(2) have "snd x \<noteq> Infty" by (auto simp add: aluprio_defs)
    hence "sum_list (map snd (\<alpha> s)) \<noteq> Infty" by (auto simp add: infadd)
    thus ?thesis using annot_correct invs False by simp
  qed
qed

lemma e_less_eq_annot: 
  
  assumes "al_annot \<alpha> invar annot" 
   "invar s" "\<forall>x\<in>set (\<alpha> s). snd x \<noteq> Infty" "\<not> e_less_eq e (annot s)"
  shows "\<forall>x \<in> set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> s)). x < e"
proof -
  interpret al_annot \<alpha> invar annot by fact
  from assms(2) have "annot s = sum_list (map snd (\<alpha> s))"
    by (auto simp add: annot_correct)
  with assms(4) have 
    "\<forall>x \<in> set (map snd (\<alpha> s)). \<not> e_less_eq e x"
    by (metis e_less_eq_sum_list)
  with assms(3) 
  show ?thesis
    by (auto simp add: e_less_eq_p_unwrap)
qed

lemma aluprio_insert_correct: 
  assumes 
  "al_splits \<alpha> invar splits"
  "al_annot \<alpha> invar annot"
  "al_isEmpty \<alpha> invar isEmpty"
  "al_app \<alpha> invar app"
  "al_consr \<alpha> invar consr"
  shows 
  "uprio_insert (aluprio_\<alpha> \<alpha>) (aluprio_invar \<alpha> invar) 
    (aluprio_insert splits annot isEmpty app consr)"
proof -
  interpret al_splits \<alpha> invar splits by fact
  interpret al_annot \<alpha> invar annot by fact
  interpret al_isEmpty \<alpha> invar isEmpty by fact
  interpret al_app \<alpha> invar app by fact
  interpret al_consr \<alpha> invar consr by fact
  show ?thesis 
  proof (unfold_locales, unfold aluprio_defs, goal_cases)
    case g1asms: (1 s e a)
    thus ?case proof (cases "e_less_eq e (annot s) \<and> \<not> isEmpty s")
      case False with g1asms show  ?thesis
        apply (auto simp add: consr_correct )
      proof goal_cases
        case prems: 1
        with assms(2) have  
          "\<forall>x \<in> set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> s)). x < e"
          by (simp add: e_less_eq_annot)
        with prems(3) show ?case
          by(auto simp add: sorted_append)
      next
        case prems: 2
        hence "annot s = sum_list (map snd (\<alpha> s))" 
          by (simp add: annot_correct)
        with prems
        show ?case 
          by (auto simp add: e_less_eq_sum_list2)
      next
        case prems: 3
        hence "\<alpha> s = []" by (auto simp add: isEmpty_correct)
        thus ?case by simp
      next
        case prems: 4
        hence "\<alpha> s = []" by (auto simp add: isEmpty_correct)
        with prems show ?case by simp
      qed
    next
      case True note T1 = this
      obtain l uu lp r where 
        l_lp_r: "(splits (e_less_eq e) Infty s) = (l, ((), lp), r) "
        by (cases "splits (e_less_eq e) Infty s", auto)
      note v2 = splits_correct[of s "e_less_eq e" Infty l "()" lp r]
      have 
        v3: "invar s" 
        "\<not> e_less_eq e Infty"
        "e_less_eq e (Infty + sum_list (map snd (\<alpha> s)))"
        using T1 g1asms annot_correct
        by (auto simp add: plus_def)
      have 
        v4: "\<alpha> s = \<alpha> l @ ((), lp) # \<alpha> r"  
        "\<not> e_less_eq e (Infty + sum_list (map snd (\<alpha> l)))"
        "e_less_eq e (Infty + sum_list (map snd (\<alpha> l)) + lp)"
        "invar l"
        "invar r"
        using v2[OF v3(1) _ v3(2) v3(3) l_lp_r] e_less_eq_mon(1) by auto
      hence v5: "e_less_eq e lp"
        by (metis e_less_eq_lem1)
      hence v6: "e \<le> (fst (p_unwrap lp))"
        by (cases lp) auto
      have "(Infty + sum_list (map snd (\<alpha> l))) = (annot l)"
        by (metis add_0_left annot_correct v4(4) zero_def)
      hence v7:"\<not> e_less_eq e (annot l)"
        using v4(2) by simp
      have "\<forall>x\<in>set (\<alpha> l). snd x \<noteq> Infty"
        using g1asms v4(1) by simp
      hence v7: "\<forall>x \<in> set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> l)). x < e"
        using v4(4) v7 assms(2)
        by(simp add: e_less_eq_annot)
      have v8:"map fst (map p_unwrap (map snd (\<alpha> s))) = 
        map fst (map p_unwrap (map snd (\<alpha> l))) @ fst(p_unwrap lp) #
        map fst (map p_unwrap (map snd (\<alpha> r)))"
        using v4(1)
        by simp
      note distinct_sortet_list_app[of "map fst (map p_unwrap (map snd (\<alpha> s)))"
        "map fst (map p_unwrap (map snd (\<alpha> l)))" "fst(p_unwrap lp)" 
        "map fst (map p_unwrap (map snd (\<alpha> r)))"]
      hence v9: 
        "\<forall> x\<in>set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> r)). fst(p_unwrap lp) < x"
        using v4(1) g1asms v8
        by auto
      have v10: 
        "sorted (map fst (map p_unwrap (map snd (\<alpha> l))))"
        "distinct (map fst (map p_unwrap (map snd (\<alpha> l))))"
        "sorted (map fst (map p_unwrap (map snd (\<alpha> r))))"
        "distinct (map fst (map p_unwrap (map snd (\<alpha> l))))"
        using g1asms v8
        by (auto simp add: sorted_append)
      
      from l_lp_r T1 g1asms show ?thesis        
      proof (fold aluprio_insert_def, cases "e < fst (p_unwrap lp)")
        case True
        hence v11: 
          "aluprio_insert splits annot isEmpty app consr s e a 
            = app (consr (consr l () (LP e a)) () lp) r"
          using l_lp_r T1
          by (auto simp add: aluprio_defs)
        have  v12: "invar (app (consr (consr l () (LP e a)) () lp) r)" 
          using v4(4,5)
          by (auto simp add: app_correct consr_correct)
        have v13: 
          "\<alpha> (app (consr (consr l () (LP e a)) () lp) r) 
            = \<alpha> l @ ((),(LP e a)) # ((), lp) # \<alpha> r"
          using v4(4,5) by (auto simp add: app_correct consr_correct)
        hence v14: 
          "(\<forall>x\<in>set (\<alpha> (app (consr (consr l () (LP e a)) () lp) r)). 
             snd x \<noteq> Infty)"
          using g1asms v4(1)
          by auto
        have v15: "e = fst(p_unwrap (LP e a))" by simp
        hence v16: 
          "sorted (map fst (map p_unwrap 
             (map snd (\<alpha> l @ ((),(LP e a)) # ((), lp) # \<alpha> r))))"              
          "distinct (map fst (map p_unwrap 
             (map snd (\<alpha> l @ ((),(LP e a)) # ((), lp) # \<alpha> r))))"              
          using v10(1,3) v7 True v9 v4(1) g1asms distinct_sorted_list_lem2
          by (auto simp add: sorted_append)              
        thus "invar (aluprio_insert splits annot isEmpty app consr s e a) \<and>
          (\<forall>x\<in>set (\<alpha> (aluprio_insert splits annot isEmpty app consr s e a)). 
             snd x \<noteq> Infty) \<and>
          sorted (map fst (map p_unwrap (map snd (\<alpha> 
             (aluprio_insert splits annot isEmpty app consr s e a))))) \<and> 
          distinct (map fst (map p_unwrap (map snd (\<alpha> 
             (aluprio_insert splits annot isEmpty app consr s e a)))))"
          using v11 v12 v13 v14
          by simp
      next
        case False            
        hence v11: 
          "aluprio_insert splits annot isEmpty app consr s e a 
             = app (consr l () (LP e a)) r"
          using l_lp_r T1
          by (auto simp add: aluprio_defs)
        have  v12: "invar (app (consr l () (LP e a)) r)" using v4(4,5)
          by (auto simp add: app_correct consr_correct)
        have v13: "\<alpha> (app (consr l () (LP e a)) r) = \<alpha> l @ ((),(LP e a)) # \<alpha> r"
          using v4(4,5) by (auto simp add: app_correct consr_correct)
        hence v14: "(\<forall>x\<in>set (\<alpha> (app (consr l () (LP e a)) r)). snd x \<noteq> Infty)"
          using g1asms v4(1)
          by auto
        have v15: "e = fst(p_unwrap (LP e a))" by simp
        have v16: "e = fst(p_unwrap lp)"
          using False v5 by (cases lp) auto
        hence v17: 
          "sorted (map fst (map p_unwrap 
            (map snd (\<alpha> l @ ((),(LP e a)) # \<alpha> r))))"              
          "distinct (map fst (map p_unwrap 
            (map snd (\<alpha> l @ ((),(LP e a)) # \<alpha> r))))"              
          using v16 v15 v10(1,3) v7 True v9 v4(1) 
            g1asms distinct_sorted_list_lem1
          by (auto simp add: sorted_append)              
        thus "invar (aluprio_insert splits annot isEmpty app consr s e a) \<and>
          (\<forall>x\<in>set (\<alpha> (aluprio_insert splits annot isEmpty app consr s e a)). 
            snd x \<noteq> Infty) \<and>
          sorted (map fst (map p_unwrap (map snd (\<alpha> 
            (aluprio_insert splits annot isEmpty app consr s e a))))) \<and> 
          distinct (map fst (map p_unwrap (map snd (\<alpha> 
            (aluprio_insert splits annot isEmpty app consr s e a)))))"
          using v11 v12 v13 v14
          by simp
      qed
    qed
  next
    case g1asms: (2 s e a)
    thus ?case proof (cases "e_less_eq e (annot s) \<and> \<not> isEmpty s")
      case False with g1asms show  ?thesis
        apply (auto simp add: consr_correct)
      proof goal_cases
        case prems: 1
        with assms(2) have  
          "\<forall>x \<in> set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> s)). x < e"
          by (simp add: e_less_eq_annot)
        hence "e \<notin> set (map fst ((map (p_unwrap \<circ> snd)) (\<alpha> s)))"
          by auto
        thus ?case
          by (auto simp add: map_of_distinct_upd)
      next
        case prems: 2
        hence "\<alpha> s = []" by (auto simp add: isEmpty_correct)
        thus ?case
          by simp
      qed
    next
      case True note T1 = this
      obtain l lp r where 
        l_lp_r: "(splits (e_less_eq e) Infty s) = (l, ((), lp), r) "
        by (cases "splits (e_less_eq e) Infty s", auto)
      note v2 = splits_correct[of s "e_less_eq e" Infty l "()" lp r]
      have 
        v3: "invar s" 
        "\<not> e_less_eq e Infty"
        "e_less_eq e (Infty + sum_list (map snd (\<alpha> s)))"
        using T1 g1asms annot_correct
        by (auto simp add: plus_def)
      have 
        v4: "\<alpha> s = \<alpha> l @ ((), lp) # \<alpha> r"  
        "\<not> e_less_eq e (Infty + sum_list (map snd (\<alpha> l)))"
        "e_less_eq e (Infty + sum_list (map snd (\<alpha> l)) + lp)"
        "invar l"
        "invar r"
        using v2[OF v3(1) _ v3(2) v3(3) l_lp_r] e_less_eq_mon(1) by auto
      hence v5: "e_less_eq e lp"
        by (metis e_less_eq_lem1)
      hence v6: "e \<le> (fst (p_unwrap lp))"
        by (cases lp) auto
      have "(Infty + sum_list (map snd (\<alpha> l))) = (annot l)"
        by (metis add_0_left annot_correct v4(4) zero_def)
      hence v7:"\<not> e_less_eq e (annot l)"
        using v4(2) by simp
      have "\<forall>x\<in>set (\<alpha> l). snd x \<noteq> Infty"
        using g1asms v4(1) by simp
      hence v7: "\<forall>x \<in> set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> l)). x < e"
        using v4(4) v7 assms(2)
        by(simp add: e_less_eq_annot)
      have v8:"map fst (map p_unwrap (map snd (\<alpha> s))) = 
        map fst (map p_unwrap (map snd (\<alpha> l))) @ fst(p_unwrap lp) #
        map fst (map p_unwrap (map snd (\<alpha> r)))"
        using v4(1)
        by simp
      note distinct_sortet_list_app[of "map fst (map p_unwrap (map snd (\<alpha> s)))"
        "map fst (map p_unwrap (map snd (\<alpha> l)))" "fst(p_unwrap lp)" 
        "map fst (map p_unwrap (map snd (\<alpha> r)))"]
      hence v9: "
        \<forall> x\<in>set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> r)). fst(p_unwrap lp) < x"
        using v4(1) g1asms v8
        by auto
      hence v10: " \<forall> x\<in>set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> r)). e < x"
        using v6 by auto
      have v11: 
        "e \<notin> set (map fst (map p_unwrap (map snd (\<alpha> l))))"
        "e \<notin> set (map fst (map p_unwrap (map snd (\<alpha> r))))"
        using v7 v10 v8 g1asms
        by auto
      from l_lp_r T1 g1asms show ?thesis        
      proof (fold aluprio_insert_def, cases "e < fst (p_unwrap lp)")
        case True
        hence v12: 
          "aluprio_insert splits annot isEmpty app consr s e a 
            = app (consr (consr l () (LP e a)) () lp) r"
          using l_lp_r T1
          by (auto simp add: aluprio_defs)
        have v13: 
          "\<alpha> (app (consr (consr l () (LP e a)) () lp) r) 
            = \<alpha> l @ ((),(LP e a)) # ((), lp) # \<alpha> r"
          using v4(4,5) by (auto simp add: app_correct consr_correct)
        have v14: "e = fst(p_unwrap (LP e a))" by simp
        have v15: "e \<notin> set (map fst (map p_unwrap (map snd(((),lp)#\<alpha> r))))"
          using v11(2) True by auto
        note map_of_distinct_upd2[OF v11(1) v15]
        thus 
          "map_of (map p_unwrap (map snd (\<alpha> 
              (aluprio_insert splits annot isEmpty app consr s e a)))) 
            = map_of (map p_unwrap (map snd (\<alpha> s)))(e \<mapsto> a)"
          using v12 v13 v4(1)
          by simp
      next
        case False            
        hence v12: 
          "aluprio_insert splits annot isEmpty app consr s e a 
            = app (consr l () (LP e a)) r"
          using l_lp_r T1
          by (auto simp add: aluprio_defs)
        have v13: 
          "\<alpha> (app (consr l () (LP e a)) r) = \<alpha> l @ ((),(LP e a)) # \<alpha> r"
          using v4(4,5) by (auto simp add: app_correct consr_correct)
        have v14: "e = fst(p_unwrap lp)"
          using False v5 by (cases lp) auto
        note v15 = map_of_distinct_upd3[OF v11(1) v11(2)]
        have v16:"(map p_unwrap (map snd (\<alpha> s))) = 
          (map p_unwrap (map snd (\<alpha> l))) @ (e,snd(p_unwrap lp)) #
          (map p_unwrap (map snd (\<alpha> r)))"
          using v4(1) v14              
          by simp
        note v15[of a "snd(p_unwrap lp)"]         
        thus 
          "map_of (map p_unwrap (map snd (\<alpha> 
              (aluprio_insert splits annot isEmpty app consr s e a)))) 
            = map_of (map p_unwrap (map snd (\<alpha> s)))(e \<mapsto> a)"
          using v12 v13 v16
          by simp
      qed
    qed
  qed
qed

subsubsection "Prio"
lemma aluprio_prio_correct: 
  assumes 
  "al_splits \<alpha> invar splits"
  "al_annot \<alpha> invar annot"
  "al_isEmpty \<alpha> invar isEmpty"
  shows 
  "uprio_prio (aluprio_\<alpha> \<alpha>) (aluprio_invar \<alpha> invar) (aluprio_prio splits annot isEmpty)"
proof -
  interpret al_splits \<alpha> invar splits by fact
  interpret al_annot \<alpha> invar annot by fact
  interpret al_isEmpty \<alpha> invar isEmpty by fact
  show ?thesis 
  proof (unfold_locales)
    fix s e
    assume inv1: "aluprio_invar \<alpha> invar s"
    hence sinv: "invar s" 
      "(\<forall> x\<in>set (\<alpha> s). snd x\<noteq>Infty)"
      "sorted (map fst (map p_unwrap (map snd (\<alpha> s))))" 
      "distinct (map fst (map p_unwrap (map snd (\<alpha> s))))"
      by (auto simp add: aluprio_defs)
    show "aluprio_prio splits annot isEmpty s e = aluprio_\<alpha> \<alpha> s e"
    proof(cases "e_less_eq e (annot s) \<and> \<not> isEmpty s")
      case False note F1 = this      
      thus ?thesis
      proof(cases "isEmpty s")
        case True
        hence "\<alpha> s = []"
          using sinv isEmpty_correct by simp
        hence "aluprio_\<alpha> \<alpha> s = Map.empty" by (simp add:aluprio_defs)
        hence "aluprio_\<alpha> \<alpha> s e = None" by simp
        thus "aluprio_prio splits annot isEmpty s e = aluprio_\<alpha> \<alpha> s e"
          using F1 
          by (auto simp add: aluprio_defs)
      next
        case False
        hence v3:"\<not> e_less_eq e (annot s)"  using F1 by simp
        note v4=e_less_eq_annot[OF assms(2)]
        note v4[OF sinv(1) sinv(2) v3]
        hence v5:"e\<notin>set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> s))"
          by auto
        hence "map_of (map (p_unwrap \<circ> snd) (\<alpha> s)) e = None"
          using map_of_eq_None_iff
          by (metis map_map map_of_eq_None_iff set_map v5) 
        thus "aluprio_prio splits annot isEmpty s e = aluprio_\<alpha> \<alpha> s e"
          using F1 
          by (auto simp add: aluprio_defs)
      qed
    next
      case True note T1 = this
      obtain l uu lp r where 
        l_lp_r: "(splits (e_less_eq e) Infty s) = (l, ((), lp), r) "
        by (cases "splits (e_less_eq e) Infty s", auto)
      note v2 = splits_correct[of s "e_less_eq e" Infty l "()" lp r]
      have 
        v3: "invar s" 
        "\<not> e_less_eq e Infty"
        "e_less_eq e (Infty + sum_list (map snd (\<alpha> s)))"
        using T1 sinv annot_correct
        by (auto simp add: plus_def)
      have 
        v4: "\<alpha> s = \<alpha> l @ ((), lp) # \<alpha> r"  
        "\<not> e_less_eq e (Infty + sum_list (map snd (\<alpha> l)))"
        "e_less_eq e (Infty + sum_list (map snd (\<alpha> l)) + lp)"
        "invar l"
        "invar r"
        using v2[OF v3(1) _ v3(2) v3(3) l_lp_r] e_less_eq_mon(1) by auto
      hence v5: "e_less_eq e lp"
        by (metis e_less_eq_lem1)
      hence v6: "e \<le> (fst (p_unwrap lp))"
        by (cases lp) auto
      have "(Infty + sum_list (map snd (\<alpha> l))) = (annot l)"
        by (metis add_0_left annot_correct v4(4) zero_def)
      hence v7:"\<not> e_less_eq e (annot l)"
        using v4(2) by simp
      have "\<forall>x\<in>set (\<alpha> l). snd x \<noteq> Infty"
        using sinv v4(1) by simp
      hence v7: "\<forall>x \<in> set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> l)). x < e"
        using v4(4) v7 assms(2)
        by(simp add: e_less_eq_annot)
      have v8:"map fst (map p_unwrap (map snd (\<alpha> s))) = 
        map fst (map p_unwrap (map snd (\<alpha> l))) @ fst(p_unwrap lp) #
        map fst (map p_unwrap (map snd (\<alpha> r)))"
        using v4(1)
        by simp
      note distinct_sortet_list_app[of "map fst (map p_unwrap (map snd (\<alpha> s)))"
        "map fst (map p_unwrap (map snd (\<alpha> l)))" "fst(p_unwrap lp)" 
        "map fst (map p_unwrap (map snd (\<alpha> r)))"]
      hence v9: 
        "\<forall> x\<in>set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> r)). fst(p_unwrap lp) < x"
        using v4(1) sinv v8
        by auto
      hence v10: " \<forall> x\<in>set (map (fst \<circ> (p_unwrap \<circ> snd)) (\<alpha> r)). e < x"
        using v6 by auto
      have v11: 
        "e \<notin> set (map fst (map p_unwrap (map snd (\<alpha> l))))"
        "e \<notin> set (map fst (map p_unwrap (map snd (\<alpha> r))))"
        using v7 v10 v8 sinv
        by auto
      from l_lp_r T1 sinv show ?thesis
      proof (cases "e = fst (p_unwrap lp)")
        case False
        have v12: "e \<notin> set (map fst (map p_unwrap (map snd(\<alpha> s))))"
          using v11 False v4(1) by auto
        hence "map_of (map (p_unwrap \<circ> snd) (\<alpha> s)) e = None"
          using map_of_eq_None_iff
          by (metis map_map map_of_eq_None_iff set_map v12)
        thus ?thesis
          using T1 False l_lp_r
          by (auto simp add: aluprio_defs)
      next
        case True
        have v12: "map (p_unwrap \<circ> snd) (\<alpha> s) = 
          map p_unwrap (map snd (\<alpha> l)) @ (e,snd (p_unwrap lp)) #
          map p_unwrap (map snd (\<alpha> r))"
          using v4(1) True by simp
        note map_of_distinct_lookup[OF v11]
        hence
          "map_of (map (p_unwrap \<circ> snd) (\<alpha> s)) e = Some (snd (p_unwrap lp))"
          using v12 by simp
        thus ?thesis
          using T1 True l_lp_r
          by (auto simp add: aluprio_defs)
      qed
    qed
  qed
qed
        

subsubsection "Pop"

lemma aluprio_pop_correct: 
  assumes "al_splits \<alpha> invar splits"
  "al_annot \<alpha> invar annot"
  "al_app \<alpha> invar app"
  shows 
  "uprio_pop (aluprio_\<alpha> \<alpha>) (aluprio_invar \<alpha> invar) (aluprio_pop splits annot app)"
proof -
  interpret al_splits \<alpha> invar splits by fact
  interpret al_annot \<alpha> invar annot by fact
  interpret al_app \<alpha> invar app by fact
  show ?thesis 
  proof (unfold_locales)
    fix s e a s'
    assume A: "aluprio_invar \<alpha> invar s" 
      "aluprio_\<alpha> \<alpha> s \<noteq> Map.empty" 
      "aluprio_pop splits annot app s = (e, a, s')"
    hence v1: "\<alpha> s \<noteq> []"
      by (auto simp add: aluprio_defs)
    obtain l lp r where
      l_lp_r: "splits (\<lambda> x. x\<le>annot s) Infty s = (l,((),lp),r)"
      by (cases "splits (\<lambda> x. x\<le>annot s) Infty s", auto)
    have invs:
      "invar s" 
      "(\<forall>x\<in>set (\<alpha> s). snd x \<noteq> Infty)"
      "sorted (map fst (map p_unwrap (map snd (\<alpha> s))))"
      "distinct (map fst (map p_unwrap (map snd (\<alpha> s))))"
      using A by (auto simp add:aluprio_defs)
    note a1 = annot_inf[of invar s \<alpha> annot]
    note a1[OF invs(1) invs(2) assms(2)]
    hence v2: "annot s \<noteq> Infty"
      using v1 by simp
    hence v3:
      "\<not> Infty \<le> annot s"
      by(cases "annot s") (auto simp add: plesseq_def)
    have v4: "annot s = sum_list (map snd (\<alpha> s))"
      by (auto simp add: annot_correct invs(1))
    hence 
      v5:
      "(Infty + sum_list (map snd (\<alpha> s))) \<le> annot s"
      by (auto simp add: plus_def)
    note p_mon = p_less_eq_mon[of _ "annot s"]
    note v6 = splits_correct[OF invs(1)]
    note v7 = v6[of "\<lambda> x. x \<le> annot s"]
    note v7[OF _ v3 v5 l_lp_r] p_mon
    hence v8: 
      " \<alpha> s = \<alpha> l @ ((), lp) # \<alpha> r"
      "\<not> Infty + sum_list (map snd (\<alpha> l)) \<le> annot s"
      "Infty + sum_list (map snd (\<alpha> l)) + lp \<le> annot s"
      "invar l"
      "invar r"
      by auto
    hence v9: "lp \<noteq> Infty"
      using invs(2) by auto
    hence v10: 
      "s' = app l r" 
      "(e,a) = p_unwrap lp"
      using l_lp_r A(3)
      apply (auto simp add: aluprio_defs)
      apply (cases lp)
      apply auto
      apply (cases lp)
      apply auto
      done
    have "lp \<le> annot s"
      using v8(2,3) p_less_eq_lem1
      by auto
    hence v11: "a \<le> snd (p_unwrap (annot s))"
      using v10(2) v2 v9
      apply (cases "annot s")
      apply auto
      apply (cases lp)
      apply (auto simp add: plesseq_def)
      done 
    note sum_list_less_elems[OF invs(2)]
    hence v12: "\<forall>y\<in>set (map snd (map p_unwrap (map snd (\<alpha> s)))). a \<le> y"
      using v4 v11 by auto
    have "ran (aluprio_\<alpha> \<alpha> s) = set (map snd (map p_unwrap (map snd (\<alpha> s))))"
      using ran_distinct[OF invs(4)]
      apply (unfold aluprio_defs)
      apply (simp only: set_map)
      done
    hence ziel1: "\<forall>y\<in>ran (aluprio_\<alpha> \<alpha> s). a \<le> y"
      using v12 by simp
    have v13:
      "map p_unwrap (map snd (\<alpha> s)) 
        = map p_unwrap (map  snd (\<alpha> l)) @ (e,a) # map p_unwrap (map snd (\<alpha> r))"
      using v8(1) v10 by auto
     hence v14:
      "map fst (map p_unwrap (map snd (\<alpha> s))) 
         = map fst (map p_unwrap (map snd (\<alpha> l))) @ e 
             # map fst (map p_unwrap (map snd (\<alpha> r)))"
       by auto
    hence v15: 
      "e \<notin> set (map fst (map p_unwrap (map snd (\<alpha> l))))"
      "e \<notin> set (map fst (map p_unwrap (map snd (\<alpha> r))))"
      using invs(4) by auto
    note map_of_distinct_lookup[OF v15]
    note this[of a]
    hence ziel2: "aluprio_\<alpha> \<alpha> s e = Some a"
      using  v13
      by (unfold aluprio_defs, auto)
    have v16: 
      "\<alpha> s' = \<alpha> l @ \<alpha> r" 
      "invar s'"
      using v8(4,5) app_correct v10 by auto
    note map_of_distinct_upd4[OF v15]
    note this[of a]
    hence 
      ziel3: "aluprio_\<alpha> \<alpha> s' = (aluprio_\<alpha> \<alpha> s)(e := None)"
      unfolding aluprio_defs
      using v16(1) v13 by auto
    have ziel4: "aluprio_invar \<alpha> invar s'"
      using v16 v8(1) invs(2,3,4)
      unfolding aluprio_defs
      by (auto simp add: sorted_append)
    
    show "aluprio_invar \<alpha> invar s' \<and>
          aluprio_\<alpha> \<alpha> s' = (aluprio_\<alpha> \<alpha> s)(e := None) \<and>
          aluprio_\<alpha> \<alpha> s e = Some a \<and> (\<forall>y\<in>ran (aluprio_\<alpha> \<alpha> s). a \<le> y)"
      using ziel1 ziel2 ziel3 ziel4 by simp
  qed
qed
    
lemmas aluprio_correct =
  aluprio_finite_correct
  aluprio_empty_correct
  aluprio_isEmpty_correct
  aluprio_insert_correct
  aluprio_pop_correct
  aluprio_prio_correct

locale aluprio_defs = StdALDefs ops 
  for ops :: "(unit,('e::linorder,'a::linorder) LP,'s) alist_ops"
begin
  definition [icf_rec_def]: "aluprio_ops \<equiv> \<lparr>
    upr_\<alpha> = aluprio_\<alpha> \<alpha>,
    upr_invar = aluprio_invar \<alpha> invar,
    upr_empty = aluprio_empty empty,
    upr_isEmpty = aluprio_isEmpty isEmpty,
    upr_insert = aluprio_insert splits annot isEmpty app consr,
    upr_pop = aluprio_pop splits annot app,
    upr_prio = aluprio_prio splits annot isEmpty
    \<rparr>"
  
end

locale aluprio = aluprio_defs ops + StdAL ops 
  for ops :: "(unit,('e::linorder,'a::linorder) LP,'s) alist_ops"
begin
  lemma aluprio_ops_impl: "StdUprio aluprio_ops"
    apply (rule StdUprio.intro)
    apply (simp_all add: icf_rec_unf)
    apply (rule aluprio_correct)
    apply (rule aluprio_correct, unfold_locales) []
    apply (rule aluprio_correct, unfold_locales) []
    apply (rule aluprio_correct, unfold_locales) []
    apply (rule aluprio_correct, unfold_locales) []
    apply (rule aluprio_correct, unfold_locales) []
    done
end

end
