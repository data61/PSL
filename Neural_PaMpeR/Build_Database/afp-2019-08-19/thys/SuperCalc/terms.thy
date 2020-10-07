theory terms

(* N. Peltier - http://membres-lig.imag.fr/peltier/ *)

imports "HOL-ex.Unification"

begin

section \<open>Terms\<close>

subsection \<open>Basic Syntax\<close>

text \<open>We use the same term representation as in the Unification theory provided in Isabelle. 
Terms are represented by binary trees built on variables and constant symbols.\<close>
 
fun is_a_variable 
where
  "(is_a_variable (Var x)) = True" |
  "(is_a_variable (Const x)) = False" |
  "(is_a_variable (Comb x y)) = False"

fun is_a_constant
where
  "(is_a_constant (Var x)) = False" |
  "(is_a_constant (Const x)) = True" |
  "(is_a_constant (Comb x y)) = False"

fun is_compound
where
  "(is_compound (Var x)) = False" |
  "(is_compound (Const x)) = False" |
  "(is_compound (Comb x y)) = True"

definition ground_term :: "'a trm \<Rightarrow> bool"
where
  "(ground_term t) = (vars_of t = {})"

lemma constants_are_not_variables :
  assumes "is_a_constant x"
  shows "\<not> (is_a_variable x)"
by (metis assms is_a_constant.elims(2) is_a_variable.elims(2) trm.distinct(2))

lemma constants_are_ground : 
  assumes "is_a_constant x"
  shows "ground_term x"
proof -
  from assms obtain y where "x = (Const y)" using is_a_constant.elims(2) by auto 
  then show ?thesis by (simp add: ground_term_def) 
qed

subsection \<open>Positions\<close>

text \<open>We define the notion of a position together with functions to access to subterms and 
replace them. We establish some basic properties of these functions.\<close>

text \<open>Since terms are binary trees, positions are sequences of binary digits.\<close>

datatype indices = Left | Right

type_synonym position = "indices list"

fun left_app
  where "left_app x = Left # x"

fun right_app
  where "right_app x = Right # x"

definition strict_prefix
where
  "strict_prefix p q = (\<exists>r. (r \<noteq> []) \<and> (q = (append p r)))"

fun subterm :: "'a trm \<Rightarrow> position \<Rightarrow> 'a trm \<Rightarrow> bool"
  where 
    "(subterm T [] S) = (T = S)" |
    "(subterm (Var v) (first # next) S) = False" |
    "(subterm (Const c) (first # next) S) = False" |
    "(subterm (Comb x y) (Left # next) S) = (subterm x next S)" |
    "(subterm (Comb x y) (Right # next) S) = (subterm y next S)"

definition occurs_in :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool"
  where
    "occurs_in t s = (\<exists>p. subterm s p t)"

definition position_in :: "position \<Rightarrow> 'a trm \<Rightarrow> bool"
  where
    "position_in p s = (\<exists>t. subterm s p t)"

fun subterms_of 
where
  "subterms_of t = { s. (occurs_in s t) }"

fun proper_subterms_of 
where
  "proper_subterms_of t = { s. \<exists>p. (p \<noteq> Nil \<and> (subterm t p s)) }"

fun pos_of 
where
  "pos_of t = { p. (position_in p t) }"
 
fun replace_subterm :: 
  "'a trm \<Rightarrow> position \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool"
  where 
    "(replace_subterm T [] u S) = (S = u) " |
    "(replace_subterm (Var x) (first # next) u S) = False" |
    "(replace_subterm (Const c) (first # next) u S) = False" |
    "(replace_subterm (Comb x y) (Left # next) u S) =  
      (\<exists>S1. (replace_subterm x next u S1) \<and> (S = Comb S1 y))" |
    "(replace_subterm (Comb x y) (Right # next) u S) = 
      (\<exists>S2. (replace_subterm y next u S2) \<and> (S = Comb x S2))"

lemma replace_subterm_is_a_function: 
  shows "\<And>t u v. subterm t p u \<Longrightarrow> \<exists>s. replace_subterm t p v s"
proof (induction p,auto)
  next case (Cons i q)
    from \<open>subterm t (Cons i q) u\<close> obtain t1 t2 where "t = (Comb t1 t2)"
      using subterm.elims(2) by blast 
    have "i = Right \<or> i = Left" using indices.exhaust by auto 
    then show ?case
    proof
      assume "i = Right"
      from this and \<open>t = (Comb t1 t2)\<close> and \<open>subterm t (Cons i q) u\<close> have "subterm t2 q u" by auto
      from this obtain s where "replace_subterm t2 q v s" using Cons.IH [of t2 u] by auto
      from this and \<open>t = (Comb t1 t2)\<close> and \<open>i = Right\<close> have "replace_subterm t (Cons i q) v (Comb t1 s)" 
        by auto
      from this show ?case by auto
    next assume "i = Left"
      from this and \<open>t = (Comb t1 t2)\<close> and \<open>subterm t (Cons i q) u\<close> have "subterm t1 q u" by auto
      from this obtain s where "replace_subterm t1 q v s" using Cons.IH [of t1 u] by auto
      from this and \<open>t = (Comb t1 t2)\<close> and \<open>i = Left\<close> have "replace_subterm t (Cons i q) v (Comb s t2)" 
        by auto
      from this show ?case by auto
    qed
qed

text \<open>We prove some useful lemmata concerning the set of variables or subterms occurring in a 
term.\<close>

lemma root_subterm:
  shows "t \<in> (subterms_of t)"
by (metis mem_Collect_eq occurs_in_def subterm.simps(1) subterms_of.simps)

lemma root_position:
  shows "Nil \<in> (pos_of t)"
by (metis mem_Collect_eq subterm.simps(1) position_in_def pos_of.simps)

lemma subterms_of_an_atomic_term:
  assumes "is_a_variable t \<or> is_a_constant t"
  shows "subterms_of t = { t }"
proof 
  show "subterms_of t \<subseteq> { t }"
  proof 
    fix x assume "x \<in> subterms_of t"
    then have "occurs_in x t" by auto
    then have "\<exists>p. (subterm t p x)" unfolding occurs_in_def by auto
    from this and assms have "x = t" 
     by (metis is_a_constant.simps(3) is_a_variable.simps(3) subterm.elims(2)) 
    thus "x \<in> { t }" by auto
  qed
next 
  show "{ t } \<subseteq> subterms_of t"
  proof
    fix x assume "x \<in> { t }"
    then show "x \<in> subterms_of t" using root_subterm by auto
  qed
qed

lemma positions_of_an_atomic_term:
  assumes "is_a_variable t \<or> is_a_constant t"
  shows "pos_of t = { Nil }"
proof 
  show "pos_of t \<subseteq> { Nil }"
  proof 
    fix x assume "x \<in> pos_of t"
    then have "position_in x t" by auto
    then have "\<exists>s. (subterm t x s)" unfolding position_in_def by auto
    from this and assms have "x = Nil" 
     by (metis is_a_constant.simps(3) is_a_variable.simps(3) subterm.elims(2)) 
    thus "x \<in> { Nil }" by auto
  qed
next 
  show "{ Nil } \<subseteq> pos_of t"
  proof
    fix x :: "indices list" assume "x \<in> { Nil }"
    then show "x \<in> pos_of t" using root_position by auto
  qed
qed

lemma subterm_of_a_subterm_is_a_subterm :
  assumes "subterm u q v"
  shows "\<And> t. subterm t p u \<Longrightarrow> subterm t (append p q) v"
proof (induction p)
  case Nil
    show "?case" using Nil.prems assms by auto  
  next case (Cons i p')
    from \<open>subterm t (Cons i p') u\<close> obtain t1 t2 where "t = (Comb t1 t2)"
      using subterm.elims(2) by blast 
    have "i = Right \<or> i = Left" using indices.exhaust by auto 
    then show ?case
    proof
      assume "i = Right"
      from this and \<open>subterm t (Cons i p') u\<close> and \<open>t = (Comb t1 t2)\<close> 
        have "subterm t2 p' u" by auto
      from this have "subterm t2 (append p' q) v" by (simp add: Cons.IH) 
      from this and  \<open>t = (Comb t1 t2)\<close> and \<open>i = Right\<close> show "subterm t  (append (Cons i p') q) v"
        by simp 
    next assume "i = Left"
      from this and \<open>subterm t (Cons i p') u\<close> and \<open>t = (Comb t1 t2)\<close> 
        have "subterm t1 p' u" by auto
      from this have "subterm t1 (append p' q) v" by (simp add: Cons.IH) 
      from this and  \<open>t = (Comb t1 t2)\<close> and \<open>i = Left\<close> show "subterm t  (append (Cons i p') q) v"
        by simp 
    qed
qed

lemma occur_in_subterm:
  assumes "occurs_in u t"
  assumes "occurs_in t s"
  shows "occurs_in u s"
by (meson assms(1) assms(2) occurs_in_def subterm_of_a_subterm_is_a_subterm)

lemma vars_of_subterm :
  assumes "x \<in> vars_of s"
  shows "\<And> t. subterm t p s \<Longrightarrow> x \<in> vars_of t"
proof (induction p)
  case Nil
    show "?case" using Nil.prems assms by auto  
  next case (Cons i p')
    from \<open>subterm t (Cons i p') s\<close> obtain t1 t2 where "t = (Comb t1 t2)"
      using subterm.elims(2) by blast 
    have "i = Right \<or> i = Left" using indices.exhaust by auto 
    then show ?case
    proof
      assume "i = Right"
      from this and \<open>subterm t (Cons i p') s\<close> and \<open>t = (Comb t1 t2)\<close> 
        have "subterm t2 p' s" by auto
      from this have "x \<in> vars_of t2" by (simp add: Cons.IH) 
      from this and  \<open>t = (Comb t1 t2)\<close> and \<open>i = Right\<close> show ?case
        by simp 
    next assume "i = Left"
      from this and \<open>subterm t (Cons i p') s\<close> and \<open>t = (Comb t1 t2)\<close> 
        have "subterm t1 p' s" by auto
      from this have "x \<in> vars_of t1" by (simp add: Cons.IH) 
      from this and  \<open>t = (Comb t1 t2)\<close> and \<open>i = Left\<close> show ?case
        by simp 
    qed
qed

lemma vars_subterm :
  assumes "subterm t p s"
  shows "vars_of s \<subseteq> vars_of t"
by (meson assms subsetI vars_of_subterm)

lemma vars_subterms_of :
  assumes "s \<in> subterms_of t"
  shows "vars_of s \<subseteq> vars_of t"
using assms occurs_in_def vars_subterm by fastforce

lemma subterms_of_a_non_atomic_term:
  shows "subterms_of (Comb t1 t2) = (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }"
proof
  show "subterms_of (Comb t1 t2) \<subseteq> (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }"
  proof
    fix x assume "x \<in> (subterms_of (Comb t1 t2))"
    then have "occurs_in x (Comb t1 t2)" by auto
    then obtain p where "subterm (Comb t1 t2) p x" unfolding occurs_in_def by auto
    have "p = [] \<or> (\<exists>i q. p = i #q)" using neq_Nil_conv by blast 
    then show "x \<in> (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }"
    proof 
      assume "p = []" 
      from this and \<open>subterm (Comb t1 t2) p x\<close> show ?thesis by auto
    next
      assume "\<exists>i q. p = i #q"
      then obtain i q where "p = i # q" by auto 
      have "i = Left \<or> i = Right" using indices.exhaust by blast  
      then show "x \<in> (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }"
      proof 
        assume "i = Left"
        from this and \<open>p = i # q\<close> and \<open>subterm (Comb t1 t2) p x\<close> 
          have "subterm t1 q x" by auto
        then have "occurs_in x t1" unfolding occurs_in_def by auto
        then show "x \<in> (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }" by auto
      next
        assume "i = Right"
        from this and \<open>p = i # q\<close> and \<open>subterm (Comb t1 t2) p x\<close> 
          have "subterm t2 q x" by auto
        then have "occurs_in x t2" unfolding occurs_in_def by auto
        then show "x \<in> (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }" by auto
      qed
    qed
  qed
next
  show "(subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) } \<subseteq> subterms_of (Comb t1 t2)"
  proof
    fix x assume "x \<in> (subterms_of t1) \<union> (subterms_of t2) \<union> { (Comb t1 t2) }"
    then have "x \<in> (subterms_of t1) \<or> (x \<in> (subterms_of t2) \<or> x = (Comb t1 t2))" by auto
    thus "x \<in> subterms_of (Comb t1 t2)"
    proof
      assume "x \<in> (subterms_of t1)"
      then have "occurs_in x t1" by auto
      then obtain p where "subterm t1 p x" unfolding occurs_in_def by auto 
      then have "subterm (Comb t1 t2) (Left # p) x" by auto
      then have "occurs_in x (Comb t1 t2)" using occurs_in_def by blast
      then show "x \<in> subterms_of (Comb t1 t2)" by auto
    next        
      assume "(x \<in> (subterms_of t2) \<or> x = (Comb t1 t2))"
      then show "x \<in> subterms_of (Comb t1 t2)" 
      proof
        assume "x \<in> (subterms_of t2)"
        then have "occurs_in x t2" by auto
        then obtain p where "subterm t2 p x" unfolding occurs_in_def by auto 
        then have "subterm (Comb t1 t2) (Right # p) x" by auto
        then have "occurs_in x (Comb t1 t2)" using occurs_in_def by blast
        then show "x \<in> subterms_of (Comb t1 t2)" by auto
      next
        assume "x = (Comb t1 t2)"
        show "x \<in> subterms_of (Comb t1 t2)" using \<open>x = t1 \<cdot> t2\<close> root_subterm by blast 
      qed
    qed
  qed
qed

lemma positions_of_a_non_atomic_term:
  shows "pos_of (Comb t1 t2) = (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }"
proof
  show "pos_of (Comb t1 t2) \<subseteq> (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }"
  proof
    fix x assume "x \<in> pos_of (Comb t1 t2)"
    then have "position_in x (Comb t1 t2)" by auto
    then obtain s where "subterm (Comb t1 t2) x s" unfolding position_in_def by auto
    have "x = [] \<or> (\<exists>i q. x = i #q)" using neq_Nil_conv by blast 
    then show "x \<in> (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }"
    proof 
      assume "x = []" 
      from this and \<open>subterm (Comb t1 t2) x s\<close> show ?thesis by auto
    next
      assume "\<exists>i q. x = i #q"
      then obtain i q where "x = i # q" by auto 
      have "i = Left \<or> i = Right" using indices.exhaust by blast  
      then show "x \<in> (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }"
      proof 
        assume "i = Left"
        from this and \<open>x = i # q\<close> and \<open>subterm (Comb t1 t2) x s\<close> 
          have "subterm t1 q s" by auto
        then have "position_in q t1" unfolding position_in_def by auto
        from this and \<open>x = i # q\<close> \<open>i = Left\<close>
          show "x \<in> (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }" by auto
      next
        assume "i = Right"
        from this and \<open>x = i # q\<close> and \<open>subterm (Comb t1 t2) x s\<close> 
          have "subterm t2 q s" by auto
        then have "position_in q t2" unfolding position_in_def by auto
        from this and \<open>x = i # q\<close> \<open>i = Right\<close>
          show "x \<in> (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }" by auto
      qed
    qed
  qed
next
  show "(left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil } \<subseteq> pos_of (Comb t1 t2)"
  proof
    fix x assume "x \<in> (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }"
    then have "(x \<in> left_app ` (pos_of t1)) \<or> ((x \<in> (right_app ` (pos_of t2))) \<or> (x = Nil))" by auto
    thus "x \<in> pos_of (Comb t1 t2)"
    proof
      assume "x \<in> left_app ` (pos_of t1)"
      then obtain q where "x = Left # q" and "position_in q t1" by auto
      then obtain s where "subterm t1 q s" unfolding position_in_def by auto 
      then have "subterm (Comb t1 t2) (Left # q) s" by auto
      from this and \<open>x = Left # q\<close> have "position_in x (Comb t1 t2)" using position_in_def by blast
      then show "x \<in> pos_of (Comb t1 t2)" by auto
    next    
      assume "(x \<in> (right_app ` (pos_of t2))) \<or> (x = Nil)"
      then show "x \<in> pos_of (Comb t1 t2)" 
      proof
        assume "x \<in> right_app ` (pos_of t2)"
        then obtain q where "x = Right # q" and "position_in q t2" by auto
        then obtain s where "subterm t2 q s" unfolding position_in_def by auto 
        then have "subterm (Comb t1 t2) (Right # q) s" by auto
        from this and \<open>x = Right # q\<close> have "position_in x (Comb t1 t2)" using position_in_def by blast
        then show "x \<in> pos_of (Comb t1 t2)" by auto
      next
        assume "x = Nil"
        show "x \<in> pos_of (Comb t1 t2)" using \<open>x = Nil\<close> root_position by blast 
      qed
    qed
  qed
qed

lemma set_of_subterms_is_finite :
  shows "(finite (subterms_of (t :: 'a trm)))"
proof (induction t)
    case (Var x)
    then show ?case using subterms_of_an_atomic_term [of "Var x"] by simp
  next
    case (Const x)
    then show ?case using subterms_of_an_atomic_term [of "Const x"]  by simp
  next
    case (Comb t1 t2) assume "finite (subterms_of t1)" and "finite (subterms_of t2)"
    have "subterms_of (Comb t1 t2) = subterms_of t1 \<union> subterms_of t2 \<union> { Comb t1 t2 }" 
      using subterms_of_a_non_atomic_term by auto
    from this and \<open>finite (subterms_of t1)\<close> and \<open>finite (subterms_of t2)\<close> 
      show "finite (subterms_of (Comb t1 t2))" by simp 
qed

lemma set_of_positions_is_finite :
  shows "(finite (pos_of (t :: 'a trm)))"
proof (induction t)
    case (Var x)
    then show ?case using positions_of_an_atomic_term [of "Var x"] by simp
  next
    case (Const x)
    then show ?case using positions_of_an_atomic_term [of "Const x"]  by simp
  next
    case (Comb t1 t2) assume "finite (pos_of t1)" and "finite (pos_of t2)"
    from \<open>finite (pos_of t1)\<close> have i: "finite (left_app ` (pos_of t1))" by auto
    from \<open>finite (pos_of t2)\<close> have ii: "finite (right_app ` (pos_of t2))" by auto
    have "pos_of (Comb t1 t2) = (left_app ` (pos_of t1)) \<union> (right_app ` (pos_of t2)) \<union> { Nil }" 
      using positions_of_a_non_atomic_term by metis
    from this and i ii show "finite (pos_of (Comb t1 t2))" by simp 
qed

lemma vars_of_instances:
  shows "vars_of (subst t \<sigma>) 
    = \<Union> { V. \<exists>x. (x \<in> (vars_of t)) \<and> (V = vars_of (subst (Var x) \<sigma>)) }"
proof (induction t)
  case (Const a)
    have "vars_of (Const a) = {}" by auto
    then have rhs_empty: "\<Union> { V. \<exists>x. (x \<in> (vars_of (Const a))) \<and> (V = vars_of (subst (Var x) \<sigma>)) } = {}" by auto
    have lhs_empty: "(subst (Const a) \<sigma>) = (Const a)" by auto
    from rhs_empty and lhs_empty show ?case by auto
  next
  case (Var a)
    have "vars_of (Var a) = { a }" by auto
    then have rhs: "\<Union> { V. \<exists>x. (x \<in> (vars_of (Var a))) \<and> (V = vars_of (subst (Var x) \<sigma>)) } = 
     vars_of (subst (Var a) \<sigma>)" by auto
    have lhs: "(subst (Var a) \<sigma>) = (subst (Var a) \<sigma>)" by auto
    from rhs and lhs show ?case by auto
  next
  case (Comb t1 t2)
    have "vars_of (Comb t1 t2) = (vars_of t1) \<union> (vars_of t2)" by auto
    then have "\<Union> { V. \<exists>x. (x \<in> (vars_of (Comb t1 t2))) \<and> (V = vars_of (subst (Var x) \<sigma>)) } 
      = \<Union> { V. \<exists>x. (x \<in> (vars_of t1)) \<and> (V = vars_of (subst(Var x) \<sigma>)) }   
        \<union> \<Union> { V. \<exists>x. (x \<in> (vars_of t2)) \<and> (V = vars_of (subst (Var x) \<sigma>)) }"
        by auto
    then have rhs: "\<Union> { V. \<exists>x. (x \<in> (vars_of (Comb t1 t2))) \<and> (V = vars_of (subst (Var x) \<sigma>)) } 
      = (vars_of (subst t1 \<sigma>))  \<union> (vars_of (subst t2 \<sigma>))"
      using \<open>vars_of (subst t1 \<sigma>) 
              = \<Union> { V. \<exists>x. (x \<in> (vars_of t1)) \<and> (V = vars_of (subst (Var x) \<sigma>)) }\<close>
        and
            \<open>vars_of (subst t2 \<sigma>) 
              = \<Union> { V. \<exists>x. (x \<in> (vars_of t2)) \<and> (V = vars_of (subst (Var x) \<sigma>)) }\<close>
      by auto   
    have "(subst (Comb t1 t2) \<sigma>) = (Comb (subst t1 \<sigma>) (subst t2 \<sigma>))" 
      by auto
    then have lhs: "(vars_of (subst (Comb t1 t2) \<sigma>)) = 
      (vars_of (subst t1 \<sigma>)) \<union> (vars_of (subst t2 \<sigma>))" by auto
    from lhs and rhs show ?case by auto
qed

lemma subterms_of_instances :
   "\<forall>u v u' s. (u = (subst v s) \<longrightarrow> (subterm u p u') 
    \<longrightarrow> (\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x s) q1 u') \<and> 
                      (subterm v q2 x) \<and> (p = (append q2 q1))) \<or> 
        ((\<exists> v'. ((\<not> is_a_variable v') \<and> (subterm v p v') \<and> (u' = (subst v' s))))))" (is "?prop p")
proof (induction p)
  case Nil
  show "?case"
  proof ((rule allI)+,(rule impI)+)
    fix u ::"'a trm" fix v u' s assume "u = (subst v s)" and "subterm u [] u'"
    then have "u = u'" by auto
    show "(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x s) q1 u') \<and> 
                      (subterm v q2 x) \<and> ([] = (append q2 q1))) \<or> 
        ((\<exists> v'. ((\<not> is_a_variable v') \<and> (subterm v [] v') \<and> (u' = (subst v' s)))))" 
    proof (cases)
      assume "is_a_variable v"
        from \<open>u = u'\<close>and \<open>u = (subst v s)\<close> 
          have "(subterm (subst v s) [] u')" by auto
        have "subterm v [] v" by auto
        from this and \<open>(subterm (subst v s) [] u')\<close> and \<open>is_a_variable v\<close>
          show ?thesis by auto
      next assume "\<not> is_a_variable v"
        from \<open>u = u'\<close> and \<open>u = (subst v s)\<close> 
        have "((subterm v [] v) \<and> (u' = (subst v s)))" by auto
        then show ?thesis  by auto
   qed
  qed
  next
  case (Cons i q)
  show ?case
  proof ((rule allI)+,(rule impI)+)
    fix u ::"'a trm" fix v u' s assume "u = (subst v s)" 
      and "subterm u (Cons i q) u'"
    show "(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x s) q1 u') \<and> 
                      (subterm v q2 x) \<and> ((Cons i q) = (append q2 q1))) \<or> 
        ((\<exists> v'. ((\<not> is_a_variable v') \<and> (subterm v (Cons i q) v') \<and> (u' = (subst v' s)))))"
    proof (cases v)
      fix x assume "v = (Var x)"
      then have "subterm v [] v" by auto 
      from \<open>v = (Var x)\<close> have "is_a_variable v" by auto
      have "Cons i q = (append [] (Cons i q))" by auto
      from \<open>subterm u (Cons i q) u'\<close> and \<open>u = (subst v s)\<close> 
        and \<open>v = (Var x)\<close> have "subterm (subst v s) (Cons i q) u'" by auto
      from \<open>is_a_variable v\<close> and \<open>subterm v [] v\<close> and \<open>Cons i q = (append [] (Cons i q))\<close> and this 
        show ?thesis  by blast
    next
      fix x assume "v = (Const x)"
      from this and \<open>u = (subst v s)\<close> have "u = v" by auto
      from this and \<open>v = (Const x)\<close> and \<open>subterm u (Cons i q) u'\<close> show ?thesis by auto
    next
      fix t1 t2 assume "v = (Comb t1 t2)"
      from this and  \<open>u = (subst v s)\<close> 
        have "u = (Comb (subst t1 s) (subst t2 s))" by auto
      have "i = Left \<or> i = Right" using indices.exhaust by auto 
      from \<open>i = Left \<or> i = Right\<close> and \<open>u = (Comb (subst t1 s) (subst t2 s))\<close> 
        and \<open>subterm u (Cons i q) u'\<close> obtain ti where 
        "subterm (subst ti s) q u'" and "ti = t1 \<or> ti = t2" and "subterm v [i] ti"
        using \<open>v = t1 \<cdot> t2\<close> by auto
      from \<open>?prop q\<close> and \<open>subterm (subst ti s) q u'\<close> have
        "(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x s) q1 u') \<and> 
                      (subterm ti q2 x) \<and> (q = (append q2 q1))) \<or> 
                      ((\<exists> v'. ((\<not> is_a_variable v') \<and> (subterm ti q v') \<and> (u' = (subst v' s)))))"  
        by auto
      then show ?thesis
      proof
        assume "(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x s) q1 u') \<and> 
                      (subterm ti q2 x) \<and> (q = (append q2 q1)))"
        then obtain x q1 q2 where "is_a_variable x" and "subterm (subst x s) q1 u'" 
            and "subterm ti q2 x" and "q = (append q2 q1)"
         by auto
        from \<open>subterm ti q2 x\<close> and \<open>subterm v [i] ti\<close> have "subterm v (i # q2) x"
        using \<open>i = indices.Left \<or> i = indices.Right\<close> \<open>v = t1 \<cdot> t2\<close> by auto
        from \<open>q = append q2 q1\<close> have "i # q = (append (i # q2) q1)" by auto
        from \<open>i # q = (append (i # q2) q1)\<close> and \<open>is_a_variable x\<close> 
          and \<open>subterm (subst x s) q1 u'\<close> and \<open>subterm v (i # q2) x\<close> 
          show ?thesis by blast 
      next
        assume "((\<exists> v'. ((\<not> is_a_variable v') \<and> (subterm ti q v') \<and> (u' = (subst v' s)))))"
        then obtain v' where "(\<not> is_a_variable v')" "(subterm ti q v')" and "u' = (subst v' s)"  by auto
        from \<open>subterm ti q v'\<close>  and \<open>subterm v [i] ti\<close> have "subterm v (i # q) v'"
          using \<open>i = indices.Left \<or> i = indices.Right\<close> \<open>v = t1 \<cdot> t2\<close> by auto
        from this and \<open>(\<not> is_a_variable v')\<close> \<open>subterm ti q v'\<close> and \<open>u' = (subst v' s)\<close> 
          show ?thesis by auto
      qed
    qed
  qed
qed

lemma vars_of_replacement:
  shows "\<And> t s. x \<in> vars_of s \<Longrightarrow> replace_subterm t p v s \<Longrightarrow> x \<in> (vars_of t) \<union> (vars_of v)"
proof (induction p)
  case Nil
    from \<open>replace_subterm t Nil v s\<close> have "s = v" by auto
    from this and \<open>x \<in> vars_of s\<close> show ?case by auto
  next case (Cons i q)
    from \<open>replace_subterm t (Cons i q) v s\<close> obtain t1 t2 where
        "t = (Comb t1 t2)"
        by (metis is_a_variable.cases replace_subterm.simps(2) replace_subterm.simps(3)) 
    have "i = Left \<or> i = Right" using indices.exhaust by blast 
    then show ?case
    proof 
      assume "i = Left"
      from this and \<open>t = Comb t1 t2\<close> and \<open>replace_subterm t (Cons i q) v s\<close> 
        obtain s1 where "s = Comb s1 t2" and "replace_subterm t1  q v s1"
          using replace_subterm.simps(4) by auto
      from \<open>s = Comb s1 t2\<close> and \<open>x \<in> vars_of s\<close> have "x \<in> vars_of s1 \<or> x \<in> vars_of t2"
        by simp
      then show ?case
      proof 
        assume "x \<in> vars_of s1"
        from this and Cons.IH [of s1 t1] and \<open>replace_subterm t1 q v s1\<close> have "x \<in> (vars_of t1) \<union> (vars_of v)"
          by auto
        from this and \<open>t = (Comb t1 t2)\<close> show ?case by auto
      next
        assume "x \<in> vars_of t2"
        from this and \<open>t = (Comb t1 t2)\<close> show ?case by auto
      qed
    next
      assume "i = Right"
      from this and \<open>t = Comb t1 t2\<close> and \<open>replace_subterm t (Cons i q) v s\<close> 
        obtain s2 where "s = Comb t1 s2" and "replace_subterm t2 q v s2"
          using replace_subterm.simps by auto
      from \<open>s = Comb t1 s2\<close> and \<open>x \<in> vars_of s\<close> have "x \<in> vars_of t1 \<or> x \<in> vars_of s2"
        by simp
      then show ?case
      proof 
        assume "x \<in> vars_of s2"
        from this and Cons.IH [of s2 t2] and \<open>replace_subterm t2 q v s2\<close> have "x \<in> (vars_of t2) \<union> (vars_of v)"
          by auto
        from this and \<open>t = (Comb t1 t2)\<close> show ?case by auto
      next
        assume "x \<in> vars_of t1"
        from this and \<open>t = (Comb t1 t2)\<close> show ?case by auto
      qed
   qed
qed

lemma vars_of_replacement_set:
  assumes "replace_subterm t p v s"
  shows "vars_of s \<subseteq> (vars_of t) \<union> (vars_of v)"
by (meson assms subsetI vars_of_replacement)

subsection \<open>Substitutions and Most General Unifiers\<close>

text \<open>Substitutions are defined in the Unification theory. We provide some 
additional definitions and lemmata.\<close>

fun subst_set :: "'a trm set => 'a subst => 'a trm set"
  where
    "(subst_set S \<sigma>) = { u. \<exists>t. u = (subst t \<sigma>) \<and> t \<in> S }"

definition subst_codomain
where
  "subst_codomain \<sigma> V = { x. \<exists>y. (subst (Var y) \<sigma>) = (Var x) \<and> (y \<in> V) }"

lemma subst_codomain_is_finite:
  assumes "finite A"
  shows "finite (subst_codomain \<eta> A)"
proof -
  have i: "((\<lambda>x. (Var x)) ` (subst_codomain \<eta> A)) \<subseteq> ((\<lambda>x. (subst (Var x) \<eta>)) ` A)" 
  proof 
    fix x assume "x \<in> ((\<lambda>x. (Var x)) ` (subst_codomain \<eta> A))"
    from this obtain y where "y \<in> (subst_codomain \<eta> A)" and "x = (Var y)" by auto
    from \<open>y \<in> (subst_codomain \<eta> A)\<close>  obtain z where "(subst (Var z) \<eta>) = (Var y)" "(z \<in> A)"
      unfolding subst_codomain_def by auto
    from \<open>(z \<in> A)\<close> \<open>x = (Var y)\<close> \<open>(subst (Var z) \<eta>) = (Var y)\<close> this show 
      "x \<in> ((\<lambda>x. (subst (Var x) \<eta>)) ` A)"using image_iff by fastforce 
  qed
  have "inj_on (\<lambda>x. (Var x)) (subst_codomain \<eta> A)" by (meson inj_onI trm.inject(1))
  from assms(1) have "finite ((\<lambda>x. (subst (Var x) \<eta>)) ` A)" by auto
  from this and i have "finite ((\<lambda>x. (Var x)) ` (subst_codomain \<eta> A))" 
    using rev_finite_subset by auto
  from this and \<open>inj_on (\<lambda>x. (Var x)) (subst_codomain \<eta> A)\<close> show ?thesis using finite_imageD [of "(\<lambda>x. (Var x))" "subst_codomain \<eta> A"]
    by auto
qed

text \<open>The notions of unifiers, most general unifiers, the unification algorithm and a 
proof of correctness are provided in the Unification theory. Below, we prove that the algorithm 
is complete.\<close>

lemma subt_decompose:
  shows "\<forall>t1 t2. Comb t1 t2 \<prec> s \<longrightarrow> (t1 \<prec> s \<and> t2\<prec> s) "
proof ((induction s),(simp),(simp))
    case (Comb s1 s2) 
     show ?case
     proof ((rule allI)+,(rule impI)) 
      fix t1 t2 assume "Comb t1 t2 \<prec> Comb s1 s2"
      show "t1 \<prec> (Comb s1 s2) \<and> t2 \<prec> (Comb s1 s2)"
      proof (rule ccontr)
        assume neg: "\<not>(t1 \<prec> (Comb s1 s2) \<and> t2 \<prec> (Comb s1 s2))"
        from \<open>Comb t1 t2 \<prec> Comb s1 s2\<close> have 
          d: "Comb t1 t2 = s1 \<or> Comb t1 t2 = s2 \<or> Comb t1 t2 \<prec> s1 \<or> Comb t1 t2 \<prec> s2" 
          by auto
        have i: "\<not> (Comb t1 t2 = s1)"
        proof 
          assume "(Comb t1 t2 = s1)"
          then have "t1 \<prec> s1" and "t2 \<prec> s1" by auto
          from this and neg  show False by auto
        qed
        have ii: "\<not> (Comb t1 t2 = s2)"
        proof 
          assume "(Comb t1 t2 = s2)"
          then have "t1 \<prec> s2" and "t2 \<prec> s2" by auto
          from this and neg  show False by auto
        qed
        have iii: "\<not> (Comb t1 t2 \<prec> s1)"
        proof 
          assume "(Comb t1 t2 \<prec> s1)"
          then have "t1 \<prec> s1 \<and> t2 \<prec> s1" using Comb.IH by metis 
          from this and neg  show False by auto
        qed
        have iv: "\<not> (Comb t1 t2 \<prec> s2)"
        proof 
          assume "(Comb t1 t2 \<prec> s2)"
          then have "t1 \<prec> s2  \<and> t2 \<prec> s2" using Comb.IH by metis
          from this and neg show False by auto
        qed
        from d and i ii iii iv show False by auto
     qed
   qed
qed

lemma subt_irrefl:
  shows "\<not> (s \<prec> s)" 
proof ((induction s),(simp),(simp))
    case (Comb t1 t2) 
     show ?case
    proof 
      assume "Comb t1 t2 \<prec> Comb t1 t2"
      then have i: "Comb t1 t2 \<noteq> t1" using Comb.IH(1) by fastforce 
      from \<open>Comb t1 t2 \<prec> Comb t1 t2\<close> have ii: "Comb t1 t2 \<noteq> t2" using Comb.IH(2) by fastforce 
      from i ii and \<open>Comb t1 t2 \<prec> Comb t1 t2\<close> have "Comb t1 t2 \<prec> t1 \<or> Comb t1 t2 \<prec> t2" by auto
      then show False
      proof
        assume "Comb t1 t2  \<prec> t1"
        then have "t1 \<prec> t1"  using subt_decompose [of t1] by metis
        from this show False using Comb.IH by auto
      next
        assume "Comb t1 t2  \<prec> t2"
        then have "t2 \<prec> t2"  using subt_decompose [of t2] by metis
        from this show False using Comb.IH by auto
      qed
    qed
qed

lemma MGU_exists:
  shows "\<forall>\<sigma>. ((subst t \<sigma>) = (subst s \<sigma>) \<longrightarrow> unify t s \<noteq> None)"
proof (rule unify.induct)
    fix x s1 s2 show "\<forall>\<sigma> :: 'a subst .((subst (Const x) \<sigma>) = (subst (Comb s1 s2) \<sigma>) 
      \<longrightarrow> unify (Const x) (Comb s1 s2) \<noteq> None)" by simp 
    next
    fix t1 t2 y show "\<forall>\<sigma> :: 'a subst.(subst (Comb t1 t2) \<sigma>) = (subst (Const y) \<sigma>) 
      \<longrightarrow> unify (Comb t1 t2) (Const y) \<noteq> None" by simp 
    next
    fix x y show "\<forall>\<sigma> :: 'a subst.(subst (Const x) \<sigma>) = (subst (Var y) \<sigma>) 
      \<longrightarrow> unify (Const x) (Var y) \<noteq> None" using unify.simps(3) by fastforce  
    next
    fix t1 t2 y show "\<forall>\<sigma> :: 'a subst.(subst (Comb t1 t2) \<sigma>) = (subst (Var y) \<sigma>) 
      \<longrightarrow> unify (Comb t1 t2) (Var y) \<noteq> None"
       by (metis option.distinct(1) subst_mono subt_irrefl unify.simps(4))
    next
    fix x s show "\<forall>\<sigma> :: 'a subst.(subst (Var x) \<sigma>) = (subst s \<sigma>) 
      \<longrightarrow> unify (Var x) s \<noteq> None"
      by (metis option.distinct(1) subst_mono subt_irrefl unify.simps(5))
    next 
    fix x y show "\<forall>\<sigma> :: 'a subst.(subst (Const x) \<sigma>) = (subst (Const y) \<sigma>) 
      \<longrightarrow> unify (Const x) (Const y) \<noteq> None" by simp 
    next
    fix t1 t2 s1 s2
    show "\<forall>\<sigma> :: 'a subst. (subst t1 \<sigma> = subst s1 \<sigma> \<longrightarrow> unify t1 s1 \<noteq> None) \<Longrightarrow>
       (\<And>x2. unify t1 s1 = Some x2 \<Longrightarrow>
              \<forall>\<sigma>. subst (t2 \<lhd> x2) \<sigma> = subst (s2 \<lhd> x2) \<sigma> \<longrightarrow>
              unify (t2 \<lhd> x2) (s2 \<lhd> x2) \<noteq> None) \<Longrightarrow>
       \<forall>\<sigma>. (subst (t1 \<cdot> t2) \<sigma> = subst (s1 \<cdot> s2) \<sigma> \<longrightarrow>
       unify (t1 \<cdot> t2) (s1 \<cdot> s2) \<noteq> None)"
    proof -
      assume h1: "\<forall>\<sigma>. (subst t1 \<sigma> = subst s1 \<sigma> \<longrightarrow> unify t1 s1 \<noteq> None)"
      assume h2: "(\<And>x2. unify t1 s1 = Some x2 \<Longrightarrow>
              \<forall>\<sigma>. subst (t2 \<lhd> x2) \<sigma> = subst (s2 \<lhd> x2) \<sigma> \<longrightarrow>
              unify (t2 \<lhd> x2) (s2 \<lhd> x2) \<noteq> None)"
      show "\<forall>\<sigma>. (subst (t1 \<cdot> t2) \<sigma> = subst (s1 \<cdot> s2) \<sigma> \<longrightarrow>
       unify (t1 \<cdot> t2) (s1 \<cdot> s2) \<noteq> None)"
      proof ((rule allI),(rule impI))
        fix \<sigma> assume h3: "subst (t1 \<cdot> t2) \<sigma> = subst (s1 \<cdot> s2) \<sigma>"
        from h3 have "subst t1 \<sigma> = subst s1 \<sigma>" by auto
        from this and h1 have "unify t1 s1 \<noteq> None" by auto
        from this obtain \<theta> where "unify t1 s1 = Some \<theta>" and "MGU \<theta> t1 s1"
            by (meson option.exhaust unify_computes_MGU) 
        from \<open>subst t1 \<sigma> = subst s1 \<sigma>\<close> have "Unifier \<sigma> t1 s1" 
            unfolding Unifier_def by auto
        from this and \<open>MGU \<theta> t1 s1\<close> obtain \<eta> where  "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>" using MGU_def by metis
        from h3 have "subst t2 \<sigma> = subst s2 \<sigma>" by auto
        from this and \<open>\<sigma> \<doteq> \<theta> \<lozenge> \<eta>\<close>   
            have "subst (subst t2 \<theta>) \<eta> 
              = subst (subst s2 \<theta>) \<eta>"
            by (simp add: subst_eq_def)
        from this and \<open>unify t1 s1 = Some \<theta>\<close> and h2 [of \<theta>] have "unify (t2 \<lhd> \<theta>) (s2 \<lhd> \<theta>) \<noteq> None"
            by auto
        from this show "unify (t1 \<cdot> t2) (s1 \<cdot> s2) \<noteq> None" 
          by (simp add: \<open>unify t1 s1 = Some \<theta>\<close> option.case_eq_if)  
      qed
   qed
qed

text \<open>We establish some useful properties of substitutions and instances.\<close>

definition ground_on :: "'a set \<Rightarrow> 'a subst \<Rightarrow> bool"
  where "ground_on V \<sigma> = (\<forall>x \<in> V. (ground_term (subst (Var x)  \<sigma>)))"

lemma comp_subst_terms:
    assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
    shows "(subst t \<sigma>) = (subst (subst t \<theta>) \<eta>)"
proof -
    from \<open>\<sigma> \<doteq> \<theta> \<lozenge> \<eta>\<close> have "((subst t \<sigma>) = (subst t (\<theta> \<lozenge> \<eta>)))" by auto
    have "(subst t (\<theta> \<lozenge> \<eta>) = (subst (subst t \<theta>) \<eta>))" by auto
    from this and \<open>((subst t \<sigma>) = (subst t (\<theta> \<lozenge> \<eta>)))\<close> show ?thesis by auto
qed

lemma ground_instance:
  assumes "ground_on (vars_of t) \<sigma>"
  shows "ground_term (subst t \<sigma>)"
proof (rule ccontr)
  assume "\<not> ground_term (subst t \<sigma>)"
  then have "vars_of (subst t \<sigma>) \<noteq> {}"  unfolding ground_term_def by auto
  then obtain x where "x \<in> vars_of (subst t \<sigma>)"  by auto
  then have "x \<in> \<Union> { V. \<exists>x. (x \<in> (vars_of t)) \<and> (V = vars_of (subst (Var x) \<sigma>)) }"
    using vars_of_instances by force  
  then obtain y where "x \<in> (vars_of (subst (Var y) \<sigma>))" and "y \<in> (vars_of t)" by blast
  from assms(1) and \<open>y \<in> (vars_of t)\<close> have "ground_term (subst (Var y) \<sigma>)" unfolding ground_on_def
    by auto
  from this and \<open>x \<in> (vars_of (subst (Var y) \<sigma>))\<close> show False unfolding ground_term_def by auto
qed

lemma substs_preserve_groundness:
  assumes "ground_term t"
  shows "ground_term (subst t \<sigma>)"
by (metis assms equals0D ground_instance ground_on_def ground_term_def)

lemma ground_subst_exists  :
  "finite V \<Longrightarrow> \<exists>\<sigma>. (ground_on V \<sigma>)"
proof (induction rule: finite.induct)
  case emptyI
  show ?case unfolding ground_on_def by simp
next
  fix A :: "'a set" and a::'a 
  assume "finite A"
  assume hyp_ind: "\<exists>\<sigma>. ground_on A \<sigma>" 
  then obtain \<sigma> where "ground_on A \<sigma>" by auto
  then show "\<exists>\<sigma>. ground_on (insert a A) \<sigma>"
  proof cases
    assume "a \<in> A"
    from this and hyp_ind show "\<exists>\<sigma>. ground_on (insert a A) \<sigma>"  
      unfolding ground_on_def by auto
  next
    assume "a \<notin> A"
    obtain c where "c = (Const a)" and "is_a_constant c" by auto
    obtain \<theta> where "\<theta> = (a,c) # \<sigma>" by auto  
    have "\<forall>x. (x \<in> insert a A \<longrightarrow> (ground_term (subst (Var x) \<theta>)))"
    proof ((rule allI)+,(rule impI)+)
      fix x assume "x \<in> insert a A"
      show "ground_term (subst (Var x) \<theta>)"
      proof cases
        assume "x = a"
        from this and \<open>\<theta> = (a,c) # \<sigma>\<close> have "(subst (Var x) \<theta>) = c" by auto
        from \<open>is_a_constant c\<close> have "ground_term c" using constants_are_ground by auto
        from this and \<open>(subst (Var x) \<theta>) = c\<close> show "ground_term (subst (Var x) \<theta>)" by auto
      next
        assume "x \<noteq> a"
        from \<open>x \<noteq> a\<close> and \<open>x \<in> insert a A\<close> have "x \<in> A" by auto
        from \<open>x \<noteq> a\<close> and  \<open>\<theta> = (a,c) # \<sigma>\<close> have "(subst (Var x) \<theta>) = (subst (Var x) \<sigma>)" by auto
        from this and \<open>x \<in> A\<close> and \<open>ground_on A \<sigma>\<close>
          show "ground_term (subst (Var x) \<theta>)" unfolding ground_on_def by auto
      qed
    qed
    from this show ?thesis unfolding ground_on_def by auto 
  qed
qed

lemma substs_preserve_ground_terms :
  assumes "ground_term t"
  shows "subst t \<sigma> = t"
by (metis agreement assms equals0D ground_term_def subst_Nil)

lemma substs_preserve_subterms :
  shows "\<And> t  s. subterm t p s \<Longrightarrow> subterm (subst t \<sigma>) p (subst s \<sigma>)"
proof (induction p)
  case Nil
    then have "t = s" using subterm.elims(2) by auto 
    from \<open>t = s\<close> have "(subst t \<sigma>) = (subst s \<sigma>)" by auto
    from this show ?case using Nil.prems by auto
  next case (Cons i q)
    from \<open>subterm t (i # q) s\<close> obtain t1 t2 where
        "t = (Comb t1 t2)" using subterm.elims(2) by blast 
    have "i = Left \<or> i = Right" using indices.exhaust by blast 
    then show "subterm (subst t \<sigma>) (i # q) (subst s \<sigma>)"
    proof 
      assume "i = Left"
      from this and \<open>t = Comb t1 t2\<close> and \<open>subterm t (i # q) s\<close>  
        have "subterm t1 q s" by auto
      from this have "subterm (subst t1 \<sigma>) q (subst s \<sigma>)" using Cons.IH by auto 
      from this and \<open>t = Comb t1 t2\<close> 
        show "subterm (subst t \<sigma>) (i # q) (subst s \<sigma>)" 
          by (simp add: \<open>i = indices.Left\<close>) 
    next assume "i = Right"
      from this and \<open>t = Comb t1 t2\<close> and \<open>subterm t (i # q) s\<close>  
        have "subterm t2 q s" by auto
      from this have "subterm (subst t2 \<sigma>) q (subst s \<sigma>)" using Cons.IH by auto 
      from this and \<open>t = Comb t1 t2\<close> 
        show "subterm (subst t \<sigma>) (i # q) (subst s \<sigma>)" 
          by (simp add: \<open>i = indices.Right\<close>) 
    qed
qed

lemma substs_preserve_occurs_in:
  assumes "occurs_in s t"
  shows "occurs_in (subst s \<sigma>) (subst t \<sigma>)"
using substs_preserve_subterms
  using assms occurs_in_def by blast 

definition coincide_on 
where "coincide_on \<sigma> \<eta> V = (\<forall>x \<in> V. (subst (Var x) \<sigma>) = ( (subst (Var x) \<eta>)))"

lemma coincide_sym:
  assumes "coincide_on \<sigma> \<eta> V"
  shows "coincide_on \<eta> \<sigma> V"
by (metis assms coincide_on_def) 

lemma coincide_on_term:
  shows "\<And> \<sigma> \<eta>. coincide_on \<sigma> \<eta> (vars_of t) \<Longrightarrow> subst t \<sigma> = subst t \<eta>"
proof (induction t)
  case (Var x)
    from this show "subst (Var x) \<sigma> = subst  (Var x) \<eta>" 
      unfolding coincide_on_def by auto
  next case (Const x)
    show "subst (Const x) \<sigma> = subst  (Const x) \<eta>"  by auto
  next case (Comb t1 t2)
    from this show ?case unfolding coincide_on_def by auto
qed

lemma ground_replacement:
  assumes "replace_subterm t p v s"
  assumes "ground_term (subst t \<sigma>)"
  assumes "ground_term (subst v \<sigma>)"
  shows "ground_term (subst s \<sigma>)"
proof -
  from assms(1) have "vars_of s \<subseteq> (vars_of t) \<union> (vars_of v)" using vars_of_replacement_set [of t p v s]
    by auto
  from assms(2) have "ground_on (vars_of t) \<sigma>" unfolding ground_on_def
    by (metis contra_subsetD ex_in_conv ground_term_def 
      occs_vars_subset subst_mono vars_iff_occseq)
  from assms(3) have "ground_on (vars_of v) \<sigma>" unfolding ground_on_def
    by (metis contra_subsetD ex_in_conv ground_term_def 
      occs_vars_subset subst_mono vars_iff_occseq)
  from \<open>vars_of s \<subseteq> (vars_of t) \<union> (vars_of v)\<close> \<open>ground_on (vars_of t) \<sigma>\<close> 
    and  \<open>ground_on (vars_of v) \<sigma>\<close> have "ground_on (vars_of s) \<sigma>" 
    by (meson UnE ground_on_def rev_subsetD) 
  from this show ?thesis using ground_instance by blast
qed

text \<open>We now show that two disjoint substitutions can always be fused.\<close>

lemma combine_substs:
  assumes "finite V1"
  assumes "V1 \<inter> V2 = {}"
  assumes "ground_on V1 \<eta>1"
  shows "\<exists>\<sigma>. (coincide_on \<sigma> \<eta>1 V1) \<and> (coincide_on \<sigma> \<eta>2 V2)"
proof -
  have "finite V1 \<Longrightarrow> ground_on V1 \<eta>1 \<Longrightarrow> V1 \<inter> V2 = {} \<Longrightarrow> \<exists>\<sigma>. (coincide_on \<sigma> \<eta>1 V1) \<and> (coincide_on \<sigma> \<eta>2 V2)"
  proof (induction rule: finite.induct)
      case emptyI
      show ?case unfolding coincide_on_def by auto
    next fix V1 :: "'a set" and a::'a 
      assume "finite V1"
      assume hyp_ind: "ground_on V1 \<eta>1 \<Longrightarrow> V1 \<inter> V2 = {} 
        \<Longrightarrow> \<exists>\<sigma>. (coincide_on \<sigma> \<eta>1 V1) \<and> (coincide_on \<sigma> \<eta>2 V2)" 
      assume  "ground_on (insert a V1) \<eta>1" 
      assume "(insert a V1) \<inter> V2 = {}"
      from this have "V1 \<inter> V2 = {}" by auto
      from \<open>ground_on (insert a V1) \<eta>1\<close> have "ground_on V1 \<eta>1" 
        unfolding ground_on_def by auto
      from this and hyp_ind and \<open>V1 \<inter> V2 = {}\<close> obtain \<sigma>' 
        where c:"(coincide_on \<sigma>' \<eta>1 V1) \<and> (coincide_on \<sigma>' \<eta>2 V2)" by auto
      let ?t = "subst (Var a) \<eta>1"
      from assms(2) have "ground_term ?t"
        by (meson \<open>ground_on (insert a V1) \<eta>1\<close> ground_on_def insertI1) 
      let ?\<sigma> = "comp [(a,?t)] \<sigma>'"
      have "coincide_on ?\<sigma> \<eta>1 (insert a V1)" 
      proof (rule ccontr)
        assume "\<not>coincide_on ?\<sigma> \<eta>1 (insert a V1)"
        then obtain x where "x \<in> (insert a V1)" and 
          "(subst (Var x) ?\<sigma>) \<noteq> ( (subst (Var x) \<eta>1))" 
          unfolding coincide_on_def by blast  
        have "subst (Var a) ?\<sigma>  = subst ?t \<sigma>'" by simp  
        from \<open>ground_term ?t\<close> have "subst (Var a) ?\<sigma>  = ?t"
          using substs_preserve_ground_terms by auto  
        from this and \<open>(subst (Var x) ?\<sigma>) \<noteq> ( (subst (Var x) \<eta>1))\<close>
          have "x \<noteq> a" by blast
        from this and \<open>x \<in> (insert a V1)\<close> have "x \<in> V1" by auto
        from \<open>x \<noteq> a\<close> have "(subst (Var x) ?\<sigma>) = (subst (Var x) \<sigma>')" by auto
        from c and \<open>x \<in> V1\<close> have "(subst (Var x) \<sigma>') = (subst (Var x) \<eta>1)"
          unfolding coincide_on_def by blast
        from this and \<open>(subst (Var x) ?\<sigma>) = (subst (Var x) \<sigma>')\<close> 
          and \<open>(subst (Var x) ?\<sigma>) \<noteq> ( (subst (Var x) \<eta>1))\<close> show False by auto
      qed
      have "coincide_on ?\<sigma> \<eta>2 V2" 
      proof (rule ccontr)
        assume "\<not>coincide_on ?\<sigma> \<eta>2 V2"
        then obtain x where "x \<in> V2" and 
          "(subst (Var x) ?\<sigma>) \<noteq> ( (subst (Var x) \<eta>2))" 
          unfolding coincide_on_def by blast  
        from \<open>(insert a V1) \<inter> V2 = {}\<close> and \<open>x \<in> V2\<close> have "x \<noteq> a" by auto
        from this  have "(subst (Var x) ?\<sigma>) = (subst (Var x) \<sigma>')" by auto
        from c and \<open>x \<in> V2\<close> have "(subst (Var x) \<sigma>') = (subst (Var x) \<eta>2)"
          unfolding coincide_on_def by blast
        from this and \<open>(subst (Var x) ?\<sigma>) = (subst (Var x) \<sigma>')\<close> 
          and \<open>(subst (Var x) ?\<sigma>) \<noteq> ( (subst (Var x) \<eta>2))\<close> show False by auto 
      qed
      from \<open>coincide_on ?\<sigma> \<eta>1 (insert a V1)\<close> \<open>coincide_on ?\<sigma> \<eta>2 V2\<close> 
        show "\<exists>\<sigma>. (coincide_on \<sigma> \<eta>1 (insert a V1)) \<and> (coincide_on \<sigma> \<eta>2 V2)" by auto
  qed  
  from this and assms show ?thesis by auto
qed

text \<open>We define a map function for substitutions and prove its correctness.\<close>

fun map_subst
  where "map_subst f Nil = Nil" 
      | "map_subst f ((x,y) # l) = (x,(f y)) # (map_subst f l)"
   
lemma map_subst_lemma:
  shows "((subst (Var x) \<sigma>) \<noteq> (Var x) \<or> (subst (Var x) \<sigma>) \<noteq> (subst (Var x) (map_subst f \<sigma>)))
            \<longrightarrow> ((subst (Var x) (map_subst f \<sigma>)) = (f (subst (Var x) \<sigma>)))"
proof (induction \<sigma>,simp)
  next case (Cons p \<sigma>)
    let ?u = "(fst p)"
    let ?v = "(snd p)"
    show ?case
    proof
      assume "((subst (Var x) (Cons p \<sigma>)) \<noteq> (Var x)  
        \<or> (subst (Var x)  (Cons p \<sigma>)) 
          \<noteq> (subst (Var x) (map_subst f  (Cons p \<sigma>))))"
      have  "map_subst f (Cons p \<sigma>) = ( (?u, (f ?v)) # (map_subst f \<sigma>))"
          by (metis map_subst.simps(2) prod.collapse) 
      show "(subst (Var x) (map_subst f (Cons p \<sigma>))) = (f (subst (Var x) (Cons p \<sigma>)))"
      proof cases
        assume "x = ?u"
        from this have "subst (Var x) (Cons p \<sigma>) = ?v"
          by (metis assoc.simps(2) prod.collapse subst.simps(1))
        from \<open>map_subst f (Cons p \<sigma>) = ( (?u, (f ?v)) # (map_subst f \<sigma>))\<close> 
          and \<open>x = ?u\<close> 
          have "subst (Var x) (map_subst f (Cons p \<sigma>)) = (f ?v)" by simp 
        from \<open>subst (Var x) (Cons p \<sigma>) = ?v\<close> \<open>subst (Var x) (map_subst f (Cons p \<sigma>)) = (f ?v)\<close> show ?thesis by auto
      next 
        assume "x \<noteq> ?u"
        from this have "subst (Var x) (Cons p \<sigma>) = (subst (Var x) \<sigma>)"
          by (metis  assoc.simps(2) prod.collapse subst.simps(1)) 
        from \<open>map_subst f (Cons p \<sigma>) = ( (?u, (f ?v)) # (map_subst f \<sigma>))\<close> 
          and \<open>x \<noteq> ?u\<close> 
          have "subst (Var x) (map_subst f (Cons p \<sigma>)) = 
            subst (Var x) (map_subst f \<sigma>)" by simp 
        from this and "Cons.IH" have 
          "subst (Var x) (map_subst f (Cons p \<sigma>)) = (f (subst (Var x) \<sigma>))"
            using \<open>subst (Var x) (p # \<sigma>) = subst (Var x) \<sigma>\<close> \<open>subst (Var x) (p # \<sigma>) \<noteq> Var x \<or> subst (Var x) (p # \<sigma>) \<noteq> subst (Var x) (map_subst f (p # \<sigma>))\<close> by auto            
        from this and \<open>subst (Var x) (Cons p \<sigma>) = (subst (Var x) \<sigma>)\<close> show ?thesis by auto
      qed
   qed
qed

subsection \<open>Congruences\<close>

text \<open>We now define the notion of a congruence on ground terms, i.e., an equivalence relation
that is closed under contextual embedding.\<close>

type_synonym 'a binary_relation_on_trms = "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool"

definition reflexive :: "'a binary_relation_on_trms \<Rightarrow> bool"
where 
    "(reflexive x) = (\<forall>y. (x y y))"

definition symmetric :: "'a binary_relation_on_trms \<Rightarrow> bool"
where 
    "(symmetric x) = (\<forall>y. \<forall>z. ((x y z) = (x z y)))"

definition transitive :: "'a binary_relation_on_trms \<Rightarrow> bool"
where 
    "(transitive x) = (\<forall>y. \<forall>z. \<forall>u. (x y z) \<longrightarrow> (x z u) \<longrightarrow> (x y u))"

definition equivalence_relation :: "'a binary_relation_on_trms \<Rightarrow> bool"
where 
  "(equivalence_relation x) = ((reflexive x) \<and> (symmetric x) \<and> (transitive x))"
 
definition compatible_with_structure :: "('a binary_relation_on_trms) \<Rightarrow> bool"
where
   "(compatible_with_structure x) = (\<forall>t1 t2 s1 s2. 
      (x t1 s1) \<longrightarrow> (x t2 s2) \<longrightarrow> (x (Comb t1 t2) (Comb s1 s2)))"

definition congruence :: "'a binary_relation_on_trms \<Rightarrow> bool"
where 
  "(congruence x) = ((equivalence_relation x) \<and> (compatible_with_structure x))"

lemma replacement_preserves_congruences :
  shows "\<And> t  s. (congruence I) \<Longrightarrow> (I (subst u \<sigma>)  (subst v \<sigma>)) 
          \<Longrightarrow> subterm t p u \<Longrightarrow> replace_subterm t p v s 
          \<Longrightarrow> (I (subst t \<sigma>)  (subst s \<sigma>))"
proof (induction p)
  case Nil
    from \<open>subterm t Nil u\<close> have "t = u" by auto 
    from \<open>replace_subterm t Nil v s\<close> have "s = v" by auto
    from \<open>t = u\<close> and \<open>s = v\<close> and \<open>(I (subst u \<sigma>)  (subst v \<sigma>))\<close> 
      show ?case by auto
  next case (Cons i q)
    from \<open>subterm t (i # q) u\<close> obtain t1 t2 where
        "t = (Comb t1 t2)" using subterm.elims(2) by blast 
    have "i = Left \<or> i = Right" using indices.exhaust by blast 
    then show "I (subst t \<sigma>)  (subst s \<sigma>)"
    proof 
      assume "i = Left"
      from this and \<open>t = Comb t1 t2\<close> and \<open>subterm t (i # q) u\<close>  
        have "subterm t1 q u" by auto
      from \<open>i = Left\<close> and \<open>t = Comb t1 t2\<close> and \<open>replace_subterm t (i # q) v s\<close>  
        obtain t1' where "replace_subterm t1 q v t1'" and "s = Comb t1' t2" by auto
      from \<open>congruence I\<close> and \<open>(I (subst u \<sigma>)  (subst v \<sigma>))\<close> 
        and \<open>subterm t1 q u\<close> and \<open>replace_subterm t1 q v t1'\<close> have 
        "I (subst t1 \<sigma>) (subst t1' \<sigma>)" using Cons.IH Cons.prems(1) by blast 
      from \<open>congruence I\<close> have "I (subst t2 \<sigma>)  (subst t2 \<sigma>)" 
        unfolding congruence_def equivalence_relation_def reflexive_def by auto
      from \<open>I (subst t1 \<sigma>) (subst t1' \<sigma>)\<close> 
        and \<open>I (subst t2 \<sigma>)  (subst t2 \<sigma>)\<close> 
        and \<open>congruence I\<close> and \<open>t = (Comb t1 t2)\<close> and \<open>s = (Comb t1' t2)\<close> 
        show "I (subst t \<sigma>)  (subst s \<sigma>)" 
          unfolding congruence_def compatible_with_structure_def by auto
    next 
      assume "i = Right"
      from this and \<open>t = Comb t1 t2\<close> and \<open>subterm t (i # q) u\<close>  
        have "subterm t2 q u" by auto
      from \<open>i = Right\<close> and \<open>t = Comb t1 t2\<close> and \<open>replace_subterm t (i # q) v s\<close>  
        obtain t2' where "replace_subterm t2 q v t2'" and "s = Comb t1 t2'" by auto
      from \<open>congruence I\<close> and \<open>(I (subst u \<sigma>)  (subst v \<sigma>))\<close> 
        and \<open>subterm t2 q u\<close> and \<open>replace_subterm t2 q v t2'\<close> have 
        "I (subst t2 \<sigma>) (subst t2' \<sigma>)" using Cons.IH Cons.prems(1) by blast 
      from \<open>congruence I\<close> have "I (subst t1 \<sigma>)  (subst t1 \<sigma>)" 
        unfolding congruence_def equivalence_relation_def reflexive_def by auto
      from \<open>I (subst t2 \<sigma>) (subst t2' \<sigma>)\<close> 
        and \<open>I (subst t1 \<sigma>)  (subst t1 \<sigma>)\<close> 
        and \<open>congruence I\<close> and \<open>t = (Comb t1 t2)\<close> and \<open>s = (Comb t1 t2')\<close> 
        show "I (subst t \<sigma>)  (subst s \<sigma>)" 
          unfolding congruence_def compatible_with_structure_def by auto
    qed
qed

definition equivalent_on 
where "equivalent_on \<sigma> \<eta> V I = (\<forall>x \<in> V. 
  (I (subst (Var x) \<sigma>) ( (subst (Var x) \<eta>))))"

lemma equivalent_on_term:
  assumes "congruence I"
  shows "\<And> \<sigma> \<eta>. equivalent_on \<sigma> \<eta> (vars_of t) I \<Longrightarrow> (I (subst t \<sigma>) (subst t \<eta>))"
proof (induction t)
  case (Var x)
    from this show "(I (subst (Var x) \<sigma>) (subst  (Var x) \<eta>))" 
      unfolding equivalent_on_def by auto
  next case (Const x)
    from assms(1) show "(I (subst (Const x) \<sigma>) (subst  (Const x) \<eta>))" 
      unfolding congruence_def equivalence_relation_def reflexive_def by auto
  next case (Comb t1 t2)
    from this assms(1) show ?case unfolding equivalent_on_def
      unfolding congruence_def compatible_with_structure_def by auto
qed
   
subsection \<open>Renamings\<close>

text \<open>We define the usual notion of a renaming. We show that fresh renamings always exist 
(provided the set of variables is infinite) and that renamings admit inverses.\<close>

definition renaming
where
  "renaming \<sigma> V = (\<forall>x \<in> V. (is_a_variable (subst (Var x) \<sigma>)) 
    \<and> (\<forall> x y. ((x \<in> V) \<longrightarrow> (y \<in> V) \<longrightarrow> x \<noteq> y \<longrightarrow> (subst (Var x) \<sigma>) \<noteq> (subst (Var y) \<sigma>))))"

lemma renamings_admit_inverse:
  shows "finite V \<Longrightarrow> renaming \<sigma> V \<Longrightarrow> \<exists> \<theta>. (\<forall> x \<in> V. (subst (subst (Var x) \<sigma> ) \<theta>) = (Var x))
    \<and> (\<forall> x. (x \<notin> (subst_codomain \<sigma> V) \<longrightarrow> (subst (Var x) \<theta>) = (Var x)))"
proof (induction rule: finite.induct)
  case emptyI
    let ?\<theta> = "[]"
    have i: "(\<forall> x \<in> {}. (subst (subst (Var x) \<sigma> ) ?\<theta>) = (Var x))" by auto
    have ii: "(\<forall> x. (x \<notin> (subst_codomain \<sigma> {}) \<longrightarrow> (subst (Var x) ?\<theta>) = (Var x)))" by auto
    from i ii show ?case  by metis
next
  fix A :: "'a set" and a::'a 
  assume "finite A"
  assume hyp_ind: "renaming \<sigma> A \<Longrightarrow> \<exists> \<theta>. (\<forall> x \<in> A. (subst (subst (Var x) \<sigma> ) \<theta>) = (Var x))
    \<and> (\<forall> x. (x \<notin> (subst_codomain \<sigma> A) \<longrightarrow> (subst (Var x) \<theta>) = (Var x)))" 
  show "renaming \<sigma> (insert a A) \<Longrightarrow> \<exists> \<theta>. (\<forall> x \<in>  (insert a A). (subst (subst (Var x) \<sigma> ) \<theta>) = (Var x))
    \<and> (\<forall> x. (x \<notin> (subst_codomain \<sigma> (insert a A)) \<longrightarrow> (subst (Var x) \<theta>) = (Var x)))" 
  proof -
    assume "renaming \<sigma> (insert a A)" 
    show "\<exists> \<theta>. (\<forall> x \<in>  (insert a A). (subst (subst (Var x) \<sigma> ) \<theta>) = (Var x))
    \<and> (\<forall> x. (x \<notin> (subst_codomain \<sigma> (insert a A)) \<longrightarrow> (subst (Var x) \<theta>) = (Var x)))"
    proof (cases)
      assume "a \<in> A"
      from this have "insert a A = A" by auto
      from this and \<open>renaming \<sigma> (insert a A)\<close> hyp_ind show ?thesis by metis 
    next assume "a \<notin> A"
      from \<open>renaming \<sigma> (insert a A)\<close> have "renaming \<sigma> A" unfolding renaming_def by blast
      from this and hyp_ind obtain \<theta> where i: "(\<forall> x \<in> A. (subst (subst (Var x) \<sigma> ) \<theta>) = (Var x))" and 
        ii:  "(\<forall> x. (x \<notin> (subst_codomain \<sigma> A) \<longrightarrow> (subst (Var x) \<theta>) = (Var x)))" by metis 
      from \<open>renaming \<sigma> (insert a A)\<close> have "is_a_variable (subst (Var a) \<sigma>)" unfolding renaming_def by blast
      from this obtain b where "(subst (Var a) \<sigma>) = (Var b)" using is_a_variable.elims(2) by auto 
      let ?\<eta> = "(b,(Var a)) # \<theta>"
      have i': "(\<forall> x \<in>  (insert a A). (subst (subst (Var x) \<sigma> ) ?\<eta>) = (Var x))"
      proof 
        fix x assume "x \<in> (insert a A)"
        show "(subst (subst (Var x) \<sigma> ) ?\<eta>) = (Var x)"
        proof (cases)
          assume "x = a"
          from this 
            have "(subst  (Var b) ( (b,(Var a)) # Nil)) = (Var a)"
            by simp
          have "b \<notin> (subst_codomain \<sigma> A)"
          proof 
            assume "b \<in> (subst_codomain \<sigma> A)"
            from this have "\<exists>y. (subst (Var y) \<sigma>) = (Var b) \<and> (y \<in> A)" unfolding subst_codomain_def 
              by force 
            then obtain a' where "a' \<in> A" and "subst (Var a') \<sigma> = (Var b)" 
              by metis
            from \<open>a' \<in> A\<close> and \<open>a \<notin> A\<close> have "a \<noteq> a'" by auto
            have "a \<in> (insert a A)" by auto
            from \<open>a \<noteq> a'\<close> and \<open>a' \<in> A\<close> and \<open>a \<in> (insert a A)\<close> and \<open>renaming \<sigma> (insert a A)\<close> 
              have "(subst (Var a) \<sigma> \<noteq> (subst (Var a') \<sigma>))"
              unfolding renaming_def by blast
            from this and \<open>subst (Var a') \<sigma> = (Var b)\<close> \<open>(subst (Var a) \<sigma>) = (Var b)\<close>  
              show False by auto
          qed
          from this and ii have "(subst (Var b) \<theta>) = (Var b)" by auto
          from this and \<open>x = a\<close> \<open>(subst (Var a) \<sigma>) = (Var b)\<close>
            \<open>(subst  (Var b) ( (b,(Var a)) # Nil)) = (Var a)\<close>
            show "(subst (subst (Var x) \<sigma> ) ?\<eta>) = (Var x)"
            by simp
         next assume "x \<noteq> a"
          from this and \<open>x \<in> insert a A\<close> obtain "x \<in> A" by auto
          from this i have "(subst (subst (Var x) \<sigma> ) \<theta>) = (Var x)"
            by auto
          then show "(subst (subst (Var x) \<sigma> ) ?\<eta>) = (Var x)"
            by (metis \<open>subst (Var a) \<sigma> = Var b\<close> \<open>renaming \<sigma> (insert a A)\<close> 
                \<open>x \<in> insert a A\<close> \<open>x \<noteq> a\<close> insertI1 is_a_variable.elims(2) 
                occs.simps(1) renaming_def repl_invariance vars_iff_occseq)
         qed 
       qed
       have ii': "(\<forall> x. (x \<notin> (subst_codomain \<sigma> (insert a A)) \<longrightarrow> (subst (Var x) ?\<eta>) = (Var x)))"
       proof ((rule allI),(rule impI))
        fix x assume "x \<notin> subst_codomain \<sigma> (insert a A)"
        from this \<open>(subst (Var a) \<sigma>) = (Var b)\<close>  have "x\<noteq> b" unfolding subst_codomain_def 
          by auto
        from this have "(subst (Var x) ?\<eta>) = (subst (Var x) \<theta>)" by auto
        from \<open>x \<notin> subst_codomain \<sigma> (insert a A)\<close> have "x \<notin> (subst_codomain \<sigma> A)" unfolding subst_codomain_def 
          by auto
        from this and ii have "(subst (Var x) \<theta>) = (Var x)" by auto
        from \<open>(subst (Var x) ?\<eta>) = (subst (Var x) \<theta>)\<close> 
          and \<open>(subst (Var x) \<theta>) = (Var x)\<close> show "(subst (Var x) ?\<eta>) = (Var x)" 
          by auto
       qed
      from i' ii' show ?thesis by auto
    qed
  qed
qed

lemma renaming_exists:
  assumes "\<not> finite (Vars :: ('a set))"
  shows "finite V \<Longrightarrow> (\<forall>V'::'a set. finite V' \<longrightarrow> (\<exists>\<eta>. ((renaming \<eta> V) \<and> ((subst_codomain \<eta> V) \<inter> V') = {})))"
proof (induction rule: finite.induct)
    case emptyI
    let ?\<eta> = "[]"
    show ?case unfolding renaming_def subst_codomain_def by auto
next
    fix A :: "'a set" and a::'a 
    assume "finite A"
    assume hyp_ind: "\<forall>V' :: 'a set. finite V' \<longrightarrow> (\<exists>\<eta>. renaming \<eta> A \<and> subst_codomain \<eta> A \<inter> V' = {})"
    show "\<forall>V':: 'a set. finite V' \<longrightarrow> (\<exists>\<eta>. renaming \<eta> (insert a A) \<and> subst_codomain \<eta> (insert a A) \<inter> V' = {})"
    proof ((rule allI),(rule impI))
      fix V':: "'a set" assume "finite V'"
      from this have "finite (insert a V')" by auto
      from this and hyp_ind obtain \<eta> where "renaming \<eta> A" and "(subst_codomain \<eta> A) \<inter> (insert a V') = {}" by metis
      from \<open>finite A\<close> have "finite (subst_codomain \<eta> A)" 
        using subst_codomain_is_finite by auto
      from this \<open>finite V'\<close> have "finite (V' \<union> (subst_codomain \<eta> A))" by auto
      from this have "finite ((insert a V') \<union> (subst_codomain \<eta> A))" by auto
      from this \<open>\<not> finite Vars\<close> have "\<not> (Vars \<subseteq> ((insert a V') \<union> (subst_codomain \<eta> A)))" using rev_finite_subset
        by metis
      from this obtain nv where "nv \<in> Vars" and "nv \<notin> (insert a V')" and "nv \<notin> (subst_codomain \<eta> A)" by auto
      let ?\<eta> = "(a,(Var nv)) # \<eta>"
      have i: "(\<forall>x \<in> (insert a A). (is_a_variable (subst (Var x) ?\<eta>)))"
      proof (rule ccontr)
        assume "\<not> (\<forall>x \<in>  (insert a A). (is_a_variable (subst (Var x) ?\<eta>)))"
        then obtain x where "x \<in>  (insert a A)" and "\<not>is_a_variable (subst (Var x) ?\<eta>)" 
          by auto
        from \<open>\<not>is_a_variable (subst (Var x) ?\<eta>)\<close> have "x \<noteq> a" by auto
        from this and \<open>x \<in>  (insert a A)\<close> have "x \<in> A" by auto
        from \<open>x \<noteq> a\<close> have "(subst (Var x) ?\<eta>) = (subst (Var x) \<eta>)" by auto
        from \<open>renaming \<eta> A\<close> and \<open>x \<in> A\<close> have "is_a_variable (subst (Var x) \<eta>)" 
          unfolding renaming_def by metis
        from this and \<open>\<not>is_a_variable (subst (Var x) ?\<eta>)\<close>
          \<open>(subst (Var x) ?\<eta>) = (subst (Var x) \<eta>)\<close> show False by auto
      qed
      have ii: "(\<forall> x y. ((x \<in> (insert a A)) \<longrightarrow> (y \<in> (insert a A)) \<longrightarrow> x \<noteq> y 
        \<longrightarrow> (subst (Var x) ?\<eta>) \<noteq> (subst (Var y) ?\<eta>)))"
      proof (rule ccontr)
        assume "\<not>(\<forall> x y. ((x \<in> (insert a A)) \<longrightarrow> (y \<in> (insert a A)) \<longrightarrow> x \<noteq> y 
          \<longrightarrow> (subst (Var x) ?\<eta>) \<noteq> (subst (Var y) ?\<eta>)))"
        from this obtain x y where "x \<in> insert a A" "y \<in> insert a A" "x \<noteq> y"
          "(subst (Var x) ?\<eta>) = (subst (Var y) ?\<eta>)" by blast
        from i obtain y' where "(subst (Var y) ?\<eta>) = (Var y')" 
          using is_a_variable.simps using \<open>y \<in> insert a A\<close> is_a_variable.elims(2) by auto 
        from i obtain x' where "(subst (Var x) ?\<eta>) = (Var x')" 
          using is_a_variable.simps using \<open>x \<in> insert a A\<close> is_a_variable.elims(2) by auto 
        from \<open>(subst (Var x) ?\<eta>) = (Var x')\<close> \<open>(subst (Var y) ?\<eta>) = (Var y')\<close> 
          \<open>(subst (Var x) ?\<eta>) = (subst (Var y) ?\<eta>)\<close> have "x' = y'" by auto
        have "x \<noteq> a"
        proof 
          assume "x = a"
          from this and \<open>x \<noteq> y\<close> and \<open>y \<in> insert a A\<close> have "y \<in> A" by auto
          from this and \<open>x \<noteq> y\<close> and \<open>x = a\<close> and \<open>(subst (Var y) ?\<eta>) = (Var y')\<close>
          have "y' \<in> (subst_codomain \<eta> A)" unfolding subst_codomain_def by auto
          from \<open>x = a\<close> and \<open>(subst (Var x) ?\<eta>) = (Var x')\<close> have "x' = nv" by auto
          from this and \<open>y' \<in> (subst_codomain \<eta> A)\<close> and \<open>x' = y'\<close> and \<open>nv \<notin> (subst_codomain \<eta> A)\<close> 
          show False by auto
        qed
        from this and \<open>x \<in> insert a A\<close> have "x \<in> A" and 
          "(subst (Var x) ?\<eta>) = (subst (Var x) \<eta>)" by auto
        have "y \<noteq> a"
        proof 
          assume "y = a"
          from this and \<open>x \<noteq> y\<close> and \<open>x \<in> insert a A\<close> have "x \<in> A" by auto
          from this and \<open>x \<noteq> y\<close> and \<open>y = a\<close> and \<open>(subst (Var x) ?\<eta>) = (Var x')\<close>
            have "x' \<in> (subst_codomain \<eta> A)" unfolding subst_codomain_def by auto
          from \<open>y = a\<close> and \<open>(subst (Var y) ?\<eta>) = (Var y')\<close> have "y' = nv" by auto
          from this and \<open>x' \<in> (subst_codomain \<eta> A)\<close> and \<open>x' = y'\<close> and \<open>nv \<notin> (subst_codomain \<eta> A)\<close> 
            show False by auto
        qed
        from this and \<open>y \<in> insert a A\<close> have "y \<in> A" and 
          "(subst (Var y) ?\<eta>) = (subst (Var y) \<eta>)" by auto
        from \<open>(subst (Var x) ?\<eta>) = (subst (Var x) \<eta>)\<close> 
          \<open>(subst (Var y) ?\<eta>) = (subst (Var y) \<eta>)\<close> 
          \<open>(subst (Var x) ?\<eta>) = (subst (Var y) ?\<eta>)\<close> 
        have "(subst (Var x) \<eta>) = (subst (Var y) \<eta>)" by auto
        from this and \<open>x \<in> A\<close> and \<open>y \<in> A\<close>and \<open>renaming \<eta> A\<close> and \<open>x \<noteq> y\<close> show False 
          unfolding renaming_def by metis
     qed
     from i ii have "renaming ?\<eta> (insert a A)" unfolding renaming_def by auto
     have "((subst_codomain ?\<eta> (insert a A)) \<inter> V') = {}"
     proof (rule ccontr)
      assume "(subst_codomain ?\<eta> (insert a A)) \<inter> V' \<noteq> {}"
      then obtain x where "x \<in> (subst_codomain ?\<eta> (insert a A))" and "x \<in> V'" by auto
      from \<open>x \<in> (subst_codomain ?\<eta> (insert a A))\<close> obtain x' where "x' \<in> (insert a A)"  
        and "subst (Var x') ?\<eta> = (Var x)" unfolding subst_codomain_def by blast
      have "x' \<noteq> a"
      proof 
        assume "x' = a"
        from this and \<open>subst (Var x') ?\<eta> = (Var x)\<close> have "x = nv" by auto
        from this and \<open>x \<in> V'\<close> and \<open>nv \<notin> (insert a V')\<close> show False by auto
      qed
      from this and \<open>x' \<in> (insert a A)\<close> have "x' \<in> A" by auto 
      from \<open>x' \<noteq> a\<close> and \<open>subst (Var x') ?\<eta> = (Var x)\<close> have 
        "(Var x) = (subst (Var x') \<eta>)" by auto
      from this and \<open>x' \<in> A\<close>  have "x \<in> subst_codomain \<eta> A" unfolding subst_codomain_def by auto
      from \<open>x \<in> subst_codomain \<eta> A\<close> and \<open>(subst_codomain \<eta> A) \<inter> (insert a V') = {}\<close> and \<open>x \<in> V'\<close> 
        show False  by auto
     qed
     from this and \<open>renaming ?\<eta> (insert a A)\<close> 
      show "\<exists>\<eta>. renaming \<eta> (insert a A) \<and> subst_codomain \<eta> (insert a A) \<inter> V' = {}" by auto
   qed
qed

end
