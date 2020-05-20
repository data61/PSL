theory equational_clausal_logic

(* N. Peltier - http://membres-lig.imag.fr/peltier/ *)

imports Main terms "HOL-Library.Multiset"

begin

section \<open>Equational Clausal Logic\<close>

text \<open>The syntax and semantics of clausal equational logic are defined as usual. 
Interpretations are congruences on binary trees.\<close>

subsection \<open>Syntax\<close>

text \<open>We first define the syntax of equational clauses.\<close>

datatype 'a equation = Eq "'a trm" "'a trm"

fun lhs
  where "lhs (Comb t1 t2) = t1" |
     "lhs (Var x) = (Var x)" |
     "lhs (Const x) = (Const x)"

fun rhs 
  where "rhs (Comb t1 t2) = t2" |
     "rhs (Var x) = (Var x)" |
     "rhs (Const x) = (Const x)"

datatype 'a literal = Pos "'a equation" | Neg "'a equation"

fun atom :: "'a literal \<Rightarrow> 'a equation"
  where 
    "(atom (Pos x)) = x" |
    "(atom (Neg x)) = x"

datatype sign = pos | neg
 
fun get_sign :: "'a literal \<Rightarrow> sign"
  where 
    "(get_sign (Pos x)) = pos" |
    "(get_sign (Neg x)) = neg"

fun positive_literal :: "'a literal \<Rightarrow> bool"
  where
    "(positive_literal (Pos x)) = True" |
    "(positive_literal (Neg x)) = False"

fun negative_literal :: "'a literal \<Rightarrow> bool"
  where
    "(negative_literal (Pos x)) = False" |
    "(negative_literal (Neg x)) = True"

fun mk_lit :: "sign \<Rightarrow> 'a equation \<Rightarrow> 'a literal"
  where 
    "(mk_lit pos x) = (Pos x)" |
    "(mk_lit neg x) = (Neg x)"

definition decompose_equation   
  where "decompose_equation e t s = (e = (Eq t s) \<or> (e = (Eq s t)))"

definition decompose_literal 
  where "decompose_literal L t s p = 
            (\<exists>e. ((p = pos \<and> (L = (Pos e)) \<and> decompose_equation e t s)
            \<or> (p = neg \<and> (L = (Neg e)) \<and> decompose_equation e t s)))"

fun subterms_of_eq 
  where "subterms_of_eq (Eq t s) = (subterms_of t \<union> subterms_of s)"

fun vars_of_eq 
  where "vars_of_eq (Eq t s) = (vars_of t \<union> vars_of s)"

lemma decompose_equation_vars:
  assumes "decompose_equation e t s"
  shows "vars_of t \<subseteq> vars_of_eq e"
by (metis assms decompose_equation_def sup.cobounded1 sup_commute vars_of_eq.simps)

fun subterms_of_lit 
  where 
    "subterms_of_lit (Pos e) = (subterms_of_eq e)" |
    "subterms_of_lit (Neg e) = (subterms_of_eq e)"

fun vars_of_lit 
  where 
    "vars_of_lit (Pos e) = (vars_of_eq e)" |
    "vars_of_lit (Neg e) = (vars_of_eq e)"

fun vars_of_cl 
  where "vars_of_cl C = { x. \<exists>L. x \<in> (vars_of_lit L) \<and> L \<in> C }"

fun subterms_of_cl 
  where "subterms_of_cl C = { x. \<exists>L. x \<in> (subterms_of_lit L) \<and> L \<in> C }"

text \<open>Note that clauses are defined as sets and not as multisets 
(identical literals are always merged).\<close>

type_synonym 'a clause = "'a literal set"

fun ground_clause :: "'a clause \<Rightarrow> bool"
where
  "(ground_clause C) = ((vars_of_cl C) = {})"

fun subst_equation :: "'a equation \<Rightarrow> 'a subst \<Rightarrow> 'a equation"
where
  "(subst_equation (Eq u v) s) 
    = (Eq (subst u s) (subst v s))"

fun subst_lit :: "'a literal \<Rightarrow> 'a subst \<Rightarrow> 'a literal"
where
  "(subst_lit (Pos e) s) 
    = (Pos (subst_equation e s))" |
  "(subst_lit (Neg e) s) 
    = (Neg (subst_equation e s))" 

fun subst_cl :: "'a clause \<Rightarrow> 'a subst \<Rightarrow> 'a clause"
where
  "(subst_cl C s) = { L. (\<exists>L'. (L' \<in> C) \<and> (L = (subst_lit L' s))) }" 

text \<open>We establish some properties of the functions returning the set of variables occurring in 
an object.\<close>

lemma decompose_literal_vars:
  assumes "decompose_literal L t s p"
  shows "vars_of t \<subseteq> vars_of_lit L"
by (metis assms decompose_equation_vars decompose_literal_def vars_of_lit.simps(1) vars_of_lit.simps(2))

lemma vars_of_cl_lem:
  assumes "L \<in> C"
  shows "vars_of_lit L \<subseteq> vars_of_cl C"
using assms by auto

lemma set_of_variables_is_finite_eq:
  shows "finite (vars_of_eq e)"
proof -
  obtain t and s where "e = Eq t s" using equation.exhaust by auto  
  then have "vars_of_eq e = (vars_of t) \<union> (vars_of s)" by auto
  from this show ?thesis by auto
qed

lemma set_of_variables_is_finite_lit:
  shows "finite (vars_of_lit l)"
proof -
  obtain e where "l = Pos e \<or> l = Neg e" using literal.exhaust by auto 
  then have "vars_of_lit l = (vars_of_eq e)" by auto
  from this show ?thesis using set_of_variables_is_finite_eq by auto
qed

lemma set_of_variables_is_finite_cl:
  assumes "finite C"
  shows "finite (vars_of_cl C)"
proof -
  let ?S = "{ x. \<exists>l. x = vars_of_lit l \<and> l \<in> C }"
  have "vars_of_cl C = \<Union> ?S" by auto
  from assms have "finite ?S" by auto
  { fix x have "x \<in> ?S \<Longrightarrow> finite x" using set_of_variables_is_finite_lit by auto }
  from this and \<open>finite ?S\<close> have "finite (\<Union> ?S)" using finite_Union by auto
  from this and \<open>vars_of_cl C = \<Union> ?S\<close> show ?thesis by auto
qed

lemma subterm_lit_vars :
  assumes "u \<in> subterms_of_lit L"
  shows "vars_of u \<subseteq> vars_of_lit L"
proof -
  obtain e where def_e: "L = (Pos e) \<or> L = (Neg e)" and "vars_of_lit L = vars_of_eq e"
    by (metis negative_literal.elims(2) negative_literal.elims(3) 
      vars_of_lit.simps(1) vars_of_lit.simps(2))
  obtain t and s where def_ts: "e = (Eq t s) \<or> e = (Eq s t)" and "vars_of_eq e = vars_of t \<union> vars_of s"
    by (metis equation.exhaust vars_of_eq.simps)
  from this and \<open>vars_of_lit L = vars_of_eq e\<close> have "vars_of_lit L = vars_of t \<union> vars_of s" by auto
  from assms(1) and def_e def_ts have "u \<in> subterms_of t \<union> subterms_of s" by auto
  from this have "vars_of u \<subseteq> vars_of t \<union> vars_of s"
    by (meson UnE sup.coboundedI1 sup.coboundedI2 vars_subterms_of)
  from this and \<open>vars_of_lit L = vars_of t \<union> vars_of s\<close> show ?thesis by auto
qed

lemma subterm_vars :
  assumes "u \<in> subterms_of_cl C"
  shows "vars_of u \<subseteq> vars_of_cl C"
proof -
  from assms(1) obtain L where "u \<in> subterms_of_lit L" and "L \<in> C" by auto
  from \<open>u \<in> subterms_of_lit L\<close> have "vars_of u \<subseteq> vars_of_lit L" using subterm_lit_vars by auto
  from  \<open>L \<in> C\<close> have "vars_of_lit L \<subseteq> vars_of_cl C" using vars_of_cl.simps by auto
  from this and \<open>vars_of u \<subseteq> vars_of_lit L\<close> show ?thesis by auto
qed

text \<open>We establish some basic properties of substitutions.\<close>

lemma subterm_cl_subst:
  assumes "x \<in> (subterms_of_cl C)"
  shows "(subst x \<sigma>) \<in>  (subterms_of_cl (subst_cl C \<sigma>))"
proof -
  from assms(1) obtain L where "L \<in> C" and "x \<in> subterms_of_lit L" by auto
  from \<open>L \<in> C\<close> have "(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)" by auto
  obtain e where "L = (Pos e) \<or> L = (Neg e)" using literal.exhaust by auto
  then show ?thesis
  proof
    assume "L = (Pos e)" 
    from this and \<open>x \<in> subterms_of_lit L\<close> have "x \<in> subterms_of_eq e" by auto
    from \<open>L = (Pos e)\<close> have "(subst_lit L \<sigma>) = (Pos (subst_equation e \<sigma>))"
      by auto
    obtain t s where "e = (Eq t s)" using equation.exhaust by auto
    from this have "(subst_equation e \<sigma>) = (Eq (subst t \<sigma>)  (subst s \<sigma>))"
      by auto
    from \<open>x \<in> subterms_of_eq e\<close> and \<open>e = (Eq t s)\<close> have "x \<in> subterms_of t \<or> x \<in> subterms_of s" by auto
    then show ?thesis
    proof
      assume "x \<in> subterms_of t"
      then have "occurs_in x t" by auto
      then obtain p where "subterm t p x" unfolding occurs_in_def by blast
      from this have "subterm (subst t \<sigma>) p (subst x \<sigma>)"
        using substs_preserve_subterms by auto 
      from this have "occurs_in (subst x \<sigma>) (subst t \<sigma>)" unfolding occurs_in_def by auto
      then have "(subst x \<sigma>) \<in> subterms_of (subst t \<sigma>)" by auto
      then have "(subst x \<sigma>) \<in> subterms_of_eq (Eq (subst t \<sigma>) (subst s \<sigma>))" by auto
      from this and \<open>L = (Pos e)\<close> and \<open>e = Eq t s\<close> 
        have "(subst x \<sigma>) \<in> (subterms_of_lit (subst_lit L \<sigma>))" by auto
      from this and \<open>(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)\<close> 
        show "(subst x \<sigma>) \<in> subterms_of_cl (subst_cl C \<sigma>)" by auto
    next
      assume "x \<in> subterms_of s"
      then have "occurs_in x s" by auto
      then obtain p where "subterm s p x" unfolding occurs_in_def by blast
      from this have "subterm (subst s \<sigma>) p (subst x \<sigma>)"
        using substs_preserve_subterms by auto 
      from this have "occurs_in (subst x \<sigma>) (subst s \<sigma>)" unfolding occurs_in_def by auto
      then have "(subst x \<sigma>) \<in> subterms_of (subst s \<sigma>)" by auto
      then have "(subst x \<sigma>) \<in> subterms_of_eq (Eq (subst t \<sigma>) (subst s \<sigma>))" by auto
      from this and \<open>L = (Pos e)\<close> and \<open>e = Eq t s\<close> 
        have "(subst x \<sigma>) \<in> (subterms_of_lit (subst_lit L \<sigma>))" by auto
      from this and \<open>(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)\<close> 
        show "(subst x \<sigma>) \<in> subterms_of_cl (subst_cl C \<sigma>)" by auto
    qed
    next
    assume "L = (Neg e)" 
    from this and \<open>x \<in> subterms_of_lit L\<close> have "x \<in> subterms_of_eq e" by auto
    from \<open>L = (Neg e)\<close> have "(subst_lit L \<sigma>) = (Neg (subst_equation e \<sigma>))"
      by auto
    obtain t s where "e = (Eq t s)" using equation.exhaust by auto
    from this have "(subst_equation e \<sigma>) = (Eq (subst t \<sigma>)  (subst s \<sigma>))"
      by auto
    from \<open>x \<in> subterms_of_eq e\<close> and \<open>e = (Eq t s)\<close> have "x \<in> subterms_of t \<or> x \<in> subterms_of s" by auto
    then show ?thesis
    proof
      assume "x \<in> subterms_of t"
      then have "occurs_in x t" by auto
      then obtain p where "subterm t p x" unfolding occurs_in_def by blast
      from this have "subterm (subst t \<sigma>) p (subst x \<sigma>)"
        using substs_preserve_subterms by auto 
      from this have "occurs_in (subst x \<sigma>) (subst t \<sigma>)" unfolding occurs_in_def by auto
      then have "(subst x \<sigma>) \<in> subterms_of (subst t \<sigma>)" by auto
      then have "(subst x \<sigma>) \<in> subterms_of_eq (Eq (subst t \<sigma>) (subst s \<sigma>))" by auto
      from this and \<open>L = (Neg e)\<close> and \<open>e = Eq t s\<close> 
        have "(subst x \<sigma>) \<in> (subterms_of_lit (subst_lit L \<sigma>))" by auto
      from this and \<open>(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)\<close> 
        show "(subst x \<sigma>) \<in> subterms_of_cl (subst_cl C \<sigma>)" by auto
    next
      assume "x \<in> subterms_of s"
      then have "occurs_in x s" by auto
      then obtain p where "subterm s p x" unfolding occurs_in_def by blast
      from this have "subterm (subst s \<sigma>) p (subst x \<sigma>)"
        using substs_preserve_subterms by auto 
      from this have "occurs_in (subst x \<sigma>) (subst s \<sigma>)" unfolding occurs_in_def by auto
      then have "(subst x \<sigma>) \<in> subterms_of (subst s \<sigma>)" by auto
      then have "(subst x \<sigma>) \<in> subterms_of_eq (Eq (subst t \<sigma>) (subst s \<sigma>))" by auto
      from this and \<open>L = (Neg e)\<close> and \<open>e = Eq t s\<close> 
        have "(subst x \<sigma>) \<in> (subterms_of_lit (subst_lit L \<sigma>))" by auto
      from this and \<open>(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)\<close> 
        show "(subst x \<sigma>) \<in> subterms_of_cl (subst_cl C \<sigma>)" by auto
    qed
  qed
qed

lemma ground_substs_yield_ground_clause:
  assumes "ground_on (vars_of_cl C) \<sigma>"
  shows "ground_clause (subst_cl C \<sigma>)"
proof (rule ccontr)
    let ?D = "(subst_cl C \<sigma>)"
    let ?V = "(vars_of_cl C)"
    assume "\<not>(ground_clause ?D)"
    then obtain x where "x \<in> (vars_of_cl ?D)" by auto
    then obtain l where "l \<in> C" and "x \<in> (vars_of_lit (subst_lit l  \<sigma>))" by auto
    from \<open>l \<in> C\<close> have "vars_of_lit l \<subseteq> vars_of_cl C" by auto
    obtain e  where "l = Pos e \<or> l = Neg e" using literal.exhaust by auto 
    then have "vars_of_lit l = vars_of_eq e" by auto
    let ?l' = "(subst_lit l \<sigma>)" 
    let ?e' = "(subst_equation e \<sigma>)" 
    obtain t and s where "e = Eq t s" using equation.exhaust by auto 
    then have "vars_of_eq e = vars_of t \<union> vars_of s" by auto
    let ?t' = "(subst t \<sigma>)" 
    let ?s' = "(subst s \<sigma>)" 
    from \<open>e = Eq t s\<close> have "?e' = (Eq ?t' ?s')" by auto
    from \<open>l = Pos e \<or> l = Neg e\<close> have "?l' = Pos ?e' \<or> ?l' = Neg ?e'" by auto    
    from \<open>l \<in> C\<close> have "?l' \<in> ?D" by auto
    from \<open>?l' = Pos ?e' \<or> ?l' = Neg ?e'\<close> and \<open>x \<in> (vars_of_lit ?l')\<close> 
      have "x \<in> (vars_of_eq ?e')" by auto
    from this and \<open>?e' = (Eq ?t' ?s')\<close> have "x \<in> (vars_of ?t' \<union> vars_of ?s')" by auto 
    then have i:"\<not>(ground_term ?t') \<or> \<not>(ground_term ?s')" unfolding ground_term_def by auto
    from \<open>vars_of_eq e = vars_of t \<union> vars_of s\<close> and \<open>vars_of_lit l = vars_of_eq e\<close> and
      \<open>vars_of_lit l \<subseteq> ?V\<close> have "vars_of t \<subseteq> ?V" and "vars_of s \<subseteq> ?V" by auto
    from \<open>vars_of t  \<subseteq> ?V\<close> and \<open>ground_on ?V \<sigma>\<close> have  "ground_on (vars_of t) \<sigma>" 
      unfolding ground_on_def by auto
    then have ii:"ground_term ?t'" using ground_instance by auto
    from \<open>vars_of s  \<subseteq> ?V\<close> and \<open>ground_on ?V \<sigma>\<close> have  "ground_on (vars_of s) \<sigma>" 
      unfolding ground_on_def by auto
    then have iii:"ground_term ?s'" using ground_instance by auto
    from i and ii and iii show False by auto
qed

lemma ground_clauses_and_ground_substs:
  assumes "ground_clause (subst_cl C \<sigma>)"
  shows "ground_on (vars_of_cl C) \<sigma>"
proof (rule ccontr)
  assume "\<not>ground_on (vars_of_cl C) \<sigma>"
  from this obtain x where "x \<in> vars_of_cl C" and "\<not> ground_term (subst (Var x) \<sigma>)"
    unfolding ground_on_def by auto
  from \<open>\<not> ground_term (subst (Var x) \<sigma>)\<close> obtain y where 
    "y \<in> vars_of (subst (Var x) \<sigma>)" unfolding ground_term_def by auto
  from \<open>x \<in> vars_of_cl C\<close> obtain L where "L \<in> C" and "x \<in> vars_of_lit L" by auto
  from \<open>x \<in> vars_of_lit L\<close> obtain e where "L = Pos e \<or> L = Neg e" and "x \<in> vars_of_eq e"
    by (metis vars_of_lit.elims) 
  from \<open>x \<in> vars_of_eq e\<close> obtain t s where "e = (Eq t s)" and "x \<in> vars_of t \<union> vars_of s"
    by (metis vars_of_eq.elims) 
  from this have "x \<in> vars_of t \<or> x \<in> vars_of s" by auto
  then have "y \<in> vars_of_eq (subst_equation e \<sigma>)"
  proof
    assume "x \<in> vars_of t"
    have i: "vars_of (subst t \<sigma>) = \<Union>{V. \<exists>x. x \<in> vars_of t \<and> V = vars_of (subst (Var x) \<sigma>) }"
      using vars_of_instances [of t \<sigma>] by meson 
    from \<open>x \<in> vars_of t\<close>  i 
      have "vars_of (subst (Var x) \<sigma>) \<subseteq> vars_of (subst t \<sigma>)" 
      by auto
    from this and \<open>y \<in> vars_of (subst (Var x) \<sigma>)\<close> \<open>e = (Eq t s)\<close> show ?thesis by auto
  next
    assume "x \<in> vars_of s"
    have i: "vars_of (subst s \<sigma>) = \<Union>{V. \<exists>x. x \<in> vars_of s \<and> V = vars_of (subst (Var x) \<sigma>) }"
      using vars_of_instances [of s \<sigma>] by meson 
    from \<open>x \<in> vars_of s\<close> i 
      have "vars_of (subst (Var x) \<sigma>) \<subseteq> vars_of (subst s \<sigma>)" 
      by auto
    from this and \<open>y \<in> vars_of (subst (Var x) \<sigma>)\<close> \<open>e = (Eq t s)\<close> show ?thesis by auto
  qed
  from this and \<open>L = Pos e \<or> L = Neg e\<close> have "y \<in> vars_of_lit (subst_lit L \<sigma>)"
    by auto
  from this and \<open>L \<in> C\<close> have "y \<in> vars_of_cl (subst_cl C \<sigma>)" by auto
  from this and assms(1) show False by auto
qed

lemma ground_instance_exists:
  assumes "finite C"
  shows "\<exists>\<sigma>. (ground_clause (subst_cl C \<sigma>))"
proof -
  let ?V = "(vars_of_cl C)"
  from assms have "finite ?V" using set_of_variables_is_finite_cl by auto
  from this obtain \<sigma> where "ground_on ?V \<sigma>" 
    using ground_subst_exists by blast
  let ?D = "(subst_cl C \<sigma>)"
  from \<open>ground_on ?V \<sigma>\<close> have "(ground_clause ?D)" using ground_substs_yield_ground_clause [of C \<sigma>] by auto
  then show ?thesis by auto
qed

lemma composition_of_substs :
  shows "(subst (subst t  \<sigma>) \<eta>) 
    = (subst t (comp \<sigma> \<eta>))"
by simp

lemma composition_of_substs_eq :
  shows "(subst_equation (subst_equation e \<sigma>) \<eta>) 
    = (subst_equation e (comp \<sigma> \<eta>))"
by (metis subst_equation.simps composition_of_substs vars_of_eq.elims)

lemma composition_of_substs_lit :
  shows "(subst_lit (subst_lit l \<sigma>) \<eta>) 
    = (subst_lit l (comp \<sigma> \<eta>))"
by (metis subst_lit.simps(1) subst_lit.simps(2) 
    composition_of_substs_eq positive_literal.cases)

lemma composition_of_substs_cl :
  shows "(subst_cl (subst_cl C \<sigma>) \<eta>) 
    = (subst_cl C (comp \<sigma> \<eta>))"
proof -
  let ?f = "(\<lambda>x. (subst_lit (subst_lit x  \<sigma>) \<eta>))"
  let ?f' = "(\<lambda>x. (subst_lit x (comp \<sigma> \<eta>)))"
  have "\<forall>l. (?f l) = (?f' l)" using composition_of_substs_lit by auto
  then show ?thesis by auto
qed

lemma substs_preserve_ground_lit :
  assumes "ground_clause C"
  assumes "y \<in> C"
  shows "subst_lit y \<sigma> = y"
proof - 
    obtain t and s where "y = Pos (Eq t s) \<or> y = Neg (Eq t s)" 
      by (metis subst_equation.elims get_sign.elims)
    from this have "vars_of t \<subseteq> vars_of_lit y" by auto 
    from this and \<open>y \<in> C\<close> have "vars_of t \<subseteq> vars_of_cl C" by auto 
    from this and assms(1) have "ground_term t" unfolding ground_term_def by auto
    then have "subst t \<sigma> = t" using substs_preserve_ground_terms by auto
    from \<open>y = Pos (Eq t s) \<or> y = Neg (Eq t s)\<close> have "vars_of s \<subseteq> vars_of_lit y" by auto 
    from this and \<open>y \<in> C\<close> have "vars_of s \<subseteq> vars_of_cl C" by auto 
    from this and assms(1) have "ground_term s" unfolding ground_term_def by auto
    then have "subst s \<sigma> = s" using substs_preserve_ground_terms by auto
    from \<open>subst s \<sigma> = s\<close> and \<open>subst t \<sigma> = t\<close> and \<open>y = Pos (Eq t s) \<or> y = Neg (Eq t s)\<close>
    show "subst_lit y \<sigma> = y" by auto
qed
  
lemma substs_preserve_ground_clause :
  assumes "ground_clause C"
  shows "subst_cl C \<sigma> = C"
proof 
  show "subst_cl C \<sigma> \<subseteq> C"
  proof
    fix x assume "x \<in> subst_cl C \<sigma>"
    then obtain y where "y \<in> C" and "x = subst_lit y \<sigma>" by auto
    from assms(1) and \<open>y \<in> C\<close> and \<open>x = subst_lit y \<sigma>\<close> 
      have "x = y" using substs_preserve_ground_lit by auto
    from this and \<open>y \<in> C\<close> show "x \<in> C" by auto
  qed
next
  show "C \<subseteq> subst_cl C \<sigma>"
  proof 
    fix x assume "x \<in> C"
    then have "subst_lit x \<sigma> \<in> subst_cl C \<sigma>" by auto
    from assms(1) and \<open>x \<in> C\<close> have "x = subst_lit x \<sigma>" 
      using substs_preserve_ground_lit [of C x] by auto
    from this and \<open>x \<in> C\<close> show "x \<in> subst_cl C \<sigma>" by auto
  qed
qed

lemma substs_preserve_finiteness :
  assumes "finite C"
  shows "finite (subst_cl C \<sigma>)"
proof -
  from assms(1) show ?thesis using Finite_Set.finite_imageI by auto
qed

text \<open>We prove that two equal substitutions yield the same objects.\<close>
 
lemma subst_eq_eq :
  assumes "subst_eq \<sigma> \<eta>"
  shows "subst_equation e \<sigma> = subst_equation e \<eta>"
proof -
  obtain t and s where "e = Eq t s" using equation.exhaust by auto 
  from assms(1) have "subst s \<sigma> = subst s \<eta>" by auto
  from assms(1) have "subst t \<sigma> = subst t \<eta>" by auto
  from \<open>subst s \<sigma> = subst s \<eta>\<close> \<open>subst t \<sigma> = subst t \<eta>\<close>
    and \<open>e = Eq t s\<close> show ?thesis by auto
qed

lemma subst_eq_lit :
  assumes "subst_eq \<sigma> \<eta>"
  shows "subst_lit l \<sigma> = subst_lit l \<eta>"
proof -
  obtain e where "l = Pos e \<or> l = Neg e" using literal.exhaust by auto 
  from assms(1)  have "subst_equation e \<sigma> = subst_equation e \<eta>" using subst_eq_eq by auto
  from this and \<open>l = Pos e \<or> l = Neg e\<close> show ?thesis by auto
qed

lemma subst_eq_cl:
  assumes "subst_eq \<sigma> \<eta>"
  shows "subst_cl C \<sigma> = subst_cl C \<eta>"
proof (rule ccontr)
  assume "subst_cl C \<sigma> \<noteq> subst_cl C \<eta>"
  then obtain L where "L \<in> C" and "subst_lit L \<sigma> \<noteq> subst_lit L \<eta>"
    by force
  from assms(1) and \<open>subst_lit L \<sigma> \<noteq> subst_lit L \<eta>\<close> 
    show False using subst_eq_lit by auto
qed

lemma coincide_on_eq :
  assumes "coincide_on \<sigma> \<eta> (vars_of_eq e)"
  shows "subst_equation e \<sigma> = subst_equation e \<eta>"
proof -
  obtain t and s where "e = Eq t s" using equation.exhaust by auto 
  then have "vars_of t \<subseteq> vars_of_eq e" by simp
  from this and \<open>coincide_on \<sigma> \<eta> (vars_of_eq e)\<close> have "coincide_on \<sigma> \<eta> (vars_of t)" 
    unfolding coincide_on_def by auto
  from this have "subst t \<sigma> = subst t \<eta>" using coincide_on_term by auto
  from \<open>e = Eq t s\<close>  have "vars_of s \<subseteq> vars_of_eq e" by simp
  from this and \<open>coincide_on \<sigma> \<eta> (vars_of_eq e)\<close> have "coincide_on \<sigma> \<eta> (vars_of s)" 
    unfolding coincide_on_def by auto
  from this have "subst s \<sigma> = subst s \<eta>" using coincide_on_term by auto
  from \<open>subst t \<sigma> = subst t \<eta>\<close> 
    and \<open>subst s \<sigma> = subst s \<eta>\<close> 
    and \<open>e = Eq t s\<close> show ?thesis by auto
qed

lemma coincide_on_lit :
  assumes "coincide_on \<sigma> \<eta> (vars_of_lit l)"
  shows "subst_lit l \<sigma> = subst_lit l \<eta>"
proof -
  obtain e where "l = Pos e \<or> l = Neg e" using literal.exhaust by auto 
  then have "vars_of_eq e \<subseteq> vars_of_lit l" by auto 
  from this and \<open>coincide_on \<sigma> \<eta> (vars_of_lit l)\<close> have "coincide_on \<sigma> \<eta> (vars_of_eq e)" 
    unfolding coincide_on_def by auto
  from this have "subst_equation e \<sigma> = subst_equation e \<eta>" 
    using coincide_on_eq by auto
  from this and \<open>l = Pos e \<or> l = Neg e\<close> show ?thesis by auto
qed

lemma coincide_on_cl :
  assumes "coincide_on \<sigma> \<eta> (vars_of_cl C)"
  shows "subst_cl C \<sigma> = subst_cl C \<eta>"
proof (rule ccontr)
  assume "subst_cl C \<sigma> \<noteq> subst_cl C \<eta>"
  then obtain L where "L \<in> C" and "subst_lit L \<sigma> \<noteq> subst_lit L \<eta>"
    by force
  from \<open>L \<in> C\<close> have "vars_of_lit L \<subseteq> vars_of_cl C" by auto
  from this and assms have "coincide_on \<sigma> \<eta> (vars_of_lit L)" unfolding coincide_on_def by auto
  from this and \<open>subst_lit L \<sigma> \<noteq> subst_lit L \<eta>\<close> 
    show False using coincide_on_lit by auto
qed

subsection \<open>Semantics\<close>

text \<open>Interpretations are congruences on the set of terms.\<close>

definition fo_interpretation :: "'a binary_relation_on_trms \<Rightarrow> bool"
where 
  "(fo_interpretation x) = (congruence x)"

fun validate_ground_eq :: "'a binary_relation_on_trms \<Rightarrow> 'a equation  \<Rightarrow> bool"
where
"(validate_ground_eq I (Eq t s) = (I t s))"

fun validate_ground_lit :: "'a binary_relation_on_trms \<Rightarrow> 'a literal  \<Rightarrow> bool"
where
"validate_ground_lit I (Pos E) = (validate_ground_eq I E)" |
"validate_ground_lit I (Neg E) = (\<not>(validate_ground_eq I E))"

fun validate_ground_clause :: "'a binary_relation_on_trms \<Rightarrow> 'a clause \<Rightarrow> bool"
where
"validate_ground_clause I C = (\<exists>L.(L \<in> C) \<and> (validate_ground_lit I L))"

fun validate_clause :: "'a binary_relation_on_trms \<Rightarrow> 'a clause \<Rightarrow> bool"
where
"validate_clause I C = (\<forall>s. (ground_clause (subst_cl C s)) 
  \<longrightarrow> (validate_ground_clause I (subst_cl C s)))"

fun validate_clause_set :: "'a binary_relation_on_trms \<Rightarrow> 'a clause set \<Rightarrow> bool"
where
"validate_clause_set I S = (\<forall>C. (C \<in> S  \<longrightarrow> (validate_clause I C)))"

definition clause_entails_clause :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  "clause_entails_clause C D = (\<forall>I. (fo_interpretation I \<longrightarrow> validate_clause I C \<longrightarrow> validate_clause I D))"

definition set_entails_clause :: "'a clause set \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  "set_entails_clause S C = (\<forall>I. (fo_interpretation I \<longrightarrow> validate_clause_set I S \<longrightarrow> validate_clause I C))"

definition satisfiable_clause_set :: "'a clause set \<Rightarrow> bool"
 where  
 "(satisfiable_clause_set S) = (\<exists>I. (fo_interpretation I) \<and> (validate_clause_set I S))"

text \<open>We state basic properties of the entailment relation.\<close>

lemma set_entails_clause_member:
  assumes "C \<in> S"
  shows "set_entails_clause S C"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this obtain I where "fo_interpretation I" "validate_clause_set I S" "\<not> validate_clause I C" 
    unfolding set_entails_clause_def by auto
  from \<open>validate_clause_set I S\<close> and assms(1) \<open>\<not> validate_clause I C\<close> show False  by auto
qed

lemma instances_are_entailed :
  assumes "validate_clause I C"
  shows "validate_clause I (subst_cl C \<sigma>)"
proof (rule ccontr)
  assume "\<not>validate_clause I (subst_cl C \<sigma>)"
  then obtain \<eta> 
    where "\<not>validate_ground_clause I (subst_cl (subst_cl C \<sigma>) \<eta>)" 
      and "ground_clause (subst_cl (subst_cl C \<sigma>) \<eta>)"
    by auto
  then have i: "\<not>validate_ground_clause I (subst_cl C (comp \<sigma> \<eta>))"
   using composition_of_substs_cl by metis 
  from \<open>ground_clause (subst_cl (subst_cl C \<sigma>) \<eta>)\<close> 
    have ii: "ground_clause (subst_cl C (comp \<sigma> \<eta>))" 
    using composition_of_substs_cl by metis
  from i and ii have "\<not>validate_clause I C" by auto
  from \<open>\<not>validate_clause I C\<close> and \<open>validate_clause I C\<close> show False by blast
qed

text \<open>We prove that two equivalent substitutions yield equivalent objects.\<close>

lemma equivalent_on_eq :
  assumes "equivalent_on \<sigma> \<eta> (vars_of_eq e) I"
  assumes "fo_interpretation I"
  shows "(validate_ground_eq I (subst_equation e \<sigma>)) = (validate_ground_eq I (subst_equation e \<eta>))"
proof -
  obtain t and s where "e = Eq t s" using equation.exhaust by auto 
  then have "vars_of t \<subseteq> vars_of_eq e" by simp
  from this and assms(1) have "equivalent_on \<sigma> \<eta> (vars_of t) I" 
    unfolding equivalent_on_def by auto
  from this assms(2) 
    have "I (subst t \<sigma>) (subst t \<eta>)" using equivalent_on_term 
    unfolding fo_interpretation_def by auto
  from \<open>e = Eq t s\<close>  have "vars_of s \<subseteq> vars_of_eq e" by simp
  from this and \<open>equivalent_on \<sigma> \<eta> (vars_of_eq e) I\<close> have "equivalent_on \<sigma> \<eta> (vars_of s) I" 
    unfolding equivalent_on_def by auto
  from this assms(2) have "I (subst s \<sigma>) (subst s \<eta>)" 
    using equivalent_on_term unfolding fo_interpretation_def by auto
  from assms(2) \<open>I (subst t \<sigma>) (subst t \<eta>)\<close> 
    and \<open>I (subst s \<sigma>) (subst s \<eta>)\<close> 
    and \<open>e = Eq t s\<close> show ?thesis unfolding fo_interpretation_def congruence_def equivalence_relation_def 
    transitive_def symmetric_def reflexive_def
    by (metis (full_types) subst_equation.simps validate_ground_eq.simps)   
qed

lemma equivalent_on_lit :
  assumes "equivalent_on \<sigma> \<eta> (vars_of_lit l) I"
  assumes "fo_interpretation I"
  shows "(validate_ground_lit I (subst_lit l \<sigma>)) 
    = (validate_ground_lit I (subst_lit l \<eta>))"
proof -
  obtain e where "l = Pos e \<or> l = Neg e" using literal.exhaust by auto 
  then have "vars_of_eq e \<subseteq> vars_of_lit l" by auto 
  from this and \<open>equivalent_on \<sigma> \<eta> (vars_of_lit l) I\<close> have "equivalent_on \<sigma> \<eta> (vars_of_eq e) I" 
    unfolding equivalent_on_def by auto
  from this assms(2) have "(validate_ground_eq I (subst_equation e \<sigma>)) = (validate_ground_eq I (subst_equation e \<eta>))" 
    using equivalent_on_eq by auto
  from this and \<open>l = Pos e \<or> l = Neg e\<close> show ?thesis by auto
qed

lemma equivalent_on_cl :
  assumes "equivalent_on \<sigma> \<eta> (vars_of_cl C) I"
  assumes "fo_interpretation I"
  shows "(validate_ground_clause I (subst_cl C \<sigma>)) 
    = (validate_ground_clause I (subst_cl C \<eta>))"
proof (rule ccontr)
  assume "(validate_ground_clause I (subst_cl C \<sigma>)) 
    \<noteq> (validate_ground_clause I (subst_cl C \<eta>))"
  then obtain L where "L \<in> C" and "(validate_ground_lit I (subst_lit L \<sigma>)) 
    \<noteq> (validate_ground_lit I (subst_lit L \<eta>))"
    by force
  from \<open>L \<in> C\<close> have "vars_of_lit L \<subseteq> vars_of_cl C" by auto
  from this and assms have "equivalent_on \<sigma> \<eta> (vars_of_lit L) I" unfolding equivalent_on_def by auto
  from this assms(2) and \<open>(validate_ground_lit I (subst_lit L \<sigma>)) 
    \<noteq> (validate_ground_lit I (subst_lit L \<eta>))\<close> 
    show False using equivalent_on_lit by metis
qed

end
