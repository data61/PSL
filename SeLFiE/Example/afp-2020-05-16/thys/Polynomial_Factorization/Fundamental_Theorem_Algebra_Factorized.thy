(*  
    Author:      René Thiemann 
    License:     BSD
*)
subsection \<open>Fundamental Theorem of Algebra for Factorizations\<close>

text \<open>Via the existing formulation of the fundamental theorem of algebra,
  we prove that we always get a linear factorization of a complex polynomial.
  Using this factorization we show that root-square-freeness of complex polynomial
  is identical to the statement that the cardinality of the set of all roots 
  is equal to the degree of the polynomial.\<close>

theory Fundamental_Theorem_Algebra_Factorized
imports 
  Order_Polynomial
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

lemma fundamental_theorem_algebra_factorized: fixes p :: "complex poly"
  shows "\<exists> as. smult (coeff p (degree p)) (\<Prod> a \<leftarrow> as. [:- a, 1:]) = p \<and> length as = degree p"
proof -
  define n where "n = degree p"
  have "degree p = n" unfolding n_def by simp
  thus ?thesis
  proof (induct n arbitrary: p)
    case (0 p)
    hence "\<exists> c. p = [: c :]" by (cases p, auto split: if_splits)
    thus ?case by (intro exI[of _ Nil], auto)
  next
    case (Suc n p)
    have dp: "degree p = Suc n" by fact
    hence "\<not> constant (poly p)" by (simp add: constant_degree)
    from fundamental_theorem_of_algebra[OF this] obtain c where rt: "poly p c = 0" by auto
    hence "[:-c,1 :] dvd p" by (simp add: dvd_iff_poly_eq_0)
    then obtain q where p: "p = q * [: -c,1 :]" by (metis dvd_def mult.commute)
    from \<open>degree p = Suc n\<close> have dq: "degree q = n" using p
      by simp (metis add.right_neutral degree_synthetic_div diff_Suc_1 mult.commute mult_left_cancel p pCons_eq_0_iff rt synthetic_div_correct' zero_neq_one) 
    from Suc(1)[OF this] obtain as where q: "[:coeff q (degree q):] * (\<Prod>a\<leftarrow>as. [:- a, 1:]) = q"
      and deg: "length as = degree q" by auto
    have dc: "degree p = degree q + degree [: -c, 1 :]" unfolding dq dp by simp
    have cq: "coeff q (degree q) = coeff p (degree p)" unfolding dc unfolding p coeff_mult_degree_sum unfolding dq by simp
    show ?case using p[unfolded q[unfolded cq, symmetric]] 
      by (intro exI[of _ "c # as"], auto simp: ac_simps, insert deg dc, auto)
  qed
qed

lemma rsquarefree_card_degree: assumes p0: "(p :: complex poly) \<noteq> 0"
  shows "rsquarefree p = (card {x. poly p x = 0} = degree p)"
proof -
  from fundamental_theorem_algebra_factorized[of p] obtain c as
    where p: "p = smult c (\<Prod> a \<leftarrow> as. [:- a, 1:])" and pas: "degree p = length as"
    and c: "c = coeff p (degree p)" by metis
  let ?prod = "(\<Prod>a\<leftarrow>as. [:- a, 1:])"
  from p0 have c: "c \<noteq> 0" unfolding c by auto
  have roots: "{x. poly p x = 0} = set as" unfolding p poly_smult_zero_iff poly_prod_list prod_list_zero_iff
    using c by auto
  have idr: "(card {x. poly p x = 0} = degree p) = distinct as" unfolding roots pas
    using card_distinct distinct_card by blast
  have id: "\<And> q. (p \<noteq> 0 \<and> q) = q" using p0 by simp
  have dist: "distinct as = (\<forall>a. (\<Sum>x\<leftarrow>as. if x = a then 1 else 0) \<le> Suc 0)" (is "?l = (\<forall> a. ?r a)")
  proof (cases "distinct as")
    case False
    from not_distinct_decomp[OF this] obtain xs ys zs a where "as = xs @ [a] @ ys @ [a] @ zs" by auto
    hence "\<not> ?r a" by auto
    thus ?thesis using False by auto
  next
    case True
    {
      fix a
      from True have "?r a"
      proof (induct as)
        case (Cons b bs)
        show ?case
        proof (cases "a = b")
          case False
          with Cons show ?thesis by auto
        next
          case True
          with Cons(2) have "a \<notin> set bs" by auto
          hence "(\<Sum>x\<leftarrow> bs. if x = a then 1 else 0) = (0 :: nat)" by (induct bs, auto)
          thus ?thesis unfolding True by auto
        qed
      qed simp
    }
    thus ?thesis using True by auto
  qed
  have "rsquarefree p = distinct as" unfolding rsquarefree_def' id unfolding p order_smult[OF c]
    by (subst order_prod_list, auto simp: o_def order_linear' dist)
  thus ?thesis unfolding idr by simp
qed


end
