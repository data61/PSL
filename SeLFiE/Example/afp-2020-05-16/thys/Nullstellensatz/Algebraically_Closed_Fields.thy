(* Author: Alexander Maletzky *)

section \<open>Algebraically Closed Fields\<close>

theory Algebraically_Closed_Fields
  imports "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

lemma prod_eq_zeroE:
  assumes "prod f I = (0::'a::{semiring_no_zero_divisors,comm_monoid_mult,zero_neq_one})"
  obtains i where "finite I" and "i \<in> I" and "f i = 0"
proof -
  have "finite I"
  proof (rule ccontr)
    assume "infinite I"
    with assms show False by simp
  qed
  moreover from this assms obtain i where "i \<in> I" and "f i = 0"
  proof (induct I arbitrary: thesis)
    case empty
    from empty(2) show ?case by simp
  next
    case (insert j I)
    from insert.hyps(1, 2) have "f j * prod f I = prod f (insert j I)" by simp
    also have "\<dots> = 0" by fact
    finally have "f j = 0 \<or> prod f I = 0" by simp
    thus ?case
    proof
      assume "f j = 0"
      with _ show ?thesis by (rule insert.prems) simp
    next
      assume "prod f I = 0"
      then obtain i where "i \<in> I" and "f i = 0" using insert.hyps(3) by blast
      from _ this(2) show ?thesis by (rule insert.prems) (simp add: \<open>i \<in> I\<close>)
    qed
  qed
  ultimately show ?thesis ..
qed

lemma degree_prod_eq:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> f i \<noteq> 0"
  shows "Polynomial.degree (prod f I :: _::semiring_no_zero_divisors poly) = (\<Sum>i\<in>I. Polynomial.degree (f i))"
  using assms
proof (induct I)
  case empty
  show ?case by simp
next
  case (insert j J)
  have 1: "f i \<noteq> 0" if "i \<in> J" for i
  proof (rule insert.prems)
    from that show "i \<in> insert j J" by simp
  qed
  hence eq: "Polynomial.degree (prod f J) = (\<Sum>i\<in>J. Polynomial.degree (f i))" by (rule insert.hyps)
  from insert.hyps(1, 2) have "Polynomial.degree (prod f (insert j J)) = Polynomial.degree (f j * prod f J)"
    by simp
  also have "\<dots> = Polynomial.degree (f j) + Polynomial.degree (prod f J)"
  proof (rule degree_mult_eq)
    show "f j \<noteq> 0" by (rule insert.prems) simp
  next
    show "prod f J \<noteq> 0"
    proof
      assume "prod f J = 0"
      then obtain i where "i \<in> J" and "f i = 0" by (rule prod_eq_zeroE)
      from this(1) have "f i \<noteq> 0" by (rule 1)
      thus False using \<open>f i = 0\<close> ..
    qed
  qed
  also from insert.hyps(1, 2) have "\<dots> = (\<Sum>i\<in>insert j J. Polynomial.degree (f i))" by (simp add: eq)
  finally show ?case .
qed

class alg_closed_field =
  assumes alg_closed_field_axiom: "\<And>p::'a::field poly. 0 < Polynomial.degree p \<Longrightarrow> \<exists>z. poly p z = 0"
begin

lemma rootE:
  assumes "0 < Polynomial.degree p"
  obtains z where "poly p z = (0::'a)"
proof -
  from assms have "\<exists>z. poly p z = 0" by (rule alg_closed_field_axiom)
  then obtain z where "poly p z = 0" ..
  thus ?thesis ..
qed

lemma infinite_UNIV: "infinite (UNIV::'a set)"
proof
  assume fin: "finite (UNIV::'a set)"
  define p where "p = (\<Prod>a\<in>UNIV. [:- a, 1::'a:]) + [:-1:]"
  have "Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:]) = (\<Sum>a\<in>UNIV. Polynomial.degree [:- a, 1::'a:])"
    using fin by (rule degree_prod_eq) simp
  also have "\<dots> = (\<Sum>a\<in>(UNIV::'a set). 1)" by simp
  also have "\<dots> = card (UNIV::'a set)" by simp
  also from fin have "\<dots> > 0" by (rule finite_UNIV_card_ge_0)
  finally have "0 < Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" .
  hence "Polynomial.degree [:-1:] < Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" by simp
  hence "Polynomial.degree p = Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" unfolding p_def
    by (rule degree_add_eq_left)
  also have "\<dots> > 0" by fact
  finally have "0 < Polynomial.degree p" .
  then obtain z where "poly p z = 0" by (rule rootE)
  hence "(\<Prod>a\<in>UNIV. (z - a)) = 1" by (simp add: p_def poly_prod)
  thus False by (metis UNIV_I cancel_comm_monoid_add_class.diff_cancel fin one_neq_zero prod_zero_iff)
qed

lemma linear_factorsE:
  fixes p :: "'a poly"
  obtains c A m where "finite A" and "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and "\<And>a. m a = 0 \<longleftrightarrow> a \<notin> A" and "c = 0 \<longleftrightarrow> p = 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)"
proof -
  obtain c A m where fin: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and *: "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A"
  proof (induct p arbitrary: thesis rule: poly_root_induct[where P="\<lambda>_. True"])
    case 0
    show ?case
    proof (rule 0)
      show "0 = Polynomial.smult 0 (\<Prod>a\<in>{}. [:- a, 1:] ^ (\<lambda>_. 0) a)" by simp
    qed simp_all
  next
    case (no_roots p)
    have "Polynomial.degree p = 0"
    proof (rule ccontr)
      assume "Polynomial.degree p \<noteq> 0"
      hence "0 < Polynomial.degree p" by simp
      then obtain z where "poly p z = 0" by (rule rootE)
      moreover have "poly p z \<noteq> 0" by (rule no_roots) blast
      ultimately show False by simp
    qed
    then obtain c where p: "p = [:c:]" by (rule degree_eq_zeroE)
    show ?case
    proof (rule no_roots)
      show "p = Polynomial.smult c (\<Prod>a\<in>{}. [:- a, 1:] ^ (\<lambda>_. 0) a)" by (simp add: p)
    qed simp_all
  next
    case (root a p)
    obtain A c m where 1: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
      and 2: "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" by (rule root.hyps) blast
    define m' where "m' = (\<lambda>x. if x = a then Suc (m x) else m x)"
    show ?case
    proof (rule root.prems)
      from 1 show "finite (insert a A)" by simp
    next
      have "[:a, - 1:] * p = [:- a, 1:] * (- p)" by simp
      also have "\<dots> = [:- a, 1:] * (Polynomial.smult (- c) (\<Prod>a\<in>A. [:- a, 1:] ^ m a))"
        by (simp add: p)
      also have "\<dots> = Polynomial.smult (- c) ([:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a))"
        by (simp only: mult_smult_right ac_simps)
      also have "[:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a) = (\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a)"
      proof (cases "a \<in> A")
        case True
        with 1 have "(\<Prod>a\<in>A. [:- a, 1:] ^ m a) = [:- a, 1:] ^ m a * (\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m a)"
          by (simp add: prod.remove)
        also from refl have "(\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m a) = (\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m' a)"
          by (rule prod.cong) (simp add: m'_def)
        finally have "[:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a) =
                          ([:- a, 1:] * [:- a, 1:] ^ m a) * (\<Prod>a\<in>A - {a}. [:- a, 1:] ^ m' a)"
          by (simp only: mult.assoc)
        also have "[:- a, 1:] * [:- a, 1:] ^ m a = [:- a, 1:] ^ m' a" by (simp add: m'_def)
        finally show ?thesis using 1 by (simp add: prod.insert_remove)
      next
        case False
        with 1 have "(\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a) = [:- a, 1:] ^ m' a * (\<Prod>a\<in>A. [:- a, 1:] ^ m' a)"
          by simp
        also from refl have "(\<Prod>a\<in>A. [:- a, 1:] ^ m' a) = (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
        proof (rule prod.cong)
          fix x
          assume "x \<in> A"
          with False have "x \<noteq> a" by blast
          thus "[:- x, 1:] ^ m' x = [:- x, 1:] ^ m x" by (simp add: m'_def)
        qed
        finally have "(\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a) = [:- a, 1:] ^ m' a * (\<Prod>a\<in>A. [:- a, 1:] ^ m a)" .
        also from False have "m' a = 1" by (simp add: m'_def 2)
        finally show ?thesis by simp
      qed
      finally show "[:a, - 1:] * p = Polynomial.smult (- c) (\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a)" .
    next
      fix x
      show "m' x = 0 \<longleftrightarrow> x \<notin> insert a A" by (simp add: m'_def 2)
    qed
  qed
  moreover have "c = 0 \<longleftrightarrow> p = 0"
  proof
    assume "p = 0"
    hence "[:c:] = 0 \<or> (\<Prod>a\<in>A. [:- a, 1:] ^ m a) = 0" by (simp add: p)
    thus "c = 0"
    proof
      assume "[:c:] = 0"
      thus ?thesis by simp
    next
      assume "(\<Prod>a\<in>A. [:- a, 1:] ^ m a) = 0"
      then obtain a where "[:- a, 1:] ^ m a = 0" by (rule prod_eq_zeroE)
      thus ?thesis by simp
    qed
  qed (simp add: p)
  moreover {
    fix z
    have "0 < m z" if "z \<in> A" by (rule ccontr) (simp add: * that)
    hence "poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)" by (auto simp: p poly_prod * fin elim: prod_eq_zeroE)
  }
  ultimately show ?thesis ..
qed

end (* alg_closed_field *)

instance complex :: alg_closed_field
  by standard (rule fundamental_theorem_of_algebra, simp add: constant_degree)

end (* theory *)
