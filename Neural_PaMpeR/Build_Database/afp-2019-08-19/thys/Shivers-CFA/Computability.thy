section \<open>Generic Computability\<close>

theory Computability
imports HOLCF HOLCFUtils
begin

text \<open>
Shivers proves the computability of the abstract semantics functions only by generic and slightly simplified example. This theory contains the abstract treatment in Section 4.4.3. Later, we will work out the details apply this to \<open>\<aPR>\<close>.
\<close>

subsection \<open>Non-branching case\<close>

text \<open>

After the following lemma (which could go into @{theory HOL.Set_Interval}), we show Shivers' Theorem 10. This says that the least fixed point of the equation
\[
f\ x = g\ x \cup f\ (r\ x)
\]
is given by 
\[
f\ x = \bigcup_{i\ge 0} g\ (r^i\ x).
\]

The proof follows the standard proof of showing an equality involving a fixed point: First we show that the right hand side fulfills the above equation and then show that our solution is less than any other solution to that equation.
\<close>

lemma insert_greaterThan:
  "insert (n::nat) {n<..} = {n..}"
by auto

lemma theorem10:
  fixes g :: "'a::cpo \<rightarrow> 'b::type set" and r :: "'a \<rightarrow> 'a"
  shows "fix\<cdot>(\<Lambda> f x. g\<cdot>x \<union> f\<cdot>(r\<cdot>x)) = (\<Lambda> x. (\<Union>i. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x)))"
proof(induct rule:fix_eqI[OF cfun_eqI cfun_belowI, case_names fp least])
case (fp x)
  have "g\<cdot>x \<union> (\<Union>i. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>(r\<cdot>x))) = g\<cdot>(r\<^bsup>0\<^esup>\<cdot>x) \<union> (\<Union>i. g\<cdot>(r\<^bsup>Suc i\<^esup>\<cdot>x))"
    by (simp add: iterate_Suc2 del: iterate_Suc)
  also have "\<dots> = g\<cdot>(r\<^bsup>0\<^esup>\<cdot>x) \<union> (\<Union>i\<in>{0<..}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x))"
    using less_iff_Suc_add by auto
  also have "\<dots>  = (\<Union>i\<in>insert 0 {0<..}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x))"
    by simp
  also have "... = (\<Union>i. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x))"
    by (simp only: insert_greaterThan atLeast_0 )
  finally
  show ?case by auto
next
case (least f x)
  hence expand: "\<And>x. f\<cdot>x = (g\<cdot>x \<union> f\<cdot>(r\<cdot>x))" by (auto simp:cfun_eq_iff)
  { fix n
    have "f\<cdot>x = (\<Union>i\<in>{..n}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x)) \<union> f\<cdot>(r\<^bsup>Suc n\<^esup>\<cdot>x)"
    proof(induct n)
      case 0 thus ?case by (auto simp add:expand[of x])
      case (Suc n)
      then have "f\<cdot>x = (\<Union>i\<in>{..n}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x)) \<union> f\<cdot>(r\<^bsup>Suc n\<^esup>\<cdot>x)" by simp
      also have "\<dots> = (\<Union>i\<in>{..n}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x))
                 \<union> g\<cdot>(r\<^bsup>Suc n\<^esup>\<cdot>x) \<union> f\<cdot>(r\<^bsup>Suc (Suc n)\<^esup>\<cdot>x)"
             by(subst expand[of "r\<^bsup>Suc n\<^esup>\<cdot>x"], auto)
      also have "\<dots> = (\<Union>i\<in>insert (Suc n) {..n}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x)) \<union> f\<cdot>(r\<^bsup>Suc (Suc n)\<^esup>\<cdot>x)"
             by auto
      also have "\<dots> = (\<Union>i\<in>{..Suc n}. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x)) \<union> f\<cdot>(r\<^bsup>Suc (Suc n)\<^esup>\<cdot>x)"
             by (simp add:atMost_Suc)
      finally show ?case .
    qed
  } note fin = this
  have "(\<Union>i. g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x)) \<subseteq> f\<cdot>x"
    proof(rule UN_least)
      fix i
      show "g\<cdot>(r\<^bsup>i\<^esup>\<cdot>x) \<subseteq> f\<cdot>x"
      using fin[of i] by auto
    qed
  thus ?case
    apply (subst sqsubset_is_subset) by auto
qed

subsection \<open>Branching case\<close>

text \<open>
Actually, our functions are more complicated than the one above: The abstract semantics functions recurse with multiple arguments. So we have to handle a recursive equation of the kind
\[
f\ x = g\ x \cup \bigcup_{a \in R\ x} f\ r.
\]
By moving to the power-set relatives of our function, e.g.
\[
{\uline g}Y = \bigcup_{a\in A} g\ a \quad \text{and} {\uline R}Y = \bigcup_{a\in R} R\ a
\]
the equation becomes
\[
{\uline f}Y ={\uline g}Y \cup {\uline f}\ ({\uline R}Y)
\]
(which is shown in Lemma 11) and we can apply Theorem 10 to obtain Theorem 12.

We define the power-set relative for a function together with some properties.
\<close>

definition powerset_lift :: "('a::cpo \<rightarrow> 'b::type set) \<Rightarrow> 'a set \<rightarrow> 'b set" ("\<^ps>")
  where "\<^ps>f = (\<Lambda> S. (\<Union>y\<in>S . f\<cdot>y))"

lemma powerset_lift_singleton[simp]:
  "\<^ps>f\<cdot>{x} = f\<cdot>x"
unfolding powerset_lift_def by simp

lemma powerset_lift_union[simp]:
  "\<^ps>f\<cdot>(A \<union> B) = \<^ps>f\<cdot>A \<union> \<^ps>f\<cdot>B"
unfolding powerset_lift_def by auto

lemma UNION_commute:"(\<Union>x\<in>A. \<Union>y\<in>B . P x y) = (\<Union>y\<in>B. \<Union>x\<in>A . P x y)"
  by auto

lemma powerset_lift_UNION:
  "(\<Union>x\<in>S. \<^ps>g\<cdot>(A x)) = \<^ps>g\<cdot>(\<Union>x\<in>S. A x)"
unfolding powerset_lift_def by auto

lemma powerset_lift_iterate_UNION:
  "(\<Union>x\<in>S. (\<^ps>g)\<^bsup>i\<^esup>\<cdot>(A x)) = (\<^ps>g)\<^bsup>i\<^esup>\<cdot>(\<Union>x\<in>S. A x)"
by (induct i, auto simp add:powerset_lift_UNION)

lemmas powerset_distr = powerset_lift_UNION powerset_lift_iterate_UNION


text \<open>
Lemma 11 shows that if a function satisfies the relation with the branching $R$, its power-set function satisfies the powerset variant of the equation.

\<close>

lemma lemma11:
  fixes f :: "'a \<rightarrow> 'b set" and g :: "'a \<rightarrow> 'b set" and R :: "'a \<rightarrow> 'a set"
  assumes "\<And>x. f\<cdot>x = g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y)"
  shows "\<^ps>f\<cdot>S = \<^ps>g\<cdot>S \<union> \<^ps>f\<cdot>(\<^ps>R\<cdot>S)"
proof-
  have "\<^ps>f\<cdot>S = (\<Union>x\<in>S . f\<cdot>x)" unfolding powerset_lift_def by auto
  also have "\<dots> = (\<Union>x\<in>S . g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y))" apply (subst assms) by simp
  also have "\<dots> = \<^ps>g\<cdot>S \<union> \<^ps>f\<cdot>(\<^ps>R\<cdot>S)" by (auto simp add:powerset_lift_def)
  finally
  show ?thesis .
qed

text \<open>
Theorem 10 as it will be used in Theorem 12.
\<close>
lemmas theorem10ps = theorem10[of "\<^ps>g" "\<^ps>r"] for g r

text \<open>
Now we can show Lemma 12: If $F$ is the least solution to the recursive power-set equation, then $x \mapsto F\ {x}$ is the least solution to the equation with branching $R$.

We fix the type variable \<open>'a\<close> to be a discrete cpo, as otherwise $x \mapsto \{x\}$ is not continuous.
\<close>

(* discrete_cpo, otherwise x \<mapsto> {x} not continous *)
lemma theorem12':
  fixes g :: "'a::discrete_cpo \<rightarrow> 'b::type set" and R :: "'a \<rightarrow> 'a set"
  assumes F_fix: "F = fix\<cdot>(\<Lambda> F x. \<^ps>g\<cdot>x \<union> F\<cdot>(\<^ps>R\<cdot>x))"
  shows "fix\<cdot>(\<Lambda> f x. g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y)) = (\<Lambda> x. F\<cdot>{x})"
proof(induct rule:fix_eqI[OF cfun_eqI cfun_belowI, case_names fp least])
have F_union: "F = (\<Lambda> x. \<Union>i. \<^ps>g\<cdot>((\<^ps>R)\<^bsup>i\<^esup>\<cdot>x))"
  using F_fix by(simp)(rule theorem10ps)
case (fp x)
   have "g\<cdot>x \<union> (\<Union>x'\<in>R\<cdot>x. F\<cdot>{x'}) = \<^ps>g\<cdot>{x} \<union> F\<cdot>(\<^ps>R\<cdot>{x})"
    unfolding powerset_lift_singleton
    by (auto simp add: powerset_distr UNION_commute F_union)
  also have "\<dots> = F\<cdot>{x}"
    by (subst (2) fix_eq4[OF F_fix], auto)
  finally show ?case by simp
next
case (least f' x)
  hence expand: "f' = (\<Lambda> x. g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f'\<cdot>y))" by simp
  have "\<^ps>f' = (\<Lambda> S. \<^ps>g\<cdot>S \<union> \<^ps>f'\<cdot>(\<^ps>R\<cdot>S))"
    by (subst expand, rule cfun_eqI, auto simp add:powerset_lift_def)
  hence "(\<Lambda> F. \<Lambda> x. \<^ps>g\<cdot>x \<union> F\<cdot>(\<^ps>R\<cdot>x))\<cdot>(\<^ps>f') = \<^ps>f'" by simp
  from fix_least[OF this] and F_fix
  have  "F \<sqsubseteq> \<^ps>f'"  by simp
  hence  "F\<cdot>{x} \<sqsubseteq> \<^ps>f'\<cdot>{x}"
    by (subst (asm)cfun_below_iff, auto simp del:powerset_lift_singleton)
  thus ?case by (auto simp add:sqsubset_is_subset)
qed

lemma theorem12:
  fixes g :: "'a::discrete_cpo \<rightarrow> 'b::type set" and R :: "'a \<rightarrow> 'a set"
  shows "fix\<cdot>(\<Lambda> f x. g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y))\<cdot>x =  \<^ps>g\<cdot>(\<Union>i.((\<^ps>R)\<^bsup>i\<^esup>\<cdot>{x}))"
  by(subst theorem12'[OF theorem10ps[THEN sym]], auto simp add:powerset_distr)

end
