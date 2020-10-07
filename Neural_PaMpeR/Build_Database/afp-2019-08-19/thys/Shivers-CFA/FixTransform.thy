section \<open>Fixed point transformations\<close>

theory FixTransform
imports HOLCF
begin

default_sort type

text \<open>
In his treatment of the computabily, Shivers gives proofs only for a generic example and leaves it to the reader to apply this to the mutually recursive functions used for the semantics. As we carry this out, we need to transform a fixed point for two functions (implemented in @{theory HOLCF} as a fixed point over a tuple) to a simple fixed point equation. The approach here works as long as both functions in the tuple have the same return type, using the equation
\[
X^A\cdot X^B = X^{A+B}.
\]

Generally, a fixed point can be transformed using any retractable continuous function:
\<close>

lemma fix_transform:
  assumes "\<And>x. g\<cdot>(f\<cdot>x)=x"
  shows "fix\<cdot>F = g\<cdot>(fix\<cdot>(f oo F oo g))"
using assms apply -
apply (rule parallel_fix_ind)
apply (rule adm_eq)
apply auto
apply (erule retraction_strict[of g f,rule_format])
done

text \<open>
The functions we use here convert a tuple of functions to a function taking a direct sum as parameters and back. We only care about discrete arguments here.
\<close>

definition tup_to_sum :: "('a discr \<rightarrow> 'c) \<times> ('b discr \<rightarrow> 'c) \<rightarrow> ('a + 'b) discr \<rightarrow> 'c::cpo"
 where "tup_to_sum = (\<Lambda> p s. (\<lambda>(f,g).
          case undiscr s of Inl x \<Rightarrow> f\<cdot>(Discr x)
                          | Inr x \<Rightarrow> g\<cdot>(Discr x)) p)"

definition sum_to_tup :: "(('a + 'b) discr \<rightarrow> 'c) \<rightarrow> ('a discr \<rightarrow> 'c) \<times> ('b discr \<rightarrow> 'c::cpo)"
 where "sum_to_tup = (\<Lambda> f. (\<Lambda> x. f\<cdot>(Discr (Inl (undiscr x))),
                             \<Lambda> x. f\<cdot>(Discr (Inr (undiscr x)))))"

text \<open>
As so often when working with @{theory HOLCF}, some continuity lemmas are required.
\<close>

lemma cont2cont_case_sum[simp,cont2cont]:
  assumes "cont f" and "cont g"
  shows "cont (\<lambda>x. case_sum (f x) (g x) s)"
using assms
by (cases s, auto intro:cont2cont_fun)

lemma cont2cont_circ[simp,cont2cont]:
 "cont (\<lambda>f. f \<circ> g)"
apply (rule cont2cont_lambda)
apply (subst comp_def)
apply (rule  cont2cont_fun[of "\<lambda>x. x", OF "cont_id"])
done

lemma cont2cont_split_pair[cont2cont,simp]:
 assumes f1: "cont f"
     and f2: "\<And> x. cont (f x)"
     and g1: "cont g"
     and g2: "\<And> x. cont (g x)"
 shows "cont (\<lambda>(a, b). (f a b, g a b))"
apply (intro cont2cont)
apply (rule cont_apply[OF cont_snd _ cont_const])
apply (rule cont_apply[OF cont_snd f2])
apply (rule cont_apply[OF cont_fst cont2cont_fun[OF f1] cont_const])

apply (rule cont_apply[OF cont_snd _ cont_const])
apply (rule cont_apply[OF cont_snd g2])
apply (rule cont_apply[OF cont_fst cont2cont_fun[OF g1] cont_const])
done

text \<open>
Using these continuity lemmas, we can show that our function are actually continuous and thus allow us to apply them to a value.
\<close>

lemma sum_to_tup_app:
 "sum_to_tup\<cdot>f = (\<Lambda> x. f\<cdot>(Discr (Inl (undiscr x))), \<Lambda> x. f\<cdot>(Discr (Inr (undiscr x))))"
unfolding sum_to_tup_def by simp

lemma tup_to_sum_app:
  "tup_to_sum\<cdot>p = (\<Lambda> s. (\<lambda>(f,g).
          case undiscr s of Inl x \<Rightarrow> f\<cdot>(Discr x)
                          | Inr x \<Rightarrow> g\<cdot>(Discr x)) p)"
unfolding tup_to_sum_def by simp

text \<open>
Generally, lambda abstractions with discrete domain are continous and can be resolved immediately.
\<close>

lemma discr_app[simp]:
  "(\<Lambda> s. f s)\<cdot>(Discr x) = f (Discr x)"
by simp

text \<open>
Our transformation functions are inverse to each other, so we can use them to transform a fixed point.
\<close>

lemma tup_to_sum_to_tup[simp]:
  shows   "sum_to_tup\<cdot>(tup_to_sum\<cdot>F) = F"
unfolding sum_to_tup_app and tup_to_sum_app
by (cases F, auto intro:cfun_eqI)

lemma fix_transform_pair_sum:
  shows "fix\<cdot>F = sum_to_tup\<cdot>(fix\<cdot>(tup_to_sum oo F oo sum_to_tup))"
by (rule fix_transform[OF tup_to_sum_to_tup])

text \<open>
After such a transformation, we want to get rid of these helper functions again. This is done by the next two simplification lemmas.
\<close>

lemma tup_sum_oo[simp]:
 assumes f1: "cont F"
     and f2: "\<And> x. cont (F x)"
     and g1: "cont G"
     and g2: "\<And> x. cont (G x)"
shows  "tup_to_sum oo (\<Lambda> p. (\<lambda>(a, b). (F a b, G a b)) p) oo sum_to_tup
  = (\<Lambda> f s. (case undiscr s of
        Inl x \<Rightarrow>
          F (\<Lambda> s. f\<cdot>(Discr (Inl (undiscr s))))
           (\<Lambda> s. f\<cdot>(Discr (Inr (undiscr s))))\<cdot>
          (Discr x)
        | Inr x \<Rightarrow>
            G (\<Lambda> s. f\<cdot>(Discr (Inl (undiscr s))))
             (\<Lambda> s. f\<cdot>(Discr (Inr (undiscr s))))\<cdot>
            (Discr x)))"
by (rule cfun_eqI, rule cfun_eqI,
    simp add: sum_to_tup_app tup_to_sum_app
       cont2cont_split_pair[OF f1 f2 g1 g2]
       cont2cont_lambda
       cont_apply[OF _ f2 cont2cont_fun[OF cont_compose[OF f1]]]
       cont_apply[OF _ g2 cont2cont_fun[OF cont_compose[OF g1]]])

lemma fst_sum_to_tup[simp]:
  "fst (sum_to_tup\<cdot>x) = (\<Lambda> xa. x\<cdot>(Discr (Inl (undiscr xa))))"
by (simp add: sum_to_tup_app)

end
