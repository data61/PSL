(*  Author:     Tobias Nipkow, 2007

A simple certificate checker for q-free linear arithmetic:
is linear combination of atoms and certificate contradictory?
*)

theory CertLin
imports LinArith
begin

declare list_add_assoc [simp]

instantiation atom :: monoid_add
begin

fun plus_atom :: "atom \<Rightarrow> atom \<Rightarrow> atom" where
  "(Eq r\<^sub>1 cs\<^sub>1) + (Eq r\<^sub>2 cs\<^sub>2) = Eq (r\<^sub>1+r\<^sub>2) (cs\<^sub>1+cs\<^sub>2)" |
  "(Eq r\<^sub>1 cs\<^sub>1) + (Less r\<^sub>2 cs\<^sub>2) = Less (r\<^sub>1+r\<^sub>2) (cs\<^sub>1+cs\<^sub>2)" |
  "(Less r\<^sub>1 cs\<^sub>1) + (Eq r\<^sub>2 cs\<^sub>2) = Less (r\<^sub>1+r\<^sub>2) (cs\<^sub>1+cs\<^sub>2)" |
  "(Less r\<^sub>1 cs\<^sub>1) + (Less r\<^sub>2 cs\<^sub>2) = Less (r\<^sub>1+r\<^sub>2) (cs\<^sub>1+cs\<^sub>2)"

definition
  "0 = Eq 0 []"

instance
apply intro_classes
apply(simp_all add: zero_atom_def)
apply(case_tac a)
apply(case_tac b)
apply(case_tac c)
apply simp_all
apply(case_tac c)
apply simp_all
apply(case_tac b)
apply(case_tac c)
apply simp_all
apply(case_tac c)
apply simp_all
apply(case_tac a)
apply simp_all
apply(case_tac a)
apply simp_all
done

end

lemma I_R_additive: "I\<^sub>R a xs \<Longrightarrow> I\<^sub>R b xs \<Longrightarrow> I\<^sub>R(a+b) xs"
apply(case_tac a)
apply(case_tac b)
apply (simp_all add:iprod_left_add_distrib)
apply(case_tac b)
apply (simp_all add:iprod_left_add_distrib)
done

fun mult_atom :: "real \<Rightarrow> atom \<Rightarrow> atom" (infix "*\<^sub>a" 70) where
"c *\<^sub>a Eq r cs = Eq (c*r) (c *\<^sub>s cs)" |
"c *\<^sub>a Less r cs = (if c=0 then Eq 0 [] else Less (c*r) (c *\<^sub>s cs))"

definition iprod_a :: "real list \<Rightarrow> atom list \<Rightarrow> atom" (infix "\<odot>\<^sub>a" 70)
where "cs \<odot>\<^sub>a as = (\<Sum>(c,a) \<leftarrow> zip cs as. c *\<^sub>a a)"

lemma iprod_a_Nil2[simp]: "cs \<odot>\<^sub>a [] = 0"
by(simp add:iprod_a_def)

lemma [simp]: "(c#cs) \<odot>\<^sub>a (a#as) = (c *\<^sub>a a) + cs \<odot>\<^sub>a as"
by(simp add:iprod_a_def)

definition contradict :: "atom list \<Rightarrow> real list \<Rightarrow> bool" where
"contradict as cs \<longleftrightarrow> size cs = size as \<and> (\<forall>c\<in>set cs. c\<ge>0) \<and>
  (case cs \<odot>\<^sub>a as of Eq r cs \<Rightarrow> r \<noteq> 0 \<and> (\<forall>c\<in>set cs. c=0)
                  | Less r cs \<Rightarrow> r \<ge> 0 \<and> (\<forall>c\<in>set cs. c=0))"

definition
"contradict_dnf ass = (\<exists>css. list_all2 contradict ass css)"

lemma refute_I:
  "\<not> Logic.interpret h (Neg f) e \<Longrightarrow> Logic.interpret h f e"
by simp

lemma I_R_mult_atom: "c \<ge> 0 \<Longrightarrow> I\<^sub>R a xs \<Longrightarrow> I\<^sub>R (c *\<^sub>a a) xs"
apply(cases a)
 apply(clarsimp)
apply(simp)
done

lemma I_R_iprod_a:
 "size cs = size as \<Longrightarrow> \<forall>(c,a) \<in> set(zip cs as). I\<^sub>R (c *\<^sub>a a) xs
 \<Longrightarrow> I\<^sub>R (cs \<odot>\<^sub>a as) xs"
apply(induct cs as rule:list_induct2)
 apply (simp add:zero_atom_def)
apply(simp add:I_R_additive)
done

lemma contradictD:
 "contradict as cs \<Longrightarrow> \<exists>a\<in>set as. \<not> I\<^sub>R a xs"
proof -
  assume "contradict as cs"
  have "\<not> I\<^sub>R (cs \<odot>\<^sub>a as) xs"
  proof (cases "cs \<odot>\<^sub>a as")
    case Less thus ?thesis using \<open>contradict as cs\<close>
      by(simp add:contradict_def iprod0_if_coeffs0)
  next
    case Eq thus ?thesis using \<open>contradict as cs\<close>
      by(simp add:contradict_def iprod0_if_coeffs0)
  qed
  thus ?thesis using \<open>contradict as cs\<close>
    by(force simp add:contradict_def intro: I_R_iprod_a I_R_mult_atom
             elim:in_set_zipE)
qed

lemma cyclic_dnfD: "qfree f \<Longrightarrow> contradict_dnf (dnf(R.nnf f)) \<Longrightarrow> \<not>R.I f xs"
apply(subst R.I_nnf[symmetric])
apply(subst R.I_dnf[symmetric])
apply(erule R.nqfree_nnf)
apply(auto simp add:contradict_dnf_def list_all2_iff in_set_conv_nth)
apply(drule_tac x="(dnf(R.nnf f) ! i, css!i)" in bspec)
apply (auto simp:set_zip)
apply(drule_tac xs=xs in contradictD)
apply auto
done

end
