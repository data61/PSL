theory Left_Coset
imports
  "HOL-Algebra.Coset"

begin

definition
  LCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"   ("lcosets\<index> _" [81] 80)
  where "lcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {a <#\<^bsub>G\<^esub> H})"

definition
  LFactGroup :: "[('a,'b) monoid_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl "LMod" 65)
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
   where "LFactGroup G H = \<lparr>carrier = lcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H\<rparr>"

lemma (in group) lcos_self: "[| x \<in> carrier G; subgroup H G |] ==> x \<in> x <# H"
apply (simp add: l_coset_def)
apply (blast intro: sym r_one subgroup.subset [THEN subsetD]
                    subgroup.one_closed)
done

text \<open>Elements of a left coset are in the carrier\<close>
lemma (in subgroup) elemlcos_carrier:
  assumes "group G"
  assumes acarr: "a \<in> carrier G"
    and a': "a' \<in> a <# H"
  shows "a' \<in> carrier G"
proof -
  interpret group G by fact
  from subset and acarr
  have "a <# H \<subseteq> carrier G" by (rule l_coset_subset_G)
  from this and a'
  show "a' \<in> carrier G"
    by fast
qed

text \<open>Step one for lemma \<open>rcos_module\<close>\<close>
lemma (in subgroup) lcos_module_imp:
  assumes "group G"
  assumes xcarr: "x \<in> carrier G"
      and x'cos: "x' \<in> x <# H"
  shows "(inv x \<otimes> x') \<in> H"
proof -
  interpret group G by fact
  from xcarr x'cos
      have x'carr: "x' \<in> carrier G"
      by (rule elemlcos_carrier[OF is_group])
  from xcarr
      have ixcarr: "inv x \<in> carrier G"
      by simp
  from x'cos
      have "\<exists>h\<in>H. x' = x \<otimes> h"
      unfolding l_coset_def
      by fast
  from this
      obtain h
        where hH: "h \<in> H"
        and x': "x' = x \<otimes> h"
      by auto
  from hH and subset
      have hcarr: "h \<in> carrier G" by fast
  note carr = xcarr x'carr hcarr
  from x' and carr
      have "(inv x) \<otimes> x' = (inv x) \<otimes> (x \<otimes> h)" by fast
  also from carr
      have "\<dots> = (x \<otimes> inv x) \<otimes> h" by (metis ixcarr l_inv m_assoc r_inv)
  also from carr
      have "\<dots> = h \<otimes> \<one>" by simp
  also from carr
      have "\<dots> = h" by simp
  finally
      have "(inv x) \<otimes> x' = h" by simp
  from hH this
      show "(inv x) \<otimes> x' \<in> H" by simp
qed

text \<open>Left cosets are subsets of the carrier.\<close> 
lemma (in subgroup) lcosets_carrier:
  assumes "group G"
  assumes XH: "X \<in> lcosets H"
  shows "X \<subseteq> carrier G"
proof -
  interpret group G by fact
  from XH have "\<exists>x\<in> carrier G. X = x <# H"
      unfolding LCOSETS_def
      by fast
  from this
      obtain x
        where xcarr: "x\<in> carrier G"
        and X: "X = x <# H"
      by fast
  from subset and xcarr
      show "X \<subseteq> carrier G"
      unfolding X
      by (rule l_coset_subset_G)
qed

lemma (in group) lcosets_part_G:
  assumes "subgroup H G"
  shows "\<Union>(lcosets H) = carrier G"
proof -
  interpret subgroup H G by fact
  show ?thesis
    apply (rule equalityI)
    apply (force simp add: LCOSETS_def l_coset_def)
    apply (auto simp add: LCOSETS_def intro: lcos_self assms)
    done
qed

lemma (in group) lcosets_subset_PowG:
     "subgroup H G  \<Longrightarrow> lcosets H \<subseteq> Pow(carrier G)"
apply (simp add: LCOSETS_def)
apply (blast dest: l_coset_subset_G subgroup.subset)
done

lemma (in group) lcos_disjoint:
  assumes "subgroup H G"
  assumes p: "a \<in> lcosets H" "b \<in> lcosets H" "a\<noteq>b"
  shows "a \<inter> b = {}"
proof -
  interpret subgroup H G by fact
  from p show ?thesis
    apply (simp add: LCOSETS_def)
    apply (metis inf.cobounded1 inf.cobounded2 l_repr_independence subgroup_axioms subset_empty subset_iff)
    done
qed

text\<open>The next two lemmas support the proof of \<open>card_cosets_equal\<close>.\<close>
lemma (in group) inj_on_f':
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> inv a) (a <# H)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G & y \<in> carrier G")
 prefer 2 apply (blast intro: l_coset_subset_G [THEN subsetD])
apply (simp add: subsetD)
done

lemma (in group) inj_on_f'':
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. inv a \<otimes> y) (a <# H)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G & y \<in> carrier G")
 prefer 2 apply (blast intro: l_coset_subset_G [THEN subsetD])
apply (simp add: subsetD)
done

lemma (in group) inj_on_g':
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. a \<otimes> y) H"
by (force simp add: inj_on_def subsetD)

lemma (in group) l_card_cosets_equal:
     "\<lbrakk>c \<in> lcosets H;  H \<subseteq> carrier G; finite(carrier G)\<rbrakk>
      \<Longrightarrow> card H = card c"
apply (auto simp add: LCOSETS_def)
apply (rule card_bij_eq)
     apply (rule inj_on_g', assumption+)
    apply (force simp add: m_assoc subsetD l_coset_def)
   apply (rule inj_on_f'', assumption+)
proof
  fix a x
  assume "H \<subseteq> carrier G" and "finite (carrier G)" and "a \<in> carrier G" and "c = a <# H"
  assume a:"x \<in> (\<otimes>) (inv a) ` (a <# H)"
  have "a \<otimes> inv a = \<one>" by (simp add: \<open>a \<in> carrier G\<close>) 
  from a have "x \<in> {y. \<exists>x\<in>\<Union>h\<in>H. {a \<otimes> h}. y = inv a \<otimes> x}" unfolding l_coset_def image_def by simp
  then have "(\<exists>x'\<in>\<Union>h\<in>H. {a \<otimes> h}. x = inv a \<otimes> x')" by blast  
  then show "x \<in> H" 
    using \<open>H \<subseteq> carrier G\<close> \<open>a \<in> carrier G\<close> is_group
    by clarify (metis inv_solve_left m_closed subsetD)
next
  show "\<And>a. H \<subseteq> carrier G \<Longrightarrow> finite (carrier G) \<Longrightarrow> a \<in> carrier G \<Longrightarrow> c = a <# H \<Longrightarrow> finite H"
  using rev_finite_subset by blast
next
  show "\<And>a. H \<subseteq> carrier G \<Longrightarrow> finite (carrier G) \<Longrightarrow> a \<in> carrier G \<Longrightarrow> c = a <# H \<Longrightarrow> finite (a <# H)"
    by (simp add: l_coset_subset_G rev_finite_subset)
qed

theorem (in group) l_lagrange:
     "\<lbrakk>finite(carrier G); subgroup H G\<rbrakk>
      \<Longrightarrow> card(lcosets H) * card(H) = order(G)"
apply (simp (no_asm_simp) add: order_def lcosets_part_G [symmetric])
apply (subst mult.commute)
apply (rule card_partition)
   apply (simp add: lcosets_subset_PowG [THEN finite_subset])
  apply (simp add: lcosets_part_G)
 apply (simp add: l_card_cosets_equal subgroup.subset)
apply (simp add: lcos_disjoint)
done

end
