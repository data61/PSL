(* Title:      Regular Algebras
   Author:     Simon Foster, Georg Struth
   Maintainer: Simon Foster <s.foster at york.ac.uk>
               Georg Struth <g.struth at sheffield.ac.uk>               
*)

section \<open>Models of Regular Algebra\<close>

theory Regular_Algebra_Models
  imports Regular_Algebras Kleene_Algebra.Kleene_Algebra_Models
begin

subsection \<open>Language Model of Salomaa Algebra\<close>

abbreviation w_length :: "'a list \<Rightarrow> nat" ( "|_|")
  where "|x| \<equiv> length x"

definition l_ewp :: "'a lan \<Rightarrow> bool" where
  "l_ewp X \<longleftrightarrow> {[]} \<subseteq> X"

interpretation lan_kozen: K2_algebra "(+)" "(\<cdot>)" "1 :: 'a lan" 0 "(\<subseteq>)" "(\<subset>)" "star" ..

interpretation lan_boffa: B1_algebra "(+)" "(\<cdot>)" "1 :: 'a lan" 0 "(\<subseteq>)" "(\<subset>)" "star" ..

lemma length_lang_pow_lb:
  assumes "\<forall>x\<in>X. |x| \<ge> k" "x \<in> X^n" 
  shows "|x| \<ge> k*n"
using assms proof (induct n arbitrary: x)
  case 0 thus ?case by auto
next
  case (Suc n) 
  note hyp = this
  thus ?case
  proof -
    have "x \<in> X\<^bsup>Suc n\<^esup> \<longleftrightarrow> (\<exists> y z. x = y@z \<and> y \<in> X \<and> z \<in> X\<^bsup>n\<^esup>)"
      by (simp add:c_prod_def times_list_def)
    also from hyp have "... \<longrightarrow> (\<exists> y z. x = y@z \<and> |y| \<ge> k \<and> |z| \<ge> k*n)"
      by auto
    also have "... \<longleftrightarrow> (\<exists> y z. x = y@z \<and> |y| \<ge> k \<and> |z| \<ge> k*n \<and> ( |x| = |y| + |z| ))"
      by force
    also have "... \<longleftrightarrow> (\<exists> y z. x = y@z \<and> |y| \<ge> k \<and> |z| \<ge> k*n \<and> ( |x| \<ge> (n + 1) * k ))"
      by (auto, metis add_mono mult.commute, force)
    finally show ?thesis
      by (metis Suc_eq_plus1 hyp(3) mult.commute)
  qed
qed

lemma l_prod_elim: "w\<in>X \<cdot> Y \<longleftrightarrow> (\<exists>u v. w = u@v \<and> u\<in>X \<and> v\<in>Y)"
  by (simp add: c_prod_def times_list_def)

lemma power_minor_var: 
  assumes "\<forall>w\<in>X. k\<le>|w|"
  shows "\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n*k\<le>|w|"
  using assms
  apply (auto simp add: l_prod_elim)
  using length_lang_pow_lb trans_le_add2
  by (simp add: length_lang_pow_lb trans_le_add2 mult.commute)
 
lemma power_lb: "(\<forall>w\<in>X. k\<le>|w| ) \<longrightarrow> (\<forall>w. w\<in>X\<^bsup>Suc n\<^esup> \<longrightarrow> n*k\<le>|w| )"
  by (metis power_minor_var)

lemma prod_lb: 
  "\<lbrakk> (\<forall>w\<in>X. m \<le> length w); (\<forall>w\<in>Y. n \<le> length w) \<rbrakk> \<Longrightarrow> (\<forall>w\<in>(X\<cdot>Y). (m+n) \<le> length w)"
  by (metis l_prod_elim add_le_mono length_append) 

lemma suicide_aux_l: 
  "\<lbrakk> (\<forall>w\<in>Y. 0\<le>length w); (\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n \<le> length w) \<rbrakk> \<Longrightarrow> (\<forall>w\<in>X\<^bsup>Suc n \<^esup>\<cdot> Y. n \<le> length w)"
  apply (auto simp: l_prod_elim)
  apply (drule_tac x="ua @ va" in bspec)
  apply (auto simp add: l_prod_elim)
done

lemma suicide_aux_r: 
  "\<lbrakk> (\<forall>w\<in>Y. 0\<le>length w); (\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n \<le> length w) \<rbrakk> \<Longrightarrow> (\<forall>w\<in>Y \<cdot> X\<^bsup>Suc n\<^esup>. n \<le> length w)"
  by (auto, metis (full_types) le0 plus_nat.add_0 prod_lb)

lemma word_suicide_l: 
  assumes "\<not> l_ewp X" "Y \<noteq> {}"  
  shows "(\<forall>w\<in>Y. \<exists>n. w\<notin>X\<^bsup>Suc n \<^esup>\<cdot> Y)"
proof -
  have  "\<forall>v\<in>Y. 0\<le>length v" 
    by (metis le0)
  from assms have "\<forall>v\<in>X. 1\<le>length v"
    by (simp add: l_ewp_def, metis le_0_eq length_0_conv not_less_eq_eq)
  hence "\<forall>w\<in>Y. \<exists>n. w\<notin>X\<^bsup>Suc n \<^esup>\<cdot> Y"
    by (metis nat_mult_1_right power_lb suicide_aux_l le0 Suc_n_not_le_n)
  thus ?thesis by metis
qed 

lemma word_suicide_r: 
  assumes "\<not> l_ewp X" "Y \<noteq> {}"  
  shows "(\<forall>w\<in>Y. \<exists>n. w\<notin>Y \<cdot> X\<^bsup>Suc n\<^esup>)"
proof -
  have  "\<forall>v\<in>Y. 0\<le>length v" 
    by (metis le0)
  from assms have "\<forall>v\<in>X. 1\<le>length v"
    by (simp add: l_ewp_def, metis le_0_eq length_0_conv not_less_eq_eq)
  hence "\<forall>w\<in>Y. \<exists>n. w\<notin>Y \<cdot> X\<^bsup>Suc n \<^esup>"
    by (metis nat_mult_1_right power_lb suicide_aux_r le0 Suc_n_not_le_n)
  thus ?thesis by metis
qed 

lemma word_suicide_lang_l: "\<lbrakk> \<not> l_ewp X; Y \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists> n. \<not> (Y \<le> X\<^bsup>Suc n \<^esup>\<cdot> Y)"
  by (metis Set.set_eqI empty_iff in_mono word_suicide_l)

lemma word_suicide_lang_r: "\<lbrakk> \<not> l_ewp X; Y \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists> n. \<not> (Y \<le> Y \<cdot> X\<^bsup>Suc n\<^esup>)"
  by (metis Set.set_eqI empty_iff in_mono word_suicide_r)

text \<open>These duality results cannot be relocated easily\<close>

context K1_algebra
begin

lemma power_dual_transfer [simp]: 
  "power.power (1::'a) (\<odot>) x n = x\<^bsup>n\<^esup>"
  by (induct n, simp_all, metis opp_mult_def power_commutes)

lemma aarden_aux_l:
  "y \<le> x \<cdot> y + z \<Longrightarrow> y \<le>  x\<^bsup>Suc n\<^esup> \<cdot> y + x\<^sup>\<star> \<cdot> z"
  using dual.aarden_aux[of "y" "x" "z" "n"]
  by (auto simp add:opp_mult_def)

end

lemma arden_l: 
  assumes "\<not> l_ewp y" "x = y\<cdot>x + z" 
  shows "x = y\<^sup>\<star> \<cdot> z"
proof (rule antisym)
  show one: "y\<^sup>\<star> \<cdot> z \<le> x"
    by (metis assms(2) join_semilattice_class.add_comm left_near_kleene_algebra_class.star_inductl_eq)
  show "x \<le> y\<^sup>\<star> \<cdot> z"
  proof (cases "x = 0")
    show "x = 0 \<Longrightarrow> x \<le> y\<^sup>\<star>\<cdot>z"  
      by simp
    assume assms': "x \<noteq> 0"
    have "\<And> n. x \<le> y\<^bsup>Suc n \<^esup>\<cdot> x + y\<^sup>\<star> \<cdot> z"
      by (metis assms(2) kleene_algebra_class.aarden_aux_l subsetI)
    moreover then have "\<And> w n. w \<in> x \<Longrightarrow> w \<in> y\<^bsup>Suc n \<^esup>\<cdot> x \<or> w \<in> y\<^sup>\<star> \<cdot> z"
      by (force simp: plus_set_def)
    ultimately show "x \<le> y\<^sup>\<star> \<cdot> z"
      by (metis (full_types) all_not_in_conv assms(1) subsetI word_suicide_l)
  qed
qed

lemma arden_r: 
  assumes "\<not> l_ewp y" "x = x \<cdot> y + z" 
  shows "x = z \<cdot> y\<^sup>\<star>"
proof (rule antisym)
  show one: "z \<cdot> y\<^sup>\<star> \<le> x"
    by (metis assms(2) join.sup_commute kleene_algebra_class.star_inductr_var order_refl)
  show "x \<le> z \<cdot> y\<^sup>\<star>"
  proof (cases "x = 0")
    show "x = 0 \<Longrightarrow> x \<le> z \<cdot> y\<^sup>\<star>"  
      by simp
    assume assms': "x \<noteq> 0"
    have "\<And> n. x \<le> x \<cdot> y\<^bsup>Suc n\<^esup> + z \<cdot> y\<^sup>\<star>"
      by (metis assms(2) kleene_algebra_class.aarden_aux subsetI)
    moreover then have "\<And> w n. w \<in> x \<Longrightarrow> w \<in> x \<cdot> y\<^bsup>Suc n\<^esup> \<or> w \<in> z \<cdot> y\<^sup>\<star>"
      by (force simp: plus_set_def)
    ultimately show "x \<le> z \<cdot> y\<^sup>\<star>"
      by (metis (full_types) all_not_in_conv assms(1) subsetI word_suicide_r)
  qed
qed

text \<open>The following two facts provide counterexamples to Arden's rule if the empty word property is not considered.\<close>

lemma arden_l_counter: "\<exists> (x::'a lan) (y::'a lan) (z::'a lan). x = y \<cdot> x + z \<and> x \<noteq> y\<^sup>\<star> \<cdot> z"
proof -
  have one: "(0::'a lan) + 1 \<cdot> 1 = 1"
    by (metis ab_near_semiring_one_class.mult_onel kleene_algebra_class.dual.add_zerol)
  have two: "(1::'a lan) \<noteq> 1\<^sup>\<star> \<cdot> 0"
  proof -
    have "\<exists>x\<^sub>1. (0::'a list set) \<noteq> x\<^sub>1"
      by auto
    hence "(1::'a list set) \<noteq> 0"
      by (metis kleene_algebra_class.dual.annir kleene_algebra_class.dual.mult.right_neutral)
    thus "(1::'a list set) \<noteq> 1\<^sup>\<star> \<cdot> 0"
      by simp
  qed
  show ?thesis using one and two
    by (metis kleene_algebra_class.dual.add_zerol kleene_algebra_class.dual.add_zeror)
qed

lemma arden_r_counter: "\<exists> (x::'a lan) (y::'a lan) (z::'a lan). x = x \<cdot> y + z \<and> x \<noteq> z \<cdot> y\<^sup>\<star>"
proof -
  have one: "(0::'a lan) + 1 \<cdot> 1 = 1"
    by (metis ab_near_semiring_one_class.mult_onel kleene_algebra_class.dual.add_zerol)
  have two: "(1::'a lan) \<noteq> 0 \<cdot> 1\<^sup>\<star>"
  proof -
    have "\<exists>x\<^sub>1. (0::'a list set) \<noteq> x\<^sub>1"
      by auto
    hence "(1::'a list set) \<noteq> 0"
      by (metis kleene_algebra_class.dual.annir kleene_algebra_class.dual.mult.right_neutral)
    thus "(1::'a list set) \<noteq> 0 \<cdot> 1\<^sup>\<star>"
      by simp
  qed
  show ?thesis using one and two
    by (metis kleene_algebra_class.dual.add_zerol kleene_algebra_class.dual.add_zeror)
qed

interpretation lan_salomaa_l: Sl_algebra "(+)" "(\<cdot>)" "1 :: 'a lan" 0 "(\<subseteq>)" "(\<subset>)" "star" "l_ewp"
proof
  fix x y z :: "'a lan"
  show "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis kleene_algebra_class.dual.star2)
  show "l_ewp x = (\<exists>y. x = 1 + y \<and> \<not> l_ewp y)"
    by (simp add:l_ewp_def one_set_def one_list_def plus_set_def, metis insertCI mk_disjoint_insert)
  show "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis kleene_algebra_class.star_unfoldl_eq)
  show "\<not> l_ewp y \<Longrightarrow> x = y \<cdot> x + z \<Longrightarrow> x = y\<^sup>\<star> \<cdot> z"
    by (metis arden_l)
qed

interpretation lan_salomaa_r: Sr_algebra "(+)" "(\<cdot>)" "1 :: 'a lan" 0 "(\<subseteq>)" "(\<subset>)" "star" "l_ewp"
proof
  fix x y z :: "'a lan"
  show "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
    by (metis kleene_algebra_class.star_unfoldr_eq)
  show "\<not> l_ewp y \<Longrightarrow> x = x \<cdot> y + z \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"
    by (metis arden_r)
qed

subsection \<open>Regular Language Model of Salomaa Algebra\<close>

notation
  Atom ("\<langle>_\<rangle>") and
  Plus (infixl "+\<^sub>r" 65) and
  Times (infixl "\<cdot>\<^sub>r" 70) and
  Star ("_\<^sup>\<star>\<^sub>r" [101] 100) and
  Zero ("0\<^sub>r") and
  One ("1\<^sub>r")

fun rexp_ewp :: "'a rexp \<Rightarrow> bool" where
  "rexp_ewp 0\<^sub>r = False" |
  "rexp_ewp 1\<^sub>r = True" |
  "rexp_ewp \<langle>a\<rangle> = False" |
  "rexp_ewp (s +\<^sub>r t) = (rexp_ewp s \<or> rexp_ewp t)" |
  "rexp_ewp (s \<cdot>\<^sub>r t) = (rexp_ewp s \<and> rexp_ewp t)" |
  "rexp_ewp (s\<^sup>\<star>\<^sub>r) = True"

abbreviation "ro(s) \<equiv> (if (rexp_ewp s) then 1\<^sub>r else 0\<^sub>r)"

lift_definition r_ewp :: "'a reg_lan \<Rightarrow> bool" is "l_ewp" .

lift_definition r_lang :: "'a rexp \<Rightarrow> 'a reg_lan"  is "lang"
  by (simp)

abbreviation r_sim :: "'a rexp \<Rightarrow> 'a rexp \<Rightarrow> bool" (infix "\<sim>" 50) where
  "p \<sim> q \<equiv> r_lang p = r_lang q"

declare Rep_reg_lan [simp]
declare Rep_reg_lan_inverse [simp]
declare Abs_reg_lan_inverse [simp]

lemma rexp_ewp_l_ewp: "l_ewp (lang x) = rexp_ewp x"
proof (induct x)
  case (Star x) thus ?case
    by (simp, metis lan_salomaa_l.EWP left_near_kleene_algebra_class.star_plus_one)
qed (simp_all add:l_ewp_def zero_set_def one_set_def one_list_def plus_set_def c_prod_def times_list_def)

theorem regexp_ewp:
  defines P_def: "P(t) \<equiv> \<exists> t'. t \<sim> ro(t) +\<^sub>r t' \<and> ro(t') = 0\<^sub>r"
  shows "P t"
proof (induct t)
  show "P(0\<^sub>r)"
    by (simp add:P_def r_lang_def, rule_tac x="0\<^sub>r" in exI, simp)
next
  fix a
  show "P(\<langle>a\<rangle>)"
    by (simp add:P_def r_lang_def, rule_tac x="\<langle>a\<rangle>" in exI, simp)
next
  show "P(1\<^sub>r)"
    by (simp add:P_def r_lang_def, rule_tac x="0\<^sub>r" in exI, simp)
next
  fix t1 t2
  assume "P(t1)" "P(t2)"
  then obtain t1' t2' 
    where "t1 \<sim> ro(t1) +\<^sub>r t1'" "ro(t1') = 0\<^sub>r"
          "t2 \<sim> ro(t2) +\<^sub>r t2'" "ro(t2') = 0\<^sub>r"
    by (metis assms rexp.distinct(1))
  thus "P(t1 +\<^sub>r t2)"
    apply (subst P_def, transfer)
    apply (rule_tac x="t1' +\<^sub>r t2'" in exI)
    apply clarsimp
    by (metis (no_types, lifting) add.left_commute join.sup_assoc join.sup_left_idem rexp.distinct(2))
 next
  fix t1 t2
  assume "P(t1)" "P(t2)"
  then obtain t1' t2' 
    where t1: "t1 \<sim> ro(t1) +\<^sub>r t1'" "ro(t1') = 0\<^sub>r" and
          t2: "t2 \<sim> ro(t2) +\<^sub>r t2'" "ro(t2') = 0\<^sub>r"
      by (metis assms rexp.distinct(1))
  thus "P(t1 \<cdot>\<^sub>r t2)"
  proof -
    let ?t' = "ro(t1) \<cdot>\<^sub>r t2' +\<^sub>r t1' \<cdot>\<^sub>r ro(t2) +\<^sub>r t1' \<cdot>\<^sub>r t2'"
    from t1 t2 have r1: "ro(?t') = 0\<^sub>r"
      by (auto)
    from t1 t2 have "t1 \<cdot>\<^sub>r t2 \<sim> (ro(t1) +\<^sub>r t1') \<cdot>\<^sub>r (ro(t2) +\<^sub>r t2')" (is "?l \<sim> ?r")
      by (transfer, simp)
    also have "?r \<sim> ro(t1) \<cdot>\<^sub>r ro(t2) +\<^sub>r ro(t1) \<cdot>\<^sub>r t2' +\<^sub>r t1' \<cdot>\<^sub>r ro(t2) +\<^sub>r t1' \<cdot>\<^sub>r t2'" (is "?l \<sim> ?r")
      apply (transfer, unfold lang.simps)
      apply (simp only: distrib_right' semiring_class.distrib_left)
      apply (metis (hide_lams, no_types) join_semilattice_class.add_comm semiring_class.combine_common_factor)
    done
    also have "?r \<sim> ro(t1 \<cdot>\<^sub>r t2) +\<^sub>r ro(t1) \<cdot>\<^sub>r t2' +\<^sub>r t1' \<cdot>\<^sub>r ro(t2) +\<^sub>r t1' \<cdot>\<^sub>r t2'" (is "?l \<sim> ?r")
      by (transfer, simp)
    also have "?r \<sim> ro(t1 \<cdot>\<^sub>r t2) +\<^sub>r ?t'"
      apply (transfer, unfold lang.simps)
      apply (metis (mono_tags) join_semilattice_class.add_assoc')
    done
    finally show ?thesis using r1
      apply (unfold P_def)
      apply (rule_tac x="?t'" in exI, simp)
    done
  qed
next
  fix s
  assume assm:"P s"
  then obtain s' where r1: "s \<sim> ro(s) +\<^sub>r s'" "ro(s') = 0\<^sub>r"
    by (metis assms rexp.distinct(1))
  thus "P (s\<^sup>\<star>\<^sub>r)"
  proof -
    let ?t' = "s' \<cdot>\<^sub>r (s')\<^sup>\<star>\<^sub>r"
    have r2: "ro(?t') = 0\<^sub>r"
      by (metis r1(2) rexp.distinct(1) rexp_ewp.simps(5))
    from assm r1 have "(ro(s) +\<^sub>r s')\<^sup>\<star>\<^sub>r \<sim> (s')\<^sup>\<star>\<^sub>r" (is "?l \<sim> ?r")
      by (transfer, auto)
    also have "?r \<sim> 1\<^sub>r +\<^sub>r s' \<cdot>\<^sub>r (s')\<^sup>\<star>\<^sub>r" (is "?l \<sim> ?r")
      by (transfer, auto)
    also have "?r \<sim> ro(s\<^sup>\<star>\<^sub>r) +\<^sub>r ?t'"
      by (metis (full_types) rexp_ewp.simps(6))
    finally show ?thesis
      by (metis assms lang.simps(6) r1(1) r2 r_lang.abs_eq r_lang.rep_eq)
  qed
qed

instantiation reg_lan :: (type) Sr_algebra
begin

lift_definition ewp_reg_lan :: "'a reg_lan \<Rightarrow> bool" is "l_ewp" .

instance proof
  fix x :: "'a reg_lan"
  show "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis kleene_algebra_class.dual.star2)
next
  fix x :: "'a reg_lan"
  show "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
    by (metis kleene_algebra_class.star_unfoldr_eq)
next
  fix x :: "'a reg_lan"
  show "ewp x = (\<exists>y. x = 1 + y \<and> \<not> ewp y)"
  proof -
    obtain t where "r_lang t = x"
      by (transfer, auto)
    moreover obtain t' where "t \<sim> ro(t) +\<^sub>r t'" "ro(t') = 0\<^sub>r"
      by (metis regexp_ewp)
    ultimately show ?thesis
      apply (transfer, auto)
      apply (metis (full_types) lang.simps(2) rexp.distinct(1) rexp_ewp_l_ewp)
      apply (metis lan_salomaa_l.EWP)
    done
  qed
next
  fix x y z :: "'a reg_lan"
  show "\<lbrakk> \<not> ewp y; x = x \<cdot> y + z \<rbrakk> \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"
    by (transfer, metis lan_salomaa_r.Ar)
qed
end

instantiation reg_lan :: (type) Sl_algebra
begin

instance proof
  fix x :: "'a reg_lan"
  show "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis left_pre_kleene_algebra_class.star_unfoldl_eq)
next
  fix x y z :: "'a reg_lan"
  show "\<lbrakk> \<not> ewp y; x = y \<cdot> x + z \<rbrakk> \<Longrightarrow> x = y\<^sup>\<star> \<cdot> z"
    by (transfer, metis lan_salomaa_l.Al)
qed
end

instance reg_lan :: (type) S_algebra ..

theorem arden_regexp_l: 
  assumes "ro(y) = 0\<^sub>r" "x \<sim> y \<cdot>\<^sub>r x +\<^sub>r z" 
  shows "x \<sim> y\<^sup>\<star>\<^sub>r \<cdot>\<^sub>r z"
  using assms
  by (transfer, metis arden_l lang.simps(4) lang.simps(5) lang.simps(6) rexp.distinct(1) rexp_ewp_l_ewp)

theorem arden_regexp_r: 
  assumes "ro(y) = 0\<^sub>r" "x \<sim> x \<cdot>\<^sub>r y +\<^sub>r z" 
  shows "x \<sim> z \<cdot>\<^sub>r y\<^sup>\<star>\<^sub>r"
  using assms
  by transfer (metis lan_salomaa_r.Ar lang.simps(4) lang.simps(5) lang.simps(6) rexp.distinct(1) rexp_ewp_l_ewp)

end
