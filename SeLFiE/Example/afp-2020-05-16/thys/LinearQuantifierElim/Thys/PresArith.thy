(*  Author:     Tobias Nipkow, 2007  *)

section\<open>Presburger arithmetic\<close>

theory PresArith
imports QE "HOL-Library.ListVector"
begin

declare iprod_assoc[simp]

subsection\<open>Syntax\<close>

datatype atom =
  Le int "int list" | Dvd int int "int list" | NDvd int int "int list"

fun divisor :: "atom \<Rightarrow> int" where
"divisor (Le i ks) = 1" |
"divisor (Dvd d i ks) = d" |
"divisor (NDvd d i ks) = d"

fun neg\<^sub>Z :: "atom \<Rightarrow> atom fm" where
"neg\<^sub>Z (Le i ks) = Atom(Le (1-i) (-ks))" |
"neg\<^sub>Z (Dvd d i ks) = Atom(NDvd d i ks)" |
"neg\<^sub>Z (NDvd d i ks) = Atom(Dvd d i ks)"

fun hd_coeff :: "atom \<Rightarrow> int" where
"hd_coeff (Le i ks) = (case ks of [] \<Rightarrow> 0 | k#_ \<Rightarrow> k)" |
"hd_coeff (Dvd d i ks) = (case ks of [] \<Rightarrow> 0 | k#_ \<Rightarrow> k)" |
"hd_coeff (NDvd d i ks) = (case ks of [] \<Rightarrow> 0 | k#_ \<Rightarrow> k)"

fun decr\<^sub>Z :: "atom \<Rightarrow> atom" where
"decr\<^sub>Z (Le i ks) = Le i (tl ks)" |
"decr\<^sub>Z (Dvd d i ks) = Dvd d i (tl ks)" |
"decr\<^sub>Z (NDvd d i ks) = NDvd d i (tl ks)"

fun I\<^sub>Z :: "atom \<Rightarrow> int list \<Rightarrow> bool" where
"I\<^sub>Z (Le i ks) xs = (i \<le> \<langle>ks,xs\<rangle>)" |
"I\<^sub>Z (Dvd d i ks) xs = (d dvd i+\<langle>ks,xs\<rangle>)" |
"I\<^sub>Z (NDvd d i ks) xs = (\<not> d dvd i+\<langle>ks,xs\<rangle>)"

definition "atoms\<^sub>0 = ATOM.atoms\<^sub>0 (\<lambda>a. hd_coeff a \<noteq> 0)"
(* FIXME !!! (incl: display should hide params)*)

interpretation Z:
  ATOM neg\<^sub>Z "(\<lambda>a. divisor a \<noteq> 0)" I\<^sub>Z "(\<lambda>a. hd_coeff a \<noteq> 0)" decr\<^sub>Z
  rewrites "ATOM.atoms\<^sub>0 (\<lambda>a. hd_coeff a \<noteq> 0) = atoms\<^sub>0"
proof goal_cases
  case 1
  thus ?case
    apply(unfold_locales)
    apply(case_tac a)
    apply simp_all
    apply(case_tac a)
    apply simp_all
    apply(case_tac a)
    apply (simp_all)
    apply arith
    apply(case_tac a)
    apply(simp_all add: split: list.splits)
    apply(case_tac a)
    apply simp_all
    done
next
  case 2
  thus ?case by(simp add:atoms\<^sub>0_def)
qed

setup \<open>Sign.revert_abbrev "" @{const_abbrev Z.I}\<close>
setup \<open>Sign.revert_abbrev "" @{const_abbrev Z.lift_dnf_qe}\<close>
(* FIXME doesn't work*)
(* FIXME does not help
setup {* Sign.revert_abbrev "" @{const_abbrev Z.normal} *}
*)

abbreviation
"hd_coeff_is1 a \<equiv>
  (case a of Le _ _ \<Rightarrow> hd_coeff a \<in> {1,-1} | _ \<Rightarrow> hd_coeff a = 1)"


fun asubst :: "int \<Rightarrow> int list \<Rightarrow> atom \<Rightarrow> atom" where
"asubst i' ks' (Le i (k#ks)) = Le (i - k*i') (k *\<^sub>s ks' + ks)" |
"asubst i' ks' (Dvd d i (k#ks)) = Dvd d (i + k*i') (k *\<^sub>s ks' + ks)" |
"asubst i' ks' (NDvd d i (k#ks)) = NDvd d (i + k*i') (k *\<^sub>s ks' + ks)" |
"asubst i' ks' a = a"

abbreviation subst :: "int \<Rightarrow> int list \<Rightarrow> atom fm \<Rightarrow> atom fm"
where "subst i ks \<equiv> map\<^sub>f\<^sub>m (asubst i ks)"

lemma IZ_asubst: "I\<^sub>Z (asubst i ks a) xs = I\<^sub>Z a ((i + \<langle>ks,xs\<rangle>) # xs)"
apply (cases a)
apply (rename_tac list)
apply (case_tac list)
apply (simp_all add:algebra_simps iprod_left_add_distrib)
apply (rename_tac list)
apply (case_tac list)
apply (simp_all add:algebra_simps iprod_left_add_distrib)
apply (rename_tac list)
apply (case_tac list)
apply (simp_all add:algebra_simps iprod_left_add_distrib)
done

lemma I_subst:
  "qfree \<phi> \<Longrightarrow> Z.I \<phi> ((i + \<langle>ks,xs\<rangle>) # xs) = Z.I (subst i ks \<phi>) xs"
by (induct \<phi>) (simp_all add:IZ_asubst)

lemma divisor_asubst[simp]: "divisor (asubst i ks a) = divisor a"
by(induct i ks a rule:asubst.induct) auto


definition "lbounds as = [(i,ks). Le i (k#ks) \<leftarrow> as, k>0]"
definition "ubounds as = [(i,ks). Le i (k#ks) \<leftarrow> as, k<0]"
lemma set_lbounds:
  "set(lbounds as) = {(i,ks)|i k ks. Le i (k#ks) \<in> set as \<and> k>0}"
by(auto simp: lbounds_def split:list.splits atom.splits if_splits)
lemma set_ubounds:
  "set(ubounds as) = {(i,ks)|i k ks. Le i (k#ks) \<in> set as \<and> k<0}"
by(auto simp: ubounds_def split:list.splits atom.splits if_splits)

lemma lbounds_append[simp]: "lbounds(as @ bs) = lbounds as @ lbounds bs"
by(simp add:lbounds_def)


subsection\<open>LCM and lemmas\<close>

fun zlcms :: "int list \<Rightarrow> int" where
"zlcms [] = 1" |
"zlcms (i#is) = lcm i (zlcms is)"

lemma dvd_zlcms: "i \<in> set is \<Longrightarrow> i dvd zlcms is"
by(induct "is") auto

lemma zlcms_pos: "\<forall>i \<in> set is. i\<noteq>0 \<Longrightarrow> zlcms is > 0"
by(induct "is")(auto simp:lcm_pos_int)

lemma zlcms0_iff[simp]: "(zlcms is = 0) = (0 \<in> set is)"
by (metis mod_by_0 dvd_eq_mod_eq_0 dvd_zlcms zlcms_pos less_le)

lemma elem_le_zlcms: "\<forall>i \<in> set is. i \<noteq> 0 \<Longrightarrow> i \<in> set is \<Longrightarrow> i \<le> zlcms is"
by (metis dvd_zlcms zdvd_imp_le zlcms_pos)


subsection\<open>Setting coeffiencients to 1 or -1\<close>

fun hd_coeff1 :: "int \<Rightarrow> atom \<Rightarrow> atom" where
"hd_coeff1 m (Le i (k#ks)) =
   (if k=0 then Le i (k#ks)
    else let m' = m div (abs k) in Le (m'*i) (sgn k # (m' *\<^sub>s ks)))" |
"hd_coeff1 m (Dvd d i (k#ks)) =
   (if k=0 then Dvd d i (k#ks)
    else let m' = m div k in Dvd (m'*d) (m'*i) (1 # (m' *\<^sub>s ks)))" |
"hd_coeff1 m (NDvd d i (k#ks)) =
   (if k=0 then NDvd d i (k#ks)
    else let m' = m div k in NDvd (m'*d) (m'*i) (1 # (m' *\<^sub>s ks)))" |
"hd_coeff1 _ a = a"

text\<open>The def of @{const hd_coeff1} on @{const Dvd} and @{const NDvd} is
different from the @{const Le} because it allows the resulting head
coefficient to be 1 rather than 1 or -1. We show that the other version has
the same semantics:\<close>

lemma "\<lbrakk> k \<noteq> 0; k dvd m \<rbrakk> \<Longrightarrow>
  I\<^sub>Z (hd_coeff1 m (Dvd d i (k#ks))) (x#e) = (let m' = m div (abs k) in
  I\<^sub>Z (Dvd (m'*d) (m'*i) (sgn k # (m' *\<^sub>s ks))) (x#e))"
apply(auto simp:algebra_simps abs_if sgn_if)
 apply(simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0[THEN iffD1] algebra_simps)
 apply (metis diff_conv_add_uminus add.left_commute dvd_minus_iff minus_add_distrib)
apply(simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0[THEN iffD1] algebra_simps)
apply (metis diff_conv_add_uminus add.left_commute dvd_minus_iff minus_add_distrib)
done


lemma I_hd_coeff1_mult_a: assumes "m>0"
shows "hd_coeff a dvd m | hd_coeff a = 0 \<Longrightarrow> I\<^sub>Z (hd_coeff1 m a) (m*x#xs) = I\<^sub>Z a (x#xs)"
proof(induct a)
  case [simp]: (Le i ks)
  show ?case
  proof(cases ks)
    case Nil thus ?thesis by simp
  next
    case [simp]: (Cons k ks')
    show ?thesis
    proof cases
      assume "k=0" thus ?thesis by simp
    next
      assume "k\<noteq>0"
      with Le have "\<bar>k\<bar> dvd m" by simp
      let ?m' = "m div \<bar>k\<bar>"
      have "?m' > 0" using \<open>\<bar>k\<bar> dvd m\<close> pos_imp_zdiv_pos_iff \<open>m>0\<close> \<open>k\<noteq>0\<close>
        by(simp add:zdvd_imp_le)
      have 1: "k*(x*?m') = sgn k * x * m"
      proof -
        have "k*(x*?m') = (sgn k * abs k) * (x * ?m')"
          by(simp only: mult_sgn_abs)
        also have "\<dots> = sgn k * x * (abs k * ?m')" by simp
        also have "\<dots> = sgn k * x * m"
          using dvd_mult_div_cancel[OF \<open>\<bar>k\<bar> dvd m\<close>] by(simp add:algebra_simps)
        finally show ?thesis .
      qed
      have "I\<^sub>Z (hd_coeff1 m (Le i ks)) (m*x#xs) \<longleftrightarrow>
            (i*?m' \<le> sgn k * m*x + ?m' * \<langle>ks',xs\<rangle>)"
        using \<open>k\<noteq>0\<close> by(simp add: algebra_simps)
      also have "\<dots> \<longleftrightarrow> ?m'*i \<le> ?m' * (k*x + \<langle>ks',xs\<rangle>)" using 1
        by(simp (no_asm_simp) add:algebra_simps)
      also have "\<dots> \<longleftrightarrow> i \<le> k*x + \<langle>ks',xs\<rangle>" using \<open>?m'>0\<close>
        by simp
      finally show ?thesis by(simp)
    qed
  qed
next
  case [simp]: (Dvd d i ks)
  show ?case
  proof(cases ks)
    case Nil thus ?thesis by simp
  next
    case [simp]: (Cons k ks')
    show ?thesis
    proof cases
      assume "k=0" thus ?thesis by simp
    next
      assume "k\<noteq>0"
      with Dvd have "k dvd m" by simp
      let ?m' = "m div k"
      have "?m' \<noteq> 0" using \<open>k dvd m\<close> zdiv_eq_0_iff \<open>m>0\<close> \<open>k\<noteq>0\<close>
        by(simp add:linorder_not_less zdvd_imp_le)
      have 1: "k*(x*?m') = x * m"
      proof -
        have "k*(x*?m') = x*(k*?m')" by(simp add:algebra_simps)
        also have "\<dots> = x*m" using dvd_mult_div_cancel[OF \<open>k dvd m\<close>]
          by(simp add:algebra_simps)
        finally show ?thesis .
      qed
      have "I\<^sub>Z (hd_coeff1 m (Dvd d i ks)) (m*x#xs) \<longleftrightarrow>
            (?m'*d dvd ?m'*i + m*x + ?m' * \<langle>ks',xs\<rangle>)"
        using \<open>k\<noteq>0\<close> by(simp add: algebra_simps)
      also have "\<dots> \<longleftrightarrow> ?m'*d dvd ?m' * (i + k*x + \<langle>ks',xs\<rangle>)" using 1
        by(simp (no_asm_simp) add:algebra_simps)
      also have "\<dots> \<longleftrightarrow> d dvd i + k*x + \<langle>ks',xs\<rangle>" using \<open>?m'\<noteq>0\<close> by(simp)
      finally show ?thesis by(simp add:algebra_simps)
    qed
  qed
next
  case [simp]: (NDvd d i ks)
  show ?case
  proof(cases ks)
    case Nil thus ?thesis by simp
  next
    case [simp]: (Cons k ks')
    show ?thesis
    proof cases
      assume "k=0" thus ?thesis by simp
    next
      assume "k\<noteq>0"
      with NDvd have "k dvd m" by simp
      let ?m' = "m div k"
      have "?m' \<noteq> 0" using \<open>k dvd m\<close> zdiv_eq_0_iff \<open>m>0\<close> \<open>k\<noteq>0\<close>
        by(simp add:linorder_not_less zdvd_imp_le)
      have 1: "k*(x*?m') = x * m"
      proof -
        have "k*(x*?m') = x*(k*?m')" by(simp add:algebra_simps)
        also have "\<dots> = x*m" using dvd_mult_div_cancel[OF \<open>k dvd m\<close>]
          by(simp add:algebra_simps)
        finally show ?thesis .
      qed
      have "I\<^sub>Z (hd_coeff1 m (NDvd d i ks)) (m*x#xs) \<longleftrightarrow>
            \<not>(?m'*d dvd ?m'*i + m*x + ?m' * \<langle>ks',xs\<rangle>)"
        using \<open>k\<noteq>0\<close> by(simp add: algebra_simps)
      also have "\<dots> \<longleftrightarrow> \<not> ?m'*d dvd ?m' * (i + k*x + \<langle>ks',xs\<rangle>)" using 1
        by(simp (no_asm_simp) add:algebra_simps)
      also have "\<dots> \<longleftrightarrow> \<not> d dvd i + k*x + \<langle>ks',xs\<rangle>" using \<open>?m'\<noteq>0\<close> by(simp)
      finally show ?thesis by(simp add:algebra_simps)
    qed
  qed
qed


lemma I_hd_coeff1_mult: assumes "m>0"
shows "qfree \<phi> \<Longrightarrow> \<forall> a \<in> set(Z.atoms\<^sub>0 \<phi>). hd_coeff a dvd m \<Longrightarrow>
 Z.I (map\<^sub>f\<^sub>m (hd_coeff1 m) \<phi>) (m*x#xs) = Z.I \<phi> (x#xs)"
proof(induct \<phi>)
  case (Atom a)
  thus ?case using I_hd_coeff1_mult_a[OF \<open>m>0\<close>] by auto
qed simp_all

end
