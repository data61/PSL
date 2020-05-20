(* Title:      Regular Algebras
   Author:     Simon Foster, Georg Struth
   Maintainer: Simon Foster <s.foster at york.ac.uk>
               Georg Struth <g.struth at sheffield.ac.uk>               
*)

section \<open>Dioids, Powers and Finite Sums\<close>

theory Dioid_Power_Sum
  imports Kleene_Algebra.Dioid Kleene_Algebra.Finite_Suprema

begin

text \<open>We add a few facts about powers and finite
 sums---in fact, finite suprema---to an existing theory field for dioids.\<close>

context dioid_one_zero

begin

lemma add_iso_r: "y \<le> z \<Longrightarrow> x + y \<le> x + z"
    using local.join.sup_mono by blast

notation power ("_\<^bsup>_\<^esup>" [101,50] 100) 

lemma power_subdist: "x\<^bsup>n\<^esup> \<le> (x + y)\<^bsup>n\<^esup>"
  apply (induct n)
  apply simp
  using local.mult_isol_var local.power_Suc2 by auto
  
lemma power_inductl_var: "x \<cdot> y \<le> y \<Longrightarrow> x\<^bsup>n\<^esup> \<cdot> y \<le> y"
  apply (induct n)
  apply simp
  by (metis (no_types, lifting) local.dual_order.trans local.mult_isol local.power_Suc2 mult_assoc)

lemma power_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^bsup>n\<^esup> \<le> y"
  by (induct n, metis eq_refl mult_oner power.simps(1), metis mult.assoc mult_isor order_refl order_trans power.simps(2) power_commutes)

definition powsum :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsub>_\<^esub>\<^bsup>_\<^esup>" [101,50,50] 100) where
  "powsum x m n = sum ((^) x) {m..n + m}"

lemmas powsum_simps = powsum_def atLeastAtMostSuc_conv numerals

lemma powsum1 [simp]: "x\<^bsub>n\<^esub>\<^bsup>0\<^esup> = x\<^bsup>n\<^esup>"
  by (simp add:powsum_simps)
  
lemma powsum2: "x\<^bsub>n\<^esub>\<^bsup>Suc m\<^esup> = x\<^bsub>n\<^esub>\<^bsup>m \<^esup>+ x\<^bsup>n+Suc m\<^esup>"
proof-
  have "x\<^bsub>n\<^esub>\<^bsup>Suc m\<^esup> = sum ((^) x) {n..(Suc m)+n}"
    using powsum_def by blast
  also have "... = sum ((^) x) {n..m+n} +  x\<^bsup>n+Suc m\<^esup>"
    by (simp add: ab_semigroup_add_class.add.commute atLeastAtMostSuc_conv local.join.sup_commute)
  finally show ?thesis
    by (simp add: powsum_def)
qed

lemma powsum_00 [simp]: "x\<^bsub>0\<^esub>\<^bsup>0 \<^esup>= 1"
  by (simp add: powsum_def)

lemma powsum_01 [simp]: "x\<^bsub>0\<^esub>\<^bsup>1\<^esup> = 1 + x" 
  by (simp add: powsum2) 

lemma powsum_10 [simp]: "x\<^bsub>1\<^esub>\<^bsup>0\<^esup> = x"  
  by (simp add: powsum_simps) 

lemma powsum_split: "x\<^bsub>m\<^esub>\<^bsup>i+Suc n\<^esup> = x\<^bsub>m\<^esub>\<^bsup>i\<^esup> + x\<^bsub>m+Suc i\<^esub>\<^bsup>n\<^esup>"
  by (induct n, simp_all add:powsum_simps ac_simps)

lemma powsum_split_var1: "x\<^bsub>0\<^esub>\<^bsup>n+1\<^esup> = 1 + x\<^bsub>1\<^esub>\<^bsup>n\<^esup>" 
proof -
  have "x\<^bsub>0\<^esub>\<^bsup>n + 1\<^esup> = x\<^bsub>0\<^esub>\<^bsup>0 + Suc n\<^esup>"
    by simp
  also have "... = x\<^bsub>0\<^esub>\<^bsup>0\<^esup> + x\<^bsub>0 + Suc 0\<^esub>\<^bsup>n\<^esup>"
    by (subst powsum_split, rule refl)
  also have "... = 1 + x\<^bsub>0 + Suc 0\<^esub>\<^bsup>n\<^esup>"
    by simp
  finally show ?thesis 
    by simp
qed

lemma powsum_split_var2 [simp]: "x\<^bsup>m\<^esup> + x\<^bsub>0\<^esub>\<^bsup>m\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m\<^esup>"
proof (induct m)
  case 0 show ?case 
    by (metis add_idem' power_0 powsum_00)
  case (Suc n) show ?case
    by (simp add: add_commute powsum2)
qed

lemma powsum_split_var3: "x\<^bsub>0\<^esub>\<^bsup>m+Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ x\<^bsub>0+Suc m\<^esub>\<^bsup>n\<^esup>" 
  by (subst powsum_split, simp)

lemma powsum_split_var4 [simp]: "x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup> + x\<^bsub>m\<^esub>\<^bsup>n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup>"
proof (induct n)
  case 0 show ?case
    by (metis add_0_iff add_comm powsum1 powsum_split_var2)
next
  case (Suc n) note hyp = this
  show ?case
  proof -
    have  "x\<^bsub>0\<^esub>\<^bsup>m + Suc n\<^esup> + x\<^bsub>m\<^esub>\<^bsup>Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m + n\<^esup> + x\<^bsup>Suc (m + n)\<^esup> + (x\<^bsub>m\<^esub>\<^bsup>n\<^esup> + x\<^bsup>m + Suc n\<^esup>)"
      by (auto simp add: powsum2)  
    also have "... = (x\<^bsub>0\<^esub>\<^bsup>m + n \<^esup>+ x\<^bsub>m\<^esub>\<^bsup>n\<^esup>) + x\<^bsup>Suc (m + n)\<^esup> + x\<^bsup>m + Suc n\<^esup>"
      by (metis add.assoc add.left_commute)
    also have "... =  x\<^bsup>Suc (m+n)\<^esup> + x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup>"
      by (metis add_Suc_right add.assoc add.commute add_idem' hyp)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>m + Suc n\<^esup>"
      by (simp add: add_commute powsum2)
    finally show ?thesis .
  qed
qed

lemma powsum_split_var6: "x\<^bsub>0\<^esub>\<^bsup>(Suc k)+Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>Suc k \<^esup>+ x\<^bsub>0+Suc (Suc k)\<^esub>\<^bsup>n\<^esup>"     
  by (metis powsum_split_var3) 

lemma powsum_ext: "x \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>" 
proof (induct n)
  case 0 show ?case
    by (metis One_nat_def local.join.sup_ge2 powsum_01)
next
  case (Suc n) thus ?case
    by (auto simp add:less_eq_def powsum_simps, metis (lifting, no_types) add.left_commute)
qed

lemma powsum_one: "1 \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"  
  by (induct n, metis One_nat_def local.join.sup.cobounded1 powsum_01, metis (full_types) Suc_eq_plus1 local.join.sup.cobounded1 powsum_split_var1)

lemma powsum_shift1: "x \<cdot> x\<^bsub>m\<^esub>\<^bsup>n\<^esup> = x\<^bsub>m+1\<^esub>\<^bsup>n\<^esup>" 
  apply (induct n)
  apply (simp_all add: powsum_simps)
  apply (metis local.add_left_comm local.distrib_left powsum_def)  
  done

lemma powsum_shift: "x\<^bsup>k \<^esup>\<cdot> x\<^bsub>m\<^esub>\<^bsup>n\<^esup> = x\<^bsub>k+m\<^esub>\<^bsup>n\<^esup>" 
  by (induct k, simp_all, metis Suc_eq_plus1 mult.assoc powsum_shift1)

lemma powsum_prod_suc: "x\<^bsub>0\<^esub>\<^bsup>m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>Suc (m+n)\<^esup>"
proof (induct m)
  case 0 show ?case
    by simp
  case (Suc m) 
  note hyp = this
  show ?case
  proof -
    have "x\<^bsub>0\<^esub>\<^bsup>Suc m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> =  x\<^bsub>0\<^esub>\<^bsup>m\<^esup> \<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> + x\<^bsup>Suc m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"
      by (simp add: powsum2)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsup>Suc m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"
      by (simp add:hyp)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsub>Suc m\<^esub>\<^bsup>Suc n\<^esup>"
      by (subst powsum_shift, simp)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + (x\<^bsub>Suc m\<^esub>\<^bsup>n\<^esup> + x\<^bsup>Suc m + Suc n\<^esup>)"
      by (simp add:powsum2)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsub>Suc m\<^esub>\<^bsup>n\<^esup> + x\<^bsup>Suc (Suc (m + n))\<^esup>"
      by (metis add_Suc_right add_Suc_shift add.assoc add.left_commute)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsup>Suc (Suc (m + n))\<^esup>"
      by (simp only: add_Suc_right[THEN sym] add_Suc_shift[THEN sym] powsum_split_var4)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (Suc m + n)\<^esup>"
      by (simp add: powsum2)
    finally show ?thesis .
  qed
qed

lemma powsum_prod: "x\<^bsub>0\<^esub>\<^bsup>m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup>"
  by (cases n, simp, simp add: powsum_prod_suc)

end

end
