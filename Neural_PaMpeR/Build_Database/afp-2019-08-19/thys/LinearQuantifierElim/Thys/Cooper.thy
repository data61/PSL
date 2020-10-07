(*  Author:     Tobias Nipkow, 2007  *)

theory Cooper
imports PresArith
begin

subsection\<open>Cooper\<close>

text\<open>This section formalizes Cooper's algorithm~\cite{Cooper72}.\<close>

lemma set_atoms0_iff:
 "qfree \<phi> \<Longrightarrow> a \<in> set(Z.atoms\<^sub>0 \<phi>) \<longleftrightarrow> a \<in> atoms \<phi> \<and> hd_coeff a \<noteq> 0"
by(induct \<phi>) (auto split:if_split_asm)

definition
"hd_coeffs1 \<phi> =
 (let m = zlcms(map hd_coeff (Z.atoms\<^sub>0 \<phi>))
  in And (Atom(Dvd m 0 [1])) (map\<^sub>f\<^sub>m (hd_coeff1 m) \<phi>))"

lemma I_hd_coeffs1:
assumes "qfree \<phi>"
shows "(\<exists>x. Z.I (hd_coeffs1 \<phi>) (x#xs)) = (\<exists>x. Z.I \<phi> (x#xs))" (is "?L = ?R")
proof -
  let ?l = "zlcms(map hd_coeff (Z.atoms\<^sub>0 \<phi>))"
  have "?l>0" by(simp add: zlcms_pos set_atoms0_iff[OF \<open>qfree \<phi>\<close>])
  have "?L = (\<exists>x. ?l dvd x+0 \<and> Z.I (map\<^sub>f\<^sub>m (hd_coeff1 ?l) \<phi>) (x#xs))"
    by(simp add:hd_coeffs1_def)
  also have "\<dots> = (\<exists>x. Z.I (map\<^sub>f\<^sub>m (hd_coeff1 ?l) \<phi>) (?l*x#xs))"
    by(rule unity_coeff_ex[THEN meta_eq_to_obj_eq,symmetric])
  also have "\<dots> = ?R"
    by(simp add: I_hd_coeff1_mult[OF \<open>?l>0\<close> \<open>qfree \<phi>\<close>] dvd_zlcms)
  finally show ?thesis .
qed


fun min_inf :: "atom fm \<Rightarrow> atom fm" ("inf\<^sub>-") where
"inf\<^sub>- (And \<phi>\<^sub>1 \<phi>\<^sub>2) = and (inf\<^sub>- \<phi>\<^sub>1) (inf\<^sub>- \<phi>\<^sub>2)" |
"inf\<^sub>- (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = or (inf\<^sub>- \<phi>\<^sub>1) (inf\<^sub>- \<phi>\<^sub>2)" |
"inf\<^sub>- (Atom(Le i (k#ks))) =
  (if k<0 then TrueF else if k>0 then FalseF else Atom(Le i (0#ks)))" |
"inf\<^sub>- \<phi> = \<phi>"


definition
"qe_cooper\<^sub>1 \<phi> =
 (let as = Z.atoms\<^sub>0 \<phi>; d = zlcms(map divisor as); ls = lbounds as
  in or (Disj [0..d - 1] (\<lambda>n. subst n [] (inf\<^sub>- \<phi>)))
        (Disj ls (\<lambda>(i,ks).
           Disj [0..d - 1] (\<lambda>n. subst (i + n) (-ks) \<phi>))))"


lemma min_inf:
  "nqfree f \<Longrightarrow> \<forall>a\<in>set(Z.atoms\<^sub>0 f). hd_coeff_is1 a
   \<Longrightarrow> \<exists>x.\<forall>y<x. Z.I (inf\<^sub>- f) (y # xs) = Z.I f (y # xs)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> \<exists>x. ?P f x")
proof(induct f rule: min_inf.induct)
  case (3 i k ks)
  { assume "k=0" hence ?case using 3 by simp }
  moreover
  { assume "k= -1"
    hence "?P (Atom(Le i (k#ks))) (-i + \<langle>ks,xs\<rangle> - 1)" using 3 by auto
    hence ?case .. }
  moreover
  { assume "k=1"
    hence "?P (Atom(Le i (k#ks))) (i - \<langle>ks,xs\<rangle> - 1)" using 3 by auto
    hence ?case .. }
  ultimately show ?case using 3 by auto
next
  case (1 f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastforce+
  hence "?P (And f1 f2) (min x1 x2)" by simp
  thus ?case ..
next
  case (2 f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastforce+
  hence "?P (Or f1 f2) (min x1 x2)" by simp
  thus ?case ..
qed simp_all


lemma min_inf_repeats:
  "nqfree \<phi> \<Longrightarrow> \<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). divisor a dvd d \<Longrightarrow>
  Z.I (inf\<^sub>- \<phi>) ((x - k*d)#xs) = Z.I (inf\<^sub>- \<phi>) (x#xs)"
proof(induct \<phi> rule:min_inf.induct)
  case ("4_4" da i ks)
  show ?case
  proof (cases ks)
    case Nil thus ?thesis by simp
  next
    case (Cons j js)
    show ?thesis
    proof cases
      assume "j=0" thus ?thesis using Cons by simp
    next
      assume "j\<noteq>0"
      hence "da dvd d" using Cons "4_4" by simp
      hence "da dvd i + (j * x - j * (k * d) + \<langle>js,xs\<rangle>) \<longleftrightarrow>
             da dvd i + (j * x + \<langle>js,xs\<rangle>)"
      proof -
        have "da dvd i + (j * x - j * (k * d) + \<langle>js,xs\<rangle>) \<longleftrightarrow>
              da dvd (i + j*x + \<langle>js,xs\<rangle>) - (j*k)*d"
          by(simp add: algebra_simps)
        also have "\<dots> \<longleftrightarrow> da dvd i + j*x + \<langle>js,xs\<rangle>" using \<open>da dvd d\<close>
          by (metis dvd_diff zdvd_zdiffD dvd_mult mult.commute)
        also have "\<dots> \<longleftrightarrow> da dvd i + (j * x + \<langle>js,xs\<rangle>)"
          by(simp add: algebra_simps)
        finally show ?thesis .
      qed
      then show ?thesis using Cons by (simp add:ring_distribs)
    qed
  qed
next
  case ("4_5" da i ks)
  show ?case
  proof (cases ks)
    case Nil thus ?thesis by simp
  next
    case (Cons j js)
    show ?thesis
    proof cases
      assume "j=0" thus ?thesis using Cons by simp
    next
      assume "j\<noteq>0"
      hence "da dvd d" using Cons "4_5" by simp
      hence "da dvd i + (j * x - j * (k * d) + \<langle>js,xs\<rangle>) \<longleftrightarrow>
             da dvd i + (j * x + \<langle>js,xs\<rangle>)"
      proof -
        have "da dvd i + (j * x - j * (k * d) + \<langle>js,xs\<rangle>) \<longleftrightarrow>
              da dvd (i + j*x + \<langle>js,xs\<rangle>) - (j*k)*d"
          by(simp add: algebra_simps)
        also have "\<dots> \<longleftrightarrow> da dvd i + j*x + \<langle>js,xs\<rangle>" using \<open>da dvd d\<close>
          by (metis dvd_diff zdvd_zdiffD dvd_mult mult.commute)
        also have "\<dots> \<longleftrightarrow> da dvd i + (j * x + \<langle>js,xs\<rangle>)"
          by(simp add: algebra_simps)
        finally show ?thesis .
      qed
      then show ?thesis using Cons by (simp add:ring_distribs)
    qed
  qed
qed simp_all


lemma atoms_subset: "qfree f \<Longrightarrow> set(Z.atoms\<^sub>0(f::atom fm)) \<le> atoms f"
by (induct f) auto

(* copied from Amine *)
lemma \<beta>:
  "\<lbrakk> nqfree \<phi>;  \<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). hd_coeff_is1 a;
     \<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). divisor a dvd d; d > 0;
     \<not>(\<exists>j\<in>{0 .. d - 1}. \<exists>(i,ks) \<in> set(lbounds(Z.atoms\<^sub>0 \<phi>)).
         x = i - \<langle>ks,xs\<rangle> + j); Z.I \<phi> (x#xs) \<rbrakk>
  \<Longrightarrow> Z.I \<phi> ((x-d)#xs)"
proof(induct \<phi>)
  case (Atom a)
  show ?case
  proof (cases a)
    case (Le i js)
    show ?thesis
    proof (cases js)
      case Nil thus ?thesis using Le Atom by simp
    next
      case (Cons k ks) thus ?thesis using Le Atom
        by (auto simp:lbounds_def Ball_def split:if_split_asm) arith
    qed
  next
    case (Dvd m i js)
    show ?thesis
    proof (cases js)
      case Nil thus ?thesis using Dvd Atom by simp
    next
      case (Cons k ks)
      show ?thesis
      proof cases
        assume "k=0" thus ?thesis using Cons Dvd Atom by simp
      next
        assume "k\<noteq>0"
        hence "m dvd d" using Cons Dvd Atom by auto
        have "m dvd i + (x + \<langle>ks,xs\<rangle>) \<Longrightarrow> m dvd i + (x - d + \<langle>ks,xs\<rangle>)"
          (is "?L \<Longrightarrow> _")
        proof -
          assume ?L
          hence "m dvd i + (x + \<langle>ks,xs\<rangle>) - d"
            by (metis \<open>m dvd d\<close> dvd_diff)
          thus ?thesis by(simp add:algebra_simps)
        qed
        thus ?thesis using Atom Dvd Cons by(auto split:if_split_asm)
      qed
    qed
  next
    case (NDvd m i js)
    show ?thesis
    proof (cases js)
      case Nil thus ?thesis using NDvd Atom by simp
    next
      case (Cons k ks)
      show ?thesis
      proof cases
        assume "k=0" thus ?thesis using Cons NDvd Atom by simp
      next
        assume "k\<noteq>0"
        hence "m dvd d" using Cons NDvd Atom by auto
        have "m dvd i + (x - d + \<langle>ks,xs\<rangle>) \<Longrightarrow> m dvd i + (x + \<langle>ks,xs\<rangle>)"
          (is "?L \<Longrightarrow> _")
        proof -
          assume ?L
          hence "m dvd i + (x + \<langle>ks,xs\<rangle>) - d" by(simp add:algebra_simps)
          thus ?thesis by (metis \<open>m dvd d\<close> zdvd_zdiffD)
        qed
        thus ?thesis using Atom NDvd Cons by(auto split:if_split_asm)
      qed
    qed
  qed
qed force+


lemma periodic_finite_ex:
  assumes dpos: "(0::int) < d" and modd: "\<forall>x k. P x = P(x - k*d)"
  shows "(\<exists>x. P x) = (\<exists>j\<in>{0..d - 1}. P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x - (x div d)*d"
    by(simp add:mult_div_mod_eq [symmetric] ac_simps eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by simp
  have "P(x mod d)" using dpos P Pmod by simp
  moreover have "x mod d \<in> {0..d - 1}" using dpos by auto
  ultimately show ?RHS ..
qed auto

lemma cpmi_eq: "(0::int) < D \<Longrightarrow> (\<exists>z. \<forall>x. x < z \<longrightarrow> (P x = P1 x))
\<Longrightarrow> \<forall>x.\<not>(\<exists>j\<in>{0..D - 1}. \<exists>b\<in>B. P(b+j)) \<longrightarrow> P (x) \<longrightarrow> P (x - D) 
\<Longrightarrow> \<forall>x. \<forall>k. P1 x = P1(x-k*D)
\<Longrightarrow> (\<exists>x. P(x)) = ((\<exists>j\<in>{0..D - 1}. P1(j)) \<or> (\<exists>j\<in>{0..D - 1}. \<exists>b\<in>B. P(b+j)))"
apply(rule iffI)
prefer 2
apply(drule minusinfinity)
apply assumption+
apply(fastforce)
apply clarsimp
apply(subgoal_tac "\<And>k. 0\<le>k \<Longrightarrow> \<forall>x. P x \<longrightarrow> P (x - k*D)")
apply(frule_tac x = x and z=z in decr_lemma)
apply(subgoal_tac "P1(x - (\<bar>x - z\<bar> + 1) * D)")
prefer 2
apply(subgoal_tac "0 \<le> (\<bar>x - z\<bar> + 1)")
prefer 2 apply arith
 apply fastforce
apply(drule (1)  periodic_finite_ex)
apply blast
apply(blast dest:decr_mult_lemma)
done


theorem cp_thm:
  assumes nq: "nqfree \<phi>"
  and u: "\<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). hd_coeff_is1 a"
  and d: "\<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). divisor a dvd d"
  and dp: "d > 0"
  shows "(\<exists>x. Z.I \<phi> (x#xs)) =
   (\<exists>j\<in>{0..d - 1}. Z.I (inf\<^sub>- \<phi>) (j#xs) \<or>
   (\<exists>(i,ks) \<in> set(lbounds(Z.atoms\<^sub>0 \<phi>)). Z.I \<phi> ((i - \<langle>ks,xs\<rangle> + j) # xs)))"
  (is "(\<exists>x. ?P (x)) = (\<exists> j\<in> ?D. ?M j \<or> (\<exists>(i,ks)\<in> ?B. ?P (?I i ks + j)))")
proof-
  from min_inf[OF nq u] have th: "\<exists>z.\<forall>x<z. ?P x = ?M x" by blast
  let ?B' = "{?I i ks |i ks. (i,ks) \<in> ?B}"
  have BB': "(\<exists>j\<in>?D. \<exists>(i,ks)\<in> ?B. ?P (?I i ks + j)) = (\<exists>j \<in> ?D. \<exists>b \<in> ?B'. ?P (b + j))" by auto
  hence th2: "\<forall> x. \<not> (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P ((b + j))) \<longrightarrow> ?P (x) \<longrightarrow> ?P ((x - d))"
    using \<beta>[OF nq u d dp, of _ xs] by(simp add:Bex_def) metis
  from min_inf_repeats[OF nq d]
  have th3: "\<forall> x k. ?M x = ?M (x-k*d)" by simp
  from cpmi_eq[OF dp th th2 th3] BB' show ?thesis by simp blast
qed

(* end of Amine *)

lemma qfree_min_inf[simp]: "qfree \<phi> \<Longrightarrow> qfree (inf\<^sub>- \<phi>)"
by (induct \<phi> rule:min_inf.induct) simp_all

lemma I_qe_cooper\<^sub>1:
assumes norm: "\<forall>a\<in>atoms \<phi>. divisor a \<noteq> 0"
and hd: "\<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). hd_coeff_is1 a" and "nqfree \<phi>"
shows "Z.I (qe_cooper\<^sub>1 \<phi>) xs = (\<exists>x. Z.I \<phi> (x#xs))"
proof -
  let ?as = "Z.atoms\<^sub>0 \<phi>"
  let ?d = "zlcms(map divisor ?as)"
  have "?d > 0" using norm atoms_subset[of \<phi>] \<open>nqfree \<phi>\<close>
    by(fastforce intro:zlcms_pos)
  have alld: "\<forall>a\<in>set(Z.atoms\<^sub>0 \<phi>). divisor a dvd ?d" by(simp add:dvd_zlcms)
  from cp_thm[OF \<open>nqfree \<phi>\<close> hd alld \<open>?d>0\<close>]
  show ?thesis using \<open>nqfree \<phi>\<close>
    by (simp add:qe_cooper\<^sub>1_def I_subst[symmetric] split_def algebra_simps) blast
qed

lemma divisor_hd_coeff1_neq0:
  "qfree \<phi> \<Longrightarrow> a \<in> atoms \<phi> \<Longrightarrow> divisor a \<noteq> 0 \<Longrightarrow>
   divisor (hd_coeff1 (zlcms (map hd_coeff (Z.atoms\<^sub>0 \<phi>))) a) \<noteq> 0"
apply (case_tac a)

apply simp
apply(rename_tac list) apply(case_tac list) apply simp apply(simp split:if_split_asm)

apply simp
apply(rename_tac list)apply(case_tac list) apply simp
apply(clarsimp split:if_split_asm)
apply(hypsubst_thin)
apply(subgoal_tac "a \<in> set(map hd_coeff (Z.atoms\<^sub>0 \<phi>))")
 apply(subgoal_tac "\<forall>i\<in>set(map hd_coeff (Z.atoms\<^sub>0 \<phi>)). i \<noteq> 0")
  apply (metis dvd_zlcms mult_eq_0_iff dvd_mult_div_cancel zlcms0_iff)
 apply (simp add:set_atoms0_iff)
apply(fastforce simp:image_def set_atoms0_iff Bex_def)

apply simp
apply(rename_tac list) apply(case_tac list) apply simp
apply(clarsimp split:if_split_asm)
apply(hypsubst_thin)
apply(subgoal_tac "a \<in> set(map hd_coeff (Z.atoms\<^sub>0 \<phi>))")
 apply(subgoal_tac "\<forall>i\<in>set(map hd_coeff (Z.atoms\<^sub>0 \<phi>)). i \<noteq> 0")
  apply (metis dvd_zlcms mult_eq_0_iff dvd_mult_div_cancel zlcms0_iff)
 apply (simp add:set_atoms0_iff)
apply(fastforce simp:image_def set_atoms0_iff Bex_def)
done

lemma hd_coeff_is1_hd_coeff1:
  "hd_coeff (hd_coeff1 m a) \<noteq> 0 \<longrightarrow> hd_coeff_is1 (hd_coeff1 m a)"
by (induct a rule: hd_coeff1.induct) (simp_all add:zsgn_def)

lemma I_cooper1_hd_coeffs1: "Z.normal \<phi> \<Longrightarrow> nqfree \<phi>
       \<Longrightarrow> Z.I (qe_cooper\<^sub>1(hd_coeffs1 \<phi>)) xs = (\<exists>x. Z.I \<phi> (x # xs))"
apply(simp add:Z.normal_def)
apply(subst I_qe_cooper\<^sub>1)
   apply(clarsimp simp:hd_coeffs1_def image_def set_atoms0_iff divisor_hd_coeff1_neq0)
  apply (clarsimp simp:hd_coeffs1_def qfree_map_fm set_atoms0_iff
                     hd_coeff_is1_hd_coeff1)
 apply(simp add:hd_coeffs1_def nqfree_map_fm)
apply(simp add: I_hd_coeffs1)
done

definition "qe_cooper = Z.lift_nnf_qe (qe_cooper\<^sub>1 \<circ> hd_coeffs1)"

lemma qfree_cooper1_hd_coeffs1: "qfree \<phi> \<Longrightarrow> qfree (qe_cooper\<^sub>1 (hd_coeffs1 \<phi>))"
by(auto simp:qe_cooper\<^sub>1_def hd_coeffs1_def qfree_map_fm
        intro!: qfree_or qfree_and qfree_list_disj qfree_min_inf)


lemma normal_min_inf: "Z.normal \<phi> \<Longrightarrow> Z.normal(inf\<^sub>- \<phi>)"
by(induct \<phi> rule:min_inf.induct) simp_all

lemma normal_cooper1: "Z.normal \<phi> \<Longrightarrow> Z.normal(qe_cooper\<^sub>1 \<phi>)"
by(simp add:qe_cooper\<^sub>1_def Logic.or_def Z.normal_map_fm normal_min_inf split_def)

lemma normal_hd_coeffs1: "qfree \<phi> \<Longrightarrow> Z.normal \<phi> \<Longrightarrow> Z.normal(hd_coeffs1 \<phi>)"
by(auto simp: hd_coeffs1_def image_def set_atoms0_iff
              divisor_hd_coeff1_neq0 Z.normal_def)

theorem I_cooper: "Z.normal \<phi> \<Longrightarrow>  Z.I (qe_cooper \<phi>) xs = Z.I \<phi> xs"
by(simp add:qe_cooper_def Z.I_lift_nnf_qe_normal qfree_cooper1_hd_coeffs1 I_cooper1_hd_coeffs1 normal_cooper1 normal_hd_coeffs1)

theorem qfree_cooper: "qfree (qe_cooper \<phi>)"
by(simp add:qe_cooper_def Z.qfree_lift_nnf_qe qfree_cooper1_hd_coeffs1)

end
