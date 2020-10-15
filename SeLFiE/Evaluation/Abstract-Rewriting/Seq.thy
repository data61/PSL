(*  Title:       Infinite Sequences
    Author:      Christian Sternagel <c-sterna@jaist.ac.jp>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2012 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
section \<open>Infinite Sequences\<close>
theory Seq
imports
  Main
  "HOL-Library.Infinite_Set"
begin

text \<open>Infinite sequences are represented by functions of type @{typ "nat \<Rightarrow> 'a"}.\<close>
type_synonym 'a seq = "nat \<Rightarrow> 'a"


subsection \<open>Operations on Infinite Sequences\<close>

text \<open>An infinite sequence is \emph{linked} by a binary predicate @{term P} if every two
consecutive elements satisfy it. Such a sequence is called a \emph{@{term P}-chain}.\<close>
abbreviation (input) chainp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>'a seq \<Rightarrow> bool" where
  "chainp P S \<equiv> \<forall>i. P (S i) (S (Suc i))"

text \<open>Special version for relations.\<close>
abbreviation (input) chain :: "'a rel \<Rightarrow> 'a seq \<Rightarrow> bool" where
  "chain r S \<equiv> chainp (\<lambda>x y. (x, y) \<in> r) S"

text \<open>Extending a chain at the front.\<close>
lemma cons_chainp:
  assumes "P x (S 0)" and "chainp P S"
  shows "chainp P (case_nat x S)" (is "chainp P ?S")
proof
  fix i show "P (?S i) (?S (Suc i))" using assms by (cases i) simp_all
qed

text \<open>Special version for relations.\<close>
lemma cons_chain:
  assumes "(x, S 0) \<in> r" and "chain r S" shows "chain r (case_nat x S)"
  using cons_chainp[of "\<lambda>x y. (x, y) \<in> r", OF assms] .

text \<open>A chain admits arbitrary transitive steps.\<close>
lemma chainp_imp_relpowp:
  assumes "chainp P S" shows "(P^^j) (S i) (S (i + j))"
proof (induct "i + j" arbitrary: j)
  case (Suc n) thus ?case using assms by (cases j) auto
qed simp

lemma chain_imp_relpow:
  assumes "chain r S" shows "(S i, S (i + j)) \<in> r^^j"
proof (induct "i + j" arbitrary: j)
  case (Suc n) thus ?case using assms by (cases j) auto
qed simp

lemma chainp_imp_tranclp:
  assumes "chainp P S" and "i < j" shows "P^++ (S i) (S j)"
proof -
  from less_imp_Suc_add[OF assms(2)] obtain n where "j = i + Suc n" by auto
  with chainp_imp_relpowp[of P S "Suc n" i, OF assms(1)]
    show ?thesis
      unfolding trancl_power[of "(S i, S j)", to_pred]
      by force
qed

lemma chain_imp_trancl:
  assumes "chain r S" and "i < j" shows "(S i, S j) \<in> r^+"
proof -
  from less_imp_Suc_add[OF assms(2)] obtain n where "j = i + Suc n" by auto
  with chain_imp_relpow[OF assms(1), of i "Suc n"]
    show ?thesis unfolding trancl_power by force
qed

text \<open>A chain admits arbitrary reflexive and transitive steps.\<close>
lemma chainp_imp_rtranclp:
  assumes "chainp P S" and "i \<le> j" shows "P^** (S i) (S j)"
proof -
  from assms(2) obtain n where "j = i + n" by (induct "j - i" arbitrary: j) force+
  with chainp_imp_relpowp[of P S, OF assms(1), of n i] show ?thesis
    by (simp add: relpow_imp_rtrancl[of "(S i, S (i + n))", to_pred])
qed

lemma chain_imp_rtrancl:
  assumes "chain r S" and "i \<le> j" shows "(S i, S j) \<in> r^*"
proof -
  from assms(2) obtain n where "j = i + n" by (induct "j - i" arbitrary: j) force+
  with chain_imp_relpow[OF assms(1), of i n] show ?thesis by (simp add: relpow_imp_rtrancl)
qed

text \<open>If for every @{term i} there is a later index @{term "f i"} such that the
corresponding elements satisfy the predicate @{term P}, then there is a @{term P}-chain.\<close>
lemma stepfun_imp_chainp':
  assumes "\<forall>i\<ge>n::nat. f i \<ge> i \<and> P (S i) (S (f i))"
  shows "chainp P (\<lambda>i. S ((f ^^ i) n))" (is "chainp P ?T")
proof
  fix i
  from assms have "(f ^^ i) n \<ge> n" by (induct i) auto
  with assms[THEN spec[of _ "(f ^^ i) n"]]
    show "P (?T i) (?T (Suc i))" by simp
qed

lemma stepfun_imp_chainp:
  assumes "\<forall>i\<ge>n::nat. f i > i \<and> P (S i) (S (f i))"
  shows "chainp P (\<lambda>i. S ((f ^^ i) n))" (is "chainp P ?T")
  using stepfun_imp_chainp'[of n f P S] and assms by force

lemma subchain:
  assumes "\<forall>i::nat>n. \<exists>j>i. P (f i) (f j)"
  shows "\<exists>\<phi>. (\<forall>i j. i < j \<longrightarrow> \<phi> i < \<phi> j) \<and> (\<forall>i. P (f (\<phi> i)) (f (\<phi> (Suc i))))"
proof -
  from assms have "\<forall>i\<in>{i. i > n}. \<exists>j>i. P (f i) (f j)" by simp
  from bchoice [OF this] obtain g
    where *: "\<forall>i>n. g i > i"
    and **: "\<forall>i>n. P (f i) (f (g i))" by auto
  define \<phi> where [simp]: "\<phi> i = (g ^^ i) (Suc n)" for i
  from * have ***: "\<And>i. \<phi> i > n" by (induct_tac i) auto
  then have "\<And>i. \<phi> i < \<phi> (Suc i)" using * by (induct_tac i) auto
  then have "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j" by (rule lift_Suc_mono_less)
  moreover have "\<And>i. P (f (\<phi> i)) (f (\<phi> (Suc i)))" using ** and *** by simp
  ultimately show ?thesis by blast
qed

text \<open>If for every @{term i} there is a later index @{term j} such that the
corresponding elements satisfy the predicate @{term P}, then there is a @{term P}-chain.\<close>
lemma steps_imp_chainp':
  assumes "\<forall>i\<ge>n::nat. \<exists>j\<ge>i. P (S i) (S j)" shows "\<exists>T. chainp P T"
proof -
  from assms have "\<forall>i\<in>{i. i \<ge> n}. \<exists>j\<ge>i. P (S i) (S j)" by auto
  from bchoice [OF this] (*choice could be replaced by an application of Least_Enum.infinitely_many2*)
    obtain f where "\<forall>i\<ge>n. f i \<ge> i \<and> P (S i) (S (f i))" by auto
  from stepfun_imp_chainp'[of n f P S, OF this] show ?thesis by fast
qed

lemma steps_imp_chainp:
  assumes "\<forall>i\<ge>n::nat. \<exists>j>i. P (S i) (S j)" shows "\<exists>T. chainp P T"
  using steps_imp_chainp' [of n P S] and assms by force


subsection \<open>Predicates on Natural Numbers\<close>

text \<open>If some property holds for infinitely many natural numbers, obtain
an index function that points to these numbers in increasing order.\<close>

locale infinitely_many =
  fixes p :: "nat \<Rightarrow> bool"
  assumes infinite: "INFM j. p j"
begin

lemma inf: "\<exists>j\<ge>i. p j" using infinite[unfolded INFM_nat_le] by auto

fun index :: "nat seq" where
  "index 0 = (LEAST n. p n)"
| "index (Suc n) = (LEAST k. p k \<and> k > index n)"

lemma index_p: "p (index n)"
proof (induct n)
  case 0
  from inf obtain j where "p j" by auto
  with LeastI[of p j] show ?case by auto
next
  case (Suc n)
  from inf obtain k where "k \<ge> Suc (index n) \<and> p k" by auto
  with LeastI[of "\<lambda> k. p k \<and> k > index n" k] show ?case by auto
qed

lemma index_ordered: "index n < index (Suc n)"
proof -
  from inf obtain k where "k \<ge> Suc (index n) \<and> p k" by auto
  with LeastI[of "\<lambda> k. p k \<and> k > index n" k] show ?thesis by auto
qed

lemma index_not_p_between:
  assumes i1: "index n < i"
    and i2: "i < index (Suc n)"
  shows "\<not> p i"
proof -
  from not_less_Least[OF i2[simplified]] i1 show ?thesis by auto
qed

lemma index_ordered_le:
  assumes "i \<le> j" shows "index i \<le> index j"
proof - 
  from assms have "j = i + (j - i)" by auto
  then obtain k where j: "j = i + k" by auto
  have "index i \<le> index (i + k)"
  proof (induct k)
    case (Suc k)
    with index_ordered[of "i + k"]
    show ?case by auto
  qed simp
  thus ?thesis unfolding j .
qed

lemma index_surj:
  assumes "k \<ge> index l"
  shows "\<exists>i j. k = index i + j \<and> index i + j < index (Suc i)"
proof -
  from assms have "k = index l + (k - index l)" by auto
  then obtain u where k: "k = index l + u" by auto
  show ?thesis unfolding k
  proof (induct u)
    case 0
    show ?case
      by (intro exI conjI, rule refl, insert index_ordered[of l], simp)
  next
    case (Suc u)
    then obtain i j
      where lu: "index l + u = index i + j" and lt: "index i + j < index (Suc i)" by auto
    hence "index l + u < index (Suc i)" by auto
    show ?case
    proof (cases "index l + (Suc u) = index (Suc i)")
      case False
      show ?thesis
        by (rule exI[of _ i], rule exI[of _ "Suc j"], insert lu lt False, auto)
    next
      case True
      show ?thesis
        by (rule exI[of _ "Suc i"], rule exI[of _ 0], insert True index_ordered[of "Suc i"], auto)
    qed
  qed
qed

lemma index_ordered_less:
  assumes "i < j" shows "index i < index j"
proof - 
  from assms have "Suc i \<le> j" by auto
  from index_ordered_le[OF this]
  have "index (Suc i) \<le> index j" .
  with index_ordered[of i] show ?thesis by auto
qed

lemma index_not_p_start: assumes i: "i < index 0" shows "\<not> p i"
proof -
  from i[simplified index.simps] have "i < Least p" .
  from not_less_Least[OF this] show ?thesis .
qed

end


subsection \<open>Assembling Infinite Words from Finite Words\<close>

text \<open>Concatenate infinitely many non-empty words to an infinite word.\<close>

fun inf_concat_simple :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)" where
  "inf_concat_simple f 0 = (0, 0)"
| "inf_concat_simple f (Suc n) = (
    let (i, j) = inf_concat_simple f n in 
    if Suc j < f i then (i, Suc j)
    else (Suc i, 0))"

lemma inf_concat_simple_add:
  assumes ck: "inf_concat_simple f k = (i, j)"
    and jl: "j + l < f i"
  shows "inf_concat_simple f (k + l) = (i,j + l)"
using jl
proof (induct l)
  case 0
  thus ?case using ck by simp
next
  case (Suc l)
  hence c: "inf_concat_simple f (k + l) = (i, j+ l)" by auto
  show ?case 
    by (simp add: c, insert Suc(2), auto)
qed

lemma inf_concat_simple_surj_zero: "\<exists> k. inf_concat_simple f k = (i,0)"
proof (induct i)
  case 0
  show ?case 
    by (rule exI[of _ 0], simp)
next
  case (Suc i)
  then obtain k where ck: "inf_concat_simple f k = (i,0)" by auto
  show ?case
  proof (cases "f i")
    case 0
    show ?thesis
      by (rule exI[of _ "Suc k"], simp add: ck 0)
  next
    case (Suc n)
    hence "0 + n < f i" by auto
    from inf_concat_simple_add[OF ck, OF this] Suc
    show ?thesis
      by (intro exI[of _ "k + Suc n"], auto)
  qed
qed

lemma inf_concat_simple_surj:
  assumes "j < f i"
  shows "\<exists> k. inf_concat_simple f k = (i,j)"
proof -
  from assms have j: "0 + j < f i" by auto
  from inf_concat_simple_surj_zero obtain k where "inf_concat_simple f k = (i,0)" by auto
  from inf_concat_simple_add[OF this, OF j] show ?thesis by auto
qed

lemma inf_concat_simple_mono:
  assumes "k \<le> k'" shows "fst (inf_concat_simple f k) \<le> fst (inf_concat_simple f k')"
proof -
  from assms have "k' = k + (k' - k)" by auto
  then obtain l where k': "k' = k + l" by auto
  show ?thesis  unfolding k'
  proof (induct l)
    case (Suc l)
    obtain i j where ckl: "inf_concat_simple f (k+l) = (i,j)" by (cases "inf_concat_simple f (k+l)", auto)
    with Suc have "fst (inf_concat_simple f k) \<le> i" by auto
    also have "... \<le> fst (inf_concat_simple f (k + Suc l))"
      by (simp add: ckl)
    finally show ?case .
  qed simp
qed


(* inf_concat assembles infinitely many (possibly empty) words to an infinite word *)
fun inf_concat :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "inf_concat n 0 = (LEAST j. n j > 0, 0)"
| "inf_concat n (Suc k) = (let (i, j) = inf_concat n k in (if Suc j < n i then (i, Suc j) else (LEAST i'. i' > i \<and> n i' > 0, 0)))"

lemma inf_concat_bounds:
  assumes inf: "INFM i. n i > 0"
    and res: "inf_concat n k = (i,j)"
  shows "j < n i"
proof (cases k)
  case 0
  with res have i: "i = (LEAST i. n i > 0)" and j: "j = 0" by auto
  from inf[unfolded INFM_nat_le] obtain i' where i': "0 < n i'" by auto
  have "0 < n (LEAST i. n i > 0)" 
    by (rule LeastI, rule i')
  with i j show ?thesis by auto
next
  case (Suc k')
  obtain i' j' where res': "inf_concat n k' = (i',j')" by force
  note res = res[unfolded Suc inf_concat.simps res' Let_def split]
  show ?thesis 
  proof (cases "Suc j' < n i'")
    case True
    with res show ?thesis by auto
  next
    case False
    with res have i: "i = (LEAST f. i' < f \<and> 0 < n f)" and j: "j = 0" by auto
    from inf[unfolded INFM_nat] obtain f where f: "i' < f \<and> 0 < n f" by auto
    have "0 < n (LEAST f. i' < f \<and> 0 < n f)"
      using LeastI[of "\<lambda> f. i' < f \<and> 0 < n f", OF f]
      by auto
    with i j show ?thesis by auto
  qed
qed

lemma inf_concat_add:
  assumes res: "inf_concat n k = (i,j)"
    and j: "j + m < n i"
  shows "inf_concat n (k + m) = (i,j+m)"
  using j
proof (induct m)
  case 0 show ?case using res by auto
next
  case (Suc m)
  hence "inf_concat n (k + m) = (i, j+m)" by auto
  with Suc(2)
  show ?case by auto
qed

lemma inf_concat_step:
  assumes res: "inf_concat n k = (i,j)"
    and j: "Suc (j + m) = n i"
  shows "inf_concat n (k + Suc m) = (LEAST i'. i' > i \<and> 0 < n i', 0)"
proof -
  from j have "j + m < n i" by auto
  note res = inf_concat_add[OF res, OF this]
  show ?thesis by (simp add: res j)
qed

lemma inf_concat_surj_zero:
  assumes "0 < n i"
  shows "\<exists>k. inf_concat n k = (i, 0)"
proof -
  {
    fix l
    have "\<forall> j. j < l \<and> 0 < n j \<longrightarrow> (\<exists> k. inf_concat n k = (j,0))"
    proof (induct l)
      case 0
      thus ?case by auto
    next
      case (Suc l)
      show ?case
      proof (intro allI impI, elim conjE)
        fix j
        assume j: "j < Suc l" and nj: "0 < n j"
        show "\<exists> k. inf_concat n k = (j, 0)"
        proof (cases "j < l")
          case True
          from Suc[THEN spec[of _ j]] True nj show ?thesis by auto
        next
          case False
          with j have j: "j = l" by auto
          show ?thesis
          proof (cases "\<exists> j'. j' < l \<and> 0 < n j'")
            case False
            have l: "(LEAST i. 0 < n i) = l"
            proof (rule Least_equality, rule nj[unfolded j])
              fix l'
              assume "0 < n l'"
              with False have "\<not> l' < l" by auto
              thus "l \<le> l'" by auto
            qed
            show ?thesis
              by (rule exI[of _ 0], simp add: l j)
          next
            case True
            then obtain lll where lll: "lll < l" and nlll: "0 < n lll" by auto 
            then obtain ll where l: "l = Suc ll" by (cases l, auto)   
            from lll l have lll: "lll = ll - (ll - lll)" by auto
            let ?l' = "LEAST d. 0 < n (ll - d)"
            have nl': "0 < n (ll - ?l')"
            proof (rule LeastI)
              show "0 < n (ll - (ll - lll))" using lll nlll by auto
            qed
            with Suc[THEN spec[of _ "ll - ?l'"]] obtain k where k:
              "inf_concat n k = (ll - ?l',0)" unfolding l by auto
            from nl' obtain off where off: "Suc (0 + off) = n (ll - ?l')" by (cases "n (ll - ?l')", auto)
            from inf_concat_step[OF k, OF off]
            have id: "inf_concat n (k + Suc off) = (LEAST i'. ll - ?l' < i' \<and> 0 < n i',0)" (is "_ = (?l,0)") .
            have ll: "?l = l" unfolding l
            proof (rule Least_equality)
              show "ll - ?l' < Suc ll \<and> 0 < n (Suc ll)" using nj[unfolded j l] by simp
            next
              fix l'
              assume ass: "ll - ?l' < l' \<and> 0 < n l'"
              show "Suc ll \<le> l'" 
              proof (rule ccontr)
                assume not: "\<not> ?thesis"
                hence "l' \<le> ll" by auto
                hence "ll = l' + (ll - l')" by auto
                then obtain k where ll: "ll = l' + k" by auto
                from ass have "l' + k - ?l' < l'" unfolding ll by auto
                hence kl': "k < ?l'" by auto
                have "0 < n (ll - k)" using ass unfolding ll by simp
                from Least_le[of "\<lambda> k. 0 < n (ll - k)", OF this] kl'
                show False by auto
              qed
            qed            
            show ?thesis unfolding j
              by (rule exI[of _ "k + Suc off"], unfold id ll, simp)
          qed
        qed
      qed
    qed
  }
  with assms show ?thesis by auto
qed

lemma inf_concat_surj:
  assumes j: "j < n i"
  shows "\<exists>k. inf_concat n k = (i, j)"
proof -
  from j have "0 < n i" by auto
  from inf_concat_surj_zero[of n, OF this]
  obtain k where "inf_concat n k = (i,0)" by auto
  from inf_concat_add[OF this, of j] j
  show ?thesis by auto
qed

lemma inf_concat_mono:
  assumes inf: "INFM i. n i > 0"
    and resk: "inf_concat n k = (i, j)"
    and reskp: "inf_concat n k' = (i', j')"
    and lt: "i < i'"
  shows "k < k'"
proof -
  note bounds = inf_concat_bounds[OF inf]
  {
    assume "k' \<le> k"
    hence "k = k' + (k - k')" by auto
    then obtain l where k: "k = k' + l" by auto
    have "i' \<le> fst (inf_concat n (k' + l))" 
    proof (induct l)
      case 0
      with reskp show ?case by auto
    next      
      case (Suc l)
      obtain i'' j'' where l: "inf_concat n (k' + l) = (i'',j'')" by force
      with Suc have one: "i' \<le> i''" by auto
      from bounds[OF l] have j'': "j'' < n i''" by auto
      show ?case 
      proof (cases "Suc j'' < n i''")
        case True
        show ?thesis by (simp add: l True one)
      next
        case False
        let ?i = "LEAST i'. i'' < i' \<and> 0 < n i'"
        from inf[unfolded INFM_nat] obtain k where "i'' < k \<and> 0 < n k" by auto
        from LeastI[of "\<lambda> k. i'' < k \<and> 0 < n k", OF this]
        have "i'' < ?i" by auto
        with one show ?thesis by (simp add: l False)
      qed
    qed      
    with resk k lt have False by auto
  }
  thus ?thesis by arith
qed

lemma inf_concat_Suc:
  assumes inf: "INFM i. n i > 0"
    and f: "\<And> i. f i (n i) = f (Suc i) 0"
    and resk: "inf_concat n k = (i, j)"
    and ressk: "inf_concat n (Suc k) = (i', j')"
  shows "f i' j' = f i (Suc j)"
proof - 
  note bounds = inf_concat_bounds[OF inf]
  from bounds[OF resk] have j: "j < n i" .
  show ?thesis
  proof (cases "Suc j < n i")
    case True
    with ressk resk
    show ?thesis by simp
  next
    case False
    let ?p = "\<lambda> i'. i < i' \<and> 0 < n i'"
    let ?i' = "LEAST i'. ?p i'"
    from False j have id: "Suc (j + 0) = n i" by auto
    from inf_concat_step[OF resk, OF id] ressk
    have i': "i' = ?i'" and j': "j' = 0" by auto
    from id have j: "Suc j = n i" by simp
    from inf[unfolded INFM_nat] obtain k where "?p k" by auto
    from LeastI[of ?p, OF this] have "?p ?i'" .
    hence "?i' = Suc i + (?i' - Suc i)" by simp
    then obtain d where ii': "?i' = Suc i + d" by auto
    from not_less_Least[of _ ?p, unfolded ii'] have d': "\<And> d'. d' < d \<Longrightarrow> n (Suc i + d') = 0" by auto
    have "f (Suc i) 0 = f ?i' 0" unfolding ii' using d'
    proof (induct d)
      case 0
      show ?case by simp
    next
      case (Suc d)
      hence "f (Suc i) 0 = f (Suc i + d) 0" by auto
      also have "... = f (Suc (Suc i + d)) 0"
        unfolding f[symmetric]
        using Suc(2)[of d] by simp
      finally show ?case by simp
    qed
    thus ?thesis unfolding i' j' j f by simp
  qed
qed

end

