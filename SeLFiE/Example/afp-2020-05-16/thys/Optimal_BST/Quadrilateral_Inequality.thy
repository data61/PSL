section \<open>Quadrangle Inequality\<close>

theory Quadrilateral_Inequality
imports Main
begin

(* did not use @{const is_arg_min} because no benefit *)
definition is_arg_min_on :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_arg_min_on f S x = (x \<in> S \<and> (\<forall>y \<in> S. f x \<le> f y))"

definition Args_min_on :: "(int \<Rightarrow> ('b::linorder)) \<Rightarrow> int set \<Rightarrow> int set" where
"Args_min_on f I = {k. is_arg_min_on f I k}"

lemmas Args_min_simps = Args_min_on_def is_arg_min_on_def

lemma is_arg_min_on_antimono: fixes f :: "_ \<Rightarrow> _::order"
shows "\<lbrakk> is_arg_min_on f S x; f y \<le> f x; y \<in> S \<rbrakk> \<Longrightarrow> is_arg_min_on f S y"
by (metis antisym is_arg_min_on_def)

lemma ex_is_arg_min_on_if_finite: fixes f :: "'a \<Rightarrow> 'b :: linorder"
shows "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. is_arg_min_on f S x"
unfolding is_arg_min_on_def using ex_min_if_finite[of "f ` S"] by fastforce


locale QI =
  fixes c_k :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat"
  fixes c :: "int \<Rightarrow> int \<Rightarrow> nat"
  and w :: "int \<Rightarrow> int \<Rightarrow> nat"
  assumes QI_w: "\<lbrakk>i \<le> i'; i' < j; j \<le> j'\<rbrakk> \<Longrightarrow>
    w i j + w i' j'\<le> w i' j + w i j'"
  assumes monotone_w: "\<lbrakk>i \<le> i'; i' < j; j \<le> j'\<rbrakk> \<Longrightarrow> w i' j \<le> w i j'"
  assumes c_def: "i < j \<Longrightarrow> c i j = Min ((c_k i j) ` {i+1..j})"
  assumes c_k_def: "\<lbrakk> i < j;  k \<in> {i+1..j} \<rbrakk> \<Longrightarrow>
    c_k i j k = w i j + c i (k-1) + c k j"
begin

abbreviation "mins i j \<equiv> Args_min_on (c_k i j) {i+1..j}"

definition "K i j \<equiv> (if i = j then i else Max (mins i j))"

lemma c_def_rec:
  "i < j \<Longrightarrow> c i j = Min ((\<lambda>k. c i (k-1) + c k j + w i j) ` {i+1..j})"
using c_def c_k_def by (auto simp: algebra_simps image_def)

lemma mins_subset: "mins i j \<subseteq> {i+1..j}"
by (auto simp: Args_min_simps)

lemma mins_nonempty: "i < j \<Longrightarrow> mins i j \<noteq> {}"
using ex_is_arg_min_on_if_finite[OF finite_atLeastAtMost_int, of "i+1" j "c_k i j"]
by(auto simp: Args_min_simps)

lemma finite_mins: "finite(mins i j)"
by(simp add: finite_subset[OF mins_subset])

lemma is_arg_min_on_Min:
assumes "finite A" "is_arg_min_on f A a" shows "Min (f ` A) = f a" 
proof -
  from assms(2) have "f ` A \<noteq> {}"
    by (fastforce simp: is_arg_min_on_def)
  thus ?thesis using assms by (simp add: antisym is_arg_min_on_def)
qed

lemma c_k_with_K: "i < j \<Longrightarrow> c i j = c_k i j (K i j)"
using Max_in[of "mins i j"] finite_mins[of i j] mins_nonempty[of i j]
  is_arg_min_on_Min[of "{i+1..j}" "c_k i j"]
by (auto simp: Args_min_simps c_def K_def)

lemma K_subset: assumes "i \<le> j" shows "K i j \<in> {i..j}" using mins_subset K_def
proof cases
  assume "i = j"
  thus ?thesis 
    using K_def by auto
next
  assume "\<not>i = j"
  hence "K i j \<in> {i+1..j}" using mins_subset K_def \<open>i \<le> j\<close>
    by (metis Max_in finite_mins less_le mins_nonempty subsetCE)

  thus ?thesis  by auto
qed

lemma lemma_2:
  "\<lbrakk> l = nat (j'- i);  i \<le> i';  i' \<le> j;  j \<le> j' \<rbrakk>
   \<Longrightarrow> c i j + c i' j' \<le> c i j' + c i' j"
proof(induction l arbitrary: i i' j j' rule:less_induct)
  case (less l)
  show ?case 
  proof cases
    assume "l \<le> 1"
    hence "i = i' \<or> j = j'" using less.prems by linarith
    thus ?case by auto
  next
    assume "\<not> l \<le> 1"
    show ?case
    proof cases
      assume "i \<ge> i'" thus ?thesis using less.prems by auto
    next
      assume "\<not>i \<ge> i'"
      hence "i < i'" by simp
      show ?thesis 
      proof cases
        assume "j \<ge> j'" thus ?thesis using less.prems by auto
      next
        assume "\<not> j \<ge> j'"
        show ?thesis 
        (*-----------------------case 1: i' = j --------------------------------------------------*)
        proof cases 
          assume "i' = j"
          let ?k = "K i j'"
          have "?k \<in> {i+1..j'}" 
            unfolding K_def
            using mins_subset Max_in[OF finite_mins mins_nonempty] less.prems \<open>\<not> i' \<le> i\<close>
            by (smt subsetCE)
          show ?thesis
          (*---------------------case 1.1: i' = j \<and> k \<le> j ----------------------------------------*)
          proof cases
            assume "?k \<le> j"

            have a: "c i j \<le> w i j + c i (?k-1) + c ?k j"
            proof -
              have "c i j = Min ((\<lambda>k. c i (k-1) + c k j + w i j) ` {i+1..j})"
                using c_def_rec \<open>\<not> i' \<le> i\<close> \<open>i' = j\<close> by auto
              also have "... \<le> c i (?k-1) + c ?k j + w i j"
                using \<open>?k\<in>{i+1..j'}\<close> \<open>?k \<le> j\<close> by simp
              finally show ?thesis by simp
            qed

            have "nat (j' - ?k) < l" using \<open>?k\<in>{i+1..j'}\<close> less.prems by simp
            hence b: "c ?k j + c j j' \<le> c ?k j' + c j j"
              using \<open>?k \<le> j\<close> less.prems
                less.IH [where i = ?k and i' = j and j = j and j' = j', OF _ refl]
              by auto

            have "c i j + c i' j' = c i j + c j j'" by (simp add: \<open>i' = j\<close>)
            also have "...\<le> w i j + c i (?k-1) + c ?k j + c j j'"
              using a by auto
            also have "... \<le> w i j'+ c i (?k-1) + c ?k j + c j j'"
              using less.prems monotone_w \<open>i < i'\<close> by simp
            also have "... \<le> w i j'+ c i (?k-1) + c ?k j' + c j j"
              using b by auto
            also have "... = c i j' + c j j" using \<open>?k\<in>{i+1..j'}\<close>
              by(simp add: c_k_def c_k_with_K)
            finally show ?thesis by(simp add: \<open>i' = j\<close>)
          next
          (*---------------------case 1.2: i' = j \<and> k \<ge> j ----------------------------------------*)
            assume "\<not> ?k \<le> j"
            hence "?k \<in> {j+1..j'}" using \<open>?k \<in> {i+1..j'}\<close> by auto
            have a: "c j j' \<le> w j j' + c j (?k-1) + c ?k j'"
            proof -
             have "c j j' = Min ((\<lambda>k. c j (k-1) + c k j' + w j j') ` {j+1..j'})"
               using c_def_rec \<open>\<not> j' \<le> j\<close> by auto
             also have "... \<le> c j (?k-1) + c ?k j' + w j j'"
              using \<open>?k \<in> {j+1..j'}\<close> by simp
             finally show "c j j' \<le> w j j' + c j (?k-1) + c ?k j'" by simp
            qed

            have "nat ((?k-1) -i) < l" using \<open>?k \<in> {i+1..j'}\<close> less.prems by simp
            hence b: "c i j + c j (?k-1) \<le> c i (?k-1) + c j j"
              using less.prems \<open>\<not> ?k \<le> j\<close>
                less.IH[where i=i and i'=j and j=j and j'="(?k-1)", OF _ refl]
              by auto

            have "c i j + c i' j' = c i j + c j j'" by(simp add: \<open>i' = j\<close>)
            also have "... \<le> w j j' + c j (?k-1) + c ?k j' + c i j"
              using a by simp
            also have "... \<le> w i j'+ c j (?k-1) + c ?k j' + c i j"
              using less.prems monotone_w \<open>?k \<in> {j+1..j'}\<close> by simp
            also have "... \<le> w i j'+ c i (?k-1) + c ?k j' + c j j"
              using b by simp
            also have "... \<le> c i j' + c j j"
              using \<open>?k\<in>{i+1..j'}\<close> by (simp add: c_k_def c_k_with_K)
            finally show ?thesis by(simp add: \<open>i' = j\<close>)
          qed
        next
          (*---------------------case 2 i' \<noteq> j ---------------------------------------------------*)
          assume "i' \<noteq> j"
          let ?y = "K i' j"
          let ?z = "K i j'"
          have "?y \<in> {i'+1..j}"
            using mins_subset less.prems \<open>i' \<noteq> j\<close> Max_in[OF finite_mins mins_nonempty]
            unfolding K_def by (metis le_less subsetCE)
          have "?z \<in> {i+1..j'}"
            using mins_subset less.prems \<open>i' \<noteq> j\<close> Max_in[OF finite_mins mins_nonempty]
            unfolding K_def by (smt subsetCE)
          have w_mon: "w i' j' + w i j \<le> w i' j + w i j'"
            using less.prems QI_w \<open>i' \<noteq> j\<close> by force

          have "i' < j'" "i < j" using \<open>i' \<noteq> j\<close> less.prems by auto
          show ?thesis
          (*---------------------case 2.1 i' \<noteq> j \<and> z \<le> y ----------------------------------------*)
          proof cases
            assume "?z \<le> ?y"
            have "?y \<in> {i'+1..j'}" using less.prems \<open>?y \<in> {i'+1..j}\<close> by simp
            have "?z \<in> {i+1..j}" using \<open>?z \<in> {i+1..j'}\<close> \<open>?z \<le> ?y\<close> \<open>?y \<in> {i'+1..j}\<close> by simp

            have a: "c i' j' \<le> w i' j' + c i' (?y-1) + c ?y j'"
            proof -
              have "c i' j' = Min((\<lambda>k. c i' (k-1) + c k j' + w i' j') ` {i'+1..j'})"
                by (simp add: c_def_rec[OF  \<open>i' < j'\<close>])
              also have "... \<le> w i' j' + c i' (?y-1) + c ?y j'"
                using \<open>?y \<in> {i'+1..j'}\<close> by simp
              finally show ?thesis .
            qed

            have b: "c i j \<le> w i j + c i (?z-1) + c ?z j"
            proof -
              have "c i j = Min ((\<lambda>k. c i (k-1) + c k j + w i j)  ` {i+1..j})"
                using \<open>i < j\<close> by (simp add: c_def_rec)
              also have "... \<le> w i j + c i (?z-1) + c ?z j"
                using \<open>?z \<in> {i+1..j}\<close> by simp
              finally show ?thesis .
            qed

            have "nat (j' - ?z) < l" using \<open>?z \<in> {i+1..j}\<close> less.prems by simp
            hence IH_step: "c ?z j + c ?y j' \<le> c ?z j' + c ?y j"
              using \<open>?z \<le> ?y\<close> \<open>j \<le> j'\<close> \<open>?y \<in> {i'+1..j}\<close>
               less.IH[where i = ?z and i' = ?y and j = j and j' = j', OF _ refl]
              by simp

            have "c i' j' + c i j
              \<le> w i' j + w i j' + c i' (?y-1) + c i (?z-1) + c ?y j' + c ?z j"
              using a b w_mon by simp
            also have "\<dots> \<le> w i j' + w i' j +  c i' (?y-1) + c i (?z-1) + c ?y j + c ?z j'"
              using IH_step by auto
            also have "... = c i j' + c i' j" using \<open>?z \<in> {i+1..j'}\<close> \<open>?y \<in> {i'+1..j}\<close>
              by(simp add: c_k_def c_k_with_K)
            finally show ?thesis by linarith
          next
            (*---------------------case 2.1 i' \<noteq> j \<and> z > y ---------------------------------------*)
            assume "\<not>?z \<le> ?y"

            have "?y \<in> {i+1..j}" using less.prems \<open>?y \<in> {i'+1..j}\<close> by simp
            have "?z \<in> {i'+1..j'}" using \<open>?z \<in> {i+1..j'}\<close> \<open>\<not>?z \<le> ?y\<close> \<open>?y \<in> {i'+1..j}\<close>
              by simp

            have a: "c i' j' \<le> w i' j' + c i' (?z-1) + c ?z j'"
            proof -
              have  "c i' j' =  Min ((\<lambda>k. c i' (k-1) + c k j' + w i' j') ` {i'+1..j'})"
                using \<open>i' < j'\<close> by(simp add: c_def_rec)
              also have "... \<le> w i' j' + c i' (?z-1) + c ?z j'"
                using \<open>?z \<in> {i'+1..j'}\<close> by simp
              finally show ?thesis .
            qed

            have b: "c i j \<le> w i j + c i (?y-1) + c ?y j"
            proof -
              have "c i j = Min ((\<lambda>k. c i (k-1) + c k j + w i j)  ` {i+1..j})"
                using \<open>i < j\<close> by(simp add: c_def_rec)
              also have "... \<le> w i j + c i (?y-1) + c ?y j"
                using \<open>?y \<in> {i+1..j}\<close> by simp
              finally show ?thesis .
            qed
            
            have "nat (?z - 1 - i) < l" using \<open>?z \<in> {i'+1..j'}\<close> less.prems by simp
            hence IH_Step: " c i (?y-1) + c i' (?z-1) \<le> c i' (?y-1) + c i (?z-1)"
              using \<open>?y \<in> {i'+1..j}\<close> \<open>\<not>?z \<le> ?y\<close> \<open>i \<le> i'\<close>
                less.IH[where i=i and i'=i' and j="?y-1" and j'="?z-1", OF _ refl]
              by simp

            have "c i' j' + c i j
              \<le> w i' j +  w i j' + c i' (?z-1) + c i (?y-1) + c ?z j' + c ?y j"
              using a b w_mon by simp
            also have "\<dots> \<le> w i' j +  w i j' + c i (?z-1) + c i' (?y-1) + c ?z j' + c ?y j"
              using IH_Step by auto
            also have "... = c i j' + c i' j" using \<open>?z \<in> {i + 1..j'}\<close> \<open>?y \<in> {i' + 1..j}\<close>
              by(simp add: c_k_def c_k_with_K)
            finally show ?thesis by linarith
          qed
        qed
      qed
    qed
  qed
qed

corollary QI': assumes "i < k" " k \<le> k'"  "k' \<le> j "  "c_k i j k' \<le> c_k i j k"
shows "c_k i (j+1) k' \<le> c_k i (j+1) k"
proof -
  have "c k j + c k' (j+1) \<le> c k' j + c k (j+1)"
    using lemma_2[of _ "j+1" k k' j] assms(1-3) by fastforce

  hence "c_k i j k + c_k i (j+1) k' \<le> c_k i j k' + c_k i (j+1) k"
    using assms(1-3) c_k_def by simp

  thus "c_k i (j+1) k' \<le> c_k i (j+1) k"
    using assms(4) by simp
qed

corollary QI'': assumes "i+1 < k" "k \<le> k'" "k' \<le> j+1" "c_k i (j+1) k' \<le> c_k i (j+1) k"
shows "c_k (i+1) (j+1) k' \<le> c_k (i+1) (j+1) k" 
proof -
  have "c i k + c (i + 1) k' \<le> c i k' + c (i + 1) k"
    using lemma_2[of _ k' i "i+1" k] assms(1,2) by fastforce

  hence "c_k i (j+1) k + c_k (i+1) (j+1) k' \<le> c_k i (j+1) k' + c_k (i+1) (j+1) k"
    using c_k_def assms(1-3) lemma_2 by simp

  thus "c_k (i+1) (j+1) k' \<le> c_k (i+1) (j+1) k"
    using assms(4) by simp
qed


lemma lemma_3_1: assumes "i \<le> j" shows "K i j \<le> K i (j+1)"
proof cases
  assume "i = j"
  thus ?thesis
    by (metis K_def K_subset atLeastAtMost_iff less_add_one less_le)
next
  assume "i\<noteq>j"
  hence "i < j" using \<open>i \<le> j\<close> by simp

  let ?k = "K i (j+1)"
  have "K i j \<in> {i+1..j}" using K_def
    by (metis Max_in \<open>i < j\<close> mins_nonempty[OF \<open>i < j\<close>] finite_mins less_le mins_subset subsetCE)

  have "i < j+1" using \<open>i < j\<close> by linarith
  hence "K i (j+1) \<in> {i+1..j+1}"
    by (metis Max_in K_def mins_nonempty[OF \<open>i < j+1\<close>] finite_mins less_le mins_subset subsetCE)

  have *: "is_arg_min_on (c_k i (j+1)) {i+1..j+1} ?k"
  proof -
    have "K i (j+1) \<in> mins i (j+1)" using finite_mins mins_nonempty \<open>i < j\<close> K_def by fastforce
    thus "is_arg_min_on (c_k i (j+1)) {i+1..j+1} (K i (j+1))"
      unfolding Args_min_simps by blast
  qed 
  show ?thesis
  proof cases
    assume "?k = j+1" thus ?thesis using \<open>K i j \<in> {i+1..j}\<close> by simp
  next
    assume "?k \<noteq> j+1"
    hence "?k \<in> {i+1..j}" using \<open>K i (j+1) \<in> {i+1..j+1}\<close> by auto
    have "i\<noteq>j" "i\<noteq>j+1" using \<open>i < j\<close> by auto
    hence K_simps: "K i j = Max (mins i j)" "K i (j+1) = Max (mins i (j+1))"
      unfolding K_def by auto
    show ?thesis unfolding K_simps
    proof (rule Max.boundedI[OF finite_mins mins_nonempty[OF \<open>i < j\<close>]])
      fix k' assume k': "k' \<in> mins i j"
      show "k' \<le> Max (mins i (j+1))"
      proof (rule ccontr) 
        assume "~ k' \<le> Max (mins i (j+1))"
        have "c_k i (j+1) k' \<le> c_k i (j+1) ?k" unfolding K_simps
        proof (rule QI')
          show "i < Max (mins i (j+1))" 
            using \<open>K i (j + 1) \<in> {i+1..j + 1}\<close> K_simps by auto
          show "Max (mins i (j+1)) \<le> k'" using \<open>~ k' \<le> Max (mins i (j+1))\<close>
            by linarith
          show "k' \<le> j" using mins_subset atLeastAtMost_iff k' by blast
          show "c_k i j k' \<le> c_k i j (Max (mins i (j + 1))) " 
            using k' \<open>?k \<in> {i+1..j}\<close> by(simp add: K_simps Args_min_simps)
        qed

        hence "is_arg_min_on (c_k i (j+1)) {i+1..j+1} k'"
          apply(rule is_arg_min_on_antimono[OF *])
          using mins_subset k' by fastforce
        hence "k' \<in> mins i (j+1)" using k' by (auto simp: Args_min_on_def)
        thus False using finite_mins \<open>\<not> k' \<le> Max (mins i (j + 1))\<close> by auto
      qed
    qed
  qed
qed

lemma lemma_3_2: assumes "i \<le> j" shows "K i (j+1) \<le> K (i+1) (j+1)"
proof cases
  assume "i = j"
  thus ?thesis
    by (metis K_def K_subset atLeastAtMost_iff less_add_one less_le)
next
  assume "i \<noteq> j"
  hence "i < j" using \<open>i \<le> j\<close> by simp
  let ?k = "K (i+1) (j+1)"
  have "K i (j+1) \<in> {i+1..j+1}" unfolding K_def
    by (metis Max_in \<open>i < j\<close> finite_mins less_irrefl mins_nonempty mins_subset subsetCE zless_add1_eq)

  have "i+1 < j+1" using \<open>i < j\<close> by linarith
  hence "K (i+1) (j+1) \<in> {i+1+1..j+1}"
    using mins_nonempty[OF \<open>i+1 < j+1\<close>] mins_subset Max_in K_def finite_mins
    by (metis atLeastatMost_empty atLeastatMost_empty_iff2 contra_subsetD empty_subsetI less_add_one psubsetI)

  have *: "is_arg_min_on (c_k (i+1)(j+1)) {i+1+1..j+1} ?k"
  proof -
    have "K (i+1) (j+1) \<in> mins (i+1) (j+1)"
      using finite_mins mins_nonempty \<open>i + 1 < j + 1\<close> unfolding K_def
      by (metis Max_in not_less_iff_gr_or_eq)
    thus "is_arg_min_on (c_k (i+1) (j+1)) {i+1+1..j+1} (K (i+1) (j+1))"
      unfolding Args_min_on_def by blast
  qed 
  show ?thesis
  proof cases
    assume "?k = j+1" thus ?thesis using \<open>K i (j+1) \<in> {i+1..j+1}\<close> by simp
  next
    assume "?k \<noteq> j+1"
    hence "?k \<in> {i+1+1..j}" using \<open>K (i+1) (j+1) \<in> {i+1+1..j+1}\<close> by auto

    have  "i\<noteq>j+1" "i+1 \<noteq> j+1" using \<open>i < j\<close> by auto
    hence K_simps: "K i (j+1) = Max (mins i (j+1))" 
                      "K (i+1) (j+1) = Max (mins (i+1) (j+1))"
      unfolding K_def by auto
    have "i < j+1" using \<open>i+1 < j+1\<close> by simp

    show ?thesis unfolding K_simps
    proof (rule Max.boundedI[OF finite_mins mins_nonempty[OF \<open>i < j+1\<close>]])
      fix k' assume k': "k' \<in> mins i (j+1)"
      show "k' \<le> Max (mins (i + 1) (j + 1))"
      proof (rule ccontr)
        assume "~ k' \<le> Max (mins (i+1)(j+1))"
        have "c_k (i+1) (j+1) k' \<le> c_k (i+1) (j+1) ?k" unfolding K_simps
          thm QI'[of "i+1" "Max(mins (i+1)(j+1))" k' "j"]
        proof (rule QI'')
          show "i+1  < Max (mins (i+1)(j+1))"
            using \<open>K (i+1) (j+1) \<in> {i+1+1..j+1}\<close> K_simps 
            by auto
          show "Max (mins (i + 1) (j + 1)) \<le> k'" 
            using \<open>~ k' \<le> Max (mins (i+1)(j+1))\<close> K_simps by linarith
          show "k' \<le> j+1"
            using mins_subset k' by fastforce
          show "c_k i (j+1) k' \<le> c_k i (j+1) (Max (mins (i + 1) (j + 1)))" 
            using k' \<open>?k \<in> {(i+1)+1..j + 1}\<close> K_simps
            by(simp add: Args_min_simps)
        qed

        hence "is_arg_min_on (c_k (i+1) (j+1)) {i+1+1..j+1} k'"
          apply(rule is_arg_min_on_antimono[OF *])
          using mins_subset k' K_simps \<open>?k \<in> {i+1+1..j}\<close>
            \<open>\<not> k' \<le> Max (mins (i + 1) (j + 1))\<close> atLeastAtMost_iff
          by force
        hence "k' \<in> mins (i+1) (j+1)" by (simp add: k' Args_min_on_def)
        thus False using finite_mins \<open>\<not> k' \<le> Max (mins (i+1)(j+1))\<close> Max_ge
          by blast
      qed
    qed
  qed
qed

lemma lemma_3: assumes "i \<le> j" 
  shows "K i j \<le> K i (j+1)" "K i (j+1) \<le> K (i+1) (j+1)"
using assms lemma_3_1 lemma_3_2 by blast+

end (* locale QI *)

end
