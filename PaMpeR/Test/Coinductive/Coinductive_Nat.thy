(*  Title:       Coinductive natural numbers
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

section {* Extended natural numbers as a codatatype *}

theory Coinductive_Nat imports
  "HOL-Library.Extended_Nat"
  "HOL-Library.Complete_Partial_Order2"
begin

lemma inj_enat [simp]: "inj_on enat A"
by(simp add: inj_on_def)

lemma Sup_range_enat [simp]: "Sup (range enat) = \<infinity>"
by(auto dest: finite_imageD simp add: Sup_enat_def)

lemmas eSuc_plus = iadd_Suc

lemmas plus_enat_eq_0_conv = iadd_is_0

lemma enat_add_sub_same:
  fixes a b :: enat shows "a \<noteq> \<infinity> \<Longrightarrow> a + b - a = b"
by(cases b) auto

lemma enat_the_enat: "n \<noteq> \<infinity> \<Longrightarrow> enat (the_enat n) = n"
by auto

lemma enat_min_eq_0_iff:
  fixes a b :: enat
  shows "min a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
by(auto simp add: min_def)

lemma enat_le_plus_same: "x \<le> (x :: enat) + y" "x \<le> y + x"
by(auto simp add: less_eq_enat_def plus_enat_def split: enat.split)

lemma the_enat_0 [simp]: "the_enat 0 = 0"
by(simp add: zero_enat_def)

lemma the_enat_eSuc: "n \<noteq> \<infinity> \<Longrightarrow> the_enat (eSuc n) = Suc (the_enat n)"
by(cases n)(simp_all add: eSuc_enat)

coinductive_set enat_set :: "enat set"
where "0 \<in> enat_set"
  | "n \<in> enat_set \<Longrightarrow> (eSuc n) \<in> enat_set"

lemma enat_set_eq_UNIV [simp]: "enat_set = UNIV"
proof
  show "enat_set \<subseteq> UNIV" by blast
  show "UNIV \<subseteq> enat_set"
  proof
    fix x :: enat
    assume "x \<in> UNIV"
    thus "x \<in> enat_set"
    proof coinduct
      case (enat_set x)
      show ?case
      proof(cases "x = 0")
        case True thus ?thesis by simp
      next
        case False
        then obtain n where "x = eSuc n"
          by(cases x)(fastforce simp add: eSuc_def zero_enat_def gr0_conv_Suc
                               split: enat.splits)+
        thus ?thesis by auto
      qed
    qed
  qed
qed

subsection {* Case operator *}

lemma enat_coexhaust:
  obtains (0) "n = 0"
     | (eSuc) n' where "n = eSuc n'"
proof -
  have "n \<in> enat_set" by auto
  thus thesis by cases (erule that)+
qed

locale co begin

free_constructors (plugins del: code) case_enat for
    "0::enat"
  | eSuc epred
where
  "epred 0 = 0"
  apply (erule enat_coexhaust, assumption)
 apply (rule eSuc_inject)
by (rule zero_ne_eSuc)

end

lemma enat_cocase_0 [simp]: "co.case_enat z s 0 = z"
by (rule co.enat.case(1))

lemma enat_cocase_eSuc [simp]: "co.case_enat z s (eSuc n) = s n"
by (rule co.enat.case(2))

lemma neq_zero_conv_eSuc: "n \<noteq> 0 \<longleftrightarrow> (\<exists>n'. n = eSuc n')"
by(cases n rule: enat_coexhaust) simp_all

lemma enat_cocase_cert:
  assumes "CASE \<equiv> co.case_enat c d"
  shows "(CASE 0 \<equiv> c) &&& (CASE (eSuc n) \<equiv> d n)"
  using assms by simp_all

lemma enat_cosplit_asm:
  "P (co.case_enat c d n) = (\<not> (n = 0 \<and> \<not> P c \<or> (\<exists>m. n = eSuc m \<and> \<not> P (d m))))"
by (rule co.enat.split_asm)

lemma enat_cosplit:
  "P (co.case_enat c d n) = ((n = 0 \<longrightarrow> P c) \<and> (\<forall>m. n = eSuc m \<longrightarrow> P (d m)))"
by (rule co.enat.split)

abbreviation epred :: "enat => enat" where "epred \<equiv> co.epred"

lemma epred_0 [simp]: "epred 0 = 0" by(rule co.enat.sel(1))
lemma epred_eSuc [simp]: "epred (eSuc n) = n" by(rule co.enat.sel(2))
declare co.enat.collapse[simp]
lemma epred_conv_minus: "epred n = n - 1"
by(cases n rule: co.enat.exhaust)(simp_all)

subsection {* Corecursion for @{typ enat} *}

lemma case_enat_numeral [simp]: "case_enat f i (numeral v) = (let n = numeral v in f n)"
by(simp add: numeral_eq_enat)

lemma case_enat_0 [simp]: "case_enat f i 0 = f 0"
by(simp add: zero_enat_def)

lemma [simp]:
  shows max_eSuc_eSuc: "max (eSuc n) (eSuc m) = eSuc (max n m)"
  and min_eSuc_eSuc: "min (eSuc n) (eSuc m) = eSuc (min n m)"
by(simp_all add: eSuc_def split: enat.split)


definition epred_numeral :: "num \<Rightarrow> enat"
where [code del]: "epred_numeral = enat \<circ> pred_numeral"

lemma numeral_eq_eSuc: "numeral k = eSuc (epred_numeral k)"
by(simp add: numeral_eq_Suc eSuc_def epred_numeral_def numeral_eq_enat)

lemma epred_numeral_simps [simp]:
  "epred_numeral num.One = 0"
  "epred_numeral (num.Bit0 k) = numeral (Num.BitM k)"
  "epred_numeral (num.Bit1 k) = numeral (num.Bit0 k)"
by(simp_all add: epred_numeral_def enat_numeral zero_enat_def)

lemma [simp]:
  shows eq_numeral_eSuc: "numeral k = eSuc n \<longleftrightarrow> epred_numeral k = n"
  and Suc_eq_numeral: "eSuc n = numeral k \<longleftrightarrow> n = epred_numeral k"
  and less_numeral_Suc: "numeral k < eSuc n \<longleftrightarrow> epred_numeral k < n"
  and less_eSuc_numeral: "eSuc n < numeral k \<longleftrightarrow> n < epred_numeral k"
  and le_numeral_eSuc: "numeral k \<le> eSuc n \<longleftrightarrow> epred_numeral k \<le> n"
  and le_eSuc_numeral: "eSuc n \<le> numeral k \<longleftrightarrow> n \<le> epred_numeral k"
  and diff_eSuc_numeral: "eSuc n - numeral k = n - epred_numeral k"
  and diff_numeral_eSuc: "numeral k - eSuc n = epred_numeral k - n"
  and max_eSuc_numeral: "max (eSuc n) (numeral k) = eSuc (max n (epred_numeral k))"
  and max_numeral_eSuc: "max (numeral k) (eSuc n) = eSuc (max (epred_numeral k) n)"
  and min_eSuc_numeral: "min (eSuc n) (numeral k) = eSuc (min n (epred_numeral k))"
  and min_numeral_eSuc: "min (numeral k) (eSuc n) = eSuc (min (epred_numeral k) n)"
by(simp_all add: numeral_eq_eSuc)

lemma enat_cocase_numeral [simp]:
  "co.case_enat a f (numeral v) = (let pv = epred_numeral v in f pv)"
by(simp add: numeral_eq_eSuc)

lemma enat_cocase_add_eq_if [simp]:
  "co.case_enat a f ((numeral v) + n) = (let pv = epred_numeral v in f (pv + n))"
by(simp add: numeral_eq_eSuc iadd_Suc)


lemma [simp]:
  shows epred_1: "epred 1 = 0"
  and epred_numeral: "epred (numeral i) = epred_numeral i"
  and epred_Infty: "epred \<infinity> = \<infinity>"
  and epred_enat: "epred (enat m) = enat (m - 1)"
by(simp_all add: epred_conv_minus one_enat_def zero_enat_def eSuc_def epred_numeral_def numeral_eq_enat split: enat.split)

lemmas epred_simps = epred_0 epred_1 epred_numeral epred_eSuc epred_Infty epred_enat

lemma epred_iadd1: "a \<noteq> 0 \<Longrightarrow> epred (a + b) = epred a + b"
apply(cases a b rule: enat.exhaust[case_product enat.exhaust])
apply(simp_all add: epred_conv_minus eSuc_def one_enat_def zero_enat_def split: enat.splits)
done

lemma epred_min [simp]: "epred (min a b) = min (epred a) (epred b)"
by(cases a b rule: enat_coexhaust[case_product enat_coexhaust]) simp_all

lemma epred_le_epredI: "n \<le> m \<Longrightarrow> epred n \<le> epred m"
by(cases m n rule: enat_coexhaust[case_product enat_coexhaust]) simp_all

lemma epred_minus_epred [simp]:
  "m \<noteq> 0 \<Longrightarrow> epred n - epred m = n - m"
by(cases n m rule: enat_coexhaust[case_product enat_coexhaust])(simp_all add: epred_conv_minus)

lemma eSuc_epred: "n \<noteq> 0 \<Longrightarrow> eSuc (epred n) = n"
by(cases n rule: enat_coexhaust) simp_all

lemma epred_inject: "\<lbrakk> x \<noteq> 0; y \<noteq> 0 \<rbrakk> \<Longrightarrow> epred x = epred y \<longleftrightarrow> x = y"
by(cases x y rule: enat.exhaust[case_product enat.exhaust])(auto simp add: zero_enat_def)

lemma monotone_fun_eSuc[partial_function_mono]:
    "monotone (fun_ord (\<lambda>y x. x \<le> y)) (\<lambda>y x. x \<le> y) (\<lambda>f. eSuc (f x))"
  by (auto simp: monotone_def fun_ord_def)

partial_function (gfp) enat_unfold :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> enat" where
  enat_unfold [code, nitpick_simp]:
  "enat_unfold stop next a = (if stop a then 0 else eSuc (enat_unfold stop next (next a)))"

lemma enat_unfold_stop [simp]: "stop a \<Longrightarrow> enat_unfold stop next a = 0"
by(simp add: enat_unfold)

lemma enat_unfold_next: "\<not> stop a \<Longrightarrow> enat_unfold stop next a = eSuc (enat_unfold stop next (next a))"
by(simp add: enat_unfold)

lemma enat_unfold_eq_0 [simp]:
  "enat_unfold stop next a = 0 \<longleftrightarrow> stop a"
by(simp add: enat_unfold)

lemma epred_enat_unfold [simp]:
  "epred (enat_unfold stop next a) = (if stop a then 0 else enat_unfold stop next (next a))"
by(simp add: enat_unfold_next)

lemma epred_max: "epred (max x y) = max (epred x) (epred y)"
by(cases x y rule: enat.exhaust[case_product enat.exhaust]) simp_all

lemma epred_Max:
  assumes "finite A" "A \<noteq> {}"
  shows "epred (Max A) = Max (epred ` A)"
using assms
proof induction
  case (insert x A)
  thus ?case by(cases "A = {}")(simp_all add: epred_max)
qed simp

lemma finite_imageD2: "\<lbrakk> finite (f ` A); inj_on f (A - B); finite B \<rbrakk> \<Longrightarrow> finite A"
by (metis Diff_subset finite_Diff2 image_mono inj_on_finite)

lemma epred_Sup: "epred (Sup A) = Sup (epred ` A)"
by(auto 4 4 simp add: bot_enat_def Sup_enat_def epred_Max inj_on_def neq_zero_conv_eSuc dest: finite_imageD2[where B="{0}"])


subsection {* Less as greatest fixpoint *}

coinductive_set Le_enat :: "(enat \<times> enat) set"
where
  Le_enat_zero: "(0, n) \<in> Le_enat"
| Le_enat_add: "\<lbrakk> (m, n) \<in> Le_enat; k \<noteq> 0 \<rbrakk> \<Longrightarrow> (eSuc m, n + k) \<in> Le_enat"

lemma ile_into_Le_enat:
  "m \<le> n \<Longrightarrow> (m, n) \<in> Le_enat"
proof -
  assume "m \<le> n"
  hence "(m, n) \<in> {(m, n)|m n. m \<le> n}" by simp
  thus ?thesis
  proof coinduct
    case (Le_enat m n)
    hence "m \<le> n" by simp
    show ?case
    proof(cases "m = 0")
      case True
      hence ?Le_enat_zero by simp
      thus ?thesis ..
    next
      case False
      with `m \<le> n` obtain m' n' where "m = eSuc m'" "n = n' + 1" "m' \<le> n'"
        by(cases m rule: enat_coexhaust, simp)
          (cases n rule: enat_coexhaust, auto simp add: eSuc_plus_1[symmetric])
      hence ?Le_enat_add by fastforce
      thus ?thesis ..
    qed
  qed
qed

lemma Le_enat_imp_ile_enat_k:
  "(m, n) \<in> Le_enat \<Longrightarrow> n < enat l \<Longrightarrow> m < enat l"
proof(induct l arbitrary: m n)
  case 0
  thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc l)
  from `(m, n) \<in> Le_enat` show ?case
  proof cases
    case Le_enat_zero
    with `n < enat (Suc l)` show ?thesis by auto
  next
    case (Le_enat_add M N K)
    from `n = N + K` `n < enat (Suc l)` `K \<noteq> 0`
    have "N < enat l" by(cases N)(cases K, auto simp add: zero_enat_def)
    with `(M, N) \<in> Le_enat` have "M < enat l" by(rule Suc)
    with `m = eSuc M` show ?thesis by(simp add: eSuc_enat[symmetric])
  qed
qed

lemma enat_less_imp_le:
  assumes k: "!!k. n < enat k \<Longrightarrow> m < enat k"
  shows "m \<le> n"
proof(cases n)
  case (enat n')
  with k[of "Suc n'"] show ?thesis by(cases m) simp_all
qed simp

lemma Le_enat_imp_ile:
  "(m, n) \<in> Le_enat \<Longrightarrow> m \<le> n"
by(rule enat_less_imp_le)(erule Le_enat_imp_ile_enat_k)

lemma Le_enat_eq_ile:
  "(m, n) \<in> Le_enat \<longleftrightarrow> m \<le> n"
by(blast intro: Le_enat_imp_ile ile_into_Le_enat)

lemma enat_leI [consumes 1, case_names Leenat, case_conclusion Leenat zero eSuc]:
  assumes major: "(m, n) \<in> X"
  and step:
    "\<And>m n. (m, n) \<in> X 
     \<Longrightarrow> m = 0 \<or> (\<exists>m' n' k. m = eSuc m' \<and> n = n' + enat k \<and> k \<noteq> 0 \<and>
                           ((m', n') \<in> X \<or> m' \<le> n'))"
  shows "m \<le> n"
apply(rule Le_enat.coinduct[unfolded Le_enat_eq_ile, where X="\<lambda>x y. (x, y) \<in> X"])
apply(fastforce simp add: zero_enat_def dest: step intro: major)+
done

lemma enat_le_coinduct[consumes 1, case_names le, case_conclusion le 0 eSuc]:
  assumes P: "P m n"
  and step:
    "\<And>m n. P m n 
     \<Longrightarrow> (n = 0 \<longrightarrow> m = 0) \<and>
         (m \<noteq> 0 \<longrightarrow> n \<noteq> 0 \<longrightarrow> (\<exists>k n'. P (epred m) n' \<and> epred n = n' + k) \<or> epred m \<le> epred n)"
  shows "m \<le> n"
proof -
  from P have "(m, n) \<in> {(m, n). P m n}" by simp
  thus ?thesis
  proof(coinduct rule: enat_leI)
    case (Leenat m n)
    hence "P m n" by simp
    show ?case
    proof(cases m rule: enat_coexhaust)
      case 0 
      thus ?thesis by simp
    next
      case (eSuc m')
      with step[OF `P m n`]
      have "n \<noteq> 0" and disj: "(\<exists>k n'. P m' n' \<and> epred n = n' + k) \<or> m' \<le> epred n" by auto
      from `n \<noteq> 0` obtain n' where n': "n = eSuc n'"
        by(cases n rule: enat_coexhaust) auto
      from disj show ?thesis
      proof
        assume "m' \<le> epred n"
        with eSuc n' show ?thesis 
          by(auto 4 3 intro: exI[where x="Suc 0"] simp add: eSuc_enat[symmetric] iadd_Suc_right zero_enat_def[symmetric])
      next
        assume "\<exists>k n'. P m' n' \<and> epred n = n' + k"
        then obtain k n'' where n'': "epred n = n'' + k" and k: "P m' n''" by blast
        show ?thesis using eSuc k n' n''
          by(cases k)(auto 4 3 simp add: iadd_Suc_right[symmetric] eSuc_enat intro: exI[where x=\<infinity>])
      qed
    qed
  qed
qed

subsection {* Equality as greatest fixpoint *}

lemma enat_equalityI [consumes 1, case_names Eq_enat,
                                  case_conclusion Eq_enat zero eSuc]:
  assumes major: "(m, n) \<in> X"
  and step:
    "\<And>m n. (m, n) \<in> X
     \<Longrightarrow> m = 0 \<and> n = 0 \<or> (\<exists>m' n'. m = eSuc m' \<and> n = eSuc n' \<and> ((m', n') \<in> X \<or> m' = n'))"
  shows "m = n"
proof(rule antisym)
  from major show "m \<le> n"
    by(coinduct rule: enat_leI)
      (drule step, auto simp add: eSuc_plus_1 enat_1[symmetric])

  from major have "(n, m) \<in> {(n, m). (m, n) \<in> X}" by simp
  thus "n \<le> m"
  proof(coinduct rule: enat_leI)
    case (Leenat n m)
    hence "(m, n) \<in> X" by simp
    from step[OF this] show ?case
      by(auto simp add: eSuc_plus_1 enat_1[symmetric])
  qed
qed

lemma enat_coinduct [consumes 1, case_names Eq_enat, case_conclusion Eq_enat zero eSuc]:
  assumes major: "P m n"
  and step: "\<And>m n. P m n 
    \<Longrightarrow> (m = 0 \<longleftrightarrow> n = 0) \<and>
       (m \<noteq> 0 \<longrightarrow> n \<noteq> 0 \<longrightarrow> P (epred m) (epred n) \<or> epred m = epred n)"
  shows "m = n"
proof -
  from major have "(m, n) \<in> {(m, n). P m n}" by simp
  thus ?thesis
  proof(coinduct rule: enat_equalityI)
    case (Eq_enat m n)
    hence "P m n" by simp
    from step[OF this] show ?case
      by(cases m n rule: enat_coexhaust[case_product enat_coexhaust]) auto
  qed
qed

lemma enat_coinduct2 [consumes 1, case_names zero eSuc]:
  "\<lbrakk> P m n; \<And>m n. P m n \<Longrightarrow> m = 0 \<longleftrightarrow> n = 0; 
     \<And>m n. \<lbrakk> P m n; m \<noteq> 0; n \<noteq> 0 \<rbrakk> \<Longrightarrow> P (epred m) (epred n) \<or> epred m = epred n \<rbrakk>
  \<Longrightarrow> m = n"
by(erule enat_coinduct) blast

subsection {* Uniqueness of corecursion *}

lemma enat_unfold_unique:
  assumes h: "!!x. h x = (if stop x then 0 else eSuc (h (next x)))"
  shows "h x = enat_unfold stop next x"
by(coinduction arbitrary: x rule: enat_coinduct)(subst (1 3) h, auto)

subsection {* Setup for partial\_function *}

lemma enat_diff_cancel_left: "\<lbrakk> m \<le> x; m \<le> y \<rbrakk> \<Longrightarrow> x - m = y - m \<longleftrightarrow> x = (y :: enat)"
by(cases x y m rule: enat.exhaust[case_product enat.exhaust[case_product enat.exhaust]])(simp_all, arith)

lemma finite_lessThan_enatI: 
  assumes "m \<noteq> \<infinity>"
  shows "finite {..<m :: enat}"
proof -
  from assms obtain m' where m: "m = enat m'" by auto
  have "{..<enat m'} \<subseteq> enat ` {..<m'}"
    by(rule subsetI)(case_tac x, auto)
  thus ?thesis unfolding m by(rule finite_subset) simp
qed

lemma infinite_lessThan_infty: "\<not> finite {..<\<infinity> :: enat}"
proof
  have "range enat \<subseteq> {..<\<infinity>}" by auto
  moreover assume "finite {..<\<infinity> :: enat}"
  ultimately have "finite (range enat)" by(rule finite_subset)
  hence "finite (UNIV :: nat set)"
    by(rule finite_imageD)(simp add: inj_on_def)
  thus False by simp
qed

lemma finite_lessThan_enat_iff:
  "finite {..<m :: enat} \<longleftrightarrow> m \<noteq> \<infinity>"
by(cases m)(auto intro: finite_lessThan_enatI simp add: infinite_lessThan_infty)

lemma enat_minus_mono1: "x \<le> y \<Longrightarrow> x - m \<le> y - (m :: enat)"
by(cases m x y rule: enat.exhaust[case_product enat.exhaust[case_product enat.exhaust]]) simp_all

lemma max_enat_minus1: "max n m - k = max (n - k) (m - k :: enat)"
by(cases n m k rule: enat.exhaust[case_product enat.exhaust[case_product enat.exhaust]]) simp_all

lemma Max_enat_minus1:
  assumes "finite A" "A \<noteq> {}"
  shows "Max A - m = Max ((\<lambda>n :: enat. n - m) ` A)"
using assms proof induct
  case (insert x A)
  thus ?case by(cases "A = {}")(simp_all add: max_enat_minus1)
qed simp

lemma Sup_enat_minus1: 
  assumes "m \<noteq> \<infinity>"
  shows "\<Squnion>A - m = \<Squnion>((\<lambda>n :: enat. n - m) ` A)"
proof -
  from assms obtain m' where "m = enat m'" by auto
  thus ?thesis
    by(auto simp add: Sup_enat_def Max_enat_minus1 finite_lessThan_enat_iff enat_diff_cancel_left inj_on_def dest!: finite_imageD2[where B="{..<enat m'}"])
qed

lemma Sup_image_eadd1:
  assumes "Y \<noteq> {}"
  shows "Sup ((\<lambda>y :: enat. x + y) ` Y) = x + Sup Y"
proof(cases "finite Y")
  case True
  have "op + x ` Y = {x + m |m. m \<in> Y}" by auto
  thus ?thesis using True by(simp add: Sup_enat_def add_Max_commute assms)
next
  case False
  thus ?thesis
  proof(cases x)
    case (enat x')
    hence "\<not> finite (op + x ` Y)" using False
      by(auto dest!: finite_imageD intro: inj_onI)
    with False show ?thesis by(simp add: Sup_enat_def assms)
  next
    case infinity
    hence "op + x ` Y = {\<infinity>}" using assms by auto
    thus ?thesis using infinity by(simp add: image_constant_conv assms)
  qed
qed

lemma Sup_image_eadd2:
  "Y \<noteq> {} \<Longrightarrow> Sup ((\<lambda>y :: enat. y + x) ` Y) = Sup Y + x"
by(subst (1 2) add.commute)(rule Sup_image_eadd1)


lemma mono2mono_eSuc [THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_eSuc: "monotone op \<le> op \<le> eSuc"
by(rule monotoneI) simp

lemma mcont2mcont_eSuc [THEN lfp.mcont2mcont, cont_intro, simp]:
  shows mcont_eSuc: "mcont Sup op \<le> Sup op \<le> eSuc"
by(intro mcontI contI)(simp_all add: monotone_eSuc eSuc_Sup)

lemma mono2mono_epred [THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_epred: "monotone op \<le> op \<le> epred"
by(rule monotoneI)(simp add: epred_le_epredI)

lemma mcont2mcont_epred [THEN lfp.mcont2mcont, cont_intro, simp]:
  shows mcont_epred: "mcont Sup op \<le> Sup op \<le> epred"
by(simp add: mcont_def monotone_epred cont_def epred_Sup)

lemma enat_cocase_mono [partial_function_mono, cont_intro]: 
  "\<lbrakk> monotone orda ordb zero; \<And>n. monotone orda ordb (\<lambda>f. esuc f n) \<rbrakk>
  \<Longrightarrow> monotone orda ordb (\<lambda>f. co.case_enat (zero f) (esuc f) x)"
by(cases x rule: co.enat.exhaust) simp_all

lemma enat_cocase_mcont [cont_intro, simp]:
  "\<lbrakk> mcont luba orda lubb ordb zero; \<And>n. mcont luba orda lubb ordb (\<lambda>f. esuc f n) \<rbrakk>
  \<Longrightarrow> mcont luba orda lubb ordb (\<lambda>f. co.case_enat (zero f) (esuc f) x)"
by(cases x rule: co.enat.exhaust) simp_all

lemma eSuc_mono [partial_function_mono]:
  "monotone (fun_ord op \<le>) op \<le> f \<Longrightarrow> monotone (fun_ord op \<le>) op \<le> (\<lambda>x. eSuc (f x))"
by(rule mono2mono_eSuc)

lemma mono2mono_enat_minus1 [THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_enat_minus1: "monotone op \<le> op \<le> (\<lambda>n. n - m :: enat)"
by(rule monotoneI)(rule enat_minus_mono1)

lemma mcont2mcont_enat_minus [THEN lfp.mcont2mcont, cont_intro, simp]:
  shows mcont_enat_minus: "m \<noteq> \<infinity> \<Longrightarrow> mcont Sup op \<le> Sup op \<le> (\<lambda>n. n - m :: enat)"
by(rule mcontI)(simp_all add: monotone_enat_minus1 contI Sup_enat_minus1)

lemma monotone_eadd1: "monotone op \<le> op \<le> (\<lambda>x. x + y :: enat)"
by(auto intro!: monotoneI)

lemma monotone_eadd2: "monotone op \<le> op \<le> (\<lambda>y. x + y :: enat)"
by(auto intro!: monotoneI)

lemma mono2mono_eadd[THEN lfp.mono2mono2, cont_intro, simp]:
  shows monotone_eadd: "monotone (rel_prod op \<le> op \<le>) op \<le> (\<lambda>(x, y). x + y :: enat)"
by(simp add: monotone_eadd1 monotone_eadd2)

lemma mcont_eadd2: "mcont Sup op \<le> Sup op \<le> (\<lambda>y. x + y :: enat)"
by(auto intro: mcontI monotone_eadd2 contI Sup_image_eadd1[symmetric])

lemma mcont_eadd1: "mcont Sup op \<le> Sup op \<le> (\<lambda>x. x + y :: enat)"
by(auto intro: mcontI monotone_eadd1 contI Sup_image_eadd2[symmetric])

lemma mcont2mcont_eadd [cont_intro, simp]:
  "\<lbrakk> mcont lub ord Sup op \<le> (\<lambda>x. f x);
    mcont lub ord Sup op \<le> (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup op \<le> (\<lambda>x. f x + g x :: enat)"
by(best intro: ccpo.mcont2mcont'[OF complete_lattice_ccpo] mcont_eadd1 mcont_eadd2 ccpo.mcont_const[OF complete_lattice_ccpo])

lemma eadd_partial_function_mono [partial_function_mono]:
  "\<lbrakk> monotone (fun_ord op \<le>) op \<le> f; monotone (fun_ord op \<le>) op \<le> g \<rbrakk>
  \<Longrightarrow> monotone (fun_ord op \<le>) op \<le> (\<lambda>x. f x + g x :: enat)"
by(rule mono2mono_eadd)

lemma monotone_max_enat1: "monotone op \<le> op \<le> (\<lambda>x. max x y :: enat)"
by(auto intro!: monotoneI simp add: max_def)

lemma monotone_max_enat2: "monotone op \<le> op \<le> (\<lambda>y. max x y :: enat)"
by(auto intro!: monotoneI simp add: max_def)

lemma mono2mono_max_enat[THEN lfp.mono2mono2, cont_intro, simp]:
  shows monotone_max_enat: "monotone (rel_prod op \<le> op \<le>) op \<le> (\<lambda>(x, y). max x y :: enat)"
by(simp add: monotone_max_enat1 monotone_max_enat2)

lemma max_Sup_enat2:
  assumes "Y \<noteq> {}"
  shows "max x (Sup Y) = Sup ((\<lambda>y :: enat. max x y) ` Y)"
proof(cases "finite Y")
  case True
  hence "max x (Max Y) = Max (max x ` Y)" using assms
  proof(induct)
    case (insert y Y)
    thus ?case
      by(cases "Y = {}")(simp_all, metis max.assoc max.left_commute max.left_idem)
  qed simp
  thus ?thesis using True by(simp add: Sup_enat_def assms)
next
  case False
  show ?thesis
  proof(cases x)
    case infinity
    hence "max x ` Y = {\<infinity>}" using assms by auto
    thus ?thesis using False by(simp add: Sup_enat_def assms)
  next
    case (enat x')
    { assume "finite (max x ` Y)"
      hence "finite (max x ` {y \<in> Y. y > x})"
        by(rule finite_subset[rotated]) auto
      hence "finite {y \<in> Y. y > x}"
        by(rule finite_imageD)(auto intro!: inj_onI simp add: max_def split: if_split_asm)
      moreover have "finite {y \<in> Y. y \<le> x}"
        by(rule finite_enat_bounded)(auto simp add: enat)
      ultimately have "finite ({y \<in> Y. y > x} \<union> {y \<in> Y. y \<le> x})" by simp
      also have "{y \<in> Y. y > x} \<union> {y \<in> Y. y \<le> x} = Y" by auto
      finally have "finite Y" . }
    thus ?thesis using False by(auto simp add: Sup_enat_def assms)
  qed
qed

lemma max_Sup_enat1:
  "Y \<noteq> {} \<Longrightarrow> max (Sup Y) x = Sup ((\<lambda>y :: enat. max y x) ` Y)"
by(subst (1 2) max.commute)(rule max_Sup_enat2)

lemma mcont_max_enat1: "mcont Sup op \<le> Sup op \<le> (\<lambda>x. max x y :: enat)"
by(auto intro!: mcontI contI max_Sup_enat1 simp add: monotone_max_enat1)

lemma mcont_max_enat2: "mcont Sup op \<le> Sup op \<le> (\<lambda>y. max x y :: enat)"
by(auto intro!: mcontI contI max_Sup_enat2 simp add: monotone_max_enat2)

lemma mcont2mcont_max_enat [cont_intro, simp]:
  "\<lbrakk> mcont lub ord Sup op \<le> (\<lambda>x. f x);
    mcont lub ord Sup op \<le> (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup op \<le> (\<lambda>x. max (f x) (g x) :: enat)"
by(best intro: ccpo.mcont2mcont'[OF complete_lattice_ccpo] mcont_max_enat1 mcont_max_enat2 ccpo.mcont_const[OF complete_lattice_ccpo])

lemma max_enat_partial_function_mono [partial_function_mono]:
  "\<lbrakk> monotone (fun_ord op \<le>) op \<le> f; monotone (fun_ord op \<le>) op \<le> g \<rbrakk>
  \<Longrightarrow> monotone (fun_ord op \<le>) op \<le> (\<lambda>x. max (f x) (g x) :: enat)"
by(rule mono2mono_max_enat)

lemma chain_epredI:
  "Complete_Partial_Order.chain op \<le> Y
  \<Longrightarrow> Complete_Partial_Order.chain op \<le> (epred ` (Y \<inter> {x. x \<noteq> 0}))"
by(auto intro: chainI dest: chainD)

lemma monotone_enat_le_case:
  fixes bot
  assumes mono: "monotone op \<le> ord (\<lambda>x. f x (eSuc x))"
  and ord: "\<And>x. ord bot (f x (eSuc x))"
  and bot: "ord bot bot"
  shows "monotone op \<le> ord (\<lambda>x. case x of 0 \<Rightarrow> bot | eSuc x' \<Rightarrow> f x' x)"
proof -
  have "monotone op \<le> ord (\<lambda>x. if x \<le> 0 then bot else f (epred x) x)"
  proof(rule monotone_if_bot)
    fix x y :: enat
    assume "x \<le> y" "\<not> x \<le> 0"
    thus "ord (f (epred x) x) (f (epred y) y)"
      by(cases x y rule: co.enat.exhaust[case_product co.enat.exhaust])(auto intro: monotoneD[OF mono])
  next
    fix x :: enat
    assume "\<not> x \<le> 0"
    thus "ord bot (f (epred x) x)"
      by(cases x rule: co.enat.exhaust)(auto intro: ord)
  qed(rule bot)
  also have "(\<lambda>x. if x \<le> 0 then bot else f (epred x) x) = (\<lambda>x. case x of 0 \<Rightarrow> bot | eSuc x' \<Rightarrow> f x' x)"
    by(auto simp add: fun_eq_iff split: co.enat.split)
  finally show ?thesis .
qed

lemma mcont_enat_le_case:
  fixes bot
  assumes ccpo: "class.ccpo lub ord (mk_less ord)"
  and mcont: "mcont Sup op \<le> lub ord (\<lambda>x. f x (eSuc x))"
  and ord: "\<And>x. ord bot (f x (eSuc x))"
  shows "mcont Sup op \<le> lub ord (\<lambda>x. case x of 0 \<Rightarrow> bot | eSuc x' \<Rightarrow> f x' x)"
proof -
  from ccpo
  have "mcont Sup op \<le> lub ord (\<lambda>x. if x \<le> 0 then bot else f (epred x) x)"
  proof(rule mcont_if_bot)
    fix x y :: enat
    assume "x \<le> y" "\<not> x \<le> 0"
    thus "ord (f (epred x) x) (f (epred y) y)"
      by(cases x y rule: co.enat.exhaust[case_product co.enat.exhaust])(auto intro: mcont_monoD[OF mcont])
  next
    fix Y :: "enat set"
    assume chain: "Complete_Partial_Order.chain op \<le> Y"
      and Y: "Y \<noteq> {}" "\<And>x. x \<in> Y \<Longrightarrow> \<not> x \<le> 0"
    from Y have Y': "Y \<inter> {x. x \<noteq> 0} \<noteq> {}" by auto
    from Y(2) have eq: "Y = eSuc ` (epred ` (Y \<inter> {x. x \<noteq> 0}))"
      by(fastforce intro: rev_image_eqI)
    let ?Y = "epred ` (Y \<inter> {x. x \<noteq> 0})"
    from chain_epredI [OF chain] Y'
    have "f (\<Squnion>?Y) (eSuc (\<Squnion>?Y)) = lub ((\<lambda>x. f x (eSuc x)) ` ?Y)"
      using mcont [THEN mcont_contD] by blast
    moreover from chain_epredI [OF chain] Y'
      have "SUPREMUM ?Y eSuc = eSuc (\<Squnion>?Y)"
      using mcont_eSuc [THEN mcont_contD, symmetric] by blast
    ultimately show "f (epred (Sup Y)) (Sup Y) = lub ((\<lambda>x. f (epred x) x) ` Y)"
      by (subst (1 2 3) eq) (simp add: image_image)
  next
    fix x :: enat
    assume "\<not> x \<le> 0"
    thus "ord bot (f (epred x) x)"
      by(cases x rule: co.enat.exhaust)(auto intro: ord)
  qed
  also have "(\<lambda>x. if x \<le> 0 then bot else f (epred x) x) = (\<lambda>x. case x of 0 \<Rightarrow> bot | eSuc x' \<Rightarrow> f x' x)"
    by(auto simp add: fun_eq_iff split: co.enat.split)
  finally show ?thesis .
qed


subsection {* Misc. *}

lemma enat_add_mono [simp]:
  "enat x + y < enat x + z \<longleftrightarrow> y < z"
by(cases y)(case_tac [!] z, simp_all)

lemma enat_add1_eq [simp]: "enat x + y = enat x + z \<longleftrightarrow> y = z"
by (metis enat_add_mono add.commute neq_iff)

lemma enat_add2_eq [simp]: "y + enat x = z + enat x \<longleftrightarrow> y = z"
by (metis enat_add1_eq add.commute)

lemma enat_less_enat_plusI: "x < y \<Longrightarrow> enat x < enat y + z"
by(cases z) simp_all

lemma enat_less_enat_plusI2:
  "enat y < z \<Longrightarrow> enat (x + y) < enat x + z"
by (metis enat_add_mono plus_enat_simps(1))

lemma min_enat1_conv_enat: "\<And>a b. min (enat a) b = enat (case b of enat b' \<Rightarrow> min a b' | \<infinity> \<Rightarrow> a)"
  and min_enat2_conv_enat: "\<And>a b. min a (enat b) = enat (case a of enat a' \<Rightarrow> min a' b | \<infinity> \<Rightarrow> b)"
by(simp_all split: enat.split)

lemma eSuc_le_iff: "eSuc x \<le> y \<longleftrightarrow> (\<exists>y'. y = eSuc y' \<and> x \<le> y')"
by(cases y rule: co.enat.exhaust) simp_all

lemma eSuc_eq_infinity_iff: "eSuc n = \<infinity> \<longleftrightarrow> n = \<infinity>"
by(cases n)(simp_all add: zero_enat_def eSuc_enat)

lemma infinity_eq_eSuc_iff: "\<infinity> = eSuc n \<longleftrightarrow> n = \<infinity>"
by(cases n)(simp_all add: zero_enat_def eSuc_enat)

lemma enat_cocase_inf: "(case \<infinity> of 0 \<Rightarrow> a | eSuc b \<Rightarrow> f b) = f \<infinity>"
by(auto split: co.enat.split simp add: infinity_eq_eSuc_iff)

lemma eSuc_Inf: "eSuc (Inf A) = Inf (eSuc ` A)"
proof -
  { assume "A \<noteq> {}"
    then obtain a where "a \<in> A" by blast
    then have "eSuc (LEAST a. a \<in> A) = (LEAST a. a \<in> eSuc ` A)"
    proof (rule LeastI2_wellorder)
      fix a assume "a \<in> A" and b: "\<forall>b. b \<in> A \<longrightarrow> a \<le> b"
      then have a: "eSuc a \<in> eSuc ` A"
        by auto
      then show "eSuc a = (LEAST a. a \<in> eSuc ` A)"
        by (rule LeastI2_wellorder) (metis (full_types) b a antisym eSuc_le_iff imageE)
    qed }
  then show ?thesis
    by (simp add: Inf_enat_def)
qed

end
