theory Rep_Fin_Groups

imports
  "HOL-Library.Function_Algebras"
  "HOL-Library.Set_Algebras"
  "HOL-Computational_Algebra.Polynomial"

begin




section \<open>Preliminaries\<close>

text \<open>
  In this section, we establish some basic facts about logic, sets, and functions that are not
  available in the HOL library. As well, we develop some theory for almost-everywhere-zero functions
  in preparation of the definition of the group ring.
\<close>


subsection \<open>Logic\<close>

lemma conjcases [case_names BothTrue OneTrue OtherTrue BothFalse] :
  assumes BothTrue: "P \<and> Q    \<Longrightarrow> R"
  and     OneTrue:   "P \<and> \<not>Q  \<Longrightarrow> R"
  and     OtherTrue: "\<not>P \<and> Q  \<Longrightarrow> R"
  and     BothFalse: "\<not>P \<and> \<not>Q \<Longrightarrow> R"
  shows   "R"
  using   assms
  by      fast


subsection \<open>Sets\<close>

lemma empty_set_diff_single : "A - {x} = {} \<Longrightarrow> A = {} \<or> A = {x}"
  by auto

lemma seteqI : "(\<And>a. a \<in> A \<Longrightarrow> a \<in> B) \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> b \<in> A) \<Longrightarrow> A = B"
  using subset_antisym subsetI by fast

lemma prod_ballI : "(\<And>a b. (a,b) \<in> AxB \<Longrightarrow> P a b) \<Longrightarrow> \<forall>(a,b)\<in>AxB. P a b"
  by fast

lemma good_card_imp_finite : "of_nat (card A) \<noteq> (0::'a::semiring_1) \<Longrightarrow> finite A"
  using card_ge_0_finite[of A] by fastforce

subsection \<open>Lists\<close>

subsubsection \<open>\<open>zip\<close>\<close>

lemma zip_truncate_left : "zip xs ys = zip (take (length ys) xs) ys"
  by (induct xs ys rule:list_induct2') auto

lemma zip_truncate_right : "zip xs ys = zip xs (take (length xs) ys)"
  by (induct xs ys rule:list_induct2') auto

text \<open>
  Lemmas \<open>zip_append1\<close> and \<open>zip_append2\<close> in theory @{theory HOL.List} have unnecessary
  \<open>take (length _)\<close> in them. Here are replacements.
\<close>

lemma zip_append_left :
  "zip (xs@ys) zs = zip xs zs @ zip ys (drop (length xs) zs)"
  using zip_append1 zip_truncate_right[of xs zs] by simp

lemma zip_append_right :
  "zip xs (ys@zs) = zip xs ys @ zip (drop (length ys) xs) zs"
  using zip_append2 zip_truncate_left[of xs ys] by simp

lemma length_concat_map_split_zip :
  "length [f x y. (x,y)\<leftarrow>zip xs ys] = min (length xs) (length ys)"
  by (induct xs ys rule: list_induct2') auto

lemma concat_map_split_eq_map_split_zip :
  "[f x y. (x,y)\<leftarrow>zip xs ys] = map (case_prod f) (zip xs ys)"
  by (induct xs ys rule: list_induct2') auto

lemma set_zip_map2 :
  "(a,z) \<in> set (zip xs (map f ys)) \<Longrightarrow> \<exists>b. (a,b) \<in> set (zip xs ys) \<and> z = f b"
  by (induct xs ys rule: list_induct2') auto

subsubsection \<open>\<open>concat\<close>\<close>

lemma concat_eq :
  "list_all2 (\<lambda>xs ys. length xs = length ys) xss yss \<Longrightarrow> concat xss = concat yss
        \<Longrightarrow> xss = yss"
  by  (induct xss yss rule: list_all2_induct) auto

lemma match_concat :
  fixes   bss :: "'b list list"
  defines eq_len: "eq_len \<equiv> \<lambda>xs ys. length xs = length ys"
  shows   "\<forall>as::'a list. length as = length (concat bss)
                \<longrightarrow> (\<exists>css::'a list list. as = concat css \<and> list_all2 eq_len css bss)"
proof (induct bss)
  from eq_len
    show "\<forall>as. length as = length (concat [])
                \<longrightarrow> (\<exists>css. as = concat css \<and> list_all2 eq_len css [])"
    by   simp
next
  fix fs :: "'b list" and fss :: "'b list list"
  assume prevcase: "\<forall>as. length as = length (concat fss)
                         \<longrightarrow> (\<exists>css. as = concat css \<and> list_all2 eq_len css fss)"
  have "\<And>as. length as = length (concat (fs # fss))
             \<Longrightarrow> (\<exists>css. as = concat css \<and> list_all2 eq_len css (fs # fss))"
  proof
    fix as :: "'a list"
    assume as: "length as = length (concat (fs#fss))"
    define xs ys where "xs = take (length fs) as" and "ys = drop (length fs) as"
    define gss where "gss = (SOME css. ys = concat css \<and> list_all2 eq_len css fss)"
    define hss where "hss = xs # gss"
    with xs_def ys_def as gss_def eq_len prevcase
      show "as = concat hss \<and> list_all2 eq_len hss (fs#fss)"
      using someI_ex[of "\<lambda>css. ys = concat css \<and> list_all2 eq_len css fss"] by auto
  qed
  thus "\<forall>as. length as = length (concat (fs # fss))
             \<longrightarrow> (\<exists>css. as = concat css \<and> list_all2 eq_len css (fs # fss))"
    by fast
qed 

subsubsection \<open>\<open>strip_while\<close>\<close>

lemma strip_while_0_nnil :
  "as \<noteq> [] \<Longrightarrow> set as \<noteq> 0 \<Longrightarrow> strip_while ((=) 0) as \<noteq> []"
  by (induct as rule: rev_nonempty_induct) auto

subsubsection \<open>\<open>sum_list\<close>\<close>

lemma const_sum_list :
  "\<forall>x \<in> set xs. f x = a \<Longrightarrow> sum_list (map f xs) = a * (length xs)"
  by (induct xs) auto

lemma sum_list_prod_cong :
  "\<forall>(x,y) \<in> set xys. f x y = g x y
        \<Longrightarrow> (\<Sum>(x,y)\<leftarrow>xys. f x y) = (\<Sum>(x,y)\<leftarrow>xys. g x y)"
  using arg_cong[of "map (case_prod f) xys" "map (case_prod g) xys" sum_list] by fastforce

lemma sum_list_prod_map2 :
  "(\<Sum>(a,y)\<leftarrow>zip as (map f bs). g a y) = (\<Sum>(a,b)\<leftarrow>zip as bs. g a (f b))"
  by (induct as bs rule: list_induct2') auto

lemma sum_list_fun_apply : "(\<Sum>x\<leftarrow>xs. f x) y = (\<Sum>x\<leftarrow>xs. f x y)"
  by (induct xs) auto

lemma sum_list_prod_fun_apply : "(\<Sum>(x,y)\<leftarrow>xys. f x y) z = (\<Sum>(x,y)\<leftarrow>xys. f x y z)"
  by (induct xys) auto

lemma (in comm_monoid_add) sum_list_plus :
  "length xs = length ys
        \<Longrightarrow> sum_list xs + sum_list ys = sum_list [a+b. (a,b)\<leftarrow>zip xs ys]"
proof (induct xs ys rule: list_induct2)
  case Cons thus ?case by (simp add: algebra_simps)
qed simp

lemma sum_list_const_mult_prod :
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'r::semiring_0"
  shows "r * (\<Sum>(x,y)\<leftarrow>xys. f x y) = (\<Sum>(x,y)\<leftarrow>xys. r * (f x y))"
  using sum_list_const_mult[of r "case_prod f"] prod.case_distrib[of "\<lambda>x. r*x" f]
  by    simp

lemma sum_list_mult_const_prod :
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'r::semiring_0"
  shows "(\<Sum>(x,y)\<leftarrow>xys. f x y) * r = (\<Sum>(x,y)\<leftarrow>xys. (f x y) * r)"
  using sum_list_mult_const[of "case_prod f" r] prod.case_distrib[of "\<lambda>x. x*r" f]
  by    simp

lemma sum_list_update :
  fixes xs :: "'a::ab_group_add list"
  shows "n < length xs \<Longrightarrow> sum_list (xs[n := y]) = sum_list xs - xs!n + y"
proof (induct xs arbitrary: n)
  case Cons thus ?case by (cases n) auto
qed simp

lemma sum_list_replicate0 : "sum_list (replicate n 0) = 0"
  by (induct n) auto

subsubsection \<open>\<open>listset\<close>\<close>

lemma listset_ConsI : "x \<in> X \<Longrightarrow> xs \<in> listset Xs \<Longrightarrow> x#xs \<in> listset (X#Xs)"
  unfolding listset_def set_Cons_def by simp

lemma listset_ConsD : "x#xs \<in> listset (A # As) \<Longrightarrow> x \<in> A \<and> xs \<in> listset As"
  unfolding listset_def set_Cons_def by auto

lemma listset_Cons_conv :
  "xs \<in> listset (A # As) \<Longrightarrow> (\<exists>y ys. y \<in> A \<and> ys \<in> listset As \<and> xs = y#ys)"
  unfolding listset_def set_Cons_def by auto

lemma listset_length : "xs \<in> listset Xs \<Longrightarrow> length xs = length Xs"
  using     listset_ConsD
  unfolding listset_def set_Cons_def
  by        (induct xs Xs rule: list_induct2') auto

lemma set_sum_list_element :
  "x \<in> (\<Sum>A\<leftarrow>As. A) \<Longrightarrow> \<exists>as \<in> listset As. x = (\<Sum>a\<leftarrow>as. a)"
proof (induct As arbitrary: x)
  case Nil hence "x = (\<Sum>a\<leftarrow>[]. a)" by simp
  moreover have "[] \<in> listset []" by simp
  ultimately show ?case by fast
next
  case (Cons A As)
  from this obtain a as
    where a_as: "a \<in> A" "as \<in> listset As" "x = (\<Sum>b\<leftarrow>(a#as). b)"
    using set_plus_def[of A]
    by    fastforce
  have "listset (A#As) = set_Cons A (listset As)" by simp
  with a_as(1,2) have "a#as \<in> listset (A#As)" unfolding set_Cons_def by fast
  with a_as(3) show "\<exists>bs\<in>listset (A#As). x = (\<Sum>b\<leftarrow>bs. b)" by fast
qed

lemma set_sum_list_element_Cons :
  assumes "x \<in> (\<Sum>X\<leftarrow>(A#As). X)"
  shows   "\<exists>a as. a\<in>A \<and> as \<in> listset As \<and> x = a + (\<Sum>b\<leftarrow>as. b)"
proof-
  from assms obtain xs where xs: "xs \<in> listset (A#As)" "x = (\<Sum>b\<leftarrow>xs. b)"
    using set_sum_list_element by fast
  from xs(1) obtain a as where "a \<in> A" "as \<in> listset As" "xs = a # as"
    using listset_Cons_conv by fast
  with xs(2) show ?thesis by auto
qed

lemma sum_list_listset : "as \<in> listset As \<Longrightarrow> sum_list as \<in> (\<Sum>A\<leftarrow>As. A)"
proof-
  have "length as = length As \<Longrightarrow> as \<in> listset As \<Longrightarrow> sum_list as \<in> (\<Sum>A\<leftarrow>As. A)"
  proof (induct as As rule: list_induct2)
    case Nil show ?case by simp
  next
    case (Cons a as A As) thus ?case
      using listset_ConsD[of a] set_plus_def by auto
  qed
  thus "as \<in> listset As \<Longrightarrow> sum_list as \<in> (\<Sum>A\<leftarrow>As. A)" using listset_length by fast
qed

lemma listsetI_nth :
  "length xs = length Xs \<Longrightarrow> \<forall>n<length xs. xs!n \<in> Xs!n \<Longrightarrow> xs \<in> listset Xs"
proof (induct xs Xs rule: list_induct2)
  case Nil show ?case by simp
next
  case (Cons x xs X Xs) thus "x#xs \<in> listset (X#Xs)"
    using listset_ConsI[of x X xs Xs] by fastforce
qed

lemma listsetD_nth : "xs \<in> listset Xs \<Longrightarrow> \<forall>n<length xs. xs!n \<in> Xs!n"
proof-
  have "length xs = length Xs \<Longrightarrow> xs \<in> listset Xs \<Longrightarrow> \<forall>n<length xs. xs!n \<in> Xs!n"
  proof (induct xs Xs rule: list_induct2)
     case Nil show ?case by simp
  next
    case (Cons x xs X Xs)
    from Cons(3) have x_xs: "x \<in> X" "xs \<in> listset Xs"
      using listset_ConsD[of x] by auto
    with Cons(2) have 1: "(x#xs)!0 \<in> (X#Xs)!0" "\<forall>n<length xs. xs!n \<in> Xs!n"
      by auto
    have "\<And>n. n < length (x#xs) \<Longrightarrow> (x#xs)!n \<in> (X#Xs)!n"
    proof-
      fix n assume "n < length (x#xs)"
      with 1 show "(x#xs)!n \<in> (X#Xs)!n" by (cases n) auto
    qed
    thus "\<forall>n < length (x#xs). (x#xs)!n \<in> (X#Xs)!n" by fast
  qed
  thus "xs \<in> listset Xs \<Longrightarrow> \<forall>n<length xs. xs!n \<in> Xs!n" using listset_length by fast
qed

lemma set_listset_el_subset :
  "xs \<in> listset Xs \<Longrightarrow> \<forall>X\<in>set Xs. X \<subseteq> A \<Longrightarrow> set xs \<subseteq> A"
proof-
  have "\<lbrakk> length xs = length Xs; xs \<in> listset Xs; \<forall>X\<in>set Xs. X \<subseteq> A \<rbrakk> 
              \<Longrightarrow> set xs \<subseteq> A"
  proof (induct xs Xs rule: list_induct2)
    case Cons thus ?case using listset_ConsD by force
  qed simp
  thus "xs \<in> listset Xs \<Longrightarrow> \<forall>X\<in>set Xs. X \<subseteq> A \<Longrightarrow> set xs \<subseteq> A"
    using listset_length by fast
qed


subsection \<open>Functions\<close>

subsubsection \<open>Miscellaneous facts\<close>

lemma sum_fun_apply : "finite A \<Longrightarrow> (\<Sum>a\<in>A. f a) x = (\<Sum>a\<in>A. f a x)"
  by (induct set: finite) auto

lemma sum_single_nonzero :
  "finite A \<Longrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. f x y = (if y = x then g x else 0)) 
        \<Longrightarrow> (\<forall>x\<in>A. sum (f x) A = g x)"
proof (induct A rule: finite_induct)
  case (insert a A)
  show "\<forall>x\<in>insert a A. sum (f x) (insert a A) = g x"
  proof
    fix x assume x: "x \<in> insert a A"
    show "sum (f x) (insert a A) = g x"
    proof (cases "x = a")
      case True
      moreover with insert(2,4) have "\<forall>y\<in>A. f x y = 0" by simp
      ultimately show ?thesis using insert(1,2,4) by simp
    next
      case False with x insert show ?thesis by simp
    qed
  qed
qed simp

lemma distrib_comp_sum_right : "(T + T') \<circ> S = (T \<circ> S) + (T' \<circ> S)"
  by auto

subsubsection \<open>Support of a function\<close>

definition supp :: "('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where "supp f = {x. f x \<noteq> 0}"

lemma suppI: "f x \<noteq> 0 \<Longrightarrow> x \<in> supp f"
  using supp_def by fast

lemma suppI_contra: "x \<notin> supp f \<Longrightarrow> f x = 0"
  using suppI by fast

lemma suppD: "x \<in> supp f \<Longrightarrow> f x \<noteq> 0"
  using supp_def by fast

lemma suppD_contra: "f x = 0 \<Longrightarrow> x \<notin> supp f"
  using suppD by fast

lemma zerofun_imp_empty_supp : "supp 0 = {}"
  unfolding supp_def by simp

lemma supp_zerofun_subset_any : "supp 0 \<subseteq> A"
  using zerofun_imp_empty_supp by fast

lemma supp_sum_subset_union_supp :
  fixes     f g :: "'a \<Rightarrow> 'b::monoid_add"
  shows     "supp (f + g) \<subseteq> supp f \<union> supp g"
  unfolding supp_def
  by        auto

lemma supp_neg_eq_supp :
  fixes     f :: "'a \<Rightarrow> 'b::group_add"
  shows     "supp (- f) = supp f"
  unfolding supp_def
  by        auto

lemma supp_diff_subset_union_supp :
  fixes     f g :: "'a \<Rightarrow> 'b::group_add"
  shows     "supp (f - g) \<subseteq> supp f \<union> supp g"
  unfolding supp_def
  by        auto

abbreviation restrict0 :: "('a\<Rightarrow>'b::zero) \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'b)" (infix "\<down>" 70)
  where "restrict0 f A \<equiv> (\<lambda>a. if a \<in> A then f a else 0)"

lemma supp_restrict0 : "supp (f\<down>A) \<subseteq> A"
proof-
  have "\<And>a. a \<notin> A \<Longrightarrow> a \<notin> supp (f\<down>A)" using suppD_contra[of "f\<down>A"] by simp
  thus ?thesis by fast
qed

lemma bij_betw_restrict0 : "bij_betw f A B \<Longrightarrow> bij_betw (f \<down> A) A B"
  using     bij_betw_imp_inj_on bij_betw_imp_surj_on
  unfolding bij_betw_def inj_on_def
  by        auto


subsubsection \<open>Convolution\<close>

definition convolution ::
  "('a::group_add \<Rightarrow> 'b::{comm_monoid_add,times}) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b)"
  where "convolution f g
              = (\<lambda>x. \<Sum>y|x - y \<in> supp f \<and> y \<in> supp g. (f (x - y)) * g y)"
  \<comment> \<open>More often than not, this definition will be used in the case that @{text "'b"} is of class
        @{text "mult_zero"}, in which case the conditions @{term "x - y \<in> supp f"} and
        @{term "y \<in> supp g"} are obviously mathematically unnecessary. However, they also serve to
        ensure that the sum is taken over a finite set in the case that at least one of @{term f}
        and @{term g} is almost everywhere zero.\<close>

lemma convolution_zero :
  fixes     f g :: "'a::group_add \<Rightarrow> 'b::{comm_monoid_add,mult_zero}"
  shows     "f = 0 \<or> g = 0 \<Longrightarrow> convolution f g = 0"
  unfolding convolution_def
  by        auto

lemma convolution_symm :
  fixes f g :: "'a::group_add \<Rightarrow> 'b::{comm_monoid_add,times}"
  shows "convolution f g
              = (\<lambda>x. \<Sum>y|y \<in> supp f \<and> -y + x \<in> supp g. (f y) * g (-y + x))"
proof
  fix x::'a
  define c1 c2 i S1 S2
    where "c1 y = (f (x - y)) * g y"
      and "c2 y = (f y) * g (-y + x)"
      and "i y = -y + x"
      and "S1 = {y. x - y \<in> supp f \<and> y \<in> supp g}"
      and "S2 = {y. y \<in> supp f \<and> -y + x \<in> supp g}"
    for y
  have "inj_on i S2" unfolding inj_on_def using i_def by simp
  hence "(\<Sum>y\<in>(i ` S2). c1 y) = (\<Sum>y\<in>S2. (c1 \<circ> i) y)"
    using sum.reindex by fast
  moreover have S1_iS2: "S1 = i ` S2"
  proof (rule seteqI)
    fix y assume y_S1: "y \<in> S1"
    define z where "z = x - y"
    hence y_eq: "-z + x = y" by (auto simp add: algebra_simps)
    hence "-z + x \<in> supp g" using y_S1 S1_def by fast
    moreover have "z \<in> supp f" using z_def y_S1 S1_def by fast
    ultimately have "z \<in> S2" using S2_def by fast
    moreover have "y = i z" using i_def [abs_def] y_eq by fast
    ultimately show "y \<in> i ` S2" by fast
  next
    fix y assume "y \<in> i ` S2"
    from this obtain z where z_S2: "z \<in> S2" and y_eq: "y = -z + x"
      using i_def by fast
    from y_eq have "x - y = z" by (auto simp add: algebra_simps)
    hence "x - y \<in> supp f \<and> y \<in> supp g" using y_eq z_S2 S2_def by fastforce
    thus "y \<in> S1" using S1_def by fast
  qed
  ultimately have "(\<Sum>y\<in>S1. c1 y) = (\<Sum>y\<in>S2. (c1 \<circ> i) y)" by fast
  with i_def c1_def c2_def have "(\<Sum>y\<in>S1. c1 y) = (\<Sum>y\<in>S2. c2 y)"
    using diff_add_eq_diff_diff_swap[of x _ x] by simp
  thus "convolution f g x
              = (\<Sum>y|y \<in> supp f \<and> -y + x \<in> supp g. (f y) * g (-y + x))"
    unfolding S1_def c1_def S2_def c2_def convolution_def by fast
qed  

lemma supp_convolution_subset_sum_supp :
  fixes f g :: "'a::group_add \<Rightarrow> 'b::{comm_monoid_add,times}"
  shows "supp (convolution f g) \<subseteq> supp f + supp g"
proof-
  define SS where "SS x = {y. x-y \<in> supp f \<and> y \<in> supp g}" for x
  have "convolution f g = (\<lambda>x. sum (\<lambda>y. (f (x - y)) * g y) (SS x))"
    unfolding SS_def convolution_def by fast
  moreover have "\<And>x. x \<notin> supp f + supp g \<Longrightarrow> SS x = {}"
  proof-
    have "\<And>x. SS x \<noteq> {} \<Longrightarrow> x \<in> supp f + supp g"
    proof-
      fix x::'a assume "SS x \<noteq> {}"
      from this obtain y where "x - y \<in> supp f" and y_G: "y \<in> supp g"
        using SS_def by fast
      from this obtain z where z_F: "z \<in> supp f" and z_eq: "x - y = z" by fast
      from z_eq have "x = z + y" using diff_eq_eq by fast
      with z_F y_G show "x \<in> supp f + supp g" by fast
    qed
    thus "\<And>x. x \<notin> supp f + supp g \<Longrightarrow> SS x = {}" by fast
  qed
  ultimately have "\<And>x. x \<notin> supp f + supp g
                        \<Longrightarrow> convolution f g x = sum (\<lambda>y. (f (x - y)) * g y) {}"
    by simp
  hence "\<And>x. x \<notin> supp f + supp g \<Longrightarrow> convolution f g x = 0"
    using sum.empty by simp
  thus ?thesis unfolding supp_def by fast
qed


subsection \<open>Almost-everywhere-zero functions\<close>

subsubsection \<open>Definition and basic properties\<close>

definition "aezfun_set = {f::'a\<Rightarrow>'b::zero. finite (supp f)}"

lemma aezfun_setD: "f \<in> aezfun_set \<Longrightarrow> finite (supp f)"
  unfolding aezfun_set_def by fast

lemma aezfun_setI: "finite (supp f) \<Longrightarrow> f \<in> aezfun_set"
  unfolding aezfun_set_def by fast

lemma zerofun_is_aezfun : "0 \<in> aezfun_set"
  unfolding supp_def aezfun_set_def by auto

lemma sum_of_aezfun_is_aezfun :
  fixes     f g :: "'a\<Rightarrow>'b::monoid_add"
  shows     "f \<in> aezfun_set \<Longrightarrow> g \<in> aezfun_set \<Longrightarrow> f + g \<in> aezfun_set"
  using     supp_sum_subset_union_supp[of f g] finite_subset[of _ "supp f \<union> supp g"]
  unfolding aezfun_set_def
  by        fastforce

lemma neg_of_aezfun_is_aezfun :
  fixes     f :: "'a\<Rightarrow>'b::group_add"
  shows     "f \<in> aezfun_set \<Longrightarrow> - f \<in> aezfun_set"
  using     supp_neg_eq_supp[of f]
  unfolding aezfun_set_def
  by        simp

lemma diff_of_aezfun_is_aezfun :
  fixes     f g :: "'a\<Rightarrow>'b::group_add"
  shows     "f \<in> aezfun_set \<Longrightarrow> g \<in> aezfun_set \<Longrightarrow> f - g \<in> aezfun_set"
  using     supp_diff_subset_union_supp[of f g] finite_subset[of _ "supp f \<union> supp g"]
  unfolding aezfun_set_def
  by        fastforce

lemma restrict_and_extend0_aezfun_is_aezfun :
  assumes "f \<in> aezfun_set"
  shows   "f\<down>A \<in> aezfun_set"
proof (rule aezfun_setI)
  have "\<And>a. a \<notin> supp f \<inter> A \<Longrightarrow> a \<notin> supp (f\<down>A)"
  proof-
    fix a assume "a \<notin> supp f \<inter> A"
    thus "a \<notin> supp (f\<down>A)" using suppI_contra[of a] suppD_contra[of "f\<down>A" a]
      by (cases "a \<in> A") auto
  qed
  with assms show "finite (supp (f\<down>A))"
    using aezfun_setD finite_subset[of "supp (f\<down>A)"] by auto
qed

subsubsection \<open>Delta (impulse) functions\<close>

text \<open>The notation is set up in the order output-input so that later when these are used to define
        the group ring RG, it will be in order ring-element-group-element.\<close>

definition deltafun :: "'b::zero \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b)" (infix "\<delta>" 70)
  where "b \<delta> a = (\<lambda>x. if x = a then b else 0)"

lemma deltafun_apply_eq : "(b \<delta> a) a = b"
  unfolding deltafun_def by simp

lemma deltafun_apply_neq : "x \<noteq> a \<Longrightarrow> (b \<delta> a) x = 0"
  unfolding deltafun_def by simp

lemma deltafun0 : "0 \<delta> a = 0"
  unfolding deltafun_def by auto

lemma deltafun_plus :
  fixes     b c :: "'b::monoid_add"
  shows     "(b+c) \<delta> a = (b \<delta> a) + (c \<delta> a)"
  unfolding deltafun_def
  by        auto

lemma supp_delta0fun :  "supp (0 \<delta> a) = {}"
  unfolding supp_def deltafun_def by simp

lemma supp_deltafun :  "b \<noteq> 0 \<Longrightarrow> supp (b \<delta> a) = {a}"
  unfolding supp_def deltafun_def by simp

lemma deltafun_is_aezfun : "b \<delta> a \<in> aezfun_set"
proof (cases "b = 0")
  case True
  hence "supp (b \<delta> a) = {}" using supp_delta0fun[of a] by fast
  thus ?thesis unfolding aezfun_set_def by simp
next
  case False thus ?thesis using supp_deltafun[of b a] unfolding aezfun_set_def by simp
qed

lemma aezfun_common_supp_spanning_set' :
  "finite A \<Longrightarrow> \<exists>as. distinct as \<and> set as = A
      \<and> ( \<forall>f::'a \<Rightarrow> 'b::semiring_1. supp f \<subseteq> A
                   \<longrightarrow> (\<exists>bs. length bs = length as \<and> f = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta> a)) )"
proof (induct rule: finite_induct)
  case empty show ?case unfolding supp_def by auto
next
  case (insert a A)
  from insert(3) obtain as
    where as: "distinct as" "set as = A"
              "\<And>f::'a \<Rightarrow> 'b. supp f \<subseteq> A
                    \<Longrightarrow> \<exists>bs. length bs = length as \<and> f = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta> a)"
    by fast
  from as(1,2) insert(2) have "distinct (a#as)" "set (a#as) = insert a A" by auto
  moreover
    have "\<And>f::'a \<Rightarrow> 'b::semiring_1. supp f \<subseteq> insert a A
                \<Longrightarrow> (\<exists>bs. length bs = length (a#as)
                  \<and> f = (\<Sum>(b,a)\<leftarrow>zip bs (a#as). b \<delta> a))"
  proof-
    fix f :: "'a \<Rightarrow> 'b" assume supp_f : "supp f \<subseteq> insert a A"
    define g where "g x = (if x = a then 0 else f x)" for x
    have "supp g \<subseteq> A"
    proof
      fix x assume x: "x \<in> supp g"
      with x supp_f g_def have "x \<in> insert a A" unfolding supp_def by auto
      moreover from x g_def have "x \<noteq> a" unfolding supp_def by auto
      ultimately show "x \<in> A" by fast
    qed
    with as(3) obtain bs
      where bs: "length bs = length as" "g = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta> a)"
      by    fast
    from bs(1) have "length ((f a) # bs) = length (a#as)" by auto
    moreover from g_def bs(2) have "f = (\<Sum>(b,a)\<leftarrow>zip ((f a) # bs) (a#as). b \<delta> a)"
      using deltafun_apply_eq[of "f a" a] deltafun_apply_neq[of _ a "f a"] by (cases) auto
    ultimately
      show "\<exists>bs. length bs = length (a#as) \<and> f = (\<Sum>(b,a)\<leftarrow>zip bs (a#as). b \<delta> a)"
      by   fast
  qed
  ultimately show ?case by fast
qed

subsubsection \<open>Convolution of almost-everywhere-zero functions\<close>

lemma convolution_eq_sum_over_supp_right :
  fixes   g f :: "'a::group_add \<Rightarrow> 'b::{comm_monoid_add,mult_zero}"
  assumes "g \<in> aezfun_set"
  shows   "convolution f g = (\<lambda>x. \<Sum>y\<in>supp g. (f (x - y)) * g y )"
proof
  fix x::'a
  define SS where "SS = {y. x - y \<in> supp f \<and> y \<in> supp g}"
  have "finite (supp g)" using assms unfolding aezfun_set_def by fast
  moreover have "SS \<subseteq> supp g" unfolding SS_def by fast
  moreover have "\<And>y. y \<in> supp g - SS \<Longrightarrow> (f (x - y)) * g y = 0" using SS_def unfolding supp_def by auto
  ultimately show "convolution f g x = (\<Sum>y\<in>supp g. (f (x - y)) * g y )"
    unfolding convolution_def
    using     SS_def sum.mono_neutral_left[of "supp g" SS "\<lambda>y. (f (x - y)) * g y"]
    by        fast
qed

lemma convolution_symm_eq_sum_over_supp_left :
  fixes   f g :: "'a::group_add \<Rightarrow> 'b::{comm_monoid_add,mult_zero}"
  assumes "f \<in> aezfun_set"
  shows   "convolution f g = (\<lambda>x. \<Sum>y\<in>supp f. (f y) * g (-y + x))"
proof
  fix x::'a
  define SS where "SS = {y. y \<in> supp f \<and> -y + x \<in> supp g}"
  have "finite (supp f)" using assms unfolding aezfun_set_def by fast
  moreover have "SS \<subseteq> supp f" using SS_def by fast
  moreover have "\<And>y. y \<in> supp f - SS \<Longrightarrow> (f y) * g (-y + x) = 0"
    using SS_def unfolding supp_def by auto
  ultimately
    have "(\<Sum>y\<in>SS. (f y) * g (-y + x)) = (\<Sum>y\<in>supp f. (f y) * g (-y + x) )"
    unfolding convolution_def
    using     SS_def sum.mono_neutral_left[of "supp f" SS "\<lambda>y. (f y) * g (-y + x)"]
    by        fast
  thus "convolution f g x = (\<Sum>y\<in>supp f. (f y) * g (-y + x) )"
    using SS_def convolution_symm[of f g] by simp
qed

lemma convolution_delta_left :
  fixes b :: "'b::{comm_monoid_add,mult_zero}"
  and   a :: "'a::group_add"
  and   f :: "'a \<Rightarrow> 'b"
  shows "convolution (b \<delta> a) f = (\<lambda>x. b * f (-a + x))"
proof (cases "b = 0")
  case True
  moreover have "convolution (b \<delta> a) f = 0"
  proof-
    from True have "convolution (b \<delta> a) f = convolution 0 f"
      using deltafun0[of a] arg_cong[of "0 \<delta> a" "0::'a\<Rightarrow>'b"]
      by (simp add: \<open>0 \<delta> a = 0\<close> \<open>b = 0\<close>)
    thus ?thesis using convolution_zero by auto
  qed
  ultimately show ?thesis by auto
next
  case False thus ?thesis
    using deltafun_is_aezfun[of b a] convolution_symm_eq_sum_over_supp_left
          supp_deltafun[of b a] deltafun_apply_eq[of b a]
    by    fastforce
qed

lemma convolution_delta_right :
  fixes b :: "'b::{comm_monoid_add,mult_zero}"
  and   f :: "'a::group_add \<Rightarrow> 'b" and a::'a
  shows "convolution f (b \<delta> a) = (\<lambda>x. f (x - a) * b)"
proof (cases "b = 0")
  case True
  moreover have "convolution f (b \<delta> a) = 0"
  proof-
    from True have "convolution f (b \<delta> a) = convolution f 0"
      using deltafun0[of a] arg_cong[of "0 \<delta> a" "0::'a\<Rightarrow>'b"] 
      by (simp add: \<open>0 \<delta> a = 0\<close>)
    thus ?thesis using convolution_zero by auto
  qed
  ultimately show ?thesis by auto
next
  case False thus ?thesis
    using deltafun_is_aezfun[of b a] convolution_eq_sum_over_supp_right
          supp_deltafun[of b a] deltafun_apply_eq[of b a]
    by    fastforce
qed

lemma   convolution_delta_delta :
  fixes b1 b2 :: "'b::{comm_monoid_add,mult_zero}"
  and   a1 a2 :: "'a::group_add"
  shows "convolution (b1 \<delta> a1) (b2 \<delta> a2) = (b1 * b2) \<delta> (a1 + a2)"
proof
  fix x::'a
  have 1: "convolution (b1 \<delta> a1) (b2 \<delta> a2) x = (b1 \<delta> a1) (x - a2) * b2"
    using convolution_delta_right[of "b1 \<delta> a1"] by simp
  show "convolution (b1 \<delta> a1) (b2 \<delta> a2) x = ((b1 * b2) \<delta> (a1 + a2)) x"
  proof (cases "x = a1 + a2")
    case True
    hence "x - a2 = a1" by (simp add: algebra_simps)
    with 1 have "convolution (b1 \<delta> a1) (b2 \<delta> a2) x = b1 * b2"
      using deltafun_apply_eq[of b1 a1] by simp
    with True show ?thesis
      using deltafun_apply_eq[of "b1 * b2" "a1 + a2"] by simp
  next
    case False
    hence "x - a2 \<noteq> a1" by (simp add: algebra_simps)
    with 1 have "convolution (b1 \<delta> a1) (b2 \<delta> a2) x = 0"
      using deltafun_apply_neq[of "x - a2" a1 b1] by simp
    with False show ?thesis using deltafun_apply_neq by simp
  qed
qed

lemma convolution_of_aezfun_is_aezfun :
  fixes     f g :: "'a::group_add \<Rightarrow> 'b::{comm_monoid_add,times}"
  shows     "f \<in> aezfun_set \<Longrightarrow> g \<in> aezfun_set \<Longrightarrow> convolution f g \<in> aezfun_set"
  using     supp_convolution_subset_sum_supp[of f g]
            finite_set_plus[of "supp f" "supp g"] finite_subset
  unfolding aezfun_set_def
  by        fastforce

lemma convolution_assoc :
  fixes   f h g :: "'a::group_add \<Rightarrow> 'b::semiring_0"
  assumes f_aez: "f \<in> aezfun_set" and h_aez: "h \<in> aezfun_set"
  shows   "convolution (convolution f g) h = convolution f (convolution g h)"
proof
  define fg gh where "fg = convolution f g" and "gh = convolution g h"
  fix x::'a
  have "convolution fg h x
              = (\<Sum>y\<in>supp f. (\<Sum>z\<in>supp h. f y * g (-y + x - z) * h z) )"
  proof-
    have "convolution fg h x = (\<Sum>z\<in>supp h. fg (x - z) * h z )"
      using h_aez convolution_eq_sum_over_supp_right[of h fg] by simp
    moreover have "\<And>z. fg (x - z) * h z
                        = (\<Sum>y\<in>supp f. f y * g (-y + x - z) * h z)"
    proof-
      fix z::'a
      have "fg (x - z) = (\<Sum>y\<in>supp f. f y * g (-y + (x - z)) )"
        using fg_def f_aez convolution_symm_eq_sum_over_supp_left by fastforce
      hence "fg (x - z) * h z = (\<Sum>y\<in>supp f. f y * g (-y + (x - z)) * h z )"
        using sum_distrib_right by simp
      thus "fg (x - z) * h z = (\<Sum>y\<in>supp f. f y * g (-y + x - z) * h z )"
        by (simp add: algebra_simps)
    qed
    ultimately 
      have  "convolution fg h x
                  = (\<Sum>z\<in>supp h. (\<Sum>y\<in>supp f. f y * g (-y + x - z) * h z) )"
      using sum.cong
      by    simp
    thus ?thesis using sum.swap by simp
  qed
  moreover have "convolution f gh x
                      = (\<Sum>y\<in>supp f. (\<Sum>z\<in>supp h. f y * g (-y + x - z) * h z) )"
  proof-
    have "convolution f gh x = (\<Sum>y\<in>supp f. f y * gh (-y + x) )"
      using f_aez convolution_symm_eq_sum_over_supp_left[of f gh] by simp
    moreover have "\<And>y. f y * gh (-y + x)
                        = (\<Sum>z\<in>supp h. f y * g (-y + x - z) * h z)"
    proof-
      fix y::'a
      have triple_cong: "\<And>z. f y * (g (-y + x - z) * h z)
                              = f y * g (-y + x - z) * h z"
        using mult.assoc[of "f y"] by simp
      have "gh (-y + x) = (\<Sum>z\<in>supp h. g (-y + x - z) * h z)"
        using gh_def h_aez convolution_eq_sum_over_supp_right by fastforce
      hence "f y * gh (-y + x) = (\<Sum>z\<in>supp h. f y * (g (-y + x - z) * h z))"
        using sum_distrib_left by simp
      also have "\<dots> = (\<Sum>z\<in>supp h. f y * g (-y + x - z) * h z)"
        using triple_cong sum.cong by simp
      finally
        show "f y * gh (-y + x) = (\<Sum>z\<in>supp h. f y * g (-y + x - z) * h z)"
        by   fast
    qed
    ultimately show ?thesis using sum.cong by simp
  qed
  ultimately show "convolution fg h x = convolution f gh x" by simp
qed

lemma convolution_distrib_left :
  fixes   g h f :: "'a::group_add \<Rightarrow> 'b::semiring_0"
  assumes "g \<in> aezfun_set" "h \<in> aezfun_set"
  shows   "convolution f (g + h) = convolution f g + convolution f h"
proof
  define gh GH where "gh = g + h" and "GH = supp g \<union> supp h"
  have fin_GH: "finite GH" using GH_def assms unfolding aezfun_set_def by fast
  have gh_aezfun: "gh \<in> aezfun_set" using gh_def assms sum_of_aezfun_is_aezfun by fast
  fix x::'a
  have zero_ext_g : "\<And>y. y \<in> GH - supp g \<Longrightarrow> (f (x - y)) * g y = 0"
  and  zero_ext_h : "\<And>y. y \<in> GH - supp h \<Longrightarrow> (f (x - y)) * h y = 0"
  and  zero_ext_gh: "\<And>y. y \<in> GH - supp gh \<Longrightarrow> (f (x - y)) * gh y = 0"
    unfolding supp_def by auto
  have "convolution f gh x = (\<Sum>y\<in>supp gh. (f (x - y)) * gh y)"
    using assms gh_aezfun convolution_eq_sum_over_supp_right[of gh f] by simp
  also from gh_def GH_def have "\<dots> = (\<Sum>y\<in>GH. (f (x - y)) * gh y)"
    using fin_GH supp_sum_subset_union_supp zero_ext_gh
          sum.mono_neutral_left[of GH "supp gh" "(\<lambda>y. (f (x - y)) * gh y)"]
    by    fast
  also from gh_def
    have  "\<dots> = (\<Sum>y\<in>GH. (f (x - y)) * g y) + (\<Sum>y\<in>GH. (f (x - y)) * h y)"
    using sum.distrib by (simp add: algebra_simps)
  finally show "convolution f gh x = (convolution f g + convolution f h) x"
    using assms GH_def fin_GH zero_ext_g zero_ext_h
          sum.mono_neutral_right[of GH "supp g" "(\<lambda>y. (f (x - y)) * g y)"]
          sum.mono_neutral_right[of GH "supp h" "(\<lambda>y. (f (x - y)) * h y)"]
          convolution_eq_sum_over_supp_right[of g f]
          convolution_eq_sum_over_supp_right[of h f]
    by    fastforce
qed

lemma convolution_distrib_right :
  fixes   f g h :: "'a::group_add \<Rightarrow> 'b::semiring_0"
  assumes "f \<in> aezfun_set" "g \<in> aezfun_set"
  shows   "convolution (f + g) h = convolution f h + convolution g h"
proof
  define fg FG where "fg = f + g" and "FG = supp f \<union> supp g"
  have fin_FG: "finite FG" using FG_def assms unfolding aezfun_set_def by fast
  have fg_aezfun: "fg \<in> aezfun_set" using fg_def assms sum_of_aezfun_is_aezfun by fast
  fix x::'a
  have zero_ext_f : "\<And>y. y \<in> FG - supp f \<Longrightarrow> (f y) * h (-y + x) = 0"
  and  zero_ext_g : "\<And>y. y \<in> FG - supp g \<Longrightarrow> (g y) * h (-y + x) = 0"
  and  zero_ext_fg: "\<And>y. y \<in> FG - supp fg \<Longrightarrow> (fg y) * h (-y + x) = 0"
    unfolding supp_def by auto
  from assms have "convolution fg h x = (\<Sum>y\<in>supp fg. (fg y) * h (-y + x))"
    using fg_aezfun convolution_symm_eq_sum_over_supp_left[of fg h] by simp
  also from fg_def FG_def have "\<dots> = (\<Sum>y\<in>FG. (fg y) * h (-y + x))"
    using fin_FG supp_sum_subset_union_supp zero_ext_fg
          sum.mono_neutral_left[of FG "supp fg" "(\<lambda>y. (fg y) * h (-y + x))"]
    by    fast
  also from fg_def
    have  "\<dots> = (\<Sum>y\<in>FG. (f y) * h (-y + x)) + (\<Sum>y\<in>FG. (g y) * h (-y + x))"
    using sum.distrib by (simp add: algebra_simps)
  finally show "convolution fg h x = (convolution f h + convolution g h) x"
    using assms FG_def fin_FG zero_ext_f zero_ext_g
          sum.mono_neutral_right[of FG "supp f" "(\<lambda>y. (f y) * h (-y + x))"]
          sum.mono_neutral_right[of FG "supp g" "(\<lambda>y. (g y) * h (-y + x))"]
          convolution_symm_eq_sum_over_supp_left[of f h]
          convolution_symm_eq_sum_over_supp_left[of g h]
    by    fastforce
qed

subsubsection \<open>Type definition, instantiations, and instances\<close>

typedef (overloaded) ('a::zero,'b) aezfun = "aezfun_set :: ('b\<Rightarrow>'a) set"
  morphisms aezfun Abs_aezfun
  using     zerofun_is_aezfun
  by        fast

setup_lifting type_definition_aezfun

lemma aezfun_finite_supp : "finite (supp (aezfun a))"
  using aezfun.aezfun unfolding aezfun_set_def by fast

lemma aezfun_transfer : "aezfun a = aezfun b \<Longrightarrow> a = b" by transfer fast

instantiation aezfun :: (zero, type) zero
begin
  lift_definition zero_aezfun :: "('a,'b) aezfun" is "0::'b\<Rightarrow>'a"
    using zerofun_is_aezfun by fast
  instance ..
end

lemma zero_aezfun_transfer : "Abs_aezfun ((0::'b::zero) \<delta> (0::'a::zero)) = 0"
proof-
  define zb za where "zb = (0::'b)" and "za = (0::'a)"
  hence "zb \<delta> za = 0" using deltafun0[of za] by fast
  moreover have "aezfun 0 = 0" using zero_aezfun.rep_eq by fast
  ultimately have "zb \<delta> za = aezfun 0" by simp
  with zb_def za_def show ?thesis using aezfun_inverse by simp
qed

lemma zero_aezfun_apply [simp]: "aezfun 0 x = 0"
  by transfer simp

instantiation aezfun :: (monoid_add, type) plus
begin
  lift_definition plus_aezfun :: "('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun"
    is    "\<lambda>f g. f + g"
    using sum_of_aezfun_is_aezfun
    by    auto
  instance ..
end

lemma plus_aezfun_apply [simp]: "aezfun (a+b) x = aezfun a x + aezfun b x"
  by transfer simp

instance aezfun :: (monoid_add, type) semigroup_add
proof
  fix a b c :: "('a, 'b) aezfun"
  have "aezfun (a + b + c) = aezfun (a + (b + c))"
  proof
    fix x::'b show "aezfun (a + b + c) x = aezfun (a + (b + c)) x" 
      using add.assoc[of "aezfun a x"] by simp
  qed
  thus "a + b + c = a + (b + c)" by transfer fast
qed

instance aezfun :: (monoid_add, type) monoid_add
proof
  fix a b c :: "('a, 'b) aezfun"
  show "0 + a = a" by transfer simp
  show "a + 0 = a" by transfer simp
qed

lemma sum_list_aezfun_apply [simp] :
  "aezfun (sum_list as) x = (\<Sum>a\<leftarrow>as. aezfun a x)"
  by (induct as) auto

lemma sum_list_map_aezfun_apply [simp] :
  "aezfun (\<Sum>a\<leftarrow>as. f a) x = (\<Sum>a\<leftarrow>as. aezfun (f a) x)"
  by (induct as) auto

lemma sum_list_map_aezfun [simp] :
  "aezfun (\<Sum>a\<leftarrow>as. f a) = (\<Sum>a\<leftarrow>as. aezfun (f a))"
  using sum_list_map_aezfun_apply[of f] sum_list_fun_apply[of "aezfun \<circ> f"] by auto

lemma sum_list_prod_map_aezfun_apply :  
  "aezfun (\<Sum>(x,y)\<leftarrow>xys. f x y) a = (\<Sum>(x,y)\<leftarrow>xys. aezfun (f x y) a)"
  by (induct xys) auto

lemma sum_list_prod_map_aezfun :
  "aezfun (\<Sum>(x,y)\<leftarrow>xys. f x y) = (\<Sum>(x,y)\<leftarrow>xys. aezfun (f x y))"
  using sum_list_prod_map_aezfun_apply[of f]
        sum_list_prod_fun_apply[of "\<lambda>y z. aezfun (f y z)"]
  by    auto

instance aezfun :: (comm_monoid_add, type) comm_monoid_add
proof
  fix a b :: "('a, 'b) aezfun"
  have "aezfun (a + b) = aezfun (b + a)"
  proof
    fix x::'b show "aezfun (a + b) x = aezfun (b + a) x" 
      using add.commute[of "aezfun a x"] by simp
  qed
  thus "a + b = b + a" by transfer fast
  show "0 + a = a" by simp
qed

lemma sum_aezfun_apply [simp] :
  "finite A \<Longrightarrow> aezfun (\<Sum>A) x = (\<Sum>a\<in>A. aezfun a x)"
  by (induct set: finite) auto

instantiation aezfun :: (group_add, type) minus
begin
  lift_definition minus_aezfun :: "('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun"
    is    "\<lambda>f g. f - g"
    using diff_of_aezfun_is_aezfun
    by    fast
  instance ..
end

lemma minus_aezfun_apply [simp]: "aezfun (a-b) x = aezfun a x - aezfun b x"
  by transfer simp

instantiation aezfun :: (group_add, type) uminus
begin
  lift_definition uminus_aezfun :: "('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun" is "\<lambda>f. - f"
    using neg_of_aezfun_is_aezfun by fast
  instance ..
end

lemma uminus_aezfun_apply [simp]: "aezfun (-a) x = - aezfun a x"
  by transfer simp

lemma aezfun_left_minus [simp] :
  fixes a :: "('a::group_add, 'b) aezfun"
  shows "- a + a = 0"
  by    transfer simp

lemma aezfun_diff_minus [simp] :
  fixes a b :: "('a::group_add, 'b) aezfun"
  shows "a - b = a + - b"
  by    transfer auto

instance aezfun :: (group_add, type) group_add
proof
  fix a b :: "('a::group_add, 'b) aezfun"
  show "- a + a = 0" "a + - b = a - b" by auto
qed

instance aezfun :: (ab_group_add, type) ab_group_add
proof
  fix a b :: "('a::ab_group_add, 'b) aezfun"
  show "- a + a = 0" by simp
  show "a - b = a + - b" using aezfun_diff_minus by fast
qed

instantiation aezfun :: ("{one,zero}", zero) one
begin
  lift_definition one_aezfun :: "('a,'b) aezfun" is "1 \<delta> 0"
    using deltafun_is_aezfun by fast
  instance ..
end

lemma one_aezfun_transfer : "Abs_aezfun (1 \<delta> 0) = 1"
proof-
  define z n where "z = (0::'b::zero)" and "n = (1::'a::{one,zero})"
  hence "aezfun 1 = n \<delta> z" using one_aezfun.rep_eq by fast
  hence "Abs_aezfun (n \<delta> z) = Abs_aezfun (aezfun 1)" by simp
  with z_def n_def show ?thesis using aezfun_inverse by simp
qed

lemma one_aezfun_apply [simp]: "aezfun 1 x = (1 \<delta> 0) x"
  by transfer rule

lemma one_aezfun_apply_eq [simp]: "aezfun 1 0 = 1"
  using deltafun_apply_eq by simp

lemma one_aezfun_apply_neq [simp]: "x \<noteq> 0 \<Longrightarrow> aezfun 1 x = 0"
  using deltafun_apply_neq by simp

instance aezfun :: (zero_neq_one, zero) zero_neq_one
proof
  have "(0::'a) \<noteq> 1" "aezfun 0 0 = 0" "aezfun (1::('a,'b) aezfun) 0 = 1"
    using zero_neq_one one_aezfun_apply_eq by auto
  thus "(0::('a,'b) aezfun) \<noteq> 1"
    using zero_neq_one one_aezfun_apply_eq
          fun_eq_iff[of "aezfun (0::('a,'b) aezfun)" "aezfun 1"]
    by    auto
qed

instantiation aezfun :: ("{comm_monoid_add,times}", group_add) times
begin
  lift_definition times_aezfun :: "('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun \<Rightarrow> ('a, 'b) aezfun"
    is    "\<lambda> f g. convolution f g"
    using convolution_of_aezfun_is_aezfun
    by    fast
  instance ..
end

lemma convolution_transfer :
  assumes "f \<in> aezfun_set" "g \<in> aezfun_set"
  shows   "Abs_aezfun (convolution f g) = Abs_aezfun f * Abs_aezfun g"
proof (rule aezfun_transfer)
  from assms have "aezfun (Abs_aezfun (convolution f g)) = convolution f g"
    using convolution_of_aezfun_is_aezfun Abs_aezfun_inverse by fast
  moreover from assms
    have  "aezfun (Abs_aezfun f * Abs_aezfun g) = convolution f g"
    using times_aezfun.rep_eq[of "Abs_aezfun f"] Abs_aezfun_inverse[of f]
          Abs_aezfun_inverse[of g]
    by    simp
  ultimately show "aezfun (Abs_aezfun (convolution f g))
                        = aezfun (Abs_aezfun f * Abs_aezfun g)"
    by simp
qed

instance aezfun :: ("{comm_monoid_add,mult_zero}", group_add) mult_zero
proof
  fix a :: "('a, 'b) aezfun"
  show "0 * a = 0" using convolution_zero[of _ "aezfun a"] by transfer fast
  show "a * 0 = 0" using convolution_zero[of   "aezfun a"] by transfer fast
qed

instance aezfun :: (semiring_0, group_add) semiring_0
proof
  fix a b c :: "('a, 'b) aezfun"
  show "a * b * c = a * (b * c)"
    using convolution_assoc[of "aezfun a" "aezfun c" "aezfun b"] by transfer
  show "(a + b) * c = a * c + b * c"
    using convolution_distrib_right[of "aezfun a" "aezfun b" "aezfun c"] by transfer
  show "a * (b + c) = a * b + a * c"
    using convolution_distrib_left[of "aezfun b" "aezfun c" "aezfun a"] by transfer
qed

instance aezfun :: (ring, group_add) ring ..

instance aezfun :: ("{semiring_0,monoid_mult,zero_neq_one}", group_add) monoid_mult
proof
  fix a :: "('a, 'b) aezfun"
  show "1 * a = a"
  proof-
    have "aezfun (1 * a) = convolution (1 \<delta> 0) (aezfun a)" by transfer fast
    hence "aezfun (1 * a) = (aezfun a)"
      using one_neq_zero convolution_delta_left[of 1 0 "aezfun a"] minus_zero by simp
    thus "1 * a = a" by transfer
  qed
  show "a * 1 = a"
  proof-
    have "aezfun (a * 1) = convolution (aezfun a) (1 \<delta> 0)" by transfer fast
    hence "aezfun (a * 1) = (aezfun a)" 
      using one_neq_zero convolution_delta_right[of "aezfun a"] by simp
    thus ?thesis by transfer
  qed
qed

instance aezfun :: (ring_1, group_add) ring_1 ..

subsubsection \<open>Transfer facts\<close>

abbreviation aezdeltafun :: "'b::zero \<Rightarrow> 'a \<Rightarrow> ('b,'a) aezfun" (infix "\<delta>\<delta>" 70)
  where "b \<delta>\<delta> a \<equiv> Abs_aezfun (b \<delta> a)"

lemma aezdeltafun : "aezfun (b \<delta>\<delta> a) = b \<delta> a"
  using deltafun_is_aezfun[of b a] Abs_aezfun_inverse by fast

lemma aezdeltafun_plus : "(b+c) \<delta>\<delta> a = (b \<delta>\<delta> a) + (c \<delta>\<delta> a)"
  using aezdeltafun[of "b+c" a] deltafun_plus aezdeltafun[of b a] aezdeltafun[of c a]
        plus_aezfun.rep_eq[of "b \<delta>\<delta> a"]
        aezfun_transfer[of "(b+c) \<delta>\<delta> a" "(b \<delta>\<delta> a) + (c \<delta>\<delta> a)"]
  by    fastforce

lemma   times_aezdeltafun_aezdeltafun :
  fixes b1 b2 :: "'b::{comm_monoid_add,mult_zero}"
  shows "(b1 \<delta>\<delta> a1) * (b2 \<delta>\<delta> a2) = (b1 * b2) \<delta>\<delta> (a1 + a2)"
  using deltafun_is_aezfun convolution_transfer[of "b1 \<delta> a1", THEN sym]
        convolution_delta_delta[of b1 a1 b2 a2]
  by    fastforce

lemma aezfun_restrict_and_extend0 : "(aezfun x)\<down>A \<in> aezfun_set"
  using aezfun.aezfun restrict_and_extend0_aezfun_is_aezfun[of "aezfun x"] by fast

lemma aezdeltafun_decomp :
  fixes b :: "'b::semiring_1"
  shows "b \<delta>\<delta> a = (b \<delta>\<delta> 0) * (1 \<delta>\<delta> a)"
  using convolution_delta_delta[of b 0 1 a] deltafun_is_aezfun[of b 0]
        deltafun_is_aezfun[of 1 a] convolution_transfer
  by    fastforce

lemma aezdeltafun_decomp' :
  fixes b :: "'b::semiring_1"
  shows "b \<delta>\<delta> a = (1 \<delta>\<delta> a) * (b \<delta>\<delta> 0)"
  using convolution_delta_delta[of 1 a b 0] deltafun_is_aezfun[of b 0]
        deltafun_is_aezfun[of 1 a] convolution_transfer
  by    fastforce

lemma supp_aezfun1 :
  "supp ( aezfun ( 1 :: ('a::zero_neq_one,'b::zero) aezfun ) ) = 0"
  using supp_deltafun[of "1::'a" "0::'b"] by transfer simp

lemma supp_aezfun_diff :
  "supp (aezfun (x - y)) \<subseteq> supp (aezfun x) \<union> supp (aezfun y)"
proof-
  have "supp (aezfun (x - y)) = supp ( (aezfun x) - (aezfun y) )" by transfer fast
  thus ?thesis using supp_diff_subset_union_supp by fast
qed

lemma supp_aezfun_times :
  "supp (aezfun (x * y)) \<subseteq> supp (aezfun x) + supp (aezfun y)"
proof-
  have "supp (aezfun (x * y)) = supp (convolution (aezfun x) (aezfun y))"
    by transfer fast
  thus ?thesis using supp_convolution_subset_sum_supp by fast
qed

subsubsection \<open>Almost-everywhere-zero functions with constrained support\<close>

text \<open>The name of the next definition anticipates \<open>aezfun_common_supp_spanning_set\<close>
        below.\<close>

definition aezfun_setspan :: "'a set \<Rightarrow> ('b::zero,'a) aezfun set"
  where "aezfun_setspan A = {x. supp (aezfun x) \<subseteq> A}"

lemma aezfun_setspanD : "x \<in> aezfun_setspan A \<Longrightarrow> supp (aezfun x) \<subseteq> A"
  unfolding aezfun_setspan_def by fast

lemma aezfun_setspanI : "supp (aezfun x) \<subseteq> A \<Longrightarrow> x \<in> aezfun_setspan A"
  unfolding aezfun_setspan_def by fast

lemma aezfun_common_supp_spanning_set :
  assumes "finite A"
  shows   "\<exists>as. distinct as \<and> set as = A \<and> (
                  \<forall>x::('b::semiring_1,'a) aezfun \<in> aezfun_setspan A.
                    \<exists>bs. length bs = length as \<and> x = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta>\<delta> a)
          )"
proof-
  from assms aezfun_common_supp_spanning_set'[of A] obtain as
    where as: "distinct as" "set as = A"
              "\<forall>f::'a \<Rightarrow> 'b. supp f \<subseteq> A
                    \<longrightarrow> (\<exists>bs. length bs = length as \<and> f = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta> a))"
    by    fast
  have "\<And>x::('b,'a) aezfun. x \<in> aezfun_setspan A \<Longrightarrow>
             (\<exists>bs. length bs = length as \<and> x = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta>\<delta> a))"
  proof-
    fix x::"('b,'a) aezfun" assume "x \<in> aezfun_setspan A"
    with as(3) obtain bs
      where bs: "length bs = length as" "aezfun x = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta> a)"
      using aezfun_setspanD
      by    fast
    have "\<And>b a. (b,a) \<in> set (zip bs as) \<Longrightarrow> b \<delta> a = aezfun (b \<delta>\<delta> a)"
    proof-
      fix b a assume "(b,a) \<in> set (zip bs as)"
      show "b \<delta> a = aezfun (b \<delta>\<delta> a)" using aezdeltafun[of b a] by simp
    qed
    with bs show "\<exists>bs. length bs = length as \<and> x = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta>\<delta> a)"
      using sum_list_prod_cong[of "zip bs as" deltafun "\<lambda>b a. aezfun (b \<delta>\<delta> a)"]
            sum_list_prod_map_aezfun[of aezdeltafun "zip bs as"]
            aezfun_transfer[of x]
      by    fastforce
  qed
  with as(1,2) show ?thesis by fast
qed

lemma aezfun_common_supp_spanning_set_decomp :
  fixes   G :: "'g::group_add set"
  assumes "finite G"
  shows   "\<exists>gs. distinct gs \<and> set gs = G \<and> (
                  \<forall>x::('r::semiring_1,'g) aezfun \<in> aezfun_setspan G.
                    \<exists>rs. length rs = length gs
                      \<and> x = (\<Sum>(r,g)\<leftarrow>zip rs gs. (r \<delta>\<delta> 0) * (1 \<delta>\<delta> g))
          )"
proof-
  from  aezfun_common_supp_spanning_set[OF assms] obtain gs
    where gs: "distinct gs" "set gs = G"
              "\<forall>x::('r,'g) aezfun \<in> aezfun_setspan G.
                    \<exists>rs. length rs = length gs
                      \<and> x = (\<Sum>(r,g)\<leftarrow>zip rs gs. r \<delta>\<delta> g)"
    by    fast
  have "\<And>x::('r,'g) aezfun. x \<in> aezfun_setspan G
              \<Longrightarrow> \<exists>rs. length rs = length gs
                \<and> x = (\<Sum>(r,g)\<leftarrow>zip rs gs. (r \<delta>\<delta> 0) * (1 \<delta>\<delta> g))"
  proof-
    fix x::"('r,'g) aezfun" assume "x \<in> aezfun_setspan G"
    with gs(3) obtain rs
      where "length rs = length gs" "x = (\<Sum>(r,g)\<leftarrow>zip rs gs. r \<delta>\<delta> g)"
      using aezfun_setspanD
      by    fast
    thus "\<exists>rs. length rs = length gs
                \<and> x = (\<Sum>(r,g)\<leftarrow>zip rs gs. (r \<delta>\<delta> 0) * (1 \<delta>\<delta> g))"
      using aezdeltafun_decomp sum_list_prod_cong[
              of "zip rs gs" "\<lambda>r g. r \<delta>\<delta> g" "\<lambda>r g. (r \<delta>\<delta> 0) * (1 \<delta>\<delta> g)"
            ]
      by    auto
  qed
  with gs(1,2) show ?thesis by fast
qed

lemma aezfun_decomp_aezdeltafun :
  fixes c :: "('r::semiring_1,'a) aezfun"
  shows "\<exists>ras. set (map snd ras) = supp (aezfun c) \<and> c = (\<Sum>(r,a)\<leftarrow>ras. r \<delta>\<delta> a)"
proof-
  from aezfun_finite_supp[of c] obtain as
    where as: "set as = supp (aezfun c)"
              "\<forall>x::('r,'a) aezfun \<in> aezfun_setspan (supp (aezfun c)).
                    \<exists>bs. length bs = length as
                      \<and> x = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta>\<delta> a)"
    using aezfun_common_supp_spanning_set[of "supp (aezfun c)"]
    by    fast
  from as(2) obtain bs
    where bs: "length bs = length as" "c = (\<Sum>(b,a)\<leftarrow>zip bs as. b \<delta>\<delta> a)"
    using aezfun_setspanI[of c "supp (aezfun c)"]
    by    fast
  from bs(1) as(1) have "set (map snd (zip bs as)) = supp (aezfun c)" by simp
  with bs(2) show ?thesis by fast
qed

lemma aezfun_setspan_el_decomp_aezdeltafun :
  fixes c :: "('r::semiring_1,'a) aezfun"
  shows "c \<in> aezfun_setspan A
              \<Longrightarrow> \<exists>ras. set (map snd ras) \<subseteq> A \<and> c = (\<Sum>(r,a)\<leftarrow>ras. r \<delta>\<delta> a)"
  using aezfun_setspanD aezfun_decomp_aezdeltafun
  by    fast

lemma aezdelta0fun_commutes' :
  fixes b1 b2 :: "'b::comm_semiring_1"
  shows "b1 \<delta>\<delta> a * (b2 \<delta>\<delta> 0) = b2 \<delta>\<delta> 0 * (b1 \<delta>\<delta> a)"
  using times_aezdeltafun_aezdeltafun[of b1 a]
        times_aezdeltafun_aezdeltafun[of b2 0 b1 a]
  by    (simp add: algebra_simps)

lemma aezdelta0fun_commutes :
  fixes b :: "'b::comm_semiring_1"
  shows "c * (b \<delta>\<delta> 0) = b \<delta>\<delta> 0 * c"
proof-
  from aezfun_decomp_aezdeltafun obtain ras
    where c: "c = (\<Sum>(r,a)\<leftarrow>ras. r \<delta>\<delta> a)"
    by    fast
  thus ?thesis
    using sum_list_mult_const_prod[of "\<lambda>r a. r \<delta>\<delta> a" ras] aezdelta0fun_commutes'
          sum_list_prod_cong[of ras "\<lambda>r a. r \<delta>\<delta> a * (b \<delta>\<delta> 0)" "\<lambda>r a. b \<delta>\<delta> 0 * (r \<delta>\<delta> a)"]
          sum_list_const_mult_prod[of "b \<delta>\<delta> 0" "\<lambda>r a. r \<delta>\<delta> a" ras]
    by    auto
qed

text \<open>
  The following definition constrains the support of arbitrary almost-everywhere-zero functions, as
  a sort of projection onto a \<open>aezfun_setspan\<close>.
\<close>

definition aezfun_setspan_proj :: "'a set \<Rightarrow> ('b::zero,'a) aezfun \<Rightarrow> ('b::zero,'a) aezfun"
  where "aezfun_setspan_proj A x \<equiv> Abs_aezfun ((aezfun x)\<down>A)"

lemma aezfun_setspan_projD1 :
  "a \<in> A \<Longrightarrow> aezfun (aezfun_setspan_proj A x) a = aezfun x a"
  using     aezfun_restrict_and_extend0[of A x] Abs_aezfun_inverse[of "(aezfun x)\<down>A"]
  unfolding aezfun_setspan_proj_def
  by        simp

lemma aezfun_setspan_projD2 :
  "a \<notin> A \<Longrightarrow> aezfun (aezfun_setspan_proj A x) a = 0"
  using     aezfun_restrict_and_extend0[of A x] Abs_aezfun_inverse[of "(aezfun x)\<down>A"]
  unfolding aezfun_setspan_proj_def
  by        simp

lemma aezfun_setspan_proj_in_setspan :
  "aezfun_setspan_proj A x \<in> aezfun_setspan A"
  using aezfun_setspan_projD2[of _ A]
        suppD_contra[of "aezfun (aezfun_setspan_proj A x)"]
        aezfun_setspanI[of "aezfun_setspan_proj A x" A]
  by    auto

lemma aezfun_setspan_proj_zero : "aezfun_setspan_proj A 0 = 0"
proof-
  have "aezfun (aezfun_setspan_proj A 0) = aezfun 0"
  proof
    fix a show "aezfun (aezfun_setspan_proj A 0) a = aezfun 0 a"
      using aezfun_setspan_projD1[of a A 0] aezfun_setspan_projD2[of a A 0]
      by    (cases "a\<in>A") auto
  qed
  thus ?thesis using aezfun_transfer by fast
qed

lemma aezfun_setspan_proj_aezdeltafun :
  "aezfun_setspan_proj A (b \<delta>\<delta> a) = (if a \<in> A then b \<delta>\<delta> a else 0)"
proof-
  have "aezfun (aezfun_setspan_proj A (b \<delta>\<delta> a))
              = aezfun (if a \<in> A then b \<delta>\<delta> a else 0)"
  proof
    fix x show "aezfun (aezfun_setspan_proj A (b \<delta>\<delta> a)) x
                      = aezfun (if a \<in> A then b \<delta>\<delta> a else 0) x"
    proof (cases "x \<in> A")
      case True thus ?thesis
        using aezfun_setspan_projD1[of x A "b \<delta>\<delta> a"] aezdeltafun[of b a]
              deltafun_apply_neq[of x]
        by    fastforce
    next
      case False
      hence "aezfun (aezfun_setspan_proj A (b \<delta>\<delta> a)) x = 0"
        using aezfun_setspan_projD2[of x A] by simp
      moreover from False
        have  "a \<in> A \<Longrightarrow> aezfun (if a \<in> A then b \<delta>\<delta> a else 0) x = 0"
        using aezdeltafun[of b a] deltafun_apply_neq[of x a b] by auto
      ultimately show ?thesis by auto
    qed
  qed
  thus ?thesis using aezfun_transfer by fast
qed

lemma aezfun_setspan_proj_add :
  "aezfun_setspan_proj A (x+y)
        = aezfun_setspan_proj A x + aezfun_setspan_proj A y"
proof-
  have "aezfun (aezfun_setspan_proj A (x+y))
             = aezfun (aezfun_setspan_proj A x + aezfun_setspan_proj A y)"
  proof
    fix a show "aezfun (aezfun_setspan_proj A (x+y)) a
                     = aezfun (aezfun_setspan_proj A x + aezfun_setspan_proj A y) a"
      using aezfun_setspan_projD1[of a A "x+y"] aezfun_setspan_projD2[of a A "x+y"]
            aezfun_setspan_projD1[of a A x] aezfun_setspan_projD1[of a A y]
            aezfun_setspan_projD2[of a A x] aezfun_setspan_projD2[of a A y]
      by    (cases "a \<in> A") auto
  qed
  thus ?thesis using aezfun_transfer by auto
qed

lemma aezfun_setspan_proj_sum_list : 
  "aezfun_setspan_proj A (\<Sum>x\<leftarrow>xs. f x) = (\<Sum>x\<leftarrow>xs. aezfun_setspan_proj A (f x))"
proof (induct xs)
  case Nil show ?case using aezfun_setspan_proj_zero by simp
next
  case (Cons x xs) thus ?case using aezfun_setspan_proj_add[of A "f x"] by simp
qed

lemma aezfun_setspan_proj_sum_list_prod :
  "aezfun_setspan_proj A (\<Sum>(x,y)\<leftarrow>xys. f x y)
        = (\<Sum>(x,y)\<leftarrow>xys. aezfun_setspan_proj A (f x y))"
  using aezfun_setspan_proj_sum_list[of A "\<lambda>xy. case_prod f xy"]
        prod.case_distrib[of "aezfun_setspan_proj A" f]
  by    simp


subsection \<open>Polynomials\<close>

lemma nonzero_coeffs_nonzero_poly : "as \<noteq> [] \<Longrightarrow> set as \<noteq> 0 \<Longrightarrow> Poly as \<noteq> 0"
  using coeffs_Poly[of as] strip_while_0_nnil[of as] by fastforce

lemma const_poly_nonzero_coeff :
  assumes "degree p = 0" "p \<noteq> 0"
  shows   "coeff p 0 \<noteq> 0"
proof
  assume z: "coeff p 0 = 0"
  have "\<And>n. coeff p n = 0"
  proof-
    fix n from z assms show "coeff p n = 0"
      using coeff_eq_0[of p] by (cases "n = 0") auto
  qed
  with assms(2) show False using poly_eqI[of p 0] by simp
qed

lemma pCons_induct2 [case_names 00 lpCons rpCons pCons2]:
  assumes 00: "P 0 0"
  and     lpCons: "\<And>a p. a \<noteq> 0 \<or> p \<noteq> 0 \<Longrightarrow> P (pCons a p) 0"
  and     rpCons: "\<And>b q. b \<noteq> 0 \<or> q \<noteq> 0 \<Longrightarrow> P 0 (pCons b q)"
  and     pCons2: "\<And>a p b q. a \<noteq> 0 \<or> p \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<or> q \<noteq> 0 \<Longrightarrow> P p q
                                                                    \<Longrightarrow> P (pCons a p) (pCons b q)"
  shows   "P p q"
proof (induct p arbitrary: q)
  case 0
  show ?case
  proof (cases q)
    fix b q' assume "q = pCons b q'"
    with 00 rpCons show ?thesis by (cases "b \<noteq> 0 \<or> q' \<noteq> 0") auto
  qed
next
  case (pCons a p)
  show ?case
  proof (cases q)
    fix b q' assume "q = pCons b q'"
    with pCons lpCons pCons2 show ?thesis by (cases "b \<noteq> 0 \<or> q' \<noteq> 0") auto
  qed
qed


subsection \<open>Algebra of sets\<close>

subsubsection \<open>General facts\<close>

lemma zeroset_eqI: "0 \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a = 0) \<Longrightarrow> A = 0"
  by auto

lemma sum_list_sets_single : "(\<Sum>X\<leftarrow>[A]. X) = A"
  using add_0_right[of A] by simp

lemma sum_list_sets_double : "(\<Sum>X\<leftarrow>[A,B]. X) = A + B"
  using add_0_right[of B] by simp

subsubsection \<open>Additive independence of sets\<close>

primrec add_independentS :: "'a::monoid_add set list \<Rightarrow> bool"
  where "add_independentS [] = True"
      | "add_independentS (A#As) = ( add_independentS As
              \<and> (\<forall>x\<in>(\<Sum>B\<leftarrow>As. B). \<forall>a\<in>A. a + x = 0 \<longrightarrow> a = 0) )"

lemma add_independentS_doubleI:
  assumes "\<And>b a. b\<in>B \<Longrightarrow> a\<in>A \<Longrightarrow> a + b = 0 \<Longrightarrow> a = 0"
  shows   "add_independentS [A,B]"
  using assms sum_list_sets_single[of B] by simp

lemma add_independentS_doubleD:
  assumes "add_independentS [A,B]"
  shows   "\<And>b a. b\<in>B \<Longrightarrow> a\<in>A \<Longrightarrow> a + b = 0 \<Longrightarrow> a = 0"
  using assms sum_list_sets_single[of B] by simp

lemma add_independentS_double_iff :
  "add_independentS [A,B] = (\<forall>b\<in>B. \<forall>a\<in>A. a + b = 0 \<longrightarrow> a = 0 )"
  using add_independentS_doubleI add_independentS_doubleD by fast

lemma add_independentS_Cons_conv_sum_right : 
  "add_independentS (A#As)
        = (add_independentS [A,\<Sum>B\<leftarrow>As. B] \<and> add_independentS As)"
  using add_independentS_double_iff[of A] by auto

lemma add_independentS_double_sum_conv_append :
  "\<lbrakk> \<forall>X\<in>set As. 0 \<in> X; add_independentS As; add_independentS Bs; 
        add_independentS [\<Sum>X\<leftarrow>As. X, \<Sum>X\<leftarrow>Bs. X] \<rbrakk>
          \<Longrightarrow> add_independentS (As@Bs)"
proof (induct As)
  case (Cons A As)
  have "add_independentS [\<Sum>X\<leftarrow>As. X, \<Sum>X\<leftarrow>Bs. X]"
  proof (rule add_independentS_doubleI)
    fix b a assume ba: "b \<in> (\<Sum>X\<leftarrow>Bs. X)" "a \<in> (\<Sum>X\<leftarrow>As. X)" "a + b = 0"
    from Cons(2) ba(2) have "a \<in> (\<Sum>X\<leftarrow>A#As. X)"
      using set_plus_intro[of 0 A a] by simp
    with ba(1,3) Cons(5) show "a = 0"
      using add_independentS_doubleD[of "\<Sum>X\<leftarrow>A # As. X" "\<Sum>X\<leftarrow>Bs. X" b a]
      by    simp
  qed
  moreover have "\<And>x a. \<lbrakk> x \<in> (\<Sum>X\<leftarrow>As@Bs. X); a \<in> A; a + x = 0 \<rbrakk> 
                      \<Longrightarrow> a = 0"
  proof-
    fix x a assume x_a: "x \<in> (\<Sum>X\<leftarrow>As@Bs. X)" "a \<in> A" "a + x = 0"
    from x_a(1) obtain xa xb
      where xa_xb: "x = xa + xb" "xa \<in> (\<Sum>X\<leftarrow>As. X)" "xb \<in> (\<Sum>X\<leftarrow>Bs. X)"
      using set_plus_elim[of x "\<Sum>X\<leftarrow>As. X"]
      by    auto
    from x_a(2) xa_xb(2) have "a + xa \<in> A + (\<Sum>X\<leftarrow>As. X)"
      using set_plus_intro by auto
    with Cons(3,5) xa_xb x_a(2,3) show "a = 0"
      using add_independentS_doubleD[
              of "\<Sum>X\<leftarrow>A # As. X" "\<Sum>X\<leftarrow>Bs. X" xb "a+xa"
            ]
            add.assoc[of a] add_independentS_doubleD
      by    simp
  qed
  ultimately show "add_independentS ((A#As)@Bs)" using Cons by simp
qed simp

lemma add_independentS_ConsI :
  assumes "add_independentS As"
          "\<And>x a. \<lbrakk> x\<in>(\<Sum>X\<leftarrow>As. X); a \<in> A; a+x = 0 \<rbrakk> \<Longrightarrow> a = 0"
  shows   "add_independentS (A#As)"
  using assms by simp

lemma add_independentS_append_reduce_right :
  "add_independentS (As@Bs) \<Longrightarrow> add_independentS Bs"
  by (induct As) auto

lemma add_independentS_append_reduce_left : 
  "add_independentS (As@Bs) \<Longrightarrow> 0 \<in> (\<Sum>X\<leftarrow>Bs. X) \<Longrightarrow> add_independentS As"
proof (induct As)
  case (Cons A As) show "add_independentS (A#As)"
  proof (rule add_independentS_ConsI)
    from Cons show "add_independentS As" by simp
  next
    fix x a assume x: "x \<in> (\<Sum>X\<leftarrow>As. X)" and a: "a \<in> A" and sum: "a+x = 0"
    from x Cons(3) have "x + 0 \<in> (\<Sum>X\<leftarrow>As. X) + (\<Sum>X\<leftarrow>Bs. X)" by fast
    with a sum Cons(2) show "a = 0" by simp
  qed
qed simp

lemma add_independentS_append_conv_double_sum : 
  "add_independentS (As@Bs) \<Longrightarrow> add_independentS [\<Sum>X\<leftarrow>As. X, \<Sum>X\<leftarrow>Bs. X]"
proof (induct As)
  case (Cons A As)
  show "add_independentS [\<Sum>X\<leftarrow>(A#As). X, \<Sum>X\<leftarrow>Bs. X]"
  proof (rule add_independentS_doubleI)
    fix b x assume bx: "b \<in> (\<Sum>X\<leftarrow>Bs. X)" "x \<in> (\<Sum>X\<leftarrow>A # As. X)" "x + b = 0"
    from bx(2) obtain a as
      where a_as: "a \<in> A" "as \<in> listset As" "x = a + (\<Sum>z\<leftarrow>as. z)"
      using set_sum_list_element_Cons
      by    fast
    from Cons(2) have "add_independentS [A,\<Sum>X\<leftarrow>As@Bs. X]"
      using add_independentS_Cons_conv_sum_right[of A "As@Bs"] by simp
    moreover from a_as(2) bx(1)
      have  "(\<Sum>z\<leftarrow>as. z) + b \<in> (\<Sum>X\<leftarrow>(As@Bs). X)"
      using sum_list_listset set_plus_intro
      by    auto
    ultimately have "a = 0"
      using a_as(1,3) bx(3) add_independentS_doubleD[of A _ _ a] add.assoc[of a]
      by    auto
    with a_as(2,3) bx(1,3) Cons show "x = 0"
      using sum_list_listset
            add_independentS_doubleD[of "\<Sum>X\<leftarrow>As. X" "\<Sum>X\<leftarrow>Bs. X" b "\<Sum>z\<leftarrow>as. z"]
      by    auto
  qed
qed simp

subsubsection \<open>Inner direct sums\<close>

definition inner_dirsum :: "'a::monoid_add set list \<Rightarrow> 'a set"
  where "inner_dirsum As = (if add_independentS As then \<Sum>A\<leftarrow>As. A else 0)"

text\<open>Some syntactic sugar for \<open>inner_dirsum\<close>, borrowed from theory @{theory HOL.List}.\<close>

syntax 
  "_inner_dirsum" :: "pttrn => 'a list => 'b => 'b"
  ("(3\<Oplus>_\<leftarrow>_. _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Oplus>M\<leftarrow>Ms. b" == "CONST inner_dirsum (CONST map (%M. b) Ms)"

abbreviation inner_dirsum_double ::
  "'a::monoid_add set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr "\<oplus>" 70)
  where "inner_dirsum_double A B \<equiv> inner_dirsum [A,B]"

lemma inner_dirsumI :
  "M = (\<Sum>N\<leftarrow>Ns. N) \<Longrightarrow> add_independentS Ns \<Longrightarrow> M = (\<Oplus>N\<leftarrow>Ns. N)"
  unfolding inner_dirsum_def by simp

lemma inner_dirsum_doubleI :
  "M = A + B \<Longrightarrow> add_independentS [A,B] \<Longrightarrow> M = A \<oplus> B"
  using inner_dirsumI[of M "[A,B]"] sum_list_sets_double[of A] by simp

lemma inner_dirsumD :
  "add_independentS Ms \<Longrightarrow> (\<Oplus>M\<leftarrow>Ms. M) = (\<Sum>M\<leftarrow>Ms. M)"
  unfolding inner_dirsum_def by simp

lemma inner_dirsumD2 : "\<not> add_independentS Ms \<Longrightarrow> (\<Oplus>M\<leftarrow>Ms. M) = 0"
  unfolding inner_dirsum_def by simp

lemma inner_dirsum_Nil : "(\<Oplus>A\<leftarrow>[]. A) = 0"
  unfolding inner_dirsum_def by simp

lemma inner_dirsum_singleD : "(\<Oplus>N\<leftarrow>[M]. N) = M"
  using inner_dirsumD[of "[M]"] sum_list_sets_single[of M] by simp

lemma inner_dirsum_doubleD : "add_independentS [M,N] \<Longrightarrow> M \<oplus> N = M + N"
  using inner_dirsumD[of "[M,N]"] sum_list_sets_double[of M N] by simp

lemma inner_dirsum_Cons :
  "add_independentS (A # As) \<Longrightarrow> (\<Oplus>X\<leftarrow>(A#As). X) = A \<oplus> (\<Oplus>X\<leftarrow>As. X)"
  using inner_dirsumD[of "A#As"] add_independentS_Cons_conv_sum_right[of A] 
        inner_dirsum_doubleD[of A] inner_dirsumD[of As]
  by    simp

lemma inner_dirsum_append :
  "add_independentS (As@Bs) \<Longrightarrow> 0 \<in> (\<Sum>X\<leftarrow>Bs. X)
        \<Longrightarrow> (\<Oplus>X\<leftarrow>(As@Bs). X) = (\<Oplus>X\<leftarrow>As. X) \<oplus> (\<Oplus>X\<leftarrow>Bs. X)"
  using inner_dirsumD[of "As@Bs"] add_independentS_append_reduce_left[of As]
        inner_dirsumD[of As] inner_dirsumD[of Bs]
        add_independentS_append_reduce_right[of As Bs]
        add_independentS_append_conv_double_sum[of As]
        inner_dirsum_doubleD[of "\<Sum>X\<leftarrow>As. X"]
  by    simp

lemma inner_dirsum_double_left0: "0 \<oplus> A = A"
  using add_independentS_doubleD inner_dirsum_doubleI[of "0+A"] add_0_left[of A] by simp

lemma add_independentS_Cons_conv_dirsum_right :
  "add_independentS (A#As) = (add_independentS [A,\<Oplus>B\<leftarrow>As. B]
        \<and> add_independentS As)"
  using add_independentS_Cons_conv_sum_right[of A As] inner_dirsumD by auto

lemma sum_list_listset_dirsum : 
  "add_independentS As \<Longrightarrow> as \<in> listset As \<Longrightarrow> sum_list as \<in> (\<Oplus>A\<leftarrow>As. A)"
  using inner_dirsumD sum_list_listset by fast




section \<open>Groups\<close>

subsection \<open>Locales and basic facts\<close>

subsubsection \<open>Locale \<open>Group\<close> and finite variant \<open>FinGroup\<close>\<close>

text \<open>
  Define a \<open>Group\<close> to be a closed subset of @{term UNIV} for the \<open>group_add\<close> class.
\<close>

locale Group =
  fixes G :: "'g::group_add set"
  assumes nonempty   : "G \<noteq> {}"
  and     diff_closed: "\<And>g h. g \<in> G \<Longrightarrow> h \<in> G \<Longrightarrow> g - h \<in> G"

lemma trivial_Group : "Group 0"
  by unfold_locales auto

locale FinGroup = Group G
  for G :: "'g::group_add set"
+ assumes finite: "finite G"

lemma (in FinGroup) Group : "Group G" by unfold_locales

lemma (in Group) FinGroupI : "finite G \<Longrightarrow> FinGroup G" by unfold_locales

context Group
begin

abbreviation Subgroup ::
  "'g set \<Rightarrow> bool" where "Subgroup H \<equiv> Group H \<and> H \<subseteq> G"

lemma SubgroupD1 : "Subgroup H \<Longrightarrow> Group H" by fast

lemma zero_closed : "0 \<in> G"
proof-
  from nonempty obtain g where "g \<in> G" by fast
  hence "g - g \<in> G" using diff_closed by fast
  thus ?thesis by simp
qed

lemma obtain_nonzero: assumes "G \<noteq> 0" obtains g where "g \<in> G" and "g \<noteq> 0"
  using assms zero_closed by auto

lemma zeroS_closed : "0 \<subseteq> G"
  using zero_closed by simp

lemma neg_closed : "g \<in> G \<Longrightarrow> -g \<in> G"
  using zero_closed diff_closed[of 0 g] by simp

lemma add_closed : "g \<in> G \<Longrightarrow> h \<in> G \<Longrightarrow> g + h \<in> G"
  using neg_closed[of h] diff_closed[of g "-h"] by simp

lemma neg_add_closed : "g \<in> G \<Longrightarrow> h \<in> G \<Longrightarrow> -g + h \<in> G"
  using neg_closed add_closed by fast

lemma sum_list_closed : "set (map f as) \<subseteq> G \<Longrightarrow> (\<Sum>a\<leftarrow>as. f a) \<in> G"
  using zero_closed add_closed by (induct as) auto

lemma sum_list_closed_prod :
  "set (map (case_prod f) xys) \<subseteq> G \<Longrightarrow> (\<Sum>(x,y)\<leftarrow>xys. f x y) \<in> G"
  using sum_list_closed by fast

lemma set_plus_closed : "A \<subseteq> G \<Longrightarrow> B \<subseteq> G \<Longrightarrow> A + B \<subseteq> G"
  using set_plus_def[of A B] add_closed by force

lemma zip_add_closed :
  "set as \<subseteq> G \<Longrightarrow> set bs \<subseteq> G \<Longrightarrow> set [a + b. (a,b)\<leftarrow>zip as bs] \<subseteq> G"
  using add_closed by (induct as bs rule: list_induct2') auto

lemma list_diff_closed :
  "set gs \<subseteq> G \<Longrightarrow> set hs \<subseteq> G \<Longrightarrow> set [x-y. (x,y)\<leftarrow>zip gs hs] \<subseteq> G"
  using diff_closed by (induct gs hs rule: list_induct2') auto

lemma add_closed_converse_right : "g+x \<in> G \<Longrightarrow> g \<in> G \<Longrightarrow> x \<in> G"
  using neg_add_closed add.assoc[of "-g" g x] by fastforce

lemma add_closed_inverse_right : "x \<notin> G \<Longrightarrow> g \<in> G \<Longrightarrow> g+x \<notin> G"
  using add_closed_converse_right by fast

lemma add_closed_converse_left : "g+x \<in> G \<Longrightarrow> x \<in> G \<Longrightarrow> g \<in> G"
  using diff_closed add.assoc[of g] by fastforce

lemma add_closed_inverse_left : "g \<notin> G \<Longrightarrow> x \<in> G \<Longrightarrow> g+x \<notin> G"
  using add_closed_converse_left by fast

lemma right_translate_bij :
  assumes "g \<in> G"
  shows   "bij_betw (\<lambda>x. x + g) G G"
unfolding bij_betw_def proof
  show "inj_on (\<lambda>x. x + g) G" by (rule inj_onI) simp
  show "(\<lambda>x. x + g) ` G = G"
  proof
    show "(\<lambda>x. x + g) ` G \<subseteq> G" using assms add_closed by fast
    show "(\<lambda>x. x + g) ` G \<supseteq> G"
    proof
      fix x assume "x \<in> G"
      with assms have "x - g \<in> G" "x = (\<lambda>x. x + g) (x - g)"
        using diff_closed diff_add_cancel[of x] by auto
      thus "x \<in> (\<lambda>x. x + g) ` G" by fast
    qed
  qed
qed

lemma right_translate_sum : "g \<in> G \<Longrightarrow> (\<Sum>h\<in>G. f h) = (\<Sum>h\<in>G. f (h + g))"
  using right_translate_bij[of g] bij_betw_def[of "\<lambda>h. h + g"]
        sum.reindex[of "\<lambda>h. h + g" G]
  by    simp

end (* context Group *)

subsubsection \<open>Abelian variant locale \<open>AbGroup\<close>\<close>

locale AbGroup = Group G
  for G :: "'g::ab_group_add set"
begin

lemmas nonempty    = nonempty
lemmas zero_closed = zero_closed
lemmas diff_closed = diff_closed
lemmas add_closed  = add_closed
lemmas neg_closed  = neg_closed

lemma sum_closed : "finite A \<Longrightarrow> f ` A \<subseteq> G \<Longrightarrow> (\<Sum>a\<in>A. f a) \<in> G"
proof (induct set: finite)
  case empty show ?case using zero_closed by simp
next
  case (insert a A) thus ?case using add_closed by simp
qed

lemma subset_plus_right : "A \<subseteq> G + A"
  using zero_closed set_zero_plus2 by fast

lemma subset_plus_left : "A \<subseteq> A + G"
  using subset_plus_right add.commute by fast

end (* context AbGroup *)


subsection \<open>Right cosets\<close>

context Group
begin

definition rcoset_rel :: "'g set \<Rightarrow> ('g\<times>'g) set" 
  where "rcoset_rel H \<equiv> {(g,g'). g \<in> G \<and> g' \<in> G \<and> g - g' \<in> H}"

lemma (in Group) rcosets :
  assumes subgrp: "Subgroup H" and g: "g \<in> G"
  shows   "(rcoset_rel H)``{g} = H + {g}"
proof (rule seteqI)
  fix x assume "x \<in> (rcoset_rel H)``{g}"
  hence "x \<in> G" "g - x \<in> H" using rcoset_rel_def by auto
  with subgrp have "x - g \<in> H"
    using Group.neg_closed minus_diff_eq[of g x] by fastforce
  from this obtain h where h: "h \<in> H" "x - g = h" by fast
  from h(2) have "x = h + g" by (simp add: algebra_simps)
  with h(1) show "x \<in> H + {g}" using set_plus_def by fast
next
  fix x assume "x \<in> H + {g}"
  from this obtain h where h: "h \<in> H" "x = h + g" unfolding set_plus_def by fast
  with subgrp g have 1: "x \<in> G" using add_closed by fast
  from h(2) have "x - g = h" by (simp add: algebra_simps)
  with subgrp h(1) have "g - x \<in> H" using Group.neg_closed by fastforce
  with g 1 show "x \<in> (rcoset_rel H)``{g}" using rcoset_rel_def by fast
qed

lemma rcoset_equiv :
  assumes "Subgroup H"
  shows   "equiv G (rcoset_rel H)"
proof (rule equivI)
  show "refl_on G (rcoset_rel H)"
  proof (rule refl_onI)
    show "(rcoset_rel H) \<subseteq> G \<times> G" using rcoset_rel_def by auto
  next
    fix x assume "x \<in> G"
    with assms show "(x,x) \<in> (rcoset_rel H)"
      using rcoset_rel_def Group.zero_closed by auto
  qed
  show "sym (rcoset_rel H)"
  proof (rule symI)
    fix a b assume "(a,b) \<in> (rcoset_rel H)"
    with assms show "(b,a) \<in> (rcoset_rel H)"
      using rcoset_rel_def Group.neg_closed[of H "a - b"] minus_diff_eq by simp
  qed
  show "trans (rcoset_rel H)"
  proof (rule transI)
    fix x y z assume "(x,y) \<in> (rcoset_rel H)" "(y,z) \<in> (rcoset_rel H)"
    with assms show "(x,z) \<in> (rcoset_rel H)"
      using rcoset_rel_def Group.add_closed[of H "x - y" "y - z"]
      by    (simp add: algebra_simps)
  qed
qed

lemma rcoset0 : "Subgroup H \<Longrightarrow> (rcoset_rel H)``{0} = H"
  using zero_closed rcosets unfolding set_plus_def by simp

definition is_rcoset_replist :: "'g set \<Rightarrow> 'g list \<Rightarrow> bool"
  where "is_rcoset_replist H gs
              \<equiv> set gs \<subseteq> G \<and> distinct (map (\<lambda>g. (rcoset_rel H)``{g}) gs)
                \<and> G = (\<Union>g\<in>set gs. (rcoset_rel H)``{g})"

lemma is_rcoset_replistD_set : "is_rcoset_replist H gs \<Longrightarrow> set gs \<subseteq> G"
  unfolding is_rcoset_replist_def by fast

lemma is_rcoset_replistD_distinct :
  "is_rcoset_replist H gs \<Longrightarrow> distinct (map (\<lambda>g. (rcoset_rel H)``{g}) gs)"
  unfolding is_rcoset_replist_def by fast

lemma is_rcoset_replistD_cosets :
  "is_rcoset_replist H gs \<Longrightarrow> G = (\<Union>g\<in>set gs. (rcoset_rel H)``{g})"
  unfolding is_rcoset_replist_def by fast

lemma group_eq_subgrp_rcoset_un :
  "Subgroup H \<Longrightarrow> is_rcoset_replist H gs \<Longrightarrow> G = (\<Union>g\<in>set gs. H + {g})"
  using is_rcoset_replistD_set is_rcoset_replistD_cosets rcosets
    by (auto, smt UN_E subsetCE, blast)

lemma is_rcoset_replist_imp_nrelated_nth :
  assumes "Subgroup H" "is_rcoset_replist H gs"
  shows   "\<And>i j. i < length gs \<Longrightarrow> j < length gs \<Longrightarrow> i \<noteq> j \<Longrightarrow> gs!i - gs!j \<notin> H"
proof
  fix i j assume ij: "i < length gs" "j < length gs" "i\<noteq>j" "gs!i - gs!j \<in> H"
  from assms(2) ij(1,2,4) have "(gs!i,gs!j) \<in> rcoset_rel H"
    using set_conv_nth is_rcoset_replistD_set rcoset_rel_def by fastforce
  with assms(1) ij(1,2)
    have  "(map (\<lambda>g. (rcoset_rel H)``{g}) gs)!i
                = (map (\<lambda>g. (rcoset_rel H)``{g}) gs)!j"
    using rcoset_equiv equiv_class_eq
    by    fastforce
  with assms(2) ij(1-3) show False
    using is_rcoset_replistD_distinct distinct_conv_nth[
            of "map (\<lambda>g. (rcoset_rel H)``{g}) gs"
          ]
    by    auto
qed

lemma is_rcoset_replist_Cons :
  "is_rcoset_replist H (g#gs) \<longleftrightarrow>
      g \<in> G \<and> set gs \<subseteq> G
    \<and> (rcoset_rel H)``{g} \<notin> set (map (\<lambda>x. (rcoset_rel H)``{x}) gs)
    \<and> distinct (map (\<lambda>x. (rcoset_rel H)``{x}) gs)
    \<and> G = (rcoset_rel H)``{g} \<union> (\<Union>x\<in>set gs. (rcoset_rel H)``{x})"
  using is_rcoset_replist_def[of H "g#gs"] by auto

lemma rcoset_replist_Hrep :
  assumes "Subgroup H" "is_rcoset_replist H gs"
  shows   "\<exists>g\<in>set gs. g \<in> H"
proof-
  from assms(2) obtain g where g: "g \<in> set gs" "0 \<in> (rcoset_rel H)``{g}"
    using zero_closed is_rcoset_replistD_cosets by fast
  from assms(1) g(2) have "g \<in> (rcoset_rel H)``{0}"
    using rcoset_equiv equivE sym_def[of "rcoset_rel H"] by force
  with assms(1) g show "\<exists>g\<in>set gs. g \<in> H" using rcoset0 by fast
qed

lemma rcoset_replist_reorder :
  "is_rcoset_replist H (gs @ g # gs') \<Longrightarrow> is_rcoset_replist H (g # gs @ gs')"
  using is_rcoset_replist_def by auto

lemma rcoset_replist_replacehd :
  assumes "Subgroup H" "g' \<in> (rcoset_rel H)``{g}" "is_rcoset_replist H (g # gs)"
  shows   "is_rcoset_replist H (g' # gs)"
proof-
  from assms(2) have "g' \<in> G" using rcoset_rel_def by simp
  moreover from assms(3) have "set gs \<subseteq> G"
    using is_rcoset_replistD_set by fastforce
  moreover from assms(1-3)
    have  "(rcoset_rel H)``{g'} \<notin> set (map (\<lambda>x. (rcoset_rel H)``{x}) gs)"
    using set_conv_nth[of gs] rcoset_equiv equiv_class_eq_iff[of G] is_rcoset_replistD_distinct
    by    fastforce
  moreover from assms(3) have "distinct (map (\<lambda>g. (rcoset_rel H)``{g}) gs)"
    using is_rcoset_replistD_distinct by fastforce
  moreover from assms(1-3)
    have  "G = (rcoset_rel H)``{g'} \<union> (\<Union>x\<in>set gs. (rcoset_rel H)``{x})"
    using is_rcoset_replistD_cosets[of H "g#gs"] rcoset_equiv equiv_class_eq_iff[of G]
    by    simp
  ultimately show ?thesis using is_rcoset_replist_Cons by auto 
qed

end (* context Group *)

lemma (in FinGroup) ex_rcoset_replist :
  assumes "Subgroup H"
  shows   "\<exists>gs. is_rcoset_replist H gs"
proof-
  define r where "r = rcoset_rel H"
  hence equiv_r: "equiv G r" using rcoset_equiv[OF assms] by fast
  have "\<forall>x\<in>G//r. \<exists>g. g \<in> x"
  proof
    fix x assume "x \<in> G//r"
    from this obtain g where g: "g \<in> G" "x = r``{g}"
      using quotient_def[of G r] by auto
    hence "g \<in> x" using equiv_r equivE[of G r] refl_onD[of G r] by auto
    thus "\<exists>g. g \<in> x" by fast
  qed
  from this obtain f where f: "\<forall>x\<in>G//r. f x \<in> x" using bchoice by force
  from r_def have "r \<subseteq> G \<times> G" using rcoset_rel_def by auto
  with finite have "finite (f`(G//r))" using finite_quotient by auto
  from this obtain gs where gs: "distinct gs" "set gs = f`(G//r)"
    using finite_distinct_list by force

  have 1: "set gs \<subseteq> G"
  proof
    fix g assume "g \<in> set gs"
    with gs(2) obtain x where x: "x \<in> G//r" "g = f x" by fast
    with f show "g \<in> G" using equiv_r Union_quotient by fast
  qed

  moreover have "distinct (map (\<lambda>g. r``{g}) gs)"
  proof-
    have "\<And>i j. \<lbrakk> i < length (map (\<lambda>g. r``{g}) gs);
                j < length (map (\<lambda>g. r``{g}) gs); i \<noteq> j \<rbrakk>
                  \<Longrightarrow> (map (\<lambda>g. r``{g}) gs)!i \<noteq> (map (\<lambda>g. r``{g}) gs)!j"
    proof
      fix i j assume ij:
        "i < length (map (\<lambda>g. r``{g}) gs)"
        "j< length (map (\<lambda>g. r``{g}) gs)"
        "i \<noteq> j"
        "(map (\<lambda>g. r``{g}) gs)!i = (map (\<lambda>g. r``{g}) gs)!j"
      from ij(1,2) have "gs!i \<in> set gs" "gs!j \<in> set gs" using set_conv_nth by auto
      from this gs(2) obtain x y
        where x: "x \<in> G//r" "gs!i = f x" and y: "y \<in> G//r" "gs!j = f y"
        by    auto
      have "x = y"
        using equiv_r x(1) y(1)
      proof (rule quotient_eqI[of G r])
        from ij(1,2,4) have "r``{gs!i} = r``{gs!j}" by simp
        with ij(1,2) 1 show "(gs!i,gs!j) \<in> r"
          using eq_equiv_class_iff[OF equiv_r] by force
        from x y f show "gs!i \<in> x" "gs!j \<in> y" by auto
      qed        
      with x(2) y(2) ij(1-3) gs(1) show False using distinct_conv_nth by fastforce
    qed
    thus ?thesis using distinct_conv_nth by fast
  qed

  moreover have "G = (\<Union>g\<in>set gs. r``{g})"
  proof (rule subset_antisym, rule subsetI)
    fix g assume "g \<in> G"
    hence rg: "r``{g} \<in> G//r" using quotientI by fast
    with gs(2) obtain g' where g': "g' \<in> set gs" "g' = f (r``{g})" by fast
    from f g'(2) rg have "g \<in> r``{g'}" using equiv_r equivE sym_def[of r] by force
    with g'(1) show "g \<in> (\<Union>g\<in>set gs. r``{g})" by fast
  next
    from r_def show "G \<supseteq> (\<Union>g\<in>set gs. r``{g})" using rcoset_rel_def by auto
  qed

  ultimately show ?thesis using r_def unfolding is_rcoset_replist_def by fastforce
qed

lemma (in FinGroup) ex_rcoset_replist_hd0 :
  assumes "Subgroup H"
  shows   "\<exists>gs. is_rcoset_replist H (0#gs)"
proof-
  from assms obtain xs where xs: "is_rcoset_replist H xs"
    using ex_rcoset_replist by fast
  with assms obtain x where x: "x \<in> set xs" "x \<in> H"
    using rcoset_replist_Hrep by fast
  from x(2) have "(0,x) \<in> rcoset_rel H" using rcoset0[OF assms] by auto
  moreover have "sym (rcoset_rel H)"
    using rcoset_equiv[OF assms] equivE[of G "rcoset_rel H"] by simp
  ultimately have "0 \<in> (rcoset_rel H)``{x}" using sym_def by fast
  with x(1) xs assms show "\<exists>gs. is_rcoset_replist H (0#gs)" 
    using split_list rcoset_replist_reorder rcoset_replist_replacehd by fast
qed




subsection \<open>Group homomorphisms\<close>

subsubsection \<open>Preliminaries\<close>

definition ker :: "('a\<Rightarrow>'b::zero) \<Rightarrow> 'a set"
  where "ker f = {a. f a = 0}"

lemma kerI : "f a = 0 \<Longrightarrow> a \<in> ker f"
  unfolding ker_def by fast

lemma kerD : "a \<in> ker f \<Longrightarrow> f a = 0"
  unfolding ker_def by fast

lemma ker_im_iff : "(A \<noteq> {} \<and> A \<subseteq> ker f) = (f ` A = 0)"
proof
  assume A: "A \<noteq> {} \<and> A \<subseteq> ker f"
  show "f ` A = 0"
  proof (rule zeroset_eqI)
    from A obtain a where a: "a \<in> A" by fast
    with A have "f a = 0" using kerD by fastforce
    from this[THEN sym] a show "0 \<in> f ` A" by fast
  next
    fix b assume "b \<in> f ` A"
    from this obtain a where "a \<in> A" "b = f a" by fast
    with A show "b = 0" using kerD by fast
  qed
next
  assume fA: "f ` A = 0"
  have "A \<noteq> {}"
  proof-
    from fA obtain a where "a \<in> A" "f a = 0" by force
    thus ?thesis by fast
  qed
  moreover have "A \<subseteq> ker f"
  proof
    fix a assume "a \<in> A"
    with fA have "f a = 0" by auto
    thus "a \<in> ker f" using kerI by fast
  qed
  ultimately show "A \<noteq> {} \<and> A \<subseteq> ker f" by fast
qed

subsubsection \<open>Locales\<close>

text \<open>The \<open>supp\<close> condition is not strictly necessary, but helps with equality
        and uniqueness arguments.\<close>

locale GroupHom = Group G
  for   G :: "'g::group_add set"
+ fixes T :: "'g \<Rightarrow> 'h::group_add"
  assumes hom : "\<And>g g'. g \<in> G \<Longrightarrow> g' \<in> G \<Longrightarrow> T (g + g') = T g + T g'"
  and     supp: "supp T \<subseteq> G" 

abbreviation (in GroupHom) "Ker \<equiv> ker T \<inter> G"
abbreviation (in GroupHom) "ImG \<equiv> T ` G"

locale GroupEnd = GroupHom G T
  for G :: "'g::group_add set"
  and T :: "'g \<Rightarrow> 'g"
+ assumes endomorph: "ImG \<subseteq> G"

locale GroupIso = GroupHom G T
  for   G :: "'g::group_add set"
  and   T :: "'g \<Rightarrow> 'h::group_add"
+ fixes H :: "'h set"
  assumes bijective: "bij_betw T G H"

subsubsection \<open>Basic facts\<close>

lemma (in Group) trivial_GroupHom : "GroupHom G (0::('g\<Rightarrow>'h::group_add))"
proof
  fix g g'
  define z z_map where "z = (0::'h)" and "z_map = (0::'g\<Rightarrow>'h)"
  thus "z_map (g + g') = z_map g + z_map g'" by simp
qed (rule supp_zerofun_subset_any)

lemma (in Group) GroupHom_idhom : "GroupHom G (id\<down>G)"
  using add_closed supp_restrict0 by unfold_locales simp

context GroupHom
begin

lemma im_zero : "T 0 = 0"
  using zero_closed hom[of 0 0] add_diff_cancel[of "T 0" "T 0"] by simp

lemma zero_in_Ker : "0 \<in> Ker"
  using im_zero kerI zero_closed by fast

lemma comp_zero : "T \<circ> 0 = 0"
  using im_zero by auto

lemma im_neg : "T (- g) = - T g"
  using im_zero hom[of g "- g"] neg_closed[of g] minus_unique[of "T g"]
        neg_closed[of "-g"] supp suppI_contra[of g T] suppI_contra[of "-g" T]
  by    fastforce

lemma im_diff : "g \<in> G \<Longrightarrow> g' \<in> G \<Longrightarrow> T (g - g') = T g - T g'"
  using hom neg_closed hom[of g "-g'"] im_neg by simp

lemma eq_im_imp_diff_in_Ker : "\<lbrakk> g \<in> G; h \<in> G; T g = T h \<rbrakk> \<Longrightarrow> g - h \<in> Ker"
  using im_diff kerI diff_closed[of g h] by force

lemma im_sum_list_prod : 
  "set (map (case_prod f) xys) \<subseteq> G
        \<Longrightarrow> T (\<Sum>(x,y)\<leftarrow>xys. f x y) = (\<Sum>(x,y)\<leftarrow>xys. T (f x y))"
proof (induct xys)
  case Nil
  show ?case using im_zero by simp
next
  case (Cons xy xys)
  define Tf where "Tf = T \<circ> (case_prod f)"
  have "T (\<Sum>(x,y)\<leftarrow>(xy#xys). f x y) = T ( (case_prod f) xy + (\<Sum>(x,y)\<leftarrow>xys. f x y) )"
    by simp
  moreover from Cons(2) have "(case_prod f) xy \<in> G" "set (map (case_prod f) xys) \<subseteq> G"
    by auto
  ultimately have "T (\<Sum>(x,y)\<leftarrow>(xy#xys). f x y) = Tf xy + (\<Sum>(x,y)\<leftarrow>xys. Tf (x,y))"
    using Tf_def sum_list_closed[of "case_prod f"] hom Cons by auto
  also have "\<dots> = (\<Sum>(x,y)\<leftarrow>(xy#xys). Tf (x,y))" by simp
  finally show ?case using Tf_def by simp
qed

lemma distrib_comp_sum_left :
  "range S \<subseteq> G \<Longrightarrow> range S' \<subseteq> G \<Longrightarrow> T \<circ> (S + S') = (T \<circ> S) + (T \<circ> S')"
  using hom by (auto simp add: fun_eq_iff)

lemma Ker_Im_iff : "(Ker = G) = (ImG = 0)"
  using nonempty ker_im_iff[of G T] by fast

lemma Ker0_imp_inj_on :
  assumes "Ker \<subseteq> 0"
  shows   "inj_on T G"
proof (rule inj_onI)
  fix x y assume xy: "x \<in> G" "y \<in> G" "T x = T y"
  hence "T (x - y) = 0" using im_diff by simp
  with xy(1,2) have "x - y \<in> Ker" using diff_closed kerI by fast
  with assms show "x = y" using zero_in_Ker by auto
qed

lemma inj_on_imp_Ker0 :
  assumes "inj_on T G"
  shows   "Ker = 0"
  using   zero_in_Ker kerD zero_closed im_zero inj_onD[OF assms]
  by      fastforce

lemma nonzero_Ker_el_imp_n_inj :
  "g \<in> G \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> T g = 0 \<Longrightarrow> \<not> inj_on T G"
  using inj_on_imp_Ker0 kerI[of T] by auto

lemma Group_Ker : "Group Ker"
proof
  show "Ker \<noteq> {}" using zero_in_Ker by fast
next
  fix g h assume "g \<in> Ker" "h \<in> Ker" thus "g - h \<in> Ker"
    using im_diff kerD[of g T] kerD[of h T] diff_closed kerI[of T] by auto
qed

lemma Group_Im : "Group ImG"
proof
  show "ImG \<noteq> {}" using nonempty by fast
next
  fix g' h' assume "g' \<in> ImG" "h' \<in> ImG"
  from this obtain g h where gh: "g \<in> G" "g' = T g" "h \<in> G" "h' = T h" by fast
  thus "g' - h' \<in> ImG" using im_diff diff_closed by force
qed

lemma GroupHom_restrict0_subgroup  :
  assumes "Subgroup H"
  shows   "GroupHom H (T \<down> H)"
proof (intro_locales, rule SubgroupD1[OF assms], unfold_locales)
  show "supp (T \<down> H) \<subseteq> H" using supp_restrict0 by fast
next
  fix h h' assume hh': "h \<in> H" "h' \<in> H"
  with assms show "(T \<down> H) (h + h') = (T \<down> H) h + (T \<down> H) h'"
    using Group.add_closed hom[of h h'] by auto
qed

lemma im_subgroup :
  assumes "Subgroup H"
  shows   "Group.Subgroup ImG (T ` H)"
proof
  from assms have "Group ((T \<down> H) ` H)"
    using GroupHom_restrict0_subgroup GroupHom.Group_Im by fast
  moreover have "(T \<down> H) ` H = T ` H" by auto
  ultimately show "Group (T ` H)" by simp
  from assms show "T ` H \<subseteq> ImG" by fast
qed

lemma GroupHom_composite_left :
  assumes "ImG \<subseteq> H" "GroupHom H S"
  shows   "GroupHom G (S \<circ> T)"
proof
  fix g g' assume "g \<in> G" "g' \<in> G"
  with hom assms(1) show "(S \<circ> T) (g + g') = (S \<circ> T) g + (S \<circ> T) g'"
    using GroupHom.hom[OF assms(2)] by fastforce
next
  from supp have "\<And>g. g \<notin> G \<Longrightarrow> (S \<circ> T) g = 0"
    using suppI_contra GroupHom.im_zero[OF assms(2)] by fastforce
  thus "supp (S \<circ> T) \<subseteq> G" using suppD_contra by fast
qed

lemma idhom_left : "T ` G \<subseteq> H \<Longrightarrow> (id\<down>H) \<circ> T = T"
  using supp suppI_contra by fastforce

end (* context GroupHom *)

subsubsection \<open>Basic facts about endomorphisms\<close>

context GroupEnd
begin

lemmas hom = hom

lemma range : "range T \<subseteq> G"
proof (rule image_subsetI)
  fix x show "T x \<in> G"
  proof (cases "x \<in> G")
    case True with endomorph show ?thesis by fast
  next
    case False with supp show ?thesis using suppI_contra zero_closed by fastforce
  qed
qed

lemma proj_decomp :
  assumes "\<And>g. g \<in> G \<Longrightarrow> T (T g) = T g"
  shows   "G = Ker \<oplus> ImG"
proof (rule inner_dirsum_doubleI, rule subset_antisym, rule subsetI)
  fix g assume g: "g \<in> G"
  have "g = (g - T g) + T g" using diff_add_cancel[of g] by simp
  moreover have "g - T g \<in> Ker"
  proof
    from g endomorph assms have "T (g - T g) = 0" using im_diff by auto
    thus "g - T g \<in> ker T" using kerI by fast
    from g endomorph show "g - T g \<in> G" using diff_closed by fast
  qed
  moreover from g have "T g \<in> ImG" by fast
  ultimately show "g \<in> Ker + ImG"
    using set_plus_intro[of "g - T g" Ker "T g"] by simp
next
  from endomorph show "G \<supseteq> Ker + ImG" using set_plus_closed by simp
  show "add_independentS [Ker,ImG]"
  proof (rule add_independentS_doubleI)
    fix g h assume gh: "h \<in> ImG" "g \<in> Ker" "g + h = 0"
    from gh(1) obtain g' where "g' \<in> G" "h = T g'" by fast
    with gh(2,3) endomorph assms have "h = 0"
      using im_zero hom[of g "T g'"] kerD by fastforce
    with gh(3) show "g = 0" by simp
  qed
qed

end (* context GroupEnd *)

subsubsection \<open>Basic facts about isomorphisms\<close>

context GroupIso
begin

abbreviation "invT \<equiv> (the_inv_into G T) \<down> H"

lemma ImG : "ImG = H" using bijective bij_betw_imp_surj_on by fast

lemma GroupH : "Group H" using ImG Group_Im by fast

lemma invT_onto : "invT ` H = G"
  using bijective bij_betw_imp_inj_on[of T] ImG the_inv_into_onto[of T] by force

lemma inj_on_invT : "inj_on invT H"
  using     bijective bij_betw_imp_inj_on[of T G] ImG inj_on_the_inv_into[of T]
  unfolding inj_on_def
  by        force

lemma bijective_invT : "bij_betw invT H G"
  using inj_on_invT invT_onto unfolding bij_betw_def by fast

lemma invT_into : "h \<in> H \<Longrightarrow> invT h \<in> G"
  using bijective bij_betw_imp_inj_on ImG the_inv_into_into[of T] by force

lemma T_invT : "h \<in> H \<Longrightarrow> T (invT h) = h"
  using bijective bij_betw_imp_inj_on ImG f_the_inv_into_f[of T] by force

lemma invT_eq: "g \<in> G \<Longrightarrow> T g = h \<Longrightarrow> invT h = g"
  using bijective bij_betw_imp_inj_on ImG the_inv_into_f_eq[of T] by force

lemma inv : "GroupIso H invT G"
proof (intro_locales, rule GroupH, unfold_locales)
  show "supp invT \<subseteq> H" using supp_restrict0 by fast
  show "bij_betw invT H G" using bijective_invT by fast
next
  fix h h' assume "h \<in> H" "h' \<in> H"
  thus "invT (h + h') = invT h + invT h'"
    using invT_into hom T_invT add_closed invT_eq by simp
qed

end (* context GroupIso *)

subsubsection \<open>Hom-sets\<close>

definition GroupHomSet :: "'g::group_add set \<Rightarrow> 'h::group_add set \<Rightarrow> ('g \<Rightarrow> 'h) set"
  where "GroupHomSet G H \<equiv> {T. GroupHom G T} \<inter> {T. T ` G \<subseteq> H}"

lemma GroupHomSetI :
  "GroupHom G T \<Longrightarrow> T ` G \<subseteq> H \<Longrightarrow> T \<in> GroupHomSet G H"
  unfolding GroupHomSet_def by fast

lemma GroupHomSetD_GroupHom :
  "T \<in> GroupHomSet G H \<Longrightarrow> GroupHom G T"
  unfolding GroupHomSet_def by fast

lemma GroupHomSetD_Im : "T \<in> GroupHomSet G H \<Longrightarrow> T ` G \<subseteq> H"
  unfolding GroupHomSet_def by fast

lemma (in Group) Group_GroupHomSet :
  fixes   H :: "'h::ab_group_add set"
  assumes "AbGroup H"
  shows   "Group (GroupHomSet G H)"
proof
  show "GroupHomSet G H \<noteq> {}"
    using trivial_GroupHom AbGroup.zero_closed[OF assms] GroupHomSetI
    by    fastforce
next
  fix S T assume ST: "S \<in> GroupHomSet G H" "T \<in> GroupHomSet G H"
  show "S - T \<in> GroupHomSet G H"
  proof (rule GroupHomSetI, unfold_locales)
    from ST show "supp (S - T) \<subseteq> G" 
      using GroupHomSetD_GroupHom[of S] GroupHomSetD_GroupHom[of T]
            GroupHom.supp[of G S] GroupHom.supp[of G T]
            supp_diff_subset_union_supp[of S T]
      by    auto
    show "(S - T) ` G \<subseteq> H"
    proof (rule image_subsetI)
      fix g assume "g \<in> G"
      with ST have "S g \<in> H" "T g \<in> H"
        using GroupHomSetD_Im[of S G] GroupHomSetD_Im[of T G] by auto
      thus "(S - T) g \<in> H" using AbGroup.diff_closed[OF assms] by simp
    qed
  next 
    fix g g' assume "g \<in> G" "g' \<in> G"
    with ST show "(S - T) (g + g') = (S - T) g + (S - T) g'"
      using GroupHomSetD_GroupHom[of S] GroupHom.hom[of G S]
            GroupHomSetD_GroupHom[of T] GroupHom.hom[of G T]
      by    simp
  qed
qed




subsection \<open>Facts about collections of groups\<close>

lemma listset_Group_plus_closed :
  "\<lbrakk> \<forall>G\<in>set Gs. Group G; as \<in> listset Gs; bs \<in> listset Gs\<rbrakk>
                                                \<Longrightarrow> [a+b. (a,b)\<leftarrow>zip as bs] \<in> listset Gs"
proof-
  have "\<lbrakk> length as = length bs; length bs = length Gs;
                as \<in> listset Gs; bs \<in> listset Gs; \<forall>G\<in>set Gs. Group G\<rbrakk>
                                                \<Longrightarrow> [a+b. (a,b)\<leftarrow>zip as bs] \<in> listset Gs"
  proof (induct as bs Gs rule: list_induct3)
    case (Cons a as b bs G Gs)
    thus "[x+y. (x,y)\<leftarrow>zip (a#as) (b#bs)] \<in> listset (G#Gs)"
      using listset_ConsD[of a] listset_ConsD[of b] Group.add_closed
            listset_ConsI[of "a+b" G]
      by    fastforce
  qed simp
  thus   "\<lbrakk> \<forall>G\<in>set Gs. Group G; as \<in> listset Gs; bs \<in> listset Gs\<rbrakk>
                                                \<Longrightarrow> [a+b. (a,b)\<leftarrow>zip as bs] \<in> listset Gs"
    using listset_length[of as Gs] listset_length[of bs Gs, THEN sym] by fastforce
qed

lemma AbGroup_set_plus :
  assumes "AbGroup H" "AbGroup G"
  shows   "AbGroup (H + G)"
proof
  from assms show "H + G \<noteq> {}" using AbGroup.nonempty by blast
next
  fix x y assume "x \<in> H + G" "y \<in> H + G"
  from this obtain xh xg yh yg
    where xy: "xh \<in> H" "xg \<in> G" "x = xh + xg" "yh \<in> H" "yg \<in> G" "y = yh + yg"
    unfolding set_plus_def by fast
  hence "x - y = (xh - yh) + (xg - yg)" by simp
  thus "x - y \<in> H + G" using assms xy(1,2,4,5) AbGroup.diff_closed by auto
qed

lemma AbGroup_sum_list :
  "(\<forall>G\<in>set Gs. AbGroup G) \<Longrightarrow> AbGroup (\<Sum>G\<leftarrow>Gs. G)"
  using trivial_Group AbGroup.intro AbGroup_set_plus
  by    (induct Gs) auto

lemma AbGroup_subset_sum_list :
  "\<forall>G \<in> set Gs. AbGroup G \<Longrightarrow> H \<in> set Gs \<Longrightarrow> H \<subseteq> (\<Sum>G\<leftarrow>Gs. G)"
proof (induct Gs arbitrary: H)
  case (Cons G Gs)
  show "H \<subseteq> (\<Sum>X\<leftarrow>(G#Gs). X)"
  proof (cases "H = G")
    case True with Cons(2) show ?thesis
      using AbGroup_sum_list AbGroup.subset_plus_left by auto
  next
    case False
    with Cons have "H \<subseteq> (\<Sum>G\<leftarrow>Gs. G)" by simp
    with Cons(2) show ?thesis using AbGroup.subset_plus_right by auto
  qed
qed simp

lemma independent_AbGroups_pairwise_int0 :
  "\<lbrakk> \<forall>G\<in>set Gs. AbGroup G; add_independentS Gs; G \<in> set Gs; G' \<in> set Gs;
        G \<noteq> G' \<rbrakk> \<Longrightarrow> G \<inter> G' = 0"
proof (induct Gs arbitrary: G G')
  case (Cons H Hs)
  from Cons(1-3) have "\<And>A B. \<lbrakk> A \<in> set Hs; B \<in> set Hs; A \<noteq> B \<rbrakk> 
                            \<Longrightarrow> A \<inter> B \<subseteq> 0"
    by simp
  moreover have "\<And>A. A \<in> set Hs \<Longrightarrow> A \<noteq> H \<Longrightarrow>  A \<inter> H \<subseteq> 0"
  proof
    fix A g assume A: "A \<in> set Hs" "A \<noteq> H" and g: "g \<in> A \<inter> H"
    from A(1) g Cons(2) have "-g \<in> (\<Sum>X\<leftarrow>Hs. X)"
      using AbGroup.neg_closed AbGroup_subset_sum_list by force
    moreover have "g + (-g) = 0" by simp
    ultimately show "g \<in> 0" using g Cons(3) by simp
  qed
  ultimately have "\<And>A B. \<lbrakk> A \<in> set (H#Hs); B \<in> set (H#Hs); A \<noteq> B \<rbrakk>
                        \<Longrightarrow> A \<inter> B \<subseteq> 0"
    by auto
  with Cons(4-6) have "G \<inter> G' \<subseteq> 0" by fast
  moreover from Cons(2,4,5) have "0 \<subseteq> G \<inter> G'"
    using AbGroup.zero_closed by auto
  ultimately show ?case by fast
qed simp

lemma independent_AbGroups_pairwise_int0_double :
  assumes "AbGroup G" "AbGroup G'" "add_independentS [G,G']"
  shows   "G \<inter> G' = 0"
proof (cases "G = 0")
  case True with assms(2) show ?thesis using AbGroup.zero_closed by auto
next
  case False show ?thesis
  proof (rule independent_AbGroups_pairwise_int0)
    from assms(1,2) show "\<forall>G\<in>set [G,G']. AbGroup G" by simp
    from assms(3) show "add_independentS [G,G']" by fast
    show "G \<in> set [G,G']" "G' \<in> set [G,G']" by auto
    show "G \<noteq> G'"
    proof
      assume GG': "G = G'"
      from False assms(1) obtain g where g: "g \<in> G" "g \<noteq> 0"
        using AbGroup.nonempty by auto
      moreover from assms(2) GG' g(1) have "-g \<in> G'"
        using AbGroup.neg_closed by fast
      moreover have "g + (-g) = 0" by simp
      ultimately show False using assms(3) by force
    qed
  qed
qed


subsection \<open>Inner direct sums of Abelian groups\<close>

subsubsection \<open>General facts\<close>

lemma AbGroup_inner_dirsum :
  "\<forall>G\<in>set Gs. AbGroup G \<Longrightarrow> AbGroup (\<Oplus>G\<leftarrow>Gs. G)"
  using inner_dirsumD[of Gs] inner_dirsumD2[of Gs] AbGroup_sum_list AbGroup.intro
        trivial_Group
  by    (cases "add_independentS Gs") auto

lemma inner_dirsum_double_leftfull_imp_right0:
  assumes "Group A" "B \<noteq> {}" "A = A \<oplus> B"
  shows   "B = 0"
proof (cases "add_independentS [A,B]")
  case True
  with assms(3) have 1: "A = A + B" using inner_dirsum_doubleD by fast
  have "\<And>b. b \<in> B \<Longrightarrow> b = 0"
  proof-
    fix b assume b: "b \<in> B"
    from assms(1) obtain a where a: "a \<in> A" using Group.nonempty by fast
    with b 1 have "a + b \<in> A" by fast
    from this obtain a' where a': "a' \<in> A" "a + b = a'" by fast
    hence "(-a'+a) + b = 0" by (simp add: add.assoc)
    with assms(1) True a a'(1) b show "b = 0"
      using Group.neg_add_closed[of A] add_independentS_doubleD[of A B b "-a'+a"]
      by    simp
  qed
  with assms(2) show ?thesis by auto
next
  case False
  hence 1: "A \<oplus> B = 0" unfolding inner_dirsum_def by auto
  moreover with assms(3) have "A = 0" by fast
  ultimately show ?thesis using inner_dirsum_double_left0 by auto
qed

lemma AbGroup_subset_inner_dirsum :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; H \<in> set Gs \<rbrakk>
        \<Longrightarrow> H \<subseteq> (\<Oplus>G\<leftarrow>Gs. G)"
  using AbGroup_subset_sum_list inner_dirsumD by fast

lemma AbGroup_nth_subset_inner_dirsum :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; n < length Gs \<rbrakk>
        \<Longrightarrow> Gs!n \<subseteq> (\<Oplus>G\<leftarrow>Gs. G)"
  using AbGroup_subset_inner_dirsum by force

lemma AbGroup_inner_dirsum_el_decomp_ex1_double :
  assumes "AbGroup G" "AbGroup H" "add_independentS [G,H]" "x \<in> G \<oplus> H"
  shows   "\<exists>!gh. fst gh \<in> G \<and> snd gh \<in> H \<and> x = fst gh + snd gh"
proof (rule ex_ex1I)
  from assms(3,4) obtain g h where "x = g + h" "g \<in> G" "h \<in> H"
    using inner_dirsum_doubleD set_plus_elim by blast
  from this have 1: "fst (g,h) \<in> G" "snd (g,h) \<in> H" "x = fst (g,h) + snd (g,h)"
    by auto
  thus "\<exists>gh. fst gh \<in> G \<and> snd gh \<in> H \<and> x = fst gh + snd gh" by fast
next
  fix gh gh' assume A:
    "fst gh  \<in> G \<and> snd gh  \<in> H \<and> x = fst gh  + snd gh "
    "fst gh' \<in> G \<and> snd gh' \<in> H \<and> x = fst gh' + snd gh'"
  show "gh = gh'"
  proof
    from A assms(1,2) have "fst gh - fst gh' \<in> G" "snd gh - snd gh' \<in> H"
      using AbGroup.diff_closed by auto
    moreover from A have z: "(fst gh - fst gh') + (snd gh - snd gh') = 0"
      by (simp add: algebra_simps)
    ultimately show "fst gh = fst gh'"
      using assms(3)
            add_independentS_doubleD[of G H "snd gh - snd gh'" "fst gh - fst gh'"]
      by    simp
    with z show "snd gh = snd gh'" by simp
  qed
qed

lemma AbGroup_inner_dirsum_el_decomp_ex1 :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs \<rbrakk>
        \<Longrightarrow> \<forall>x \<in> (\<Oplus>G\<leftarrow>Gs. G). \<exists>!gs\<in>listset Gs. x = sum_list gs"
proof (induct Gs)
  case Nil
  have "\<And>x::'a. x \<in> (\<Oplus>H\<leftarrow>[]. H) \<Longrightarrow> \<exists>!gs\<in>listset []. x = sum_list gs"
  proof
    fix x::'a assume "x \<in> (\<Oplus>G\<leftarrow>[]. G)"
    moreover define f :: "'a \<Rightarrow> 'a list" where "f x = []" for x
    ultimately show "f x \<in> listset [] \<and> x = sum_list (f x)"
      using inner_dirsum_Nil by auto
  next
    fix x::'a and gs
    assume  x: "x \<in> (\<Oplus>G\<leftarrow>[]. G)"
    and    gs: "gs \<in> listset [] \<and> x = sum_list gs"
    thus "gs = []" by simp
  qed
  thus "\<forall>x::'a \<in> (\<Oplus>H\<leftarrow>[]. H). \<exists>!gs\<in>listset []. x = sum_list gs" by fast
next
  case (Cons G Gs)
  hence prevcase: "\<forall>x\<in>(\<Oplus>H\<leftarrow>Gs. H). \<exists>!gs\<in>listset Gs. x = sum_list gs" by auto
  from Cons(2) have grps: "AbGroup G" "AbGroup (\<Oplus>H\<leftarrow>Gs. H)"
    using AbGroup_inner_dirsum by auto
  from Cons(3) have ind: "add_independentS [G, \<Oplus>H\<leftarrow>Gs. H]"
    using add_independentS_Cons_conv_dirsum_right by fast
  have "\<And>x. x \<in> (\<Oplus>H\<leftarrow>(G#Gs). H) \<Longrightarrow> \<exists>!gs\<in>listset (G#Gs). x = sum_list gs"
  proof (rule ex_ex1I)
    fix x assume "x \<in> (\<Oplus>H\<leftarrow>(G#Gs). H)"
    with Cons(3) have "x \<in> G \<oplus> (\<Oplus>H\<leftarrow>Gs. H)"
      using inner_dirsum_Cons by fast
    with grps ind obtain gh
      where gh: "fst gh \<in> G" "snd gh \<in> (\<Oplus>H\<leftarrow>Gs. H)" "x = fst gh + snd gh"
      using AbGroup_inner_dirsum_el_decomp_ex1_double
      by    blast
    from gh(2) prevcase obtain gs where gs: "gs \<in> listset Gs" "snd gh = sum_list gs"
      by fast
    with gh(1) gs(1) have "fst gh # gs \<in> listset (G#Gs)"
      using set_Cons_def by fastforce
    moreover from gh(3) gs(2) have "x = sum_list (fst gh # gs)" by simp
    ultimately show "\<exists>gs. gs \<in> listset (G#Gs) \<and> x = sum_list gs" by fast
  next
    fix x gs hs
    assume "x \<in> (\<Oplus>H\<leftarrow>(G#Gs). H)"
      and gs: "gs \<in> listset (G#Gs) \<and> x = sum_list gs"
      and hs: "hs \<in> listset (G#Gs) \<and> x = sum_list hs"
    hence "gs \<in> set_Cons G (listset Gs)" "hs \<in> set_Cons G (listset Gs)" by auto
    from this obtain a as b bs
      where     a_as: "gs = a#as" "a\<in>G" "as \<in> listset Gs"
      and       b_bs: "hs = b#bs" "b\<in>G" "bs \<in> listset Gs"
      unfolding set_Cons_def
      by        fast
    from a_as(3) b_bs(3) Cons(3) 
      have  as: "sum_list as \<in> (\<Oplus>H\<leftarrow>Gs. H)" and bs: "sum_list bs \<in> (\<Oplus>H\<leftarrow>Gs. H)"
      using sum_list_listset_dirsum
      by    auto
    with a_as(2) b_bs(2) grps
      have  "a - b \<in> G" "sum_list as - sum_list bs \<in> (\<Oplus>H\<leftarrow>Gs. H)"
      using AbGroup.diff_closed
      by    auto
    moreover from gs hs a_as(1) b_bs(1)
      have z: "(a - b) + (sum_list as - sum_list bs) = 0"
      by   (simp add: algebra_simps)
    ultimately have "a - b = 0" using ind add_independentS_doubleD by blast
    with z have 1: "a = b" and z': "sum_list as = sum_list bs" by auto
    from z' prevcase as a_as(3) bs b_bs(3) have 2: "as = bs" by fast
    from 1 2 a_as(1) b_bs(1) show "gs = hs" by fast
  qed
  thus "\<forall>x\<in>(\<Oplus>H\<leftarrow>(G#Gs). H). \<exists>!gs. gs \<in> listset (G#Gs) \<and> x = sum_list gs"
    by fast
qed

lemma AbGroup_inner_dirsum_pairwise_int0 :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; G \<in> set Gs; G' \<in> set Gs;
        G \<noteq> G' \<rbrakk> \<Longrightarrow> G \<inter> G' = 0"
proof (induct Gs arbitrary: G G')
  case (Cons H Hs)
  from Cons(1-3) have "\<And>A B. \<lbrakk> A \<in> set Hs; B \<in> set Hs; A \<noteq> B \<rbrakk> 
                            \<Longrightarrow> A \<inter> B \<subseteq> 0"
    by simp
  moreover have "\<And>A. A \<in> set Hs \<Longrightarrow> A \<noteq> H \<Longrightarrow>  A \<inter> H \<subseteq> 0"
  proof
    fix A g assume A: "A \<in> set Hs" "A \<noteq> H" and g: "g \<in> A \<inter> H"
    from A(1) g Cons(2) have "-g \<in> (\<Sum>X\<leftarrow>Hs. X)"
      using AbGroup.neg_closed AbGroup_subset_sum_list by force
    moreover have "g + (-g) = 0" by simp
    ultimately show "g \<in> 0" using g Cons(3) by simp
  qed
  ultimately have "\<And>A B. \<lbrakk> A \<in> set (H#Hs); B \<in> set (H#Hs); A \<noteq> B \<rbrakk> 
                        \<Longrightarrow> A \<inter> B \<subseteq> 0"
    by auto
  with Cons(4-6) have "G \<inter> G' \<subseteq> 0" by fast
  moreover from Cons(2,4,5) have "0 \<subseteq> G \<inter> G'"
    using AbGroup.zero_closed by auto
  ultimately show ?case by fast
qed simp

lemma AbGroup_inner_dirsum_pairwise_int0_double :
  assumes "AbGroup G" "AbGroup G'" "add_independentS [G,G']"
  shows   "G \<inter> G' = 0"
proof (cases "G = 0")
  case True with assms(2) show ?thesis using AbGroup.zero_closed by auto
next
  case False show ?thesis
  proof (rule AbGroup_inner_dirsum_pairwise_int0)
    from assms(1,2) show "\<forall>G\<in>set [G,G']. AbGroup G" by simp
    from assms(3) show "add_independentS [G,G']" by fast
    show "G \<in> set [G,G']" "G' \<in> set [G,G']" by auto
    show "G \<noteq> G'"
    proof
      assume GG': "G = G'"
      from False assms(1) obtain g where g: "g \<in> G" "g \<noteq> 0"
        using AbGroup.nonempty by auto
      moreover from assms(2) GG' g(1) have "-g \<in> G'"
        using AbGroup.neg_closed by fast
      moreover have "g + (-g) = 0" by simp
      ultimately show False using assms(3) by force
    qed
  qed
qed

subsubsection \<open>Element decomposition and projection\<close>

definition inner_dirsum_el_decomp ::
  "'g::ab_group_add set list \<Rightarrow> ('g \<Rightarrow> 'g list)" ("\<Oplus>_\<leftarrow>")
  where "\<Oplus>Gs\<leftarrow> = (\<lambda>x. if x \<in> (\<Oplus>G\<leftarrow>Gs. G)
              then THE gs. gs \<in> listset Gs \<and> x = sum_list gs else [])"

abbreviation inner_dirsum_el_decomp_double ::
  "'g::ab_group_add set \<Rightarrow> 'g set \<Rightarrow> ('g \<Rightarrow> 'g list)" ("_\<oplus>_\<leftarrow>") where "G\<oplus>H\<leftarrow> \<equiv> \<Oplus>[G,H]\<leftarrow>"

abbreviation inner_dirsum_el_decomp_nth ::
  "'g::ab_group_add set list \<Rightarrow> nat \<Rightarrow> ('g \<Rightarrow> 'g)" ("\<Oplus>_\<down>_")
  where "\<Oplus>Gs\<down>n \<equiv> restrict0 (\<lambda>x. (\<Oplus>Gs\<leftarrow>x)!n) (\<Oplus>G\<leftarrow>Gs. G)"

lemma AbGroup_inner_dirsum_el_decompI :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; x \<in> (\<Oplus>G\<leftarrow>Gs. G) \<rbrakk>
        \<Longrightarrow> (\<Oplus>Gs\<leftarrow>x) \<in> listset Gs \<and> x = sum_list (\<Oplus>Gs\<leftarrow>x)"
  using     AbGroup_inner_dirsum_el_decomp_ex1 theI'[
              of "\<lambda>gs. gs \<in> listset Gs \<and> x = sum_list gs"
            ]
  unfolding inner_dirsum_el_decomp_def
  by        fastforce

lemma (in AbGroup) abSubgroup_inner_dirsum_el_decomp_set :
  "\<lbrakk> \<forall>H \<in> set Hs. Subgroup H; add_independentS Hs; x \<in> (\<Oplus>H\<leftarrow>Hs. H) \<rbrakk>
    \<Longrightarrow> set (\<Oplus>Hs\<leftarrow>x) \<subseteq> G"
  using AbGroup.intro AbGroup_inner_dirsum_el_decompI[of Hs x]
        set_listset_el_subset[of "(\<Oplus>Hs\<leftarrow>x)" Hs G]
  by    fast

lemma AbGroup_inner_dirsum_el_decomp_eq :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; x \<in> (\<Oplus>G\<leftarrow>Gs. G);
        gs \<in> listset Gs; x = sum_list gs \<rbrakk> \<Longrightarrow> (\<Oplus>Gs\<leftarrow>x) = gs"
  using AbGroup_inner_dirsum_el_decomp_ex1[of Gs]
        inner_dirsum_el_decomp_def[of Gs]
  by    force

lemma AbGroup_inner_dirsum_el_decomp_plus :
  assumes "\<forall>G \<in> set Gs. AbGroup G" "add_independentS Gs" "x \<in> (\<Oplus>G\<leftarrow>Gs. G)"
          "y \<in> (\<Oplus>G\<leftarrow>Gs. G)"
  shows   "(\<Oplus>Gs\<leftarrow>(x+y)) = [a+b. (a,b)\<leftarrow>zip (\<Oplus>Gs\<leftarrow>x) (\<Oplus>Gs\<leftarrow>y)]"
proof-
  define xs ys where "xs = (\<Oplus>Gs\<leftarrow>x)" and "ys = (\<Oplus>Gs\<leftarrow>y)"
  with assms
    have  xy: "xs \<in> listset Gs" "x = sum_list xs" "ys \<in> listset Gs" "y = sum_list ys"
    using AbGroup_inner_dirsum_el_decompI
    by    auto
  from assms(1) xy(1,3) have "[a+b. (a,b)\<leftarrow>zip xs ys] \<in> listset Gs"
    using AbGroup.axioms listset_Group_plus_closed by fast
  moreover from xy have "x + y = sum_list [a+b. (a,b)\<leftarrow>zip xs ys]"
    using listset_length[of xs Gs] listset_length[of ys Gs, THEN sym] sum_list_plus
    by    simp
  ultimately show "(\<Oplus>Gs\<leftarrow>(x+y)) = [a+b. (a,b)\<leftarrow>zip xs ys]"
    using assms AbGroup_inner_dirsum AbGroup.add_closed
          AbGroup_inner_dirsum_el_decomp_eq
    by    fast
qed

lemma AbGroup_length_inner_dirsum_el_decomp :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; x \<in> (\<Oplus>G\<leftarrow>Gs. G) \<rbrakk>
        \<Longrightarrow> length (\<Oplus>Gs\<leftarrow>x) = length Gs"
  using AbGroup_inner_dirsum_el_decompI listset_length by fastforce

lemma AbGroup_inner_dirsum_el_decomp_in_nth :
  assumes "\<forall>G \<in> set Gs. AbGroup G" "add_independentS Gs" "n < length Gs"
          "x \<in> Gs!n"
  shows   "(\<Oplus>Gs\<leftarrow>x) = (replicate (length Gs) 0)[n := x]"
proof-
  from assms have x: "x \<in> (\<Oplus>G\<leftarrow>Gs. G)"
    using AbGroup_nth_subset_inner_dirsum by fast
  define xgs where "xgs = (replicate (length Gs) (0::'a))[n := x]"
  hence "length xgs = length Gs" by simp
  moreover have "\<forall>k<length xgs. xgs!k \<in> Gs!k"
  proof-
    have "\<And>k. k < length xgs \<Longrightarrow> xgs!k \<in> Gs!k"
    proof-
      fix k assume "k < length xgs"
      with assms(1,4) xgs_def show "xgs!k \<in> Gs!k" 
        using AbGroup.zero_closed[of "Gs!k"] by (cases "k = n") auto
    qed
    thus ?thesis by fast
  qed
  ultimately have "xgs \<in> listset Gs" using listsetI_nth by fast
  moreover from xgs_def assms(3) have "x = sum_list xgs"
    using sum_list_update[of n "replicate (length Gs) 0" x] nth_replicate sum_list_replicate0
    by    simp
  ultimately show "(\<Oplus>Gs\<leftarrow>x) = xgs"
    using assms(1,2) x xgs_def AbGroup_inner_dirsum_el_decomp_eq by fast
qed

lemma AbGroup_inner_dirsum_el_decomp_nth_in_nth :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; k < length Gs;
        n < length Gs; x \<in> Gs!n \<rbrakk> \<Longrightarrow> (\<Oplus>Gs\<down>k) x = (if k = n then x else 0)"
  using AbGroup_nth_subset_inner_dirsum
        AbGroup_inner_dirsum_el_decomp_in_nth[of Gs n x]
  by    auto

lemma AbGroup_inner_dirsum_el_decomp_nth_id_on_nth :
  "\<lbrakk> \<forall>G \<in> set Gs. AbGroup G; add_independentS Gs; n < length Gs; x \<in> Gs!n \<rbrakk> 
        \<Longrightarrow> (\<Oplus>Gs\<down>n) x = x"
  using AbGroup_inner_dirsum_el_decomp_nth_in_nth by fastforce

lemma AbGroup_inner_dirsum_el_decomp_nth_onto_nth :
  assumes "\<forall>G \<in> set Gs. AbGroup G" "add_independentS Gs" "n < length Gs"
  shows   "(\<Oplus>Gs\<down>n) ` (\<Oplus>G\<leftarrow>Gs. G) = Gs!n"
proof
  from assms show "(\<Oplus>Gs\<down>n) ` (\<Oplus>G\<leftarrow>Gs. G) \<supseteq> Gs!n"
    using AbGroup_nth_subset_inner_dirsum[of Gs n]
          AbGroup_inner_dirsum_el_decomp_nth_id_on_nth[of Gs n]
    by    force
  from assms show "(\<Oplus>Gs\<down>n) ` (\<Oplus>G\<leftarrow>Gs. G) \<subseteq> Gs!n"
      using AbGroup_inner_dirsum_el_decompI listset_length listsetD_nth by fastforce
qed

lemma AbGroup_inner_dirsum_subset_proj_eq_0 :
  assumes "Gs \<noteq> []" "\<forall>G \<in> set Gs. AbGroup G" "add_independentS Gs"
          "X \<subseteq> (\<Oplus>G\<leftarrow>Gs. G)" "\<forall>i < length Gs. (\<Oplus>Gs\<down>i) ` X = 0"
  shows   "X = 0"
proof-
  have "X \<subseteq> 0"
  proof
    fix x assume x: "x \<in> X"
    with assms(2-4) have "x = (\<Sum>i=0..< length Gs. (\<Oplus>Gs\<down>i) x)"
      using AbGroup_inner_dirsum_el_decompI sum_list_sum_nth[of "(\<Oplus>Gs\<leftarrow>x)"]
            AbGroup_length_inner_dirsum_el_decomp
      by    fastforce
    moreover from x assms(5) have "\<forall>i<length Gs. (\<Oplus>Gs\<down>i) x = 0" by auto
    ultimately show "x \<in> 0" by simp
  qed
  moreover from assms(1,5) have "X \<noteq> {}" by auto
  ultimately show ?thesis by auto
qed

lemma GroupEnd_inner_dirsum_el_decomp_nth :
  assumes "\<forall>G \<in> set Gs. AbGroup G" "add_independentS Gs" "n < length Gs"
  shows   "GroupEnd (\<Oplus>G\<leftarrow>Gs. G) (\<Oplus>Gs\<down>n)"
proof (intro_locales)
  from assms(1) show grp: "Group (\<Oplus>G\<leftarrow>Gs. G)"
    using AbGroup_inner_dirsum AbGroup.axioms by fast
  show "GroupHom_axioms (\<Oplus>G\<leftarrow>Gs. G) \<Oplus>Gs\<down>n"
  proof
    show "supp (\<Oplus>Gs\<down>n) \<subseteq> (\<Oplus>G\<leftarrow>Gs. G)" using supp_restrict0 by fast
  next
    fix x y assume xy: "x \<in> (\<Oplus>G\<leftarrow>Gs. G)" "y \<in> (\<Oplus>G\<leftarrow>Gs. G)"
    with assms(1,2) have "(\<Oplus>Gs\<leftarrow>(x+y)) = [x+y. (x,y)\<leftarrow>zip (\<Oplus>Gs\<leftarrow>x) (\<Oplus>Gs\<leftarrow>y)]"
      using AbGroup_inner_dirsum_el_decomp_plus by fast
    hence "(\<Oplus>Gs\<leftarrow>(x+y)) = map (case_prod (+)) (zip (\<Oplus>Gs\<leftarrow>x) (\<Oplus>Gs\<leftarrow>y))"
      using concat_map_split_eq_map_split_zip by simp
    moreover from assms xy
      have  "n < length (\<Oplus>Gs\<leftarrow>x)" "n < length (\<Oplus>Gs\<leftarrow>y)"
            "n < length (zip (\<Oplus>Gs\<leftarrow>x) (\<Oplus>Gs\<leftarrow>y))"
      using AbGroup_length_inner_dirsum_el_decomp[of Gs x]
            AbGroup_length_inner_dirsum_el_decomp[of Gs y]
      by    auto
    ultimately show "(\<Oplus>Gs\<down>n) (x + y) = (\<Oplus>Gs\<down>n) x + (\<Oplus>Gs\<down>n) y"
      using xy assms(1) AbGroup_inner_dirsum
            AbGroup.add_closed[of "\<Oplus>G\<leftarrow>Gs. G"]
      by    auto
  qed
  show "GroupEnd_axioms (\<Oplus>G\<leftarrow>Gs. G) \<Oplus>Gs\<down>n"
    using assms AbGroup_inner_dirsum_el_decomp_nth_onto_nth AbGroup_nth_subset_inner_dirsum
    by    unfold_locales fast
qed


subsection \<open>Rings\<close>

subsubsection \<open>Preliminaries\<close>

lemma (in ring_1) map_times_neg1_eq_map_uminus : "[(-1)*r. r\<leftarrow>rs] = [-r. r\<leftarrow>rs]"
  using map_eq_conv by simp

subsubsection \<open>Locale and basic facts\<close>

text \<open>Define a \<open>Ring1\<close> to be a multiplicatively closed additive subgroup of @{term UNIV} for
        the \<open>ring_1\<close> class.\<close>

(* Don't need to use AbGroup for R because ring_1 already assumes add_commute *)
locale Ring1 = Group R
  for R :: "'r::ring_1 set"
+ assumes one_closed : "1 \<in> R"
  and     mult_closed: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow> r * s \<in> R"
begin

lemma AbGroup : "AbGroup R"
  using Ring1_axioms Ring1.axioms(1) AbGroup.intro by fast

lemmas zero_closed         = zero_closed
lemmas add_closed          = add_closed
lemmas neg_closed          = neg_closed
lemmas diff_closed         = diff_closed
lemmas zip_add_closed      = zip_add_closed
lemmas sum_closed       = AbGroup.sum_closed[OF AbGroup]
lemmas sum_list_closed      = sum_list_closed
lemmas sum_list_closed_prod = sum_list_closed_prod
lemmas list_diff_closed    = list_diff_closed

abbreviation Subring1 :: "'r set \<Rightarrow> bool" where "Subring1 S \<equiv> Ring1 S \<and> S \<subseteq> R"

lemma Subring1D1 : "Subring1 S \<Longrightarrow> Ring1 S" by fast

end (* context Ring1 *)

lemma (in ring_1) full_Ring1 : "Ring1 UNIV" 
  by unfold_locales auto


subsection \<open>The group ring\<close>

subsubsection \<open>Definition and basic facts\<close>

text \<open>
  Realize the group ring as the set of almost-every-zero functions from group to ring. One can
  recover the usual notion of group ring element by considering such a function to send group
  elements to their coefficients. Here the codomain of such functions is not restricted to some
  \<open>Ring1\<close> subset since we will not be interested in having the ability to change the ring of
  scalars for a group ring.
\<close>

context Group
begin

abbreviation group_ring :: "('a::zero, 'g) aezfun set"
  where "group_ring \<equiv> aezfun_setspan G"

lemmas group_ringD = aezfun_setspan_def[of G]

lemma RG_one_closed : "(1::('r::zero_neq_one,'g) aezfun) \<in> group_ring"
proof-
  have "supp (aezfun (1::('r,'g) aezfun)) \<subseteq> G"
    using supp_aezfun1 zeroS_closed by fast
  thus ?thesis using group_ringD by fast
qed

lemma RG_zero_closed : "(0::('r::zero,'g) aezfun) \<in> group_ring"
proof-
  have "aezfun (0::('r,'g) aezfun) = (0::'g\<Rightarrow>'r)" using zero_aezfun.rep_eq by fast
  hence "supp (aezfun (0::('r,'g) aezfun)) = supp (0::'g\<Rightarrow>'r)" by simp
  moreover have "supp (0::'g\<Rightarrow>'r) \<subseteq> G" using supp_zerofun_subset_any by fast
  ultimately show ?thesis using group_ringD by fast
qed

lemma RG_n0 : "group_ring \<noteq> (0::('r::zero_neq_one, 'g) aezfun set)"
  using RG_one_closed zero_neq_one by force

lemma RG_mult_closed :
  defines RG: "RG \<equiv> group_ring :: ('r::ring_1, 'g) aezfun set"
  shows   "x \<in> RG \<Longrightarrow> y \<in> RG \<Longrightarrow> x * y \<in> RG"
  using   RG supp_aezfun_times[of x y]
          set_plus_closed[of "supp (aezfun x)" "supp (aezfun y)"]
          group_ringD
  by      blast

lemma Ring1_RG :
  defines RG: "RG \<equiv> group_ring :: ('r::ring_1, 'g) aezfun set"
  shows   "Ring1 RG"
proof
  from RG show "RG \<noteq> {}" "1 \<in> RG" "\<And>x y. x \<in> RG \<Longrightarrow> y \<in> RG \<Longrightarrow> x * y \<in> RG"
    using RG_one_closed RG_mult_closed by auto
next
  fix x y assume "x \<in> RG" "y \<in> RG"
  with RG show "x - y \<in> RG" using supp_aezfun_diff[of x y] group_ringD by blast
qed

lemma RG_aezdeltafun_closed :
  defines RG: "RG \<equiv> group_ring :: ('r::ring_1, 'g) aezfun set"
  assumes "g \<in> G"
  shows   "r \<delta>\<delta> g \<in> RG"
proof-
  have supp: "supp (aezfun (r \<delta>\<delta> g)) = supp (r \<delta> g)"
    using aezdeltafun arg_cong[of _ _ "supp"] by fast
  have "supp (aezfun (r \<delta>\<delta> g)) \<subseteq> G"
  proof (cases "r = 0")
    case True with supp show ?thesis using supp_delta0fun by fast
  next
    case False with assms supp show ?thesis using supp_deltafun[of r g] by fast
  qed
  with RG show ?thesis using group_ringD by fast
qed

lemma RG_aezdelta0fun_closed : "(r::'r::ring_1) \<delta>\<delta> 0 \<in> group_ring"
  using zero_closed RG_aezdeltafun_closed[of 0] by fast

lemma RG_sum_list_rddg_closed :
  defines RG: "RG \<equiv> group_ring :: ('r::ring_1, 'g) aezfun set"
  assumes "set (map snd rgs) \<subseteq> G"
  shows   "(\<Sum>(r,g)\<leftarrow>rgs. r \<delta>\<delta> g) \<in> RG"
proof (rule Ring1.sum_list_closed_prod)
  from RG show "Ring1 RG" using Ring1_RG by fast
  from assms show "set (map (case_prod aezdeltafun) rgs) \<subseteq> RG"
    using RG_aezdeltafun_closed by fastforce
qed

lemmas RG_el_decomp_aezdeltafun = aezfun_setspan_el_decomp_aezdeltafun[of _ G]

lemma Subgroup_imp_Subring :
  fixes   H  :: "'g set"
  and     FH :: "('r::ring_1,'g) aezfun set"
  and     FG :: "('r,'g) aezfun set"
  defines "FH \<equiv> Group.group_ring H"
  and     "FG \<equiv> group_ring"
  shows   "Subgroup H \<Longrightarrow> Ring1.Subring1 FG FH"
  using   assms Group.Ring1_RG Group.RG_el_decomp_aezdeltafun RG_sum_list_rddg_closed
  by      fast

end (* context Group *)

lemma (in FinGroup) group_ring_spanning_set :
  "\<exists>gs. distinct gs \<and> set gs = G
        \<and> (\<forall>f\<in> (group_ring :: ('b::semiring_1, 'g) aezfun set). \<exists>bs.
          length bs = length gs \<and> f = (\<Sum>(b,g)\<leftarrow>zip bs gs. (b \<delta>\<delta> 0) * (1 \<delta>\<delta> g)) )"
  using     finite aezfun_common_supp_spanning_set_decomp[of G] group_ringD
  by        fast

subsubsection \<open>Projecting almost-everywhere-zero functions onto a group ring\<close>

context Group
begin

abbreviation "RG_proj \<equiv> aezfun_setspan_proj G"

lemmas RG_proj_in_RG        = aezfun_setspan_proj_in_setspan
lemmas RG_proj_sum_list_prod = aezfun_setspan_proj_sum_list_prod[of G]

lemma RG_proj_mult_leftdelta' :
  fixes   r s :: "'r::{comm_monoid_add,mult_zero}"
  shows   "g \<in> G \<Longrightarrow> RG_proj (r \<delta>\<delta> g * (s \<delta>\<delta> g')) = r \<delta>\<delta> g * RG_proj (s \<delta>\<delta> g')"
  using   add_closed add_closed_inverse_right times_aezdeltafun_aezdeltafun[of r g]
          aezfun_setspan_proj_aezdeltafun[of G "r*s"]
          aezfun_setspan_proj_aezdeltafun[of G s]
  by      simp

lemma RG_proj_mult_leftdelta :
  fixes   r :: "'r::semiring_1"
  assumes "g \<in> G"
  shows   "RG_proj ((r \<delta>\<delta> g) * x) = r \<delta>\<delta> g * RG_proj x"
proof-                                                                                
  from aezfun_decomp_aezdeltafun obtain rgs
    where rgs: "x = (\<Sum>(s,h)\<leftarrow>rgs. s \<delta>\<delta> h)"
    using RG_el_decomp_aezdeltafun
    by    fast
  hence "RG_proj ((r \<delta>\<delta> g) * x) = (\<Sum>(s,h)\<leftarrow>rgs. RG_proj ((r \<delta>\<delta> g) * (s \<delta>\<delta> h)))"
    using sum_list_const_mult_prod[of "r \<delta>\<delta> g" "\<lambda>s h. s \<delta>\<delta> h"] RG_proj_sum_list_prod
    by    simp
  also from assms rgs have "\<dots> = (r \<delta>\<delta> g) * RG_proj x"
    using RG_proj_mult_leftdelta'[of g r]
          sum_list_const_mult_prod[of "r \<delta>\<delta> g" "\<lambda>s h. RG_proj (s \<delta>\<delta> h)"]
          RG_proj_sum_list_prod[of "\<lambda>s h. s \<delta>\<delta> h" rgs]
    by    simp
  finally show ?thesis by fast
qed

lemma RG_proj_mult_rightdelta' :
  fixes   r s :: "'r::{comm_monoid_add,mult_zero}"
  assumes "g' \<in> G"
  shows   "RG_proj (r \<delta>\<delta> g * (s \<delta>\<delta> g')) = RG_proj (r \<delta>\<delta> g) * (s \<delta>\<delta> g')"
  using   assms times_aezdeltafun_aezdeltafun[of r g]
          aezfun_setspan_proj_aezdeltafun[of G "r*s"]
          add_closed add_closed_inverse_left aezfun_setspan_proj_aezdeltafun[of G r]
  by      simp

lemma RG_proj_mult_rightdelta :
  fixes   r :: "'r::semiring_1"
  assumes "g \<in> G"
  shows   "RG_proj (x * (r \<delta>\<delta> g)) = (RG_proj x) * (r \<delta>\<delta> g)"
proof-
  from aezfun_decomp_aezdeltafun obtain rgs
    where rgs: "x = (\<Sum>(s,h)\<leftarrow>rgs. s \<delta>\<delta> h)"
    using RG_el_decomp_aezdeltafun
    by    fast
  hence "RG_proj (x * (r \<delta>\<delta> g)) = (\<Sum>(s,h)\<leftarrow>rgs. RG_proj ((s \<delta>\<delta> h) * (r \<delta>\<delta> g)))"
    using sum_list_mult_const_prod[of "\<lambda>s h. s \<delta>\<delta> h" rgs] RG_proj_sum_list_prod
    by    simp
  with assms rgs show ?thesis
    using RG_proj_mult_rightdelta'[of g _ _ r]
          sum_list_prod_cong[of
            rgs "\<lambda>s h. RG_proj ((s \<delta>\<delta> h) * (r \<delta>\<delta> g))"
            "\<lambda>s h. RG_proj (s \<delta>\<delta> h) * (r \<delta>\<delta> g)"
          ]
          sum_list_mult_const_prod[of "\<lambda>s h. RG_proj (s \<delta>\<delta> h)" rgs]
          RG_proj_sum_list_prod[of "\<lambda>s h. s \<delta>\<delta> h" rgs]
          sum_list_mult_const_prod[of "\<lambda>s h. RG_proj (s \<delta>\<delta> h)" rgs "r \<delta>\<delta> g"]
          RG_proj_sum_list_prod[of "\<lambda>s h. s \<delta>\<delta> h" rgs]
    by    simp
qed

lemma RG_proj_mult_right :
  "x \<in> (group_ring :: ('r::ring_1, 'g) aezfun set)
        \<Longrightarrow> RG_proj (y * x) = RG_proj y * x"
  using RG_el_decomp_aezdeltafun sum_list_const_mult_prod[of y "\<lambda>r g. r \<delta>\<delta> g"]
        RG_proj_sum_list_prod[of "\<lambda>r g. y * (r \<delta>\<delta> g)"] RG_proj_mult_rightdelta[of _ y]
        sum_list_prod_cong[
          of _ "\<lambda>r g. RG_proj (y * (r \<delta>\<delta> g))" "\<lambda>r g. RG_proj y * (r \<delta>\<delta> g)"
        ]
        sum_list_const_mult_prod[of "RG_proj y" "\<lambda>r g. r \<delta>\<delta> g"]
  by    fastforce

end (* context Group *)


section \<open>Modules\<close>


subsection \<open>Locales and basic facts\<close>

subsubsection \<open>Locales\<close>

locale scalar_mult =
  fixes smult :: "'r::ring_1 \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)

locale R_scalar_mult = scalar_mult smult + Ring1 R
  for R     :: "'r::ring_1 set"
  and smult :: "'r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)

lemma (in scalar_mult) R_scalar_mult : "R_scalar_mult UNIV"
  using full_Ring1 R_scalar_mult.intro by fast

lemma (in R_scalar_mult) Ring1 : "Ring1 R" ..

locale RModule = R_scalars?: R_scalar_mult R smult + VecGroup?: Group M
  for R     :: "'r::ring_1 set"
  and smult :: "'r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and M     :: "'m set"
+ assumes smult_closed : "\<lbrakk> r \<in> R; m \<in> M \<rbrakk> \<Longrightarrow> r \<cdot> m \<in> M"
  and smult_distrib_left  [simp] : "\<lbrakk> r \<in> R; m \<in> M; n \<in> M \<rbrakk>
                                          \<Longrightarrow> r \<cdot> (m + n) = r \<cdot> m + r \<cdot> n"
  and smult_distrib_right [simp] : "\<lbrakk> r \<in> R; s \<in> R; m \<in> M \<rbrakk>
                                          \<Longrightarrow> (r + s) \<cdot> m = r \<cdot> m + s \<cdot> m"
  and smult_assoc [simp] : "\<lbrakk> r \<in> R; s \<in> R; m \<in> M \<rbrakk>
                                  \<Longrightarrow> r \<cdot> s \<cdot> m = (r * s) \<cdot> m"
  and one_smult [simp] : "m \<in> M \<Longrightarrow> 1 \<cdot> m = m"

lemmas RModuleI = RModule.intro[OF R_scalar_mult.intro]

locale Module = RModule UNIV smult M
  for smult :: "'r::ring_1 \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and M     :: "'m set"

lemmas ModuleI = RModuleI[of UNIV, OF full_Ring1, THEN Module.intro]

subsubsection \<open>Basic facts\<close>

lemma trivial_RModule :
  fixes   smult :: "'r::ring_1 \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)  
  assumes "Ring1 R" "\<forall>r\<in>R. smult r (0::'m::ab_group_add) = 0"
  shows   "RModule R smult (0::'m set)"
proof (rule RModuleI, rule assms(1), rule trivial_Group, unfold_locales)
  define Z where "Z = (0::'m set)"
  fix r s m n assume rsmn: "r \<in> R" "s \<in> R" "m \<in> Z" "n \<in> Z"
  from rsmn(1,3) Z_def assms(2) show "r \<cdot> m \<in> Z" by simp
  from rsmn(1,3,4) Z_def assms(2) show "r \<cdot> (m+n) = r \<cdot> m + r \<cdot> n" by simp
  from rsmn(1-3) Z_def assms show "(r + s) \<cdot> m = r \<cdot> m + s \<cdot> m"
    using Ring1.add_closed by auto
  from rsmn(1-3) Z_def assms show "r \<cdot> (s \<cdot> m) = (r*s) \<cdot> m"
    using Ring1.mult_closed by auto
next
  define Z where "Z = (0::'m set)"
  fix m assume "m \<in> Z" with Z_def assms show "1 \<cdot> m = m"
    using Ring1.one_closed by auto
qed

context RModule
begin

abbreviation RSubmodule :: "'m set \<Rightarrow> bool"
  where "RSubmodule N \<equiv> RModule R smult N \<and> N \<subseteq> M"

lemma Group : "Group M"
  using RModule_axioms RModule.axioms(2) by fast

lemma Subgroup_RSubmodule : "RSubmodule N \<Longrightarrow> Subgroup N"
  using RModule.Group by fast

lemma AbGroup : "AbGroup M"
  using AbGroup.intro Group by fast

lemmas zero_closed     = zero_closed
lemmas diff_closed     = diff_closed
lemmas set_plus_closed = set_plus_closed
lemmas sum_closed   = AbGroup.sum_closed[OF AbGroup]

lemma map_smult_closed :
  "r \<in> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> set (map ((\<cdot>) r) ms) \<subseteq> M"
  using smult_closed by (induct ms) auto

lemma zero_smult : "m \<in> M \<Longrightarrow> 0 \<cdot> m = 0"
  using R_scalars.zero_closed smult_distrib_right[of 0] add_left_imp_eq by simp

lemma smult_zero : "r \<in> R \<Longrightarrow> r \<cdot> 0 = 0"
  using zero_closed smult_distrib_left[of r 0] by simp

lemma neg_smult : "r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> (-r) \<cdot> m = - (r \<cdot> m)"
  using R_scalars.neg_closed smult_distrib_right[of r "-r" m]
        zero_smult minus_unique[of "r \<cdot> m"]
  by    simp

lemma neg_eq_neg1_smult : "m \<in> M \<Longrightarrow> (-1) \<cdot> m = - m"
  using one_closed neg_smult one_smult by fastforce

lemma smult_neg : "r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> r \<cdot> (- m) = - (r \<cdot> m)"
  using neg_eq_neg1_smult one_closed R_scalars.neg_closed smult_assoc[of r "- 1"]
        smult_closed
  by    force

lemma smult_distrib_left_diff :
  "\<lbrakk> r \<in> R; m \<in> M; n \<in> M \<rbrakk> \<Longrightarrow> r \<cdot> (m - n) = r \<cdot> m - r \<cdot> n"
  using neg_closed smult_distrib_left[of r m "-n"] smult_neg by (simp add: algebra_simps)

lemma smult_distrib_right_diff :
  "\<lbrakk> r \<in> R; s \<in> R; m \<in> M \<rbrakk> \<Longrightarrow> (r - s) \<cdot> m = r \<cdot> m - s \<cdot> m"
  using R_scalars.neg_closed smult_distrib_right[of r "-s"] neg_smult
  by    (simp add: algebra_simps)

lemma smult_sum_distrib :
  assumes "r \<in> R"
  shows   "finite A \<Longrightarrow> f ` A \<subseteq> M \<Longrightarrow> r \<cdot> (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A. r \<cdot> f a)"
proof (induct set: finite)
  case empty from assms show ?case using smult_zero by simp
next
  case (insert a A) with assms show ?case using sum_closed[of A] by simp
qed

lemma sum_smult_distrib :
  assumes "m \<in> M"
  shows   "finite A \<Longrightarrow> f ` A \<subseteq> R \<Longrightarrow> (\<Sum>a\<in>A. f a) \<cdot> m = (\<Sum>a\<in>A. (f a) \<cdot> m)"
proof (induct set: finite)
  case empty from assms show ?case using zero_smult by simp
next
  case (insert a A) with assms show ?case using R_scalars.sum_closed[of A] by simp
qed

lemma smult_sum_list_distrib :
  "r \<in> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> r \<cdot> (sum_list ms) = (\<Sum>m\<leftarrow>ms. r \<cdot> m)"
  using smult_zero sum_list_closed[of id] by (induct ms) auto

lemma sum_list_prod_map_smult_distrib :
  "m \<in> M \<Longrightarrow> set (map (case_prod f) xys) \<subseteq> R
        \<Longrightarrow> (\<Sum>(x,y)\<leftarrow>xys. f x y) \<cdot> m = (\<Sum>(x,y)\<leftarrow>xys. f x y \<cdot> m)"
  using zero_smult R_scalars.sum_list_closed_prod[of f]
  by    (induct xys) auto

lemma RSubmoduleI :
  assumes "Subgroup N" "\<And>r n. r \<in> R \<Longrightarrow> n \<in> N \<Longrightarrow> r \<cdot> n \<in> N"
  shows   "RSubmodule N"
proof
  show "RModule R smult N"
  proof (intro_locales, rule SubgroupD1[OF assms(1)], unfold_locales)
    from assms(2) show "\<And>r m. r \<in> R \<Longrightarrow> m \<in> N \<Longrightarrow> r \<cdot> m \<in> N" by fast
    from assms(1)
      show  "\<And>r m n. \<lbrakk> r \<in> R; m \<in> N; n \<in> N \<rbrakk> \<Longrightarrow> r \<cdot> (m + n) = r \<cdot> m + r \<cdot> n"
      using smult_distrib_left
      by    blast
    from assms(1)
      show  "\<And>r s m. \<lbrakk> r \<in> R; s \<in> R; m \<in> N \<rbrakk> \<Longrightarrow> (r + s) \<cdot> m = r \<cdot> m + s \<cdot> m"
      using smult_distrib_right
      by    blast
    from assms(1)
      show  "\<And>r s m. \<lbrakk> r \<in> R; s \<in> R; m \<in> N \<rbrakk> \<Longrightarrow> r \<cdot> s \<cdot> m = (r * s) \<cdot> m"
      using smult_assoc
      by    blast
    from assms(1) show "\<And>m. m \<in> N \<Longrightarrow> 1 \<cdot> m = m" using one_smult by blast
  qed
  from assms(1) show "N \<subseteq> M" by fast
qed

end (* context RModule *)

lemma (in R_scalar_mult) listset_RModule_Rsmult_closed :
  "\<lbrakk> \<forall>M\<in>set Ms. RModule R smult M; r \<in> R; ms \<in> listset Ms \<rbrakk> 
        \<Longrightarrow> [r \<cdot> m. m\<leftarrow>ms] \<in> listset Ms"
proof-
  have "\<lbrakk> length ms = length Ms; ms \<in> listset Ms;
              \<forall>M\<in>set Ms. RModule R smult M; r \<in> R \<rbrakk>
                \<Longrightarrow> [r \<cdot> m. m\<leftarrow>ms] \<in> listset Ms"
  proof (induct ms Ms rule: list_induct2)
    case (Cons m ms M Ms) thus ?case
      using listset_ConsD[of m] RModule.smult_closed listset_ConsI[of "r \<cdot> m" M]
      by    fastforce
  qed simp
  thus "\<lbrakk> \<forall>M\<in>set Ms. RModule R smult M; r \<in> R; ms \<in> listset Ms \<rbrakk> 
              \<Longrightarrow> [r \<cdot> m. m\<leftarrow>ms] \<in> listset Ms"
    using listset_length[of ms Ms] by fast
qed

context Module
begin

abbreviation Submodule :: "'m set \<Rightarrow> bool"
  where "Submodule \<equiv> RModule.RSubmodule UNIV smult M"

lemmas AbGroup    = AbGroup
lemmas SubmoduleI = RSubmoduleI

end (* context Module *)

subsubsection \<open>Module and submodule instances\<close>

lemma (in R_scalar_mult) trivial_RModule :
  "(\<And>r. r \<in> R \<Longrightarrow> r \<cdot> 0 = 0) \<Longrightarrow> RModule R smult 0"
  using trivial_Group add_closed mult_closed one_closed by unfold_locales auto

context RModule
begin

lemma trivial_RSubmodule : "RSubmodule 0"
  using zeroS_closed smult_zero trivial_RModule by fast

lemma RSubmodule_set_plus :
  assumes "RSubmodule L" "RSubmodule N"
  shows   "RSubmodule (L + N)"
proof (rule RSubmoduleI)
  from assms have "Group (L + N)"
    using RModule.AbGroup AbGroup_set_plus[of L N] AbGroup.axioms by fast
  moreover from assms have "L + N \<subseteq> M"
    using Group Group.set_plus_closed by auto
  ultimately show "Subgroup (L + N)" by fast
next
  fix r x assume rx: "r \<in> R" "x \<in> L + N"
  from rx(2) obtain m n where mn: "m \<in> L" "n \<in> N" "x = m + n"
    using set_plus_def[of L N] by fast
  with assms rx(1) show "r \<cdot> x \<in> L + N"
    using RModule.smult_closed[of R smult L] RModule.smult_closed[of R smult N]
          smult_distrib_left set_plus_def
    by    fast
qed

lemma RSubmodule_sum_list :
  "(\<forall>N\<in>set Ns. RSubmodule N) \<Longrightarrow> RSubmodule (\<Sum>N\<leftarrow>Ns. N)"
  using trivial_RSubmodule RSubmodule_set_plus
  by    (induct Ns) auto

lemma RSubmodule_inner_dirsum :
  assumes "(\<forall>N\<in>set Ns. RSubmodule N)"
  shows   "RSubmodule (\<Oplus>N\<leftarrow>Ns. N)"
proof (cases "add_independentS Ns")
  case True with assms show ?thesis
    using RSubmodule_sum_list inner_dirsumD by fastforce
next
  case False thus ?thesis
    using inner_dirsumD2[of Ns] trivial_RSubmodule by simp
qed

lemma RModule_inner_dirsum :
  "(\<forall>N\<in>set Ns. RSubmodule N) \<Longrightarrow> RModule R smult (\<Oplus>N\<leftarrow>Ns. N)"
  using RSubmodule_inner_dirsum by fast

lemma SModule_restrict_scalars :
  assumes "Subring1 S"
  shows   "RModule S smult M"
proof (rule RModuleI, rule Subring1D1[OF assms], rule Group, unfold_locales)
  from assms show
    "\<And>r m. r \<in> S \<Longrightarrow> m \<in> M \<Longrightarrow> r \<cdot> m \<in> M"
    "\<And>r m n. r \<in> S \<Longrightarrow> m \<in> M \<Longrightarrow> n \<in> M \<Longrightarrow> r \<cdot> (m + n) = r \<cdot> m + r \<cdot> n"
    "\<And>m. m \<in> M \<Longrightarrow> 1 \<cdot> m = m"
    using smult_closed smult_distrib_left
    by    auto
  from assms
    show  "\<And>r s m. r \<in> S \<Longrightarrow> s \<in> S \<Longrightarrow> m \<in> M \<Longrightarrow> (r + s) \<cdot> m = r \<cdot> m + s \<cdot> m"
    using Ring1.add_closed smult_distrib_right
    by    fast
  from assms
    show  "\<And>r s m. r \<in> S \<Longrightarrow> s \<in> S \<Longrightarrow> m \<in> M \<Longrightarrow> r \<cdot> s \<cdot> m = (r * s) \<cdot> m"
    using Ring1.mult_closed smult_assoc
    by    fast
qed

end (* context RModule *)


subsection \<open>Linear algebra in modules\<close>

subsubsection \<open>Linear combinations: \<open>lincomb\<close>\<close>

context scalar_mult
begin

definition lincomb :: "'r list \<Rightarrow> 'm list \<Rightarrow> 'm" (infix "\<bullet>\<cdot>" 70)
  where "rs \<bullet>\<cdot> ms = (\<Sum>(r,m)\<leftarrow>zip rs ms. r \<cdot> m)"

text \<open>Note: \<open>zip\<close> will truncate if lengths of coefficient and vector lists differ.\<close>

lemma lincomb_Nil : "rs = [] \<or> ms = [] \<Longrightarrow> rs \<bullet>\<cdot> ms = 0"
  unfolding lincomb_def by auto

lemma lincomb_singles : "[a] \<bullet>\<cdot> [m] = a \<cdot> m"
  using lincomb_def by simp

lemma lincomb_Cons : "(r # rs) \<bullet>\<cdot> (m # ms) = r \<cdot> m + rs \<bullet>\<cdot> ms"
  unfolding lincomb_def by simp

lemma lincomb_append :
  "length rs = length ms \<Longrightarrow> (rs@ss) \<bullet>\<cdot> (ms@ns) = rs \<bullet>\<cdot> ms + ss \<bullet>\<cdot> ns"
  unfolding lincomb_def by simp

lemma lincomb_append_left :
  "(rs @ ss) \<bullet>\<cdot> ms = rs \<bullet>\<cdot> ms + ss \<bullet>\<cdot> drop (length rs) ms"
  using zip_append_left[of rs ss ms] unfolding lincomb_def by simp

lemma lincomb_append_right :
  "rs \<bullet>\<cdot> (ms@ns) = rs \<bullet>\<cdot> ms + (drop (length ms) rs) \<bullet>\<cdot> ns"
  using zip_append_right[of rs ms] unfolding lincomb_def by simp

lemma lincomb_conv_take_right : "rs \<bullet>\<cdot> ms = rs \<bullet>\<cdot> take (length rs) ms"
  using lincomb_Nil lincomb_Cons by (induct rs ms rule: list_induct2') auto

end (* context scalar_mult *)

context RModule
begin

lemmas lincomb_Nil  = lincomb_Nil
lemmas lincomb_Cons = lincomb_Cons

lemma lincomb_closed : "set rs \<subseteq> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> rs \<bullet>\<cdot> ms \<in> M"
proof (induct ms arbitrary: rs)
  case Nil show ?case using lincomb_Nil zero_closed by simp
next
  case (Cons m ms)
  hence Cons1: "\<And>rs. set rs \<subseteq> R \<Longrightarrow> rs \<bullet>\<cdot> ms \<in> M" "m \<in> M" "set rs \<subseteq> R" by auto
  show "rs \<bullet>\<cdot> (m#ms) \<in> M"
  proof (cases rs)
    case Nil thus ?thesis using lincomb_Nil zero_closed by simp
  next
    case Cons with Cons1 show ?thesis
      using lincomb_Cons smult_closed add_closed by fastforce
  qed
qed

lemma smult_lincomb :
  "\<lbrakk> set rs \<subseteq> R; s \<in> R; set ms \<subseteq> M \<rbrakk> \<Longrightarrow> s \<cdot> (rs \<bullet>\<cdot> ms) = [s*r. r\<leftarrow>rs] \<bullet>\<cdot> ms"
  using lincomb_Nil smult_zero lincomb_Cons smult_closed lincomb_closed
  by    (induct rs ms rule: list_induct2') auto

lemma neg_lincomb :
  "set rs \<subseteq> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> - (rs \<bullet>\<cdot> ms) = [-r. r\<leftarrow>rs] \<bullet>\<cdot> ms"
  using lincomb_closed neg_eq_neg1_smult one_closed R_scalars.neg_closed[of 1]
        smult_lincomb[of rs "- 1"] map_times_neg1_eq_map_uminus
  by    auto

lemma lincomb_sum_left :
  "\<lbrakk> set rs \<subseteq> R; set ss \<subseteq> R; set ms \<subseteq> M; length rs \<le> length ss \<rbrakk>
        \<Longrightarrow> [r + s. (r,s)\<leftarrow>zip rs ss] \<bullet>\<cdot> ms = rs \<bullet>\<cdot> ms + (take (length rs) ss) \<bullet>\<cdot> ms"
proof (induct rs ss arbitrary: ms rule: list_induct2')
  case 1 show ?case using lincomb_Nil by simp
next
  case (2 r rs)
  show "\<And>ms. length (r#rs) \<le> length []
              \<Longrightarrow> [a + b. (a,b)\<leftarrow>zip (r#rs) []] \<bullet>\<cdot> ms
                = (r#rs) \<bullet>\<cdot> ms + (take (length (r#rs)) []) \<bullet>\<cdot> ms"
    by simp
next
  case 3 show ?case using lincomb_Nil by simp
next
  case (4 r rs s ss)
  thus "[a+b. (a,b)\<leftarrow>zip (r#rs) (s#ss)] \<bullet>\<cdot> ms
              = (r#rs) \<bullet>\<cdot> ms + (take (length (r#rs)) (s#ss)) \<bullet>\<cdot> ms"
    using lincomb_Nil lincomb_Cons by (cases ms) auto
qed

lemma lincomb_sum :
  assumes "set rs \<subseteq> R" "set ss \<subseteq> R" "set ms \<subseteq> M" "length rs \<le> length ss"
  shows   "rs \<bullet>\<cdot> ms + ss \<bullet>\<cdot> ms
                = ([a + b. (a,b)\<leftarrow>zip rs ss] @ (drop (length rs) ss)) \<bullet>\<cdot> ms"
proof-
  define zs fss bss
    where "zs = [a + b. (a,b)\<leftarrow>zip rs ss]"
      and "fss = take (length rs) ss"
      and "bss = drop (length rs) ss"
  from assms(4) zs_def fss_def have "length zs = length rs" "length fss = length rs"
    using length_concat_map_split_zip[of "\<lambda>a b. a + b" rs] by auto
  hence "(zs @ bss) \<bullet>\<cdot> ms = rs \<bullet>\<cdot> ms + (fss @ bss) \<bullet>\<cdot> ms"
    using assms(1,2,3) zs_def fss_def lincomb_sum_left lincomb_append_left
    by    simp
  thus ?thesis using fss_def bss_def zs_def by simp
qed

lemma lincomb_diff_left :
  "\<lbrakk> set rs \<subseteq> R; set ss \<subseteq> R; set ms \<subseteq> M; length rs \<le> length ss \<rbrakk>
        \<Longrightarrow> [r - s. (r,s)\<leftarrow>zip rs ss] \<bullet>\<cdot> ms = rs \<bullet>\<cdot> ms - (take (length rs) ss) \<bullet>\<cdot> ms"
proof (induct rs ss arbitrary: ms rule: list_induct2')
  case 1 show ?case using lincomb_Nil by simp
next
  case (2 r rs)
  show "\<And>ms. length (r#rs) \<le> length []
              \<Longrightarrow> [a - b. (a,b)\<leftarrow>zip (r#rs) []] \<bullet>\<cdot> ms
                = (r#rs) \<bullet>\<cdot> ms - (take (length (r#rs)) []) \<bullet>\<cdot> ms"
    by simp
next
  case 3 show ?case using lincomb_Nil by simp
next
  case (4 r rs s ss)
  thus "[a-b. (a,b)\<leftarrow>zip (r#rs) (s#ss)] \<bullet>\<cdot> ms
              = (r#rs) \<bullet>\<cdot> ms - (take (length (r#rs)) (s#ss)) \<bullet>\<cdot> ms"
    using lincomb_Nil lincomb_Cons smult_distrib_right_diff by (cases ms) auto
qed

lemma lincomb_replicate_left : 
  "r \<in> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> (replicate k r) \<bullet>\<cdot> ms = r \<cdot> ( \<Sum>m\<leftarrow>(take k ms). m )"
proof (induct k arbitrary: ms)
  case 0 thus ?case using lincomb_Nil smult_zero by simp
next
  case (Suc k)
  show ?case
  proof (cases ms)
    case Nil with Suc(2) show ?thesis using lincomb_Nil smult_zero by simp
  next
    case (Cons m ms) with Suc show ?thesis
      using lincomb_Cons set_take_subset[of k ms] sum_list_closed[of id]
      by    auto
  qed
qed

lemma lincomb_replicate0_left : "set ms \<subseteq> M \<Longrightarrow> (replicate k 0) \<bullet>\<cdot> ms = 0"
proof-
  assume ms: "set ms \<subseteq> M"
  hence "(replicate k 0) \<bullet>\<cdot> ms = 0 \<cdot> (\<Sum>m\<leftarrow>(take k ms). m)" 
    using R_scalars.zero_closed lincomb_replicate_left by fast
  moreover from ms have "(\<Sum>m\<leftarrow>(take k ms). m) \<in> M"
    using set_take_subset sum_list_closed by fastforce
  ultimately show "(replicate k 0) \<bullet>\<cdot> ms = 0" using zero_smult by simp
qed

lemma lincomb_0coeffs : "set ms \<subseteq> M \<Longrightarrow> \<forall>s\<in>set rs. s = 0 \<Longrightarrow> rs \<bullet>\<cdot> ms = 0"
  using lincomb_Nil lincomb_Cons zero_smult
  by    (induct rs ms rule: list_induct2') auto

lemma delta_scalars_lincomb_eq_nth :
  "set ms \<subseteq> M \<Longrightarrow> n < length ms
        \<Longrightarrow> ((replicate (length ms) 0)[n := 1]) \<bullet>\<cdot> ms = ms!n"
proof (induct ms arbitrary: n)
  case (Cons m ms) thus ?case
    using lincomb_Cons lincomb_replicate0_left zero_smult by (cases n) auto
qed simp

lemma lincomb_obtain_same_length_Rcoeffs :
  "set rs \<subseteq> R \<Longrightarrow> set ms \<subseteq> M
        \<Longrightarrow> \<exists>ss. set ss \<subseteq> R \<and> length ss = length ms
          \<and> take (length rs) ss = take (length ms) rs \<and> rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms"
proof (induct rs ms rule: list_induct2')
  case 1 show ?case using lincomb_Nil by simp
next
  case 2 thus ?case using lincomb_Nil by simp
next
  case (3 m ms)
  define ss where "ss = replicate (Suc (length ms)) (0::'r)"
  from 3(2) ss_def
    have  "set ss \<subseteq> R" "length ss = length (m#ms)" "[] \<bullet>\<cdot> (m#ms) = ss \<bullet>\<cdot> (m#ms)"
    using R_scalars.zero_closed lincomb_Nil
          lincomb_replicate0_left[of "m#ms" "Suc (length ms)"]
    by    auto
  thus ?case by auto
next
  case (4 r rs m ms)
  from this obtain ss
    where ss: "set ss \<subseteq> R" "length ss = length ms"
              "take (length rs) ss = take (length ms) rs" "rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms"
      by  auto
  from 4(2) ss have 
    "set (r#ss) \<subseteq> R" "length (r#ss) = length (m#ms)"
    "take (length (r#rs)) (r#ss) = take (length (m#ms)) (r#rs)"
    "(r#rs) \<bullet>\<cdot> (m#ms) = (r#ss) \<bullet>\<cdot> (m#ms)"
    using lincomb_Cons
    by    auto
  thus ?case by fast
qed

lemma lincomb_concat :
  "list_all2 (\<lambda>rs ms. length rs = length ms) rss mss
        \<Longrightarrow> (concat rss) \<bullet>\<cdot> (concat mss) = (\<Sum>(rs,ms)\<leftarrow>zip rss mss. rs \<bullet>\<cdot> ms)"
  using lincomb_Nil lincomb_append by (induct rss mss rule: list_induct2') auto

lemma lincomb_snoc0 : "set ms \<subseteq> M \<Longrightarrow> (as@[0]) \<bullet>\<cdot> ms = as \<bullet>\<cdot> ms"
  using lincomb_append_left set_drop_subset lincomb_replicate0_left[of _ 1] by fastforce

lemma lincomb_strip_while_0coeffs :
  assumes "set ms \<subseteq> M"
  shows   "(strip_while ((=) 0) as) \<bullet>\<cdot> ms = as \<bullet>\<cdot> ms"
proof (induct as rule: rev_induct)
  case (snoc a as)
  hence caseassm: "strip_while ((=) 0) as \<bullet>\<cdot> ms = as \<bullet>\<cdot> ms" by fast
  show ?case
  proof (cases "a = 0")
    case True
    moreover with assms have "(as@[a]) \<bullet>\<cdot> ms = as \<bullet>\<cdot> ms"
      using lincomb_snoc0 by fast
    ultimately show "strip_while ((=) 0) (as @ [a]) \<bullet>\<cdot> ms = (as@[a]) \<bullet>\<cdot> ms"
      using caseassm by simp
  qed simp
qed simp

end (* context RModule *)

lemmas (in Module) lincomb_obtain_same_length_coeffs = lincomb_obtain_same_length_Rcoeffs
lemmas (in Module) lincomb_concat                    = lincomb_concat

subsubsection \<open>Spanning: \<open>RSpan\<close> and \<open>Span\<close>\<close>

context R_scalar_mult
begin

primrec RSpan :: "'m list \<Rightarrow> 'm set"
  where "RSpan [] = 0"
      | "RSpan (m#ms) = { r \<cdot> m | r. r \<in> R } + RSpan ms"

lemma RSpan_single : "RSpan [m] = { r \<cdot> m | r. r \<in> R }"
  using add_0_right[of "{ r \<cdot> m | r. r \<in> R }"] by simp

lemma RSpan_Cons : "RSpan (m#ms) = RSpan [m] + RSpan ms"
  using RSpan_single by simp

lemma in_RSpan_obtain_same_length_coeffs :
  "n \<in> RSpan ms \<Longrightarrow> \<exists>rs. set rs \<subseteq> R \<and> length rs = length ms \<and> n = rs \<bullet>\<cdot> ms"
proof (induct ms arbitrary: n)
  case Nil
  hence "n = 0" by simp
  thus "\<exists>rs. set rs \<subseteq> R \<and> length rs = length [] \<and> n = rs \<bullet>\<cdot> []"
    using lincomb_Nil by simp
next
  case (Cons m ms)
  from this obtain r rs
    where "set (r#rs) \<subseteq> R" "length (r#rs) = length (m#ms)" "n = (r#rs) \<bullet>\<cdot> (m#ms)"
    using set_plus_def[of _ "RSpan ms"] lincomb_Cons
    by    fastforce
  thus "\<exists>rs. set rs \<subseteq> R \<and> length rs = length (m#ms) \<and> n = rs \<bullet>\<cdot> (m#ms)" by fast
qed

lemma in_RSpan_Cons_obtain_same_length_coeffs :
  "n \<in> RSpan (m#ms) \<Longrightarrow> \<exists>r rs. set (r#rs) \<subseteq> R \<and> length rs = length ms 
        \<and> n = r \<cdot> m + rs \<bullet>\<cdot> ms"
proof-
  assume "n \<in> RSpan (m#ms)"
  from this obtain x y where "x \<in> RSpan [m]" "y \<in> RSpan ms" "n = x + y"
    using RSpan_Cons set_plus_def[of "RSpan [m]"] by auto
  thus "\<exists>r rs. set (r # rs) \<subseteq> R \<and> length rs = length ms \<and> n = r \<cdot> m + rs \<bullet>\<cdot> ms"
    using RSpan_single in_RSpan_obtain_same_length_coeffs[of y ms] by auto
qed

lemma RSpanD_lincomb :
  "RSpan ms = { rs \<bullet>\<cdot> ms | rs. set rs \<subseteq> R \<and> length rs = length ms}"
proof
  show "RSpan ms \<subseteq> {rs \<bullet>\<cdot> ms |rs. set rs \<subseteq> R \<and> length rs = length ms}"
    using in_RSpan_obtain_same_length_coeffs by fast
  show "{rs \<bullet>\<cdot> ms |rs. set rs \<subseteq> R \<and> length rs = length ms} \<subseteq> RSpan ms"
  proof
    fix x assume "x \<in> {rs \<bullet>\<cdot> ms |rs. set rs \<subseteq> R  \<and> length rs = length ms}"
    from this obtain rs where rs: "set rs \<subseteq> R" "length rs = length ms" "x = rs \<bullet>\<cdot> ms"
      by fast
    from rs(2) have "set rs \<subseteq> R \<Longrightarrow> rs \<bullet>\<cdot> ms \<in> RSpan ms"
      using lincomb_Nil lincomb_Cons by (induct rs ms rule: list_induct2) auto
    with rs(1,3) show "x \<in> RSpan ms" by fast
  qed
qed

lemma RSpan_append : "RSpan (ms @ ns) = RSpan ms + RSpan ns"
proof (induct ms)
  case Nil show ?case using add_0_left[of "RSpan ns"] by simp
next
  case (Cons m ms) thus ?case
    using RSpan_Cons[of m "ms@ns"] add.assoc by fastforce
qed

end (* context R_scalar_mult *)

context scalar_mult
begin

abbreviation "Span \<equiv> R_scalar_mult.RSpan UNIV smult"

lemmas Span_append = R_scalar_mult.RSpan_append[OF R_scalar_mult, of smult]
lemmas SpanD_lincomb
          = R_scalar_mult.RSpanD_lincomb [OF R_scalar_mult, of smult]

lemmas in_Span_obtain_same_length_coeffs
          = R_scalar_mult.in_RSpan_obtain_same_length_coeffs[
              OF R_scalar_mult, of _ smult
            ]

end (* context scalar_mult *)

context RModule
begin

lemma RSpan_contains_spanset_single : "m \<in> M \<Longrightarrow> m \<in> RSpan [m]"
  using one_closed RSpan_single by fastforce

lemma RSpan_single_nonzero : "m \<in> M \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> RSpan [m] \<noteq> 0"
  using RSpan_contains_spanset_single by auto

lemma Group_RSpan_single :
  assumes "m \<in> M"
  shows   "Group (RSpan [m])"
proof
  from assms show "RSpan [m] \<noteq> {}" using RSpan_contains_spanset_single by fast
next
  fix x y assume "x \<in> RSpan [m]" "y \<in> RSpan [m]"
  from this obtain r s where rs: "r \<in> R" "x = r \<cdot> m" "s \<in> R" "y = s \<cdot> m"
    using RSpan_single by auto
  with assms have "x - y = (r - s) \<cdot> m" using smult_distrib_right_diff by simp
  with rs(1,3) show "x - y \<in> RSpan [m]"
    using R_scalars.diff_closed[of r s] RSpan_single[of m] by auto
qed

lemma Group_RSpan : "set ms \<subseteq> M \<Longrightarrow> Group (RSpan ms)"
proof (induct ms)
  case Nil show ?case using trivial_Group by simp
next
  case (Cons m ms)
  hence "Group (RSpan [m])" "Group (RSpan ms)"
    using Group_RSpan_single[of m] by auto
  thus ?case
    using RSpan_Cons[of m ms] AbGroup.intro AbGroup_set_plus AbGroup.axioms(1)
    by    fastforce
qed

lemma RSpanD_lincomb_arb_len_coeffs :
  "set ms \<subseteq> M \<Longrightarrow> RSpan ms = { rs \<bullet>\<cdot> ms | rs. set rs \<subseteq> R }"
proof
  show "RSpan ms \<subseteq> { rs \<bullet>\<cdot> ms | rs. set rs \<subseteq> R }" using RSpanD_lincomb by fast
  show "set ms \<subseteq> M \<Longrightarrow> RSpan ms \<supseteq> { rs \<bullet>\<cdot> ms | rs. set rs \<subseteq> R }"
  proof (induct ms)
    case Nil show ?case using lincomb_Nil by auto
  next
    case (Cons m ms) show ?case
    proof
      fix x assume "x \<in> { rs \<bullet>\<cdot> (m#ms) | rs. set rs \<subseteq> R }"
      from this obtain rs where rs: "set rs \<subseteq> R" "x = rs \<bullet>\<cdot> (m#ms)" by fast
      with Cons show "x \<in> RSpan (m#ms)"
        using lincomb_Nil Group_RSpan[of "m#ms"] Group.zero_closed lincomb_Cons
        by    (cases rs) auto
    qed
  qed
qed

lemma RSpanI_lincomb_arb_len_coeffs :
  "set rs \<subseteq> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> rs \<bullet>\<cdot> ms \<in> RSpan ms"
  using RSpanD_lincomb_arb_len_coeffs by fast

lemma RSpan_contains_RSpans_Cons_left :
  "set ms \<subseteq> M \<Longrightarrow> RSpan [m] \<subseteq> RSpan (m#ms)"
  using RSpan_Cons Group_RSpan AbGroup.intro AbGroup.subset_plus_left by fast

lemma RSpan_contains_RSpans_Cons_right :
  "m \<in> M \<Longrightarrow> RSpan ms \<subseteq> RSpan (m#ms)"
  using RSpan_Cons Group_RSpan_single AbGroup.intro AbGroup.subset_plus_right by fast

lemma RSpan_contains_RSpans_append_left :
  "set ns \<subseteq> M \<Longrightarrow> RSpan ms \<subseteq> RSpan (ms@ns)"
  using RSpan_append Group_RSpan AbGroup.intro AbGroup.subset_plus_left
  by    fast

lemma RSpan_contains_spanset : "set ms \<subseteq> M \<Longrightarrow> set ms \<subseteq> RSpan ms"
proof (induct ms)
  case Nil show ?case by simp
next
  case (Cons m ms) thus ?case
    using RSpan_contains_spanset_single
          RSpan_contains_RSpans_Cons_left[of ms m]
          RSpan_contains_RSpans_Cons_right[of m ms]
    by    auto
qed

lemma RSpan_contains_spanset_append_left :
  "set ms \<subseteq> M \<Longrightarrow> set ns \<subseteq> M \<Longrightarrow> set ms \<subseteq> RSpan (ms@ns)"
  using RSpan_contains_spanset[of "ms@ns"] by simp

lemma RSpan_contains_spanset_append_right :
  "set ms \<subseteq> M \<Longrightarrow> set ns \<subseteq> M \<Longrightarrow> set ns \<subseteq> RSpan (ms@ns)"
  using RSpan_contains_spanset[of "ms@ns"] by simp

lemma RSpan_zero_closed : "set ms \<subseteq> M \<Longrightarrow> 0 \<in> RSpan ms"
  using Group_RSpan Group.zero_closed by fast

lemma RSpan_single_closed : "m \<in> M \<Longrightarrow> RSpan [m] \<subseteq> M"
  using RSpan_single smult_closed by auto

lemma RSpan_closed : "set ms \<subseteq> M \<Longrightarrow> RSpan ms \<subseteq> M"
proof (induct ms)
  case Nil show ?case using zero_closed by simp
next
  case (Cons m ms) thus ?case 
    using RSpan_single_closed RSpan_Cons Group Group.set_plus_closed[of M]
    by    simp
qed

lemma RSpan_smult_closed :
  assumes "r \<in> R" "set ms \<subseteq> M" "n \<in> RSpan ms"
  shows "r \<cdot> n \<in> RSpan ms"
proof-
  from assms(2,3) obtain rs where rs: "set rs \<subseteq> R" "n = rs \<bullet>\<cdot> ms"
    using RSpanD_lincomb_arb_len_coeffs by fast
  with assms(1,2) show ?thesis
    using smult_lincomb[OF rs(1) assms(1,2)] mult_closed
          RSpanI_lincomb_arb_len_coeffs[of "[r*a. a\<leftarrow>rs]" ms]
    by    auto
qed

lemma RSpan_add_closed :
  assumes "set ms \<subseteq> M" "n \<in> RSpan ms" "n' \<in> RSpan ms"
  shows   "n + n' \<in> RSpan ms"
proof-
  from assms (2,3) obtain rs ss
    where rs: "set rs \<subseteq> R" "length rs = length ms" "n = rs \<bullet>\<cdot> ms"
    and   ss: "set ss \<subseteq> R" "length ss = length ms" "n' = ss \<bullet>\<cdot> ms"
    using RSpanD_lincomb by auto
  with assms(1) have "n + n' = [r + s. (r,s)\<leftarrow>zip rs ss] \<bullet>\<cdot> ms"
    using lincomb_sum_left by simp
  moreover from rs(1) ss(1) have "set [r + s. (r,s)\<leftarrow>zip rs ss] \<subseteq> R"
    using set_zip_leftD[of _ _ rs ss] set_zip_rightD[of _ _ rs ss]  
          R_scalars.add_closed R_scalars.zip_add_closed by blast
  ultimately show "n + n' \<in> RSpan ms"
    using assms(1) RSpanI_lincomb_arb_len_coeffs by simp
qed

lemma RSpan_lincomb_closed :
  "\<lbrakk> set rs \<subseteq> R; set ms \<subseteq> M; set ns \<subseteq> RSpan ms \<rbrakk> \<Longrightarrow> rs \<bullet>\<cdot> ns \<in> RSpan ms"
  using lincomb_Nil RSpan_zero_closed lincomb_Cons RSpan_smult_closed RSpan_add_closed
  by    (induct rs ns rule: list_induct2') auto

lemma RSpanI : "set ms \<subseteq> M \<Longrightarrow> M \<subseteq> RSpan ms \<Longrightarrow> M = RSpan ms"
  using RSpan_closed by fast

lemma RSpan_contains_RSpan_take :
  "set ms \<subseteq> M \<Longrightarrow> RSpan (take k ms) \<subseteq> RSpan ms"
  using append_take_drop_id set_drop_subset
        RSpan_contains_RSpans_append_left[of "drop k ms"]
  by    fastforce

lemma RSubmodule_RSpan_single :
  assumes "m \<in> M"
  shows   "RSubmodule (RSpan [m])"
proof (rule RSubmoduleI)
  from assms show "Subgroup (RSpan [m])"
    using Group_RSpan_single RSpan_closed[of "[m]"] by simp
next
  fix r n assume rn: "r \<in> R" "n \<in> RSpan [m]"
  from rn(2) obtain s where s: "s \<in> R" "n = s \<cdot> m" using RSpan_single by fast
  with assms rn(1) have "r * s \<in> R" "r \<cdot> n = (r * s) \<cdot> m"
    using mult_closed by auto
  thus "r \<cdot> n \<in> RSpan [m]" using RSpan_single by fast
qed

lemma RSubmodule_RSpan : "set ms \<subseteq> M \<Longrightarrow> RSubmodule (RSpan ms)"
proof (induct ms)
  case Nil show ?case using trivial_RSubmodule by simp
next
  case (Cons m ms)
  hence "RSubmodule (RSpan [m])" "RSubmodule (RSpan ms)"
    using RSubmodule_RSpan_single by auto
  thus ?case using RSpan_Cons RSubmodule_set_plus by simp
qed

lemma RSpan_RSpan_closed :
  "set ms \<subseteq> M \<Longrightarrow> set ns \<subseteq> RSpan ms \<Longrightarrow> RSpan ns \<subseteq> RSpan ms"
  using RSpanD_lincomb[of ns] RSpan_lincomb_closed by auto

lemma spanset_reduce_Cons :
  "set ms \<subseteq> M \<Longrightarrow> m \<in> RSpan ms \<Longrightarrow> RSpan (m#ms) = RSpan ms"
  using RSpan_Cons RSpan_RSpan_closed[of ms "[m]"]
        RSpan_contains_RSpans_Cons_right[of m ms]
        RSubmodule_RSpan[of ms]
        RModule.set_plus_closed[of R smult "RSpan ms" "RSpan [m]" "RSpan ms"]
  by    auto

lemma RSpan_replace_hd :
  assumes "n \<in> M" "set ms \<subseteq> M" "m \<in> RSpan (n # ms)"
  shows   "RSpan (m # ms) \<subseteq> RSpan (n # ms)"
proof
  fix x assume "x \<in> RSpan (m # ms)"
  from this assms(3) obtain r rs s ss
    where r_rs: "r \<in> R" "set rs \<subseteq> R" "length rs = length ms" "x = r \<cdot> m + rs \<bullet>\<cdot> ms"
    and   s_ss: "s \<in> R" "set ss \<subseteq> R" "length ss = length ms" "m = s \<cdot> n + ss \<bullet>\<cdot> ms"
    using in_RSpan_Cons_obtain_same_length_coeffs[of x m ms]
          in_RSpan_Cons_obtain_same_length_coeffs[of m n ms]
    by    fastforce
  from r_rs(1) s_ss(2) have set1: "set [r*a. a\<leftarrow>ss] \<subseteq> R" using mult_closed by auto
  have "x = ((r * s) # [a + b. (a,b)\<leftarrow>zip [r*a. a\<leftarrow>ss] rs]) \<bullet>\<cdot> (n # ms)"
  proof-
    from r_rs(2,3) s_ss(3) assms(2)
      have  "[r*a. a\<leftarrow>ss] \<bullet>\<cdot> ms + rs \<bullet>\<cdot> ms
                  = [a + b. (a,b)\<leftarrow>zip [r*a. a\<leftarrow>ss] rs] \<bullet>\<cdot> ms"
      using set1 lincomb_sum
      by    simp
    moreover from assms(1,2) r_rs(1,2,4) s_ss(1,2,4)
      have  "x = (r * s) \<cdot> n + ([r*a. a\<leftarrow>ss] \<bullet>\<cdot> ms + rs \<bullet>\<cdot> ms)"
      using smult_closed lincomb_closed smult_lincomb mult_closed lincomb_sum
      by    simp
    ultimately show ?thesis using lincomb_Cons by simp
  qed
  moreover have "set ((r * s) # [a + b. (a,b)\<leftarrow>zip [r*a. a\<leftarrow>ss] rs]) \<subseteq> R"
  proof-
    from r_rs(2) have "set [a + b. (a,b)\<leftarrow>zip [r*a. a\<leftarrow>ss] rs] \<subseteq> R" 
      using set1 R_scalars.zip_add_closed by fast
    with r_rs(1) s_ss(1) show ?thesis using mult_closed by simp
  qed
  ultimately show "x \<in> RSpan (n # ms)"
    using assms(1,2) RSpanI_lincomb_arb_len_coeffs[of _ "n#ms"] by fastforce
qed

end (* context RModule *)

lemmas (in scalar_mult)
  Span_Cons = R_scalar_mult.RSpan_Cons[OF R_scalar_mult, of smult]

context Module
begin

lemmas SpanD_lincomb_arb_len_coeffs       = RSpanD_lincomb_arb_len_coeffs
lemmas SpanI                              = RSpanI
lemmas SpanI_lincomb_arb_len_coeffs       = RSpanI_lincomb_arb_len_coeffs
lemmas Span_contains_Spans_Cons_right     = RSpan_contains_RSpans_Cons_right
lemmas Span_contains_spanset              = RSpan_contains_spanset
lemmas Span_contains_spanset_append_left  = RSpan_contains_spanset_append_left
lemmas Span_contains_spanset_append_right = RSpan_contains_spanset_append_right
lemmas Span_closed                        = RSpan_closed
lemmas Span_smult_closed                  = RSpan_smult_closed
lemmas Span_contains_Span_take            = RSpan_contains_RSpan_take
lemmas Span_replace_hd                    = RSpan_replace_hd
lemmas Submodule_Span                     = RSubmodule_RSpan

end (* context Module *)

subsubsection \<open>Finitely generated modules\<close>

context R_scalar_mult
begin

abbreviation "R_fingen M \<equiv> (\<exists>ms. set ms \<subseteq> M \<and> RSpan ms = M)"

text \<open>
  Similar to definition of \<open>card\<close> for finite sets, we default \<open>dim\<close> to 0 if no finite
  spanning set exists. Note that @{term "RSpan [] = 0"} implies that @{term "dim_R {0} = 0"}.
\<close>

definition dim_R :: "'m set \<Rightarrow> nat"
  where "dim_R M = (if R_fingen M then (
                LEAST n. \<exists>ms. length ms = n \<and> set ms \<subseteq> M \<and> RSpan ms = M
              ) else 0)"

lemma dim_R_nonzero :
  assumes "dim_R M > 0"
  shows   "M \<noteq> 0"
proof
  assume M: "M = 0"
  hence "dim_R M
              = (LEAST n. \<exists>ms. length ms = n \<and> set ms \<subseteq> M \<and> RSpan ms = M)"
    using dim_R_def by simp
  moreover from M have "length [] = 0 \<and> set [] \<subseteq> M \<and> RSpan [] = M" by simp
  ultimately show False using assms by simp
qed

end (* context R_scalar_mult *)


hide_const real_vector.dim
hide_const (open) Real_Vector_Spaces.dim

abbreviation (in scalar_mult) "fingen \<equiv> R_scalar_mult.R_fingen UNIV smult"
abbreviation (in scalar_mult) "dim    \<equiv> R_scalar_mult.dim_R UNIV smult"

lemmas (in Module) dim_nonzero = dim_R_nonzero

subsubsection \<open>@{term R}-linear independence\<close>

context R_scalar_mult
begin

primrec R_lin_independent :: "'m list \<Rightarrow> bool" where
  R_lin_independent_Nil: "R_lin_independent [] = True" |
  R_lin_independent_Cons:
  "R_lin_independent (m#ms) = (R_lin_independent ms
        \<and> (\<forall>r rs. (set (r#rs) \<subseteq> R \<and> (r#rs) \<bullet>\<cdot> (m#ms) = 0) \<longrightarrow> r = 0))"

lemma R_lin_independent_ConsI :
  assumes "R_lin_independent ms"
          "\<And>r rs. set (r#rs) \<subseteq> R \<Longrightarrow> (r#rs) \<bullet>\<cdot> (m#ms) = 0 \<Longrightarrow> r = 0"
  shows   "R_lin_independent (m#ms)"
  using   assms R_lin_independent_Cons
  by      fast

lemma R_lin_independent_ConsD1 :
  "R_lin_independent (m#ms) \<Longrightarrow> R_lin_independent ms"
  by simp

lemma R_lin_independent_ConsD2 :
  "\<lbrakk> R_lin_independent (m#ms); set (r#rs) \<subseteq> R; (r#rs) \<bullet>\<cdot> (m#ms) = 0 \<rbrakk> 
        \<Longrightarrow> r = 0"
  by auto

end (* context R_scalar_mult *)

context RModule
begin

lemma R_lin_independent_imp_same_scalars :
  "\<lbrakk> length rs = length ss; length rs \<le> length ms; set rs \<subseteq> R; set ss \<subseteq> R;
        set ms \<subseteq> M; R_lin_independent ms; rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms \<rbrakk> \<Longrightarrow> rs = ss"
proof (induct rs ss arbitrary: ms rule: list_induct2)
  case (Cons r rs s ss)
  from Cons(3) have "ms \<noteq> []" by auto
  from this obtain n ns where ms: "ms = n#ns"
    using neq_Nil_conv[of ms] by fast
  from Cons(4,5) have "set ([a-b. (a,b)\<leftarrow>zip (r#rs) (s#ss)]) \<subseteq> R"
    using Ring1 Ring1.list_diff_closed by fast
  hence "set ((r-s)#[a-b. (a,b)\<leftarrow>zip rs ss]) \<subseteq> R" by simp
  moreover from Cons(1,4-6,8) ms
    have  1: "((r-s)#[a-b. (a,b)\<leftarrow>zip rs ss]) \<bullet>\<cdot> (n#ns) = 0"
    using lincomb_diff_left[of "r#rs" "s#ss"]
    by    simp
  ultimately have "r - s = 0" using Cons(7) ms R_lin_independent_Cons by fast
  hence 2: "r = s" by simp
  with 1 Cons(1,4-6) ms have "rs \<bullet>\<cdot> ns = ss \<bullet>\<cdot> ns"
    using lincomb_Cons zero_smult lincomb_diff_left by simp
  with Cons(2-7) ms have "rs = ss" by simp
  with 2 show ?case by fast
qed fast

lemma R_lin_independent_obtain_unique_scalars :
  "\<lbrakk> set ms \<subseteq> M; R_lin_independent ms; n \<in> RSpan ms \<rbrakk>
        \<Longrightarrow> (\<exists>! rs. set rs \<subseteq> R \<and> length rs = length ms \<and> n = rs \<bullet>\<cdot> ms)"
  using in_RSpan_obtain_same_length_coeffs[of n ms]
        R_lin_independent_imp_same_scalars[of _ _ ms]
  by    auto

lemma R_lin_independentI_all_scalars :
  "set ms \<subseteq> M \<Longrightarrow>
        (\<forall>rs. set rs \<subseteq> R \<and> length rs = length ms \<and> rs \<bullet>\<cdot> ms = 0 \<longrightarrow> set rs \<subseteq> 0)
          \<Longrightarrow> R_lin_independent ms"
proof (induct ms)
  case (Cons m ms) show ?case
  proof (rule R_lin_independent_ConsI)
    have "\<And>rs. \<lbrakk> set rs \<subseteq> R; length rs = length ms; rs \<bullet>\<cdot> ms = 0 \<rbrakk> \<Longrightarrow> set rs \<subseteq> 0"
    proof-
      fix rs assume rs: "set rs \<subseteq> R" "length rs = length ms" "rs \<bullet>\<cdot> ms = 0"
      with Cons(2) have "set (0#rs) \<subseteq> R" "length (0#rs)
                              = length (m#ms)" "(0#rs) \<bullet>\<cdot> (m#ms) = 0"
        using R_scalars.zero_closed lincomb_Cons zero_smult by auto
      with Cons(3) have "set (0#rs) \<subseteq> 0" by fast
      thus "set rs \<subseteq> 0" by simp
    qed
    with Cons(1,2) show "R_lin_independent ms" by simp
  next
    fix r rs assume r_rs: "set (r # rs) \<subseteq> R" "(r # rs) \<bullet>\<cdot> (m # ms) = 0"
    from r_rs(1) Cons(2) obtain ss
      where ss: "set ss \<subseteq> R" "length ss = length ms" "rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms"
      using lincomb_obtain_same_length_Rcoeffs[of rs ms]
      by    auto
    with r_rs have "(r#ss) \<bullet>\<cdot> (m#ms) = 0" using lincomb_Cons by simp
    moreover from r_rs(1) ss(1) have "set (r#ss) \<subseteq> R" by simp
    moreover from ss(2) have "length (r#ss) = length (m#ms)" by simp
    ultimately have "set (r#ss) \<subseteq> 0" using Cons(3) by fast
    thus "r = 0" by simp
  qed
qed simp

lemma R_lin_independentI_concat_all_scalars :
  defines eq_len: "eq_len \<equiv> \<lambda>xs ys. length xs = length ys"
  assumes "set (concat mss) \<subseteq> M"
          "\<And>rss. set (concat rss) \<subseteq> R \<Longrightarrow> list_all2 eq_len rss mss
              \<Longrightarrow> (concat rss) \<bullet>\<cdot> (concat mss) = 0 \<Longrightarrow> (\<forall>rs \<in> set rss. set rs \<subseteq> 0)"
  shows   "R_lin_independent (concat mss)"
  using   assms(2)
proof (rule R_lin_independentI_all_scalars)
  have "\<And>rs. \<lbrakk> set rs \<subseteq> R; length rs = length (concat mss); rs \<bullet>\<cdot> concat mss = 0 \<rbrakk>
              \<Longrightarrow> set rs \<subseteq> 0"
  proof-
    fix rs
    assume rs: "set rs \<subseteq> R" "length rs = length (concat mss)" "rs \<bullet>\<cdot> concat mss = 0"
    from rs(2) eq_len obtain rss where "rs = concat rss" "list_all2 eq_len rss mss"
      using match_concat by fast
    with rs(1,3) assms(3) show "set rs \<subseteq> 0" by auto
  qed
  thus "\<forall>rs. set rs \<subseteq> R \<and> length rs = length (concat mss) \<and> rs \<bullet>\<cdot> concat mss = 0
              \<longrightarrow> set rs \<subseteq> 0"
    by auto
qed

lemma R_lin_independentD_all_scalars :
  "\<lbrakk> set rs \<subseteq> R; set ms \<subseteq> M; length rs \<le> length ms; R_lin_independent ms;
        rs \<bullet>\<cdot> ms = 0 \<rbrakk> \<Longrightarrow> set rs \<subseteq> 0"
proof (induct rs ms rule: list_induct2')
  case (4 r rs m ms)
  from 4(2,5,6) have "r = 0" by auto
  moreover with 4 have "set rs \<subseteq> 0" using lincomb_Cons zero_smult by simp
  ultimately show ?case by simp
qed auto

lemma R_lin_independentD_all_scalars_nth :
  assumes "set rs \<subseteq> R" "set ms \<subseteq> M" "R_lin_independent ms" "rs \<bullet>\<cdot> ms = 0"
          "k < min (length rs) (length ms)"
  shows   "rs!k = 0"
proof-
  from assms(1,2) obtain ss
    where ss: "set ss \<subseteq> R" "length ss = length ms"
              "take (length rs) ss = take (length ms) rs" "rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms"
    using lincomb_obtain_same_length_Rcoeffs[of rs ms]
    by    fast
  from ss(1,2,4) assms(2,3,4) have "set ss \<subseteq> 0"
    using R_lin_independentD_all_scalars by auto
  moreover from assms(5) ss(3) have "rs!k = (take (length rs) ss)!k" by simp
  moreover from assms(5) ss(2) have "k < length (take (length rs) ss)" by simp
  ultimately show ?thesis using in_set_conv_nth by force
qed

lemma R_lin_dependent_dependence_relation :
  "set ms \<subseteq> M \<Longrightarrow> \<not> R_lin_independent ms
        \<Longrightarrow> \<exists>rs. set rs \<subseteq> R \<and> set rs \<noteq> 0 \<and> length rs = length ms \<and> rs \<bullet>\<cdot> ms = 0"
proof (induct ms)
  case (Cons m ms) show ?case
  proof (cases "R_lin_independent ms")
    case True
    with Cons(3)
      have "\<not> (\<forall>r rs. (set (r#rs) \<subseteq> R \<and> (r#rs) \<bullet>\<cdot> (m#ms) = 0) \<longrightarrow> r = 0)"
      by   simp
    from this obtain r rs
      where r_rs: "set (r#rs) \<subseteq> R" "(r#rs) \<bullet>\<cdot> (m#ms) = 0" "r \<noteq> 0"
      by    fast
    from r_rs(1) Cons(2) obtain ss  
      where ss: "set ss \<subseteq> R" "length ss = length ms" "rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms"
      using lincomb_obtain_same_length_Rcoeffs[of rs ms]
      by    auto
    from ss r_rs have "set (r#ss) \<subseteq> R \<and> set (r#ss) \<noteq> 0
                            \<and> length (r#ss) = length (m#ms) \<and> (r#ss) \<bullet>\<cdot> (m#ms) = 0"
      using lincomb_Cons
      by    simp
    thus ?thesis by fast
  next
    case False
    with Cons(1,2) obtain rs  
      where rs: "set rs \<subseteq> R" "set rs \<noteq> 0" "length rs = length ms" "rs \<bullet>\<cdot> ms = 0"
      by    fastforce
    from False rs Cons(2)
      have  "set (0#rs) \<subseteq> R \<and> set (0#rs) \<noteq> 0 \<and> length (0#rs) = length (m#ms)
                  \<and> (0#rs) \<bullet>\<cdot> (m#ms) = 0"
      using Ring1.zero_closed[OF Ring1] lincomb_Cons[of 0 rs m ms]
            zero_smult[of m] empty_set_diff_single[of "set rs"]
      by    fastforce
    thus ?thesis by fast
  qed
qed simp

lemma R_lin_independent_imp_distinct :
  "set ms \<subseteq> M \<Longrightarrow> R_lin_independent ms \<Longrightarrow> distinct ms"
proof (induct ms)
  case (Cons m ms)
  have "\<And>n. n \<in> set ms \<Longrightarrow> m \<noteq> n"
  proof
    fix n assume n: "n \<in> set ms" "m = n"
    from n(1) obtain xs ys where "ms = xs @ n # ys" using split_list by fast
    with Cons(2) n(2)
      have  "(1 # replicate (length xs) 0 @ [-1]) \<bullet>\<cdot> (m # ms) = 0"
      using lincomb_Cons lincomb_append lincomb_replicate0_left lincomb_Nil neg_eq_neg1_smult
      by    simp
    with Cons(3) have "1 = 0"
      using R_scalars.zero_closed one_closed R_scalars.neg_closed by force
    thus False using one_neq_zero by fast
  qed
  with Cons show ?case by auto
qed simp

lemma R_lin_independent_imp_independent_take : 
  "set ms \<subseteq> M \<Longrightarrow> R_lin_independent ms \<Longrightarrow> R_lin_independent (take n ms)"
proof (induct ms arbitrary: n)
  case (Cons m ms) show ?case
  proof (cases n)
    case (Suc k)
    hence "take n (m#ms) = m # take k ms" by simp
    moreover have "R_lin_independent (m # take k ms)"
    proof (rule R_lin_independent_ConsI)
      from Cons show "R_lin_independent (take k ms)" by simp
    next
      fix r rs assume r_rs: "set (r#rs) \<subseteq> R" "(r#rs)\<bullet>\<cdot>(m # take k ms) = 0"
      from r_rs(1) Cons(2) obtain ss
        where ss: "set ss \<subseteq> R" "length ss = length (take k ms)"
                  "rs \<bullet>\<cdot> take k ms = ss \<bullet>\<cdot> take k ms"
        using set_take_subset[of k ms] lincomb_obtain_same_length_Rcoeffs
        by    force
      from r_rs(1) ss(1) have "set (r#ss) \<subseteq> R" by simp
      moreover from r_rs(2) ss have "(r#ss) \<bullet>\<cdot> (m#ms) = 0"
        using lincomb_Cons lincomb_Nil
              lincomb_append_right[of ss "take k ms" "drop k ms"]
        by    simp
      ultimately show "r = 0" using Cons(3) by auto
    qed
    ultimately show ?thesis by simp
  qed simp
qed simp

lemma R_lin_independent_Cons_imp_independent_RSpans :
  assumes "m \<in> M" "R_lin_independent (m#ms)"
  shows   "add_independentS [RSpan [m], RSpan ms]"
proof (rule add_independentS_doubleI)
  fix x y assume xy: "x \<in> RSpan [m]" "y \<in> RSpan ms" "x + y = 0"
  from xy(1,2) obtain r rs where r_rs: "r \<in> R" "x = r \<cdot> m" "set rs \<subseteq> R" "y = rs \<bullet>\<cdot> ms"
    using RSpan_single RSpanD_lincomb by fast
  with xy(3) have "set (r#rs) \<subseteq> R" "(r#rs) \<bullet>\<cdot> (m#ms) = 0"
    using lincomb_Cons by auto
  with assms r_rs(2) show "x = 0" using zero_smult by auto
qed

lemma hd0_imp_R_lin_dependent : "\<not> R_lin_independent (0#ms)"
  using lincomb_Cons[of 1 "[]" 0 ms] lincomb_Nil[of "[]" ms] smult_zero one_closed 
        R_lin_independent_Cons
  by    fastforce

lemma R_lin_independent_imp_hd_n0 : "R_lin_independent (m#ms) \<Longrightarrow> m \<noteq> 0"
  using hd0_imp_R_lin_dependent by fast

lemma R_lin_independent_imp_hd_independent_from_RSpan :
  assumes "m \<in> M" "set ms \<subseteq> M" "R_lin_independent (m#ms)"
  shows   "m \<notin> RSpan ms"
proof
  assume m: "m \<in> RSpan ms"
  with assms(2) have "(-1) \<cdot> m \<in> RSpan ms"
    using RSubmodule_RSpan[of ms]
          RModule.smult_closed[of R smult "RSpan ms" "-1" m]
          one_closed R_scalars.neg_closed[of 1]
    by    simp
  moreover from assms(1) have "m + (-1) \<cdot> m = 0"
    using neg_eq_neg1_smult by simp
  ultimately show False
    using RSpan_contains_spanset_single assms R_lin_independent_Cons_imp_independent_RSpans
          add_independentS_doubleD R_lin_independent_imp_hd_n0
    by    fast
qed

lemma R_lin_independent_reduce :
  assumes "n \<in> M"
  shows   "set ms \<subseteq> M \<Longrightarrow> R_lin_independent (ms @ n # ns)
                \<Longrightarrow> R_lin_independent (ms @ ns)"
proof (induct ms)
  case (Cons m ms)
  moreover have "\<And>r rs. set (r#rs) \<subseteq> R \<Longrightarrow> (r#rs) \<bullet>\<cdot> (m#ms@ns) = 0
                      \<Longrightarrow> r = 0"
  proof-
    fix r rs assume r_rs: "set (r#rs) \<subseteq> R" "(r#rs) \<bullet>\<cdot> (m # ms @ ns) = 0"
    from Cons(2) r_rs(1) obtain ss
      where ss: "set ss \<subseteq> R" "length ss = length ms" "rs \<bullet>\<cdot> ms = ss \<bullet>\<cdot> ms"
      using lincomb_obtain_same_length_Rcoeffs[of rs ms]
      by    auto
    from assms ss(2,3) r_rs(2)
      have  "(r # ss @ 0 # drop (length ms) rs) \<bullet>\<cdot> (m # ms @ n # ns) = 0"
      using lincomb_Cons
            lincomb_append_right add.assoc[of "r\<cdot>m" "rs\<bullet>\<cdot>ms" "(drop (length ms) rs)\<bullet>\<cdot>ns"]
            zero_smult lincomb_append
      by    simp
    moreover from r_rs(1) ss(1)
      have  "set (r # ss @ 0 # drop (length ms) rs) \<subseteq> R"
      using R_scalars.zero_closed set_drop_subset[of _ rs]
      by    auto
    ultimately show "r = 0"
      using Cons(3)
            R_lin_independent_ConsD2[of m _ r "ss @ 0 # drop (length ms) rs"]
      by    simp
  qed
  ultimately show "R_lin_independent ( (m#ms) @ ns)" by auto
qed simp

lemma R_lin_independent_vs_lincomb0 :
  assumes "set (ms@n#ns) \<subseteq> M" "R_lin_independent (ms @ n # ns)"
          "set (rs@s#ss) \<subseteq> R" "length rs = length ms"
          "(rs@s#ss) \<bullet>\<cdot> (ms@n#ns) = 0"
  shows   "s = 0"
proof-
  define k where "k = length rs"
  hence "(rs@s#ss)!k = s" by simp
  moreover from k_def assms(4) have "k < min (length (rs@s#ss)) (length (ms@n#ns))"
    by simp
  ultimately show ?thesis
    using assms(1,2,3,5) R_lin_independentD_all_scalars_nth[of "rs@s#ss" "ms@n#ns"]
    by    simp
qed

lemma R_lin_independent_append_imp_independent_RSpans :
  "set ms \<subseteq> M \<Longrightarrow> R_lin_independent (ms@ns)
        \<Longrightarrow> add_independentS [RSpan ms, RSpan ns]"
proof (induct ms)
  case (Cons m ms)
  show ?case
  proof (rule add_independentS_doubleI)
    fix x y assume xy: "y \<in> RSpan ns""x \<in> RSpan (m#ms)"  "x + y = 0"
    from xy(2) obtain x1 x2
      where x1_x2: "x1 \<in> RSpan [m]" "x2 \<in> RSpan ms" "x = x1 + x2"
      using RSpan_Cons set_plus_def[of "RSpan [m]"]
      by    auto
    from x1_x2(1,2) xy(1) obtain r rs ss
      where r_rs_ss: "set (r#(rs@ss)) \<subseteq> R" "length rs = length ms" "x1 = r \<cdot> m"
                     "x2 = rs \<bullet>\<cdot> ms" "y = ss \<bullet>\<cdot> ns"
      using RSpan_single in_RSpan_obtain_same_length_coeffs[of x2 ms]
            RSpanD_lincomb[of ns]
      by    auto
    have x1_0: "x1 = 0"
    proof-
      from xy(3) x1_x2(3) r_rs_ss(2-5) have "(r#(rs@ss)) \<bullet>\<cdot> (m#(ms@ns)) = 0"
        using lincomb_append lincomb_Cons by (simp add: algebra_simps)
      with r_rs_ss(1,3) Cons(2,3) show ?thesis
        using R_lin_independent_ConsD2[of m "ms@ns" r "rs@ss"] zero_smult by simp
    qed
    moreover have "x2 = 0"
    proof-
      from x1_0 xy(3) x1_x2(3) have "x2 + y = 0" by simp
      with xy(1) x1_x2(2) Cons show ?thesis
        using add_independentS_doubleD by simp
    qed
    ultimately show "x = 0" using x1_x2(3) by simp
  qed
qed simp

end (* context RModule *)

subsubsection \<open>Linear independence over \<open>UNIV\<close>\<close>

context scalar_mult
begin

abbreviation "lin_independent ms
                    \<equiv> R_scalar_mult.R_lin_independent UNIV smult ms"

lemmas lin_independent_ConsI
              = R_scalar_mult.R_lin_independent_ConsI [OF R_scalar_mult, of smult]
lemmas lin_independent_ConsD1
              = R_scalar_mult.R_lin_independent_ConsD1[OF R_scalar_mult, of smult]

end (* context scalar_mult *)

context Module
begin

lemmas lin_independent_imp_independent_take = R_lin_independent_imp_independent_take
lemmas lin_independent_reduce               = R_lin_independent_reduce
lemmas lin_independent_vs_lincomb0          = R_lin_independent_vs_lincomb0
lemmas lin_dependent_dependence_relation    = R_lin_dependent_dependence_relation
lemmas lin_independent_imp_distinct         = R_lin_independent_imp_distinct

lemmas lin_independent_imp_hd_independent_from_Span
                                                = R_lin_independent_imp_hd_independent_from_RSpan
lemmas lin_independent_append_imp_independent_Spans
                                                = R_lin_independent_append_imp_independent_RSpans

end (* context Module *)

subsubsection \<open>Rank\<close>

context R_scalar_mult
begin

definition R_finrank :: "'m set \<Rightarrow> bool"
  where "R_finrank M = (\<exists>n. \<forall>ms. set ms \<subseteq> M
              \<and> R_lin_independent ms \<longrightarrow> length ms \<le> n)"

lemma R_finrankI :
  "(\<And>ms. set ms \<subseteq> M \<Longrightarrow> R_lin_independent ms \<Longrightarrow> length ms \<le> n) 
        \<Longrightarrow> R_finrank M"
  unfolding R_finrank_def by blast

lemma R_finrankD :
  "R_finrank M \<Longrightarrow> \<exists>n. \<forall>ms. set ms \<subseteq> M \<and> R_lin_independent ms 
        \<longrightarrow> length ms \<le> n"
  unfolding R_finrank_def by fast

lemma submodule_R_finrank : "R_finrank M \<Longrightarrow> N \<subseteq> M \<Longrightarrow> R_finrank N"
  unfolding R_finrank_def by blast

end (* context R_scalar_mult *)

context scalar_mult
begin

abbreviation finrank :: "'m set \<Rightarrow> bool"
  where "finrank \<equiv> R_scalar_mult.R_finrank UNIV smult"

lemmas finrankI = R_scalar_mult.R_finrankI[OF R_scalar_mult, of _ smult]
lemmas finrankD = R_scalar_mult.R_finrankD[OF R_scalar_mult, of smult]
lemmas submodule_finrank
              = R_scalar_mult.submodule_R_finrank [OF R_scalar_mult, of smult]

end (* context scalar_mult *)


subsection \<open>Module homomorphisms\<close>

subsubsection \<open>Locales\<close>

locale RModuleHom = Domain?: RModule R smult M
+ Codomain?: scalar_mult smult'
+ GroupHom?: GroupHom M T
  for R      :: "'r::ring_1 set"
  and smult  :: "'r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and M      :: "'m set"
  and smult' :: "'r \<Rightarrow> 'n::ab_group_add \<Rightarrow> 'n" (infixr "\<star>" 70)
  and T      :: "'m \<Rightarrow> 'n"
+ assumes R_map: "\<And>r m. r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> T (r \<cdot> m) = r \<star> T m"

abbreviation (in RModuleHom) lincomb' :: "'r list \<Rightarrow> 'n list \<Rightarrow> 'n" (infix "\<bullet>\<star>" 70)
  where "lincomb' \<equiv> Codomain.lincomb"

lemma (in RModule) RModuleHomI :
  assumes "GroupHom M T"
          "\<And>r m. r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> T (r \<cdot> m) = smult' r (T m)"
  shows   "RModuleHom R smult M smult' T"
  by      (
            rule RModuleHom.intro, rule RModule_axioms, rule assms(1), unfold_locales,
            rule assms(2)
          )

locale RModuleEnd = RModuleHom R smult M smult T
  for R     :: "'r::ring_1 set"
  and smult :: "'r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and M     :: "'m set"
  and T     :: "'m \<Rightarrow> 'm"
+ assumes endomorph: "ImG \<subseteq> M"

locale ModuleHom = RModuleHom UNIV smult M smult' T
  for smult  :: "'r::ring_1 \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and M      :: "'m set"
  and smult' :: "'r \<Rightarrow> 'n::ab_group_add \<Rightarrow> 'n" (infixr "\<star>" 70)
  and T      :: "'m \<Rightarrow> 'n"

lemmas (in ModuleHom) hom = hom

lemmas (in Module) ModuleHomI = RModuleHomI[THEN ModuleHom.intro]

locale ModuleEnd = ModuleHom smult M smult T
  for smult :: "'r::ring_1 \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and M     :: "'m set" and T :: "'m \<Rightarrow> 'm"
+ assumes endomorph: "ImG \<subseteq> M"

locale RModuleIso = RModuleHom R smult M smult' T
  for   R      :: "'r::ring_1 set"
  and   smult  :: "'r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  and   M      :: "'m set"
  and   smult' :: "'r \<Rightarrow> 'n::ab_group_add \<Rightarrow> 'n" (infixr "\<star>" 70)
  and   T      :: "'m \<Rightarrow> 'n"
+ fixes N      :: "'n set"
  assumes bijective: "bij_betw T M N"

lemma (in RModule) RModuleIsoI :
  assumes "GroupIso M T N"
          "\<And>r m. r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> T (r \<cdot> m) = smult' r (T m)"
  shows   "RModuleIso R smult M smult' T N"
proof (rule RModuleIso.intro)
  from assms show "RModuleHom R (\<cdot>) M smult' T"
    using GroupIso.axioms(1) RModuleHomI by fastforce
  from assms(1) show "RModuleIso_axioms M T N"
    using GroupIso.bijective by unfold_locales
qed

subsubsection \<open>Basic facts\<close>

lemma (in RModule) trivial_RModuleHom :
  "\<forall>r\<in>R. smult' r 0 = 0 \<Longrightarrow> RModuleHom R smult M smult' 0"
  using trivial_GroupHom RModuleHomI by fastforce

lemma (in RModule) RModHom_idhom : "RModuleHom R smult M smult (id\<down>M)"
  using RModule_axioms GroupHom_idhom
proof (rule RModuleHom.intro)
  show "RModuleHom_axioms R (\<cdot>) M (\<cdot>) (id \<down> M)"
    using smult_closed by unfold_locales simp
qed

context RModuleHom
begin

lemmas additive        = hom
lemmas supp            = supp
lemmas im_zero         = im_zero
lemmas im_diff         = im_diff
lemmas Ker_Im_iff      = Ker_Im_iff
lemmas Ker0_imp_inj_on = Ker0_imp_inj_on

lemma GroupHom : "GroupHom M T" ..

lemma codomain_smult_zero : "r \<in> R \<Longrightarrow> r \<star> 0 = 0"
  using im_zero smult_zero zero_closed R_map[of r 0] by simp

lemma RSubmodule_Ker : "Domain.RSubmodule Ker"
proof (rule Domain.RSubmoduleI, rule conjI, rule Group_Ker)
  fix r m assume r: "r \<in> R" and m: "m \<in> Ker"
  thus "r \<cdot> m \<in> Ker"
    using R_map[of r m] kerD[of m T] codomain_smult_zero kerI Domain.smult_closed
    by    simp
qed fast

lemma RModule_Im : "RModule R smult' ImG"
  using Ring1 Group_Im
proof (rule RModuleI, unfold_locales)
  show "\<And>n. n \<in> T ` M \<Longrightarrow> 1 \<star> n = n" using one_closed R_map[of 1] by auto
next
  fix r s m n assume r: "r \<in> R" and s: "s \<in> R" and m: "m \<in> T ` M"
    and n: "n \<in> T ` M"
  from m n obtain m' n'
    where m': "m' \<in> M" "m = T m'" and n': "n' \<in> M" "n = T n'"
    by    fast
  from m' r R_map have "r \<star> m = T (r \<cdot> m')" by simp
  with r m'(1) show "r \<star> m \<in> T ` M" using smult_closed by fast
  from r m' n' show "r \<star> (m + n) = r \<star> m + r \<star> n"
    using hom add_closed R_map[of r "m'+n'"] smult_closed R_map[of r] by simp
  from r s m' show "(r + s) \<star> m = r \<star> m + s \<star> m"
    using R_scalars.add_closed R_map[of "r+s"] smult_closed hom R_map by simp
  from r s m' show "r \<star> s \<star> m = (r * s) \<star> m"
    using smult_closed R_map[of s] R_map[of r "s \<cdot> m'"] mult_closed R_map[of "r*s"]
    by    simp
qed

lemma im_submodule :
  assumes "RSubmodule N"
  shows   "RModule.RSubmodule R smult' ImG (T ` N)"
proof (rule RModule.RSubmoduleI, rule RModule_Im)
  from assms show "Group.Subgroup (T ` M) (T ` N)"
    using im_subgroup Subgroup_RSubmodule by fast
  from assms R_map  show "\<And>r n. r \<in> R \<Longrightarrow> n \<in> T ` N \<Longrightarrow> r \<star> n \<in> T ` N"
    using RModule.smult_closed by force
qed

lemma RModHom_composite_left :
  assumes "T ` M \<subseteq> N" "RModuleHom R smult' N smult'' S"
  shows   "RModuleHom R smult M smult'' (S \<circ> T)"
proof (rule RModule.RModuleHomI, rule RModule_axioms)
  from assms(1) show "GroupHom M (S \<circ> T)"
    using RModuleHom.GroupHom[OF assms(2)] GroupHom_composite_left
    by    auto
  from assms(1)
    show  "\<And>r m. r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> (S \<circ> T) (r \<cdot> m) = smult'' r ((S \<circ> T) m)"
    using R_map RModuleHom.R_map[OF assms(2)]
    by    auto
qed

lemma RModuleHom_restrict0_submodule :
  assumes "RSubmodule N"
  shows   "RModuleHom R smult N smult' (T \<down> N)"
proof (rule RModuleHom.intro)
  from assms show "RModule R (\<cdot>) N" by fast
  from assms show "GroupHom N (T \<down> N)"
    using RModule.Group GroupHom_restrict0_subgroup by fast
  show "RModuleHom_axioms R (\<cdot>) N (\<star>) (T \<down> N)"
  proof
    fix r m assume "r \<in> R" "m \<in> N"
    with assms show "(T \<down> N) (r \<cdot> m) = r \<star> (T \<down> N) m"
      using RModule.smult_closed R_map by fastforce
  qed
qed

lemma distrib_lincomb :
  "set rs \<subseteq> R \<Longrightarrow> set ms \<subseteq> M \<Longrightarrow> T (rs \<bullet>\<cdot> ms) = rs \<bullet>\<star> map T ms"
  using Domain.lincomb_Nil im_zero Codomain.lincomb_Nil R_map Domain.lincomb_Cons
        Domain.smult_closed Domain.lincomb_closed additive Codomain.lincomb_Cons
  by    (induct rs ms rule: list_induct2') auto

lemma same_image_on_RSpanset_imp_same_hom :
  assumes "RModuleHom R smult M smult' S" "set ms \<subseteq> M"
          "M = Domain.R_scalars.RSpan ms" "\<forall>m\<in>set ms. S m = T m"
  shows   "S = T"
proof
  fix m show "S m = T m"
  proof (cases "m \<in> M")
    case True
    with assms(2,3) obtain rs where rs: "set rs \<subseteq> R" "m = rs \<bullet>\<cdot> ms"
      using Domain.RSpanD_lincomb_arb_len_coeffs by fast
    from rs(1) assms(2) have "S (rs \<bullet>\<cdot> ms) = rs \<bullet>\<star> (map S ms)"
      using RModuleHom.distrib_lincomb[OF assms(1)] by simp
    moreover from rs(1) assms(2) have "T (rs \<bullet>\<cdot> ms) = rs \<bullet>\<star> (map T ms)"
      using distrib_lincomb by simp
    ultimately show ?thesis using assms(4) map_ext[of ms S T] rs(2) by auto
  next
    case False with assms(1) supp show ?thesis
      using RModuleHom.supp suppI_contra[of _ S] suppI_contra[of _ T] by fastforce
  qed
qed

end (* context RModuleHom *)

lemma RSubmodule_eigenspace :
  fixes   smult :: "'r::ring_1 \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm" (infixr "\<cdot>" 70)
  assumes RModHom: "RModuleHom R smult M smult T"
  and     r: "r \<in> R" "\<And>s m. s \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> s \<cdot> r \<cdot> m = r \<cdot> s \<cdot> m"
  defines E: "E \<equiv> {m \<in> M. T m = r \<cdot> m}"
  shows   "RModule.RSubmodule R smult M E"
proof (rule RModule.RSubmoduleI)
  from RModHom show rmod: "RModule R smult M"
    using RModuleHom.axioms(1) by fast
  have "Group E"
  proof
    from r(1) E show "E \<noteq> {}"
      using RModule.zero_closed[OF rmod] RModuleHom.im_zero[OF RModHom]
            RModule.smult_zero[OF rmod]
      by    auto
  next
    fix m n assume "m \<in> E" "n \<in> E"
    with r(1) E show "m - n \<in> E"
      using RModule.diff_closed[OF rmod] RModuleHom.im_diff[OF RModHom] 
            RModule.smult_distrib_left_diff[OF rmod]
      by    simp
  qed
  with E show "Group.Subgroup M E" by fast
  show "\<And>s m. s \<in> R \<Longrightarrow> m \<in> E \<Longrightarrow> s \<cdot> m \<in> E"
  proof-
    fix s m assume "s \<in> R" "m \<in> E"
    with E r RModuleHom.R_map[OF RModHom] show "s \<cdot> m \<in> E"
      using RModule.smult_closed[OF rmod] by simp
  qed
qed

subsubsection \<open>Basic facts about endomorphisms\<close>

lemma (in RModule) Rmap_endomorph_is_RModuleEnd :
  assumes grpend: "GroupEnd M T"
  and     Rmap  : "\<And>r m. r \<in> R \<Longrightarrow> m \<in> M \<Longrightarrow> T (r \<cdot> m) = r \<cdot> (T m)"
  shows   "RModuleEnd R smult M T"
proof (rule RModuleEnd.intro, rule RModuleHomI)
  from grpend show "GroupHom M T" using GroupEnd.axioms(1) by fast
  from grpend show "RModuleEnd_axioms M T"
    using GroupEnd.endomorph by unfold_locales
qed (rule Rmap)

lemma (in RModuleEnd) GroupEnd : "GroupEnd M T"
proof (rule GroupEnd.intro)
  from endomorph show "GroupEnd_axioms M T" by unfold_locales
qed (unfold_locales)

lemmas (in RModuleEnd) proj_decomp    = GroupEnd.proj_decomp[OF GroupEnd]

lemma (in ModuleEnd) RModuleEnd : "RModuleEnd UNIV smult M T"
  using endomorph RModuleEnd.intro by unfold_locales

lemmas (in ModuleEnd) GroupEnd = RModuleEnd.GroupEnd[OF RModuleEnd]

lemma RModuleEnd_over_UNIV_is_ModuleEnd :
  "RModuleEnd UNIV rsmult M T \<Longrightarrow> ModuleEnd rsmult M T"
proof (rule ModuleEnd.intro, rule ModuleHom.intro)
  assume endo: "RModuleEnd UNIV rsmult M T"
  thus "RModuleHom UNIV rsmult M rsmult T"
    using RModuleEnd.axioms(1) by fast
  from endo show "ModuleEnd_axioms M T"
    using RModuleEnd.endomorph by unfold_locales
qed

subsubsection \<open>Basic facts about isomorphisms\<close>

context RModuleIso
begin

abbreviation "invT \<equiv> (the_inv_into M T) \<down> N"

lemma GroupIso : "GroupIso M T N"
proof (rule GroupIso.intro)
  show "GroupHom M T" ..
  from bijective show "GroupIso_axioms M T N" by unfold_locales
qed

lemmas ImG           = GroupIso.ImG         [OF GroupIso]
lemmas GroupHom_inv = GroupIso.inv        [OF GroupIso]
lemmas invT_into    = GroupIso.invT_into  [OF GroupIso]
lemmas T_invT       = GroupIso.T_invT     [OF GroupIso]
lemmas invT_eq      = GroupIso.invT_eq    [OF GroupIso]

lemma RModuleN : "RModule R smult' N" using RModule_Im ImG by fast

lemma inv : "RModuleIso R smult' N smult invT M"
  using RModuleN GroupHom_inv
proof (rule RModule.RModuleIsoI)
  fix r n assume rn: "r \<in> R" "n \<in> N"
  thus "invT (r \<star> n) = r \<cdot> invT n"
    using invT_into smult_closed R_map T_invT invT_eq by simp
qed

end (* context RModuleIso *)


subsection \<open>Inner direct sums of RModules\<close>

lemma (in RModule) RModule_inner_dirsum_el_decomp_Rsmult :
  assumes "\<forall>N\<in>set Ns. RSubmodule N" "add_independentS Ns" "r \<in> R"
          "x \<in> (\<Oplus>N\<leftarrow>Ns. N)"
  shows   "(\<Oplus>Ns\<leftarrow>(r \<cdot> x)) = [r \<cdot> m. m\<leftarrow>(\<Oplus>Ns\<leftarrow>x)]"
proof-
  define xs where "xs = (\<Oplus>Ns\<leftarrow>x)"
  with assms have x: "xs \<in> listset Ns" "x = sum_list xs"
    using RModule.AbGroup[of R] AbGroup_inner_dirsum_el_decompI[of Ns x]
    by    auto
  from assms(1,2,4) xs_def have xs_M: "set xs \<subseteq> M"
    using Subgroup_RSubmodule
          AbGroup.abSubgroup_inner_dirsum_el_decomp_set[OF AbGroup]
    by    fast
  from assms(1,3) x(1) have "[r \<cdot> m. m\<leftarrow>xs] \<in> listset Ns"
    using listset_RModule_Rsmult_closed by fast
  moreover from x assms(3) xs_M have "r \<cdot> x = sum_list [r \<cdot> m. m\<leftarrow>xs]"
    using smult_sum_list_distrib by fast
  moreover from assms(1,3,4) have "r \<cdot> x \<in> (\<Oplus>M\<leftarrow>Ns. M)" 
    using RModule_inner_dirsum RModule.smult_closed by fast
  ultimately show "(\<Oplus>Ns\<leftarrow>(r \<cdot> x)) = [r \<cdot> m. m\<leftarrow>xs]"
    using assms(1,2) RModule.AbGroup AbGroup_inner_dirsum_el_decomp_eq
     by   fast
qed

lemma (in RModule) RModuleEnd_inner_dirsum_el_decomp_nth :
  assumes "\<forall>N \<in> set Ns. RSubmodule N" "add_independentS Ns" "n < length Ns"
  shows   "RModuleEnd R smult (\<Oplus>N\<leftarrow>Ns. N) (\<Oplus>Ns\<down>n)"
proof (rule RModule.Rmap_endomorph_is_RModuleEnd)
  from assms(1) show "RModule R smult (\<Oplus>N\<leftarrow>Ns. N)"
    using RSubmodule_inner_dirsum by fast
  from assms show "GroupEnd (\<Oplus>N\<leftarrow>Ns. N) \<Oplus>Ns\<down>n"
    using RModule.AbGroup GroupEnd_inner_dirsum_el_decomp_nth[of Ns] by fast
  show "\<And>r m. r \<in> R \<Longrightarrow> m \<in> (\<Oplus>N\<leftarrow>Ns. N)
              \<Longrightarrow> (\<Oplus>Ns\<down>n) (r \<cdot> m) = r \<cdot> ((\<Oplus>Ns\<down>n) m)"
  proof-
    fix r m assume "r \<in> R" "m \<in> (\<Oplus>N\<leftarrow>Ns. N)"
    moreover with assms(1) have "r \<cdot> m \<in> (\<Oplus>M\<leftarrow>Ns. M)" 
      using RModule_inner_dirsum RModule.smult_closed by fast
    ultimately show "(\<Oplus>Ns\<down>n) (r \<cdot> m) = r \<cdot> (\<Oplus>Ns\<down>n) m"
      using assms RModule.AbGroup[of R smult]
            AbGroup_length_inner_dirsum_el_decomp[of Ns]
            RModule_inner_dirsum_el_decomp_Rsmult
      by    simp
  qed
qed




section \<open>Vector Spaces\<close>


subsection \<open>Locales and basic facts\<close>

text \<open>Here we don't care about being able to switch scalars.\<close>

locale fscalar_mult = scalar_mult smult
  for smult :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)

abbreviation (in fscalar_mult) "findim \<equiv> fingen"

locale VectorSpace = Module smult V
  for smult :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and V     :: "'v set"

lemmas VectorSpaceI = ModuleI[THEN VectorSpace.intro]

sublocale VectorSpace < fscalar_mult proof- qed

locale FinDimVectorSpace = VectorSpace
+ assumes findim: "findim V"

lemma (in VectorSpace) FinDimVectorSpaceI :
  "findim V \<Longrightarrow> FinDimVectorSpace (\<cdot>) V"
  by unfold_locales fast

context VectorSpace
begin

abbreviation Subspace :: "'v set \<Rightarrow> bool" where "Subspace \<equiv> Submodule"

lemma SubspaceD1 : "Subspace U \<Longrightarrow> VectorSpace smult U"
  using VectorSpace.intro Module.intro by fast

lemmas AbGroup                           = AbGroup
lemmas add_closed                        = add_closed
lemmas smult_closed                      = smult_closed
lemmas one_smult                         = one_smult
lemmas smult_assoc                       = smult_assoc
lemmas smult_distrib_left                = smult_distrib_left
lemmas smult_distrib_right               = smult_distrib_right
lemmas zero_closed                       = zero_closed
lemmas zero_smult                        = zero_smult
lemmas smult_zero                        = smult_zero
lemmas smult_lincomb                     = smult_lincomb
lemmas smult_distrib_left_diff           = smult_distrib_left_diff
lemmas smult_sum_distrib              = smult_sum_distrib
lemmas sum_smult_distrib              = sum_smult_distrib
lemmas lincomb_sum                       = lincomb_sum
lemmas lincomb_closed                    = lincomb_closed
lemmas lincomb_concat                    = lincomb_concat
lemmas lincomb_replicate0_left           = lincomb_replicate0_left
lemmas delta_scalars_lincomb_eq_nth      = delta_scalars_lincomb_eq_nth
lemmas SpanI                             = SpanI
lemmas Span_closed                       = Span_closed
lemmas SpanD_lincomb_arb_len_coeffs      = SpanD_lincomb_arb_len_coeffs
lemmas SpanI_lincomb_arb_len_coeffs      = SpanI_lincomb_arb_len_coeffs
lemmas in_Span_obtain_same_length_coeffs = in_Span_obtain_same_length_coeffs
lemmas SubspaceI                         = SubmoduleI
lemmas subspace_finrank                  = submodule_finrank

lemma cancel_scalar: "\<lbrakk> a \<noteq> 0; u \<in> V; v \<in> V; a \<cdot> u = a \<cdot> v \<rbrakk> \<Longrightarrow> u = v"
  using smult_assoc[of "1/a" a u] by simp

end (* context VectorSpace *)


subsection \<open>Linear algebra in vector spaces\<close>

subsubsection \<open>Linear independence and spanning\<close>

context VectorSpace
begin

lemmas Subspace_Span                         = Submodule_Span
lemmas lin_independent_Nil                   = R_lin_independent_Nil
lemmas lin_independentI_concat_all_scalars   = R_lin_independentI_concat_all_scalars
lemmas lin_independentD_all_scalars          = R_lin_independentD_all_scalars
lemmas lin_independent_obtain_unique_scalars = R_lin_independent_obtain_unique_scalars

lemma lincomb_Cons_0_imp_in_Span :
  "\<lbrakk> v \<in> V; set vs \<subseteq> V; a \<noteq> 0; (a#as) \<bullet>\<cdot> (v#vs) = 0 \<rbrakk> \<Longrightarrow> v \<in> Span vs"
  using lincomb_Cons eq_neg_iff_add_eq_0[of "a \<cdot> v" "as \<bullet>\<cdot> vs"]
        neg_lincomb smult_assoc[of "1/a" a v] smult_lincomb SpanD_lincomb_arb_len_coeffs
  by    auto

lemma lin_independent_Cons_conditions :  
  "\<lbrakk> v \<in> V; set vs \<subseteq> V; v \<notin> Span vs; lin_independent vs \<rbrakk>
        \<Longrightarrow> lin_independent (v#vs)"
  using lincomb_Cons_0_imp_in_Span lin_independent_ConsI by fast

lemma coeff_n0_imp_in_Span_others :
  assumes "v \<in> V" "set us \<subseteq> V" "set vs \<subseteq> V" "b \<noteq> 0" "length as = length us"
          "w = (as @ b # bs) \<bullet>\<cdot> (us @ v # vs)"
  shows   "v \<in> Span (w # us @ vs)"
proof-
  define x where "x = (1 # [- c. c\<leftarrow>as@bs]) \<bullet>\<cdot> (w # us @ vs)"
  from assms(1,4-6) have "v = (1/b) \<cdot> (w + - ( (as@bs) \<bullet>\<cdot> (us@vs) ))"
    using lincomb_append lincomb_Cons by simp
  moreover from assms(1,2,3,6) have w: "w \<in> V" using lincomb_closed by simp
  ultimately have "v = (1/b) \<cdot> x"
    using x_def assms(2,3) neg_lincomb[of _ "us@vs"] lincomb_Cons[of 1 _ w] by simp
  with x_def w assms(2,3) show ?thesis
    using SpanD_lincomb_arb_len_coeffs[of "w # us @ vs"]
          Span_smult_closed[of "1/b" "w # us @ vs" x]
    by    auto
qed

lemma lin_independent_replace1_by_lincomb :
  assumes "set us \<subseteq> V" "v \<in> V" "set vs \<subseteq> V" "lin_independent (us @ v # vs)"
          "length as = length us" "b \<noteq> 0"
  shows   "lin_independent ( ((as @ b # bs) \<bullet>\<cdot> (us @ v # vs)) # us @ vs )"
proof-
  define w where "w = (as @ b # bs) \<bullet>\<cdot> (us @ v # vs)"
  from assms(1,2,4) have "lin_independent (us @ vs)"
    using lin_independent_reduce by fast
  hence "lin_independent (w # us @ vs)"
  proof (rule lin_independent_ConsI)
    fix c cs assume A: "(c#cs) \<bullet>\<cdot> (w # us @ vs) = 0"
    from assms(1,3) obtain ds es fs
      where dsesfs: "length ds = length vs" "bs \<bullet>\<cdot> vs = ds \<bullet>\<cdot> vs"
                    "length es = length vs" "(drop (length us) cs) \<bullet>\<cdot> vs = es \<bullet>\<cdot> vs"
                    "length fs = length us" "cs \<bullet>\<cdot> us = fs \<bullet>\<cdot> us"
      using lincomb_obtain_same_length_coeffs[of bs vs]
            lincomb_obtain_same_length_coeffs[of "drop (length us) cs" vs]
            lincomb_obtain_same_length_coeffs[of cs us]
      by    auto
    define xs ys
      where "xs = [x+y. (x,y)\<leftarrow>zip [c*a. a\<leftarrow>as] fs]"
        and "ys = [x+y. (x,y)\<leftarrow>zip es [c*d. d\<leftarrow>ds]]"
    with assms(5) dsesfs(5) have len_xs: "length xs = length us"
      using length_concat_map_split_zip[of _ "[c*a. a\<leftarrow>as]" fs] by simp
    from A w_def assms(1-3,5) dsesfs(2,4,6)
      have "0 = c \<cdot> as \<bullet>\<cdot> us + fs \<bullet>\<cdot> us + (c * b) \<cdot> v + es \<bullet>\<cdot> vs + c \<cdot> ds \<bullet>\<cdot> vs"
      using lincomb_Cons lincomb_append_right lincomb_append add_closed smult_closed
            lincomb_closed
      by    (simp add: algebra_simps)
    also from assms(1,3,5) dsesfs(1,3,5) xs_def ys_def len_xs
      have "\<dots> = (xs @ (c * b) # ys) \<bullet>\<cdot> (us @ v # vs)"
      using smult_lincomb lincomb_sum lincomb_Cons lincomb_append by simp
    finally have "(xs @ (c * b) # ys) \<bullet>\<cdot> (us @ v # vs) = 0" by simp
    with assms(1-3,4,6) len_xs show "c = 0"
      using lin_independent_vs_lincomb0 by fastforce
  qed
  with w_def show ?thesis by fast
qed

lemma build_lin_independent_seq :
  assumes us_V: "set us \<subseteq> V"
  and     indep_us: "lin_independent us"
  shows   "\<exists>ws. set ws \<subseteq> V \<and> lin_independent (ws @ us) \<and> (Span (ws @ us) = V
                \<or> length ws = n)"
proof (induct n)
  case 0 from indep_us show ?case by force
next
  case (Suc m)
  from this obtain ws 
    where ws: "set ws \<subseteq> V" "lin_independent (ws @ us)"
              "Span (ws@us) = V \<or> length ws = m"
    by    auto
  show ?case
  proof (cases "V = Span (ws@us)")
    case True with ws show ?thesis by fast
  next
    case False
    moreover from ws(1) us_V have ws_us_V: "set (ws @ us) \<subseteq> V" by simp
    ultimately have "Span (ws@us) \<subset> V" using Span_closed by fast
    from this obtain w where w: "w \<in> V" "w \<notin> Span (ws@us)" by fast
    define vs where "vs = w # ws"
    with w ws_us_V ws(2,3)
      have  "set (vs @ us) \<subseteq> V" "lin_independent (vs @ us)" "length vs = Suc m"
      using lin_independent_Cons_conditions[of w "ws@us"]
      by    auto
    thus ?thesis by auto
  qed
qed

end (* context VectorSpace *)

subsubsection \<open>Basis for a vector space: \<open>basis_for\<close>\<close>

abbreviation (in fscalar_mult) basis_for :: "'v set \<Rightarrow> 'v list \<Rightarrow> bool"
  where "basis_for V vs \<equiv> (set vs \<subseteq> V \<and> V = Span vs \<and> lin_independent vs)"

context VectorSpace
begin

lemma spanset_contains_basis :
  "set vs \<subseteq> V \<Longrightarrow> \<exists>us. set us \<subseteq> set vs \<and> basis_for (Span vs) us"
proof (induct vs)
  case Nil show ?case using lin_independent_Nil by simp
next
  case (Cons v vs)
  from this obtain ws where ws: "set ws \<subseteq> set vs" "basis_for (Span vs) ws" by auto
  show ?case
  proof (cases "v \<in> Span vs")
    case True
    with Cons(2) ws(2) have "basis_for (Span (v#vs)) ws"
      using spanset_reduce_Cons by force
    with ws(1) show ?thesis by auto
  next
    case False
    from Cons(2) ws
      have  "set (v#ws) \<subseteq> set (v#vs)" "set (v#ws) \<subseteq> Span (v#vs)"
            "Span (v#vs) = Span (v#ws)"
      using Span_contains_spanset[of "v#vs"]
            Span_contains_Spans_Cons_right[of v vs] Span_Cons
      by    auto
    moreover have "lin_independent (v#ws)"
    proof (rule lin_independent_Cons_conditions)
      from Cons(2) ws(1) show "v \<in> V" "set ws \<subseteq> V" by auto
      from ws(2) False show "v \<notin> Span ws" "lin_independent ws" by auto
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma basis_for_Span_ex : "set vs \<subseteq> V \<Longrightarrow> \<exists>us. basis_for (Span vs) us"
  using spanset_contains_basis by fastforce

lemma replace_basis_one_step :
  assumes closed: "set vs \<subseteq> V" "set us \<subseteq> V" and indep: "lin_independent (us@vs)"
  and     new_w: "w \<in> Span (us@vs) - Span us"
  shows   "\<exists>xs y ys. vs = xs @ y # ys
                \<and> basis_for (Span (us@vs)) (w # us @ xs @ ys)"
proof-
  from new_w obtain u v where uv: "u \<in> Span us" "v \<in> Span vs" "w = u + v"
    using Span_append set_plus_def[of "Span us"] by auto
  from uv(1,3) new_w have v_n0: "v \<noteq> 0" by auto
  from uv(1,2) obtain as bs
    where as_bs: "length as = length us" "u = as \<bullet>\<cdot> us" "length bs = length vs"
                 "v = bs \<bullet>\<cdot> vs"
    using in_Span_obtain_same_length_coeffs
    by    blast
  from v_n0 as_bs(4) closed(1) obtain b where b: "b \<in> set bs" "b \<noteq> 0"
    using lincomb_0coeffs[of vs] by auto
  from b(1) obtain cs ds where cs_ds: "bs = cs @ b # ds" using split_list by fast
  define n where "n = length cs"
  define fvs where "fvs = take n vs"
  define y where "y = vs!n"
  define bvs where "bvs = drop (Suc n) vs"
  define ufvs where "ufvs = us @ fvs"
  define acs where "acs = as @ cs"
  from as_bs(1,3) cs_ds n_def acs_def ufvs_def fvs_def
    have n_len_vs: "n < length vs" and len_acs: "length acs = length ufvs"
    by   auto
  from n_len_vs fvs_def y_def bvs_def have vs_decomp: "vs = fvs @ y # bvs"
    using id_take_nth_drop by simp
  with uv(3) as_bs(1,2,4) cs_ds acs_def ufvs_def
    have  w_decomp: "w = (acs @ b # ds) \<bullet>\<cdot> (ufvs @ y # bvs)"
    using lincomb_append
    by    simp
  from closed(1) vs_decomp
    have y_V: "y \<in> V" and fvs_V: "set fvs \<subseteq> V" and bvs_V: "set bvs \<subseteq> V"
    by   auto
  from ufvs_def fvs_V closed(2) have ufvs_V: "set ufvs \<subseteq> V" by simp
  from w_decomp ufvs_V y_V bvs_V have w_V: "w \<in> V"
    using lincomb_closed by simp
  have "Span (us@vs) = Span (w # ufvs @ bvs)"
  proof
    from vs_decomp ufvs_def have 1: "Span (us@vs) = Span (y # ufvs @ bvs)"
      using Span_append Span_Cons[of y bvs] Span_Cons[of y ufvs]
            Span_append[of "y#ufvs" bvs]
      by    (simp add: algebra_simps)
    with new_w y_V ufvs_V bvs_V show "Span (w # ufvs @ bvs) \<subseteq> Span (us@vs)"
      using Span_replace_hd by simp
    from len_acs w_decomp y_V ufvs_V bvs_V have "y \<in> Span (w # ufvs @ bvs)"
      using b(2) coeff_n0_imp_in_Span_others by simp
    with w_V ufvs_V bvs_V have "Span (y # ufvs @ bvs) \<subseteq> Span (w # ufvs @ bvs)"
      using Span_replace_hd by simp
    with 1 show "Span (us@vs) \<subseteq> Span (w # ufvs @ bvs)" by fast
  qed
  moreover from ufvs_V y_V bvs_V ufvs_def indep vs_decomp w_decomp len_acs b(2)
    have  "lin_independent (w # ufvs @ bvs)"
    using lin_independent_replace1_by_lincomb[of ufvs y bvs acs b ds]
    by    simp
  moreover have "set (w # (us@fvs) @ bvs) \<subseteq> Span (us@vs)"
  proof-
    from new_w have "w \<in> Span (us@vs)" by fast
    moreover from closed have "set us \<subseteq> Span (us@vs)"
      using Span_contains_spanset_append_left by fast
    moreover from closed fvs_def have "set fvs \<subseteq> Span (us@vs)"
      using Span_contains_spanset_append_right[of us] set_take_subset by fastforce
    moreover from closed bvs_def have "set bvs \<subseteq> Span (us@vs)"
      using Span_contains_spanset_append_right[of us] set_drop_subset by fastforce
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis using ufvs_def vs_decomp by auto
qed

lemma replace_basis :
  assumes closed: "set vs \<subseteq> V" and indep_vs: "lin_independent vs"
  shows   "\<lbrakk> length us \<le> length vs; set us \<subseteq> Span vs; lin_independent us \<rbrakk>
                \<Longrightarrow> \<exists>pvs. length pvs = length vs \<and> set pvs = set vs
                  \<and> basis_for (Span vs) (take (length vs) (us @ pvs))"
proof (induct us)
  case Nil from closed indep_vs show ?case
    using Span_contains_spanset[of vs] by fastforce
next
  case (Cons u us)
  from this obtain ppvs
    where ppvs: "length ppvs = length vs" "set ppvs = set vs"
                "basis_for (Span vs) (take (length vs) (us @ ppvs))"
    using lin_independent_ConsD1[of u us]
    by    auto
  define fppvs bppvs
    where "fppvs = take (length vs - length us) ppvs"
      and "bppvs = drop (length vs - length us) ppvs"
  with ppvs(1) Cons(2)
    have ppvs_decomp: "ppvs = fppvs @ bppvs"
    and  len_fppvs  : "length fppvs = length vs - length us"
    by    auto
  from closed Cons(3) have uus_V:  "u \<in> V" "set us \<subseteq> V"
    using Span_closed by auto
  from closed ppvs(2) have "set ppvs \<subseteq> V" by fast
  with fppvs_def have fppvs_V: "set fppvs \<subseteq> V" using set_take_subset[of _ ppvs] by fast
  from fppvs_def Cons(2)
    have prev_basis_decomp: "take (length vs) (us @ ppvs) = us @ fppvs"
    by   auto
  with Cons(3,4) ppvs(3) fppvs_V uus_V obtain xs y ys
    where xs_y_ys: "fppvs = xs @ y # ys" "basis_for (Span vs) (u # us @ xs @ ys)"
    using lin_independent_imp_hd_independent_from_Span
          replace_basis_one_step[of fppvs us u]
    by    auto
  define pvs where "pvs = xs @ ys @ y # bppvs"
  with xs_y_ys len_fppvs ppvs_decomp ppvs(1,2)
    have "length pvs = length vs" "set pvs = set vs" 
         "basis_for (Span vs) (take (length vs) ((u # us) @ pvs))"
    using take_append[of "length vs" "u # us @ xs @ ys"]
    by    auto
  thus ?case by fast
qed

lemma replace_basis_completely :
  "\<lbrakk> set vs \<subseteq> V; lin_independent vs; length us = length vs;
        set us \<subseteq> Span vs; lin_independent us \<rbrakk> \<Longrightarrow> basis_for (Span vs) us"
  using replace_basis[of vs us] by auto

lemma basis_for_obtain_unique_scalars :
  "basis_for V vs \<Longrightarrow> v \<in> V \<Longrightarrow> \<exists>! as. length as = length vs \<and> v = as \<bullet>\<cdot> vs"
  using lin_independent_obtain_unique_scalars by fast

lemma add_unique_scalars :
  assumes vs: "basis_for V vs" and v: "v \<in> V" and v': "v' \<in> V"
  defines as: "as \<equiv> (THE ds. length ds = length vs \<and> v = ds \<bullet>\<cdot> vs)"
  and     bs: "bs \<equiv> (THE ds. length ds = length vs \<and> v' = ds \<bullet>\<cdot> vs)"
  and     cs: "cs \<equiv> (THE ds. length ds = length vs \<and> v+v' = ds \<bullet>\<cdot> vs)"
  shows   "cs = [a+b. (a,b)\<leftarrow>zip as bs]"
proof-
  from vs v v' as bs
    have  as': "length as = length vs \<and> v = as \<bullet>\<cdot> vs"
    and   bs': "length bs = length vs \<and> v' = bs \<bullet>\<cdot> vs"
    using basis_for_obtain_unique_scalars theI'[
            of "\<lambda>ds. length ds = length vs \<and> v = ds \<bullet>\<cdot> vs"
          ]
          theI'[of "\<lambda>ds. length ds = length vs \<and> v' = ds \<bullet>\<cdot> vs"]
    by    auto
  have "length [a+b. (a,b)\<leftarrow>zip as bs] = length (zip as bs)"
    by (induct as bs rule: list_induct2') auto
  with vs as' bs'
    have  "length [a+b. (a,b)\<leftarrow>zip as bs]
                = length vs \<and> v + v' = [a + b. (a,b)\<leftarrow>zip as bs] \<bullet>\<cdot> vs"
    using lincomb_sum
    by    auto
  moreover from vs v v' have "\<exists>! ds. length ds = length vs \<and> v+v' = ds \<bullet>\<cdot> vs"
    using add_closed basis_for_obtain_unique_scalars by force
  ultimately show ?thesis using cs the1_equality by fast
qed

lemma smult_unique_scalars :
  fixes   a::'f
  assumes vs: "basis_for V vs" and v: "v \<in> V"
  defines as: "as \<equiv> (THE cs. length cs = length vs \<and> v = cs \<bullet>\<cdot> vs)"
  and     bs: "bs \<equiv> (THE cs. length cs = length vs \<and> a \<cdot> v = cs \<bullet>\<cdot> vs)"
  shows   "bs = map ((*) a) as"
proof-
  from vs v as have "length as = length vs \<and> v = as \<bullet>\<cdot> vs"
    using basis_for_obtain_unique_scalars theI'[
            of "\<lambda>cs. length cs = length vs \<and> v = cs \<bullet>\<cdot> vs"
          ]
    by    auto
  with vs have "length (map ((*) a) as)
                      = length vs \<and> a \<cdot> v = (map ((*) a) as) \<bullet>\<cdot> vs"
    using smult_lincomb by auto
  moreover from vs v have "\<exists>! cs. length cs = length vs \<and> a \<cdot> v = cs \<bullet>\<cdot> vs"
    using smult_closed basis_for_obtain_unique_scalars by fast
  ultimately show ?thesis using bs the1_equality by fast
qed

lemma max_lin_independent_set_in_Span :
  assumes "set vs \<subseteq> V" "set us \<subseteq> Span vs" "lin_independent us"
  shows   "length us \<le> length vs"
proof (cases us)
  case (Cons x xs)
  from assms(1) spanset_contains_basis[of vs] obtain bvs
    where bvs: "set bvs \<subseteq> set vs" "basis_for (Span vs) bvs"
    by    auto
  with assms(1) have len_bvs: "length bvs \<le> length vs"
    using lin_independent_imp_distinct[of bvs] distinct_card finite_set 
          card_mono[of "set vs" "set bvs"] card_length[of vs]
    by    fastforce
  moreover have "length (x#xs) > length bvs \<Longrightarrow> \<not> lin_independent (x#xs)"
  proof
    assume A: "length (x#xs) > length bvs" "lin_independent (x#xs)"
    define ws where "ws = take (length bvs) xs"
    from Cons assms(1,2) have xxs_V: "x \<in> V" "set xs \<subseteq> V"
      using Span_closed by auto
    from ws_def A(1) have "length ws = length bvs" by simp
    moreover from Cons assms(2) bvs(2) ws_def have "set ws \<subseteq> Span bvs"
      using set_take_subset by fastforce
    ultimately have "basis_for (Span vs) ws"
      using A(2) ws_def assms(1) bvs xxs_V lin_independent_ConsD1
            lin_independent_imp_independent_take replace_basis_completely[of bvs ws]
      by    force
    with Cons assms(2) ws_def A(2) xxs_V show False
      using Span_contains_Span_take[of xs]
            lin_independent_imp_hd_independent_from_Span[of x xs]
      by    auto
  qed
  ultimately show ?thesis using Cons assms(3) by fastforce
qed simp

lemma finrank_Span : "set vs \<subseteq> V \<Longrightarrow> finrank (Span vs)"
  using max_lin_independent_set_in_Span finrankI by blast

end (* context VectorSpace *)


subsection \<open>Finite dimensional spaces\<close>

context VectorSpace
begin

lemma dim_eq_size_basis : "basis_for V vs \<Longrightarrow> length vs = dim V"
  using max_lin_independent_set_in_Span
        Least_equality[
          of "\<lambda>n::nat. \<exists>us. length us = n \<and> set us \<subseteq> V \<and> RSpan us = V" "length vs"
        ]
  unfolding dim_R_def by fastforce

lemma finrank_imp_findim :
  assumes "finrank V"
  shows   "findim V"
proof-
  from assms obtain n
    where "\<forall>vs. set vs \<subseteq> V \<and> lin_independent vs \<longrightarrow> length vs \<le> n"
    using finrankD
    by    fastforce
  moreover from build_lin_independent_seq[of "[]"] obtain ws
    where "set ws \<subseteq> V" "lin_independent ws" "Span ws = V \<or> length ws = Suc n"
    by    auto
  ultimately show ?thesis by auto
qed

lemma subspace_Span_is_findim :
  "\<lbrakk> set vs \<subseteq> V; Subspace W; W \<subseteq> Span vs \<rbrakk> \<Longrightarrow> findim W"
  using finrank_Span subspace_finrank[of "Span vs" W] SubspaceD1[of W]
        VectorSpace.finrank_imp_findim
  by    auto

end (* context VectorSpace *)

context FinDimVectorSpace
begin

lemma Subspace_is_findim : "Subspace U \<Longrightarrow> findim U"
  using findim subspace_Span_is_findim by fast

lemma basis_ex : "\<exists>vs. basis_for V vs"
  using findim basis_for_Span_ex by auto

lemma lin_independent_length_le_dim :
  "set us \<subseteq> V \<Longrightarrow> lin_independent us \<Longrightarrow> length us \<le> dim V"
  using basis_ex max_lin_independent_set_in_Span dim_eq_size_basis
  by    force

lemma too_long_lin_dependent :
  "set us \<subseteq> V \<Longrightarrow> length us > dim V \<Longrightarrow> \<not> lin_independent us"
  using lin_independent_length_le_dim by fastforce

lemma extend_lin_independent_to_basis :
  assumes "set us \<subseteq> V" "lin_independent us"
  shows   "\<exists>vs. basis_for V (vs @ us)"
proof-
  define n where "n = Suc (dim V - length us)"
  from assms obtain vs
    where vs: "set vs \<subseteq> V" "lin_independent (vs @ us)"
              "Span (vs @ us) = V \<or> length vs = n"
    using build_lin_independent_seq[of us n]
    by    fast
  with assms n_def show ?thesis
    using set_append lin_independent_length_le_dim[of "vs @ us"] by auto
qed

lemma extend_Subspace_basis :
  "U \<subseteq> V \<Longrightarrow> basis_for U us \<Longrightarrow> \<exists>vs. basis_for V (vs@us)"
  using Span_contains_spanset extend_lin_independent_to_basis by fast

lemma Subspace_dim_le :
  assumes "Subspace U"
  shows   "dim U \<le> dim V"
  using   assms findim 
proof-
  from assms obtain us where "basis_for U us"
    using Subspace_is_findim SubspaceD1
          VectorSpace.FinDimVectorSpaceI[of "(\<cdot>)" U]
          FinDimVectorSpace.basis_ex[of "(\<cdot>)" U]
    by    auto
  with assms show ?thesis
    using RSpan_contains_spanset[of us] lin_independent_length_le_dim[of us]
          SubspaceD1 VectorSpace.dim_eq_size_basis[of "(\<cdot>)" U us]
    by    auto
qed

lemma Subspace_eqdim_imp_equal :
  assumes "Subspace U" "dim U = dim V"
  shows   "U = V"
proof-
  from assms(1) obtain us where us: "basis_for U us"
    using Subspace_is_findim SubspaceD1
          VectorSpace.FinDimVectorSpaceI[of "(\<cdot>)" U]
          FinDimVectorSpace.basis_ex[of "(\<cdot>)" U]
    by    auto
  with assms(1) obtain vs where vs: "basis_for V (vs@us)"
    using extend_Subspace_basis[of U us] by fast
  from assms us vs show ?thesis
    using SubspaceD1 VectorSpace.dim_eq_size_basis[of smult U]
          dim_eq_size_basis[of "vs@us"]
    by    auto
qed

lemma Subspace_dim_lt : "Subspace U \<Longrightarrow> U \<noteq> V \<Longrightarrow> dim U < dim V"
  using Subspace_dim_le Subspace_eqdim_imp_equal by fastforce

lemma semisimple :
  assumes "Subspace U"
  shows   "\<exists>W. Subspace W \<and> (V = W \<oplus> U)"
proof-
  from assms obtain us where us: "basis_for U us"
    using SubspaceD1 Subspace_is_findim VectorSpace.FinDimVectorSpaceI
          FinDimVectorSpace.basis_ex[of _ U]
    by    fastforce
  with assms obtain ws where basis: "basis_for V (ws@us)"
    using extend_Subspace_basis by fastforce
  hence ws_V: "set ws \<subseteq> V" and ind_ws_us: "lin_independent (ws@us)"
    and V_eq: "V = Span (ws@us)"
    by  auto
  have "V = Span ws \<oplus> Span us"
  proof (rule inner_dirsum_doubleI)
    from V_eq show "V = Span ws + Span us" using Span_append by fast
    from ws_V ind_ws_us show "add_independentS [Span ws, Span us]"
      using lin_independent_append_imp_independent_Spans by auto
  qed
  with us ws_V have "Subspace (Span ws) \<and> V = (Span ws) \<oplus> U"
    using Subspace_Span by auto
  thus ?thesis by fast
qed

end (* context FinDimVectorSpace *)


subsection \<open>Vector space homomorphisms\<close>

subsubsection \<open>Locales\<close>

locale VectorSpaceHom = ModuleHom smult V smult' T
  for smult  :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and V      :: "'v set"
  and smult' :: "'f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and T      :: "'v \<Rightarrow> 'w"

sublocale VectorSpaceHom < VectorSpace ..

lemmas (in VectorSpace)
  VectorSpaceHomI = ModuleHomI[THEN VectorSpaceHom.intro]

lemma (in VectorSpace) VectorSpaceHomI_fromaxioms :
  assumes "\<And>g g'. g \<in> V \<Longrightarrow> g' \<in> V \<Longrightarrow> T (g + g') = T g + T g'"
          "supp T \<subseteq> V"
          "\<And>r m. r \<in> UNIV \<Longrightarrow> m \<in> V \<Longrightarrow> T (r \<cdot> m) = smult' r (T m)"
  shows   "VectorSpaceHom smult V smult' T"
  using   assms
  by      unfold_locales

locale VectorSpaceEnd = VectorSpaceHom smult V smult T
  for smult :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and V     :: "'v set"
  and T     :: "'v \<Rightarrow> 'v"
+ assumes endomorph: "ImG \<subseteq> V"

abbreviation (in VectorSpace) "VEnd \<equiv> VectorSpaceEnd smult V"

lemma VectorSpaceEndI :
  fixes   smult :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
  assumes "VectorSpaceHom smult V smult T" "T ` V \<subseteq> V"
  shows   "VectorSpaceEnd smult V T"
  by      (rule VectorSpaceEnd.intro, rule assms(1), unfold_locales, rule assms(2))

lemma (in VectorSpaceEnd) VectorSpaceHom: "VectorSpaceHom smult V smult T"
  ..

lemma (in VectorSpaceEnd) ModuleEnd : "ModuleEnd smult V T"
  using endomorph ModuleEnd.intro by unfold_locales

locale VectorSpaceIso = VectorSpaceHom smult V smult' T
  for   smult  :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and   V      :: "'v set"
  and   smult' :: "'f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and   T      :: "'v \<Rightarrow> 'w"
+ fixes W      :: "'w set"
  assumes bijective: "bij_betw T V W"

abbreviation (in VectorSpace) isomorphic ::
  "('f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w) \<Rightarrow> 'w set \<Rightarrow> bool"
  where "isomorphic smult' W \<equiv> (\<exists> T. VectorSpaceIso smult V smult' T W)"

subsubsection \<open>Basic facts\<close>

lemma (in VectorSpace) trivial_VectorSpaceHom :
  "(\<And>a. smult' a 0 = 0) \<Longrightarrow> VectorSpaceHom smult V smult' 0"
  using trivial_RModuleHom[of smult'] ModuleHom.intro VectorSpaceHom.intro
  by    fast

lemma (in VectorSpace) VectorSpaceHom_idhom :
  "VectorSpaceHom smult V smult (id\<down>V)"
  using smult_zero RModHom_idhom ModuleHom.intro VectorSpaceHom.intro
  by    fast

context VectorSpaceHom
begin

lemmas hom             = hom
lemmas supp            = supp
lemmas f_map           = R_map
lemmas im_zero         = im_zero
lemmas im_sum_list_prod = im_sum_list_prod
lemmas additive        = additive
lemmas GroupHom        = GroupHom
lemmas distrib_lincomb = distrib_lincomb

lemmas same_image_on_spanset_imp_same_hom
  = same_image_on_RSpanset_imp_same_hom[
      OF ModuleHom.axioms(1), OF VectorSpaceHom.axioms(1)
    ]

lemma VectorSpace_Im : "VectorSpace smult' ImG"
  using RModule_Im VectorSpace.intro Module.intro by fast

lemma VectorSpaceHom_scalar_mul :
  "VectorSpaceHom smult V smult' (\<lambda>v. a \<star> T v)"
proof
  show "\<And>v v'. v \<in> V \<Longrightarrow> v' \<in> V \<Longrightarrow> a \<star> T (v + v') = a \<star> T v + a \<star> T v'"
    using additive VectorSpace.smult_distrib_left[OF VectorSpace_Im] by simp
  have "\<And>v. v \<notin> V \<Longrightarrow> v \<notin> supp (\<lambda>v. a \<star> T v)"
  proof-
    fix v assume "v \<notin> V"
    hence "a \<star> T v = 0"
      using supp suppI_contra[of _ T] codomain_smult_zero by fastforce
    thus "v \<notin> supp (\<lambda>v. a \<star> T v)" using suppD_contra by fast
  qed
  thus "supp (\<lambda>v. a \<star> T v) \<subseteq> V" by fast
  show "\<And>c v. v \<in> V \<Longrightarrow> a \<star> T (c \<cdot> v) = c \<star> a \<star> T v"
    using f_map VectorSpace.smult_assoc[OF VectorSpace_Im] by (simp add: field_simps)
qed

lemma VectorSpaceHom_composite_left :
  assumes "ImG \<subseteq> W" "VectorSpaceHom smult' W smult'' S"
  shows   "VectorSpaceHom smult V smult'' (S \<circ> T)"
proof-
  have "RModuleHom UNIV smult' W smult'' S"
    using VectorSpaceHom.axioms(1)[OF assms(2)] ModuleHom.axioms(1)
    by    fast
  with assms(1) have "RModuleHom UNIV smult V smult'' (S \<circ> T)"
    using RModHom_composite_left[of W] by fast
  thus ?thesis using ModuleHom.intro VectorSpaceHom.intro by fast
qed

lemma findim_domain_findim_image :
  assumes "findim V"
  shows   "fscalar_mult.findim smult' ImG"
proof-
  from assms obtain vs where vs: "set vs \<subseteq> V" "scalar_mult.Span smult vs = V"
    by fast
  define ws where "ws = map T vs"
  with vs(1) have 1: "set ws \<subseteq> ImG" by auto
  moreover have "Span ws = ImG"
  proof
    show "Span ws \<subseteq> ImG"
      using 1 VectorSpace.Span_closed[OF VectorSpace_Im] by fast
    from vs ws_def show "Span ws \<supseteq> ImG"
      using 1 SpanD_lincomb_arb_len_coeffs distrib_lincomb
            VectorSpace.SpanD_lincomb_arb_len_coeffs[OF VectorSpace_Im]
      by auto
  qed
  ultimately show ?thesis by fast
qed

end (* context VectorSpaceHom *)

lemma (in VectorSpace) basis_im_defines_hom :
  fixes   smult'   :: "'f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     lincomb' :: "'f list \<Rightarrow> 'w list \<Rightarrow> 'w" (infixr "\<bullet>\<star>" 70)
  defines lincomb'  : "lincomb' \<equiv> scalar_mult.lincomb smult'"
  assumes VSpW      : "VectorSpace smult' W"
  and     basisV    : "basis_for V vs"
  and     basisV_im : "set ws \<subseteq> W" "length ws = length vs"
  shows   "\<exists>! T. VectorSpaceHom smult V smult' T \<and> map T vs = ws"
proof (rule ex_ex1I)
  define T where "T = restrict0 (\<lambda>v. (THE as. length as = length vs \<and> v = as \<bullet>\<cdot> vs) \<bullet>\<star> ws) V"
  have "VectorSpaceHom (\<cdot>) V smult' T"
  proof
    fix v v' assume vv': "v \<in> V" "v' \<in> V"
    with T_def lincomb' basisV basisV_im(1) show "T (v + v') = T v + T v'"
      using basis_for_obtain_unique_scalars theI'[
              of "\<lambda>ds. length ds = length vs \<and> v = ds \<bullet>\<cdot> vs"
            ]
            theI'[of "\<lambda>ds. length ds = length vs \<and> v' = ds \<bullet>\<cdot> vs"] add_closed
            add_unique_scalars VectorSpace.lincomb_sum[OF VSpW]
      by    auto
  next
    from T_def show "supp T \<subseteq> V" using supp_restrict0 by fast
  next
    fix a v assume v: "v \<in> V"
    with basisV basisV_im(1) T_def lincomb' show "T (a \<cdot> v) = a \<star> T v"
      using smult_closed smult_unique_scalars VectorSpace.smult_lincomb[OF VSpW] by auto
  qed
  moreover have "map T vs = ws"
  proof (rule nth_equalityI)
    from basisV_im(2) show "length (map T vs) = length ws" by simp
    have "\<And>i. i<length (map T vs) \<Longrightarrow> map T vs ! i = ws ! i"
    proof-
      fix i assume i: "i < length (map T vs)"
      define zs where "zs = (replicate (length vs) (0::'f))[i:=1]"
      with basisV i have "length zs = length vs \<and> vs!i = zs \<bullet>\<cdot> vs" 
        using delta_scalars_lincomb_eq_nth by auto
      moreover from basisV i have "vs!i \<in> V" by auto
      ultimately show "(map T vs)!i = ws!i"
        using basisV basisV_im T_def lincomb' zs_def i
              basis_for_obtain_unique_scalars[of vs "vs!i"]
              the1_equality[of "\<lambda>zs. length zs = length vs \<and> vs!i = zs \<bullet>\<cdot> vs"]
              VectorSpace.delta_scalars_lincomb_eq_nth[OF VSpW, of ws]
        by    force
    qed
    thus "\<And>i. i < length (map T vs) \<Longrightarrow> map T vs ! i = ws ! i" by fast
  qed
  ultimately have "VectorSpaceHom (\<cdot>) V smult' T \<and> map T vs = ws" by fast
  thus "\<exists>T. VectorSpaceHom (\<cdot>) V smult' T \<and> map T vs = ws" by fast
next
  fix S T assume
    "VectorSpaceHom (\<cdot>) V smult' S \<and> map S vs = ws" 
    "VectorSpaceHom (\<cdot>) V smult' T \<and> map T vs = ws"
  with basisV show "S = T"
    using VectorSpaceHom.same_image_on_spanset_imp_same_hom map_eq_conv
    by    fastforce  (* slow *)
qed

subsubsection \<open>Hom-sets\<close>

definition VectorSpaceHomSet ::
  "('f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow> 'v set \<Rightarrow> ('f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w)
        \<Rightarrow> 'w set \<Rightarrow> ('v \<Rightarrow> 'w) set"
  where "VectorSpaceHomSet fsmult V fsmult' W
              \<equiv> {T. VectorSpaceHom fsmult V fsmult' T} \<inter> {T. T ` V \<subseteq> W}"

abbreviation (in VectorSpace) "VectorSpaceEndSet \<equiv> {S. VEnd S}"

lemma VectorSpaceHomSetI :
  "VectorSpaceHom fsmult V fsmult' T \<Longrightarrow> T ` V \<subseteq> W
        \<Longrightarrow> T \<in> VectorSpaceHomSet fsmult V fsmult' W"
  unfolding VectorSpaceHomSet_def by fast

lemma VectorSpaceHomSetD_VectorSpaceHom :
  "T \<in> VectorSpaceHomSet fsmult V fsmult' N
        \<Longrightarrow> VectorSpaceHom fsmult V fsmult' T"
  unfolding VectorSpaceHomSet_def by fast

lemma VectorSpaceHomSetD_Im :
  "T \<in> VectorSpaceHomSet fsmult V fsmult' W \<Longrightarrow> T ` V \<subseteq> W"
  unfolding VectorSpaceHomSet_def by fast

context VectorSpace
begin

lemma VectorSpaceHomSet_is_fmaps_in_GroupHomSet :
  fixes smult' :: "'f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  shows "VectorSpaceHomSet smult V smult' W
              = (GroupHomSet V W) \<inter> {T. \<forall>a. \<forall>v\<in>V. T (a \<cdot> v) = a \<star> (T v)}"
proof
  show "VectorSpaceHomSet smult V smult' W
              \<subseteq> (GroupHomSet V W) \<inter> {T. \<forall>a. \<forall>v\<in>V. T (a \<cdot> v) = a \<star> (T v)}"
    using VectorSpaceHomSetD_VectorSpaceHom[of _ smult]
          VectorSpaceHomSetD_Im[of _ smult]
          VectorSpaceHom.GroupHom[of smult] GroupHomSetI[of V _ W]
          VectorSpaceHom.f_map[of smult]
    by    fastforce
  show "VectorSpaceHomSet smult V smult' W
              \<supseteq> (GroupHomSet V W) \<inter> {T. \<forall>a. \<forall>v\<in>V. T (a \<cdot> v) = a \<star> (T v)}"
  proof
    fix T assume T: "T \<in> (GroupHomSet V W)
                          \<inter> {T. \<forall>a. \<forall>v\<in>V. T (a \<cdot> v) = a \<star> (T v)}"
    have "VectorSpaceHom smult V smult' T"
    proof (rule VectorSpaceHom.intro, rule ModuleHom.intro, rule RModuleHom.intro)
      show "RModule UNIV (\<cdot>) V" ..
      from T show "GroupHom V T" using GroupHomSetD_GroupHom by fast
      from T show "RModuleHom_axioms UNIV smult V smult' T"
        by unfold_locales fast
    qed
    with T show "T \<in> VectorSpaceHomSet smult V smult' W"
      using GroupHomSetD_Im[of T] VectorSpaceHomSetI by fastforce
  qed
qed

lemma Group_VectorSpaceHomSet :
  fixes   smult' :: "'f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  assumes "VectorSpace smult' W"
  shows   "Group (VectorSpaceHomSet smult V smult' W)"
proof
  show "VectorSpaceHomSet smult V smult' W \<noteq> {}"
    using VectorSpace.smult_zero[OF assms] VectorSpace.zero_closed[OF assms]
          trivial_VectorSpaceHom[of smult'] VectorSpaceHomSetI
    by    fastforce
next
  fix S T
  assume S: "S \<in> VectorSpaceHomSet smult V smult' W"
    and  T: "T \<in> VectorSpaceHomSet smult V smult' W"
  from S T
    have  ST: "S \<in> (GroupHomSet V W)
                    \<inter> {T. \<forall>a. \<forall>v\<in>V. T (a \<cdot> v) = a \<star> (T v)}"
              "T \<in> (GroupHomSet V W) \<inter> {T. \<forall>a. \<forall>v\<in>V. T (a \<cdot> v) = a \<star> (T v)}"
    using VectorSpaceHomSet_is_fmaps_in_GroupHomSet
    by    auto
  hence "S - T \<in> GroupHomSet V W"
    using VectorSpace.AbGroup[OF assms] Group_GroupHomSet Group.diff_closed
    by    fast
  moreover have "\<And>a v. v \<in> V \<Longrightarrow> (S - T) (a \<cdot> v) = a \<star> ((S-T) v)"
  proof-
    fix a v assume "v \<in> V"
    with ST show "(S - T) (a \<cdot> v) = a \<star> ((S - T) v)" 
      using GroupHomSetD_Im
            VectorSpace.smult_distrib_left_diff[OF assms, of a "S v" "T v"]
      by    fastforce
  qed
  ultimately show "S - T \<in> VectorSpaceHomSet (\<cdot>) V (\<star>) W"
    using VectorSpaceHomSet_is_fmaps_in_GroupHomSet[of smult' W] by fast
qed

lemma VectorSpace_VectorSpaceHomSet :
  fixes   smult'    :: "'f \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     hom_smult :: "'f \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('v \<Rightarrow> 'w)" (infixr "\<star>\<cdot>" 70)
  defines hom_smult: "hom_smult \<equiv> \<lambda>a T v. a \<star> T v"
  assumes VSpW: "VectorSpace smult' W"
  shows   "VectorSpace hom_smult (VectorSpaceHomSet smult V smult' W)"
proof (rule VectorSpace.intro, rule Module.intro, rule RModule.intro, rule R_scalar_mult)

  from VSpW show "Group (VectorSpaceHomSet (\<cdot>) V (\<star>) W)"
    using Group_VectorSpaceHomSet by fast

  show "RModule_axioms UNIV hom_smult (VectorSpaceHomSet (\<cdot>) V (\<star>) W)"
  proof
    fix a b S T
    assume S: "S \<in> VectorSpaceHomSet (\<cdot>) V (\<star>) W"
      and  T: "T \<in> VectorSpaceHomSet (\<cdot>) V (\<star>) W"
    show "a \<star>\<cdot> T \<in> VectorSpaceHomSet (\<cdot>) V (\<star>) W"
    proof (rule VectorSpaceHomSetI)
      from assms T show "VectorSpaceHom (\<cdot>) V (\<star>) (a \<star>\<cdot> T)"
        using VectorSpaceHomSetD_VectorSpaceHom VectorSpaceHomSetD_Im
              VectorSpaceHom.VectorSpaceHom_scalar_mul
        by    fast
      from hom_smult show "(a \<star>\<cdot> T) ` V \<subseteq> W"
        using VectorSpaceHomSetD_Im[OF T] VectorSpace.smult_closed[OF VSpW]
        by    auto
    qed

    show "a \<star>\<cdot> (S + T) = a \<star>\<cdot> S + a \<star>\<cdot> T"
    proof
      fix v from assms show "(a \<star>\<cdot> (S + T)) v = (a \<star>\<cdot> S + a \<star>\<cdot> T) v"
        using VectorSpaceHomSetD_Im[OF S] VectorSpaceHomSetD_Im[OF T]
              VectorSpace.smult_distrib_left[OF VSpW, of a "S v" "T v"]
              VectorSpaceHomSetD_VectorSpaceHom[OF S]
              VectorSpaceHomSetD_VectorSpaceHom[OF S]
              VectorSpaceHom.supp suppI_contra[of v S] suppI_contra[of v T]
              VectorSpace.smult_zero
        by    fastforce
    qed

    show "(a + b) \<star>\<cdot> T = a \<star>\<cdot> T + b \<star>\<cdot> T"
    proof
      fix v from assms show "((a + b) \<star>\<cdot> T) v = (a \<star>\<cdot> T + b \<star>\<cdot> T) v"
        using VectorSpaceHomSetD_Im[OF T] VectorSpace.smult_distrib_right
              VectorSpaceHomSetD_VectorSpaceHom[OF T] VectorSpaceHom.supp
              suppI_contra[of v] VectorSpace.smult_zero
        by    fastforce
    qed

    show "a \<star>\<cdot> b \<star>\<cdot> T = (a * b) \<star>\<cdot> T"
    proof
      fix v from assms show "(a \<star>\<cdot> b \<star>\<cdot> T) v = ((a * b) \<star>\<cdot> T) v"
        using VectorSpaceHomSetD_Im[OF T] VectorSpace.smult_assoc
              VectorSpaceHomSetD_VectorSpaceHom[OF T]
              VectorSpaceHom.supp suppI_contra[of v]
              VectorSpace.smult_zero[OF VSpW, of b]
              VectorSpace.smult_zero[OF VSpW, of a]
              VectorSpace.smult_zero[OF VSpW, of "a * b"]
        by    fastforce
    qed

    show "1 \<star>\<cdot> T = T"
    proof
      fix v from assms T show "(1 \<star>\<cdot> T) v = T v"
        using VectorSpaceHomSetD_Im VectorSpace.one_smult
              VectorSpaceHomSetD_VectorSpaceHom VectorSpaceHom.supp
              suppI_contra[of v] VectorSpace.smult_zero
        by    fastforce
    qed

  qed
qed

end (* context VectorSpace *)

subsubsection \<open>Basic facts about endomorphisms\<close>

lemma ModuleEnd_over_field_is_VectorSpaceEnd :
  fixes   smult :: "'f::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
  assumes "ModuleEnd smult V T"
  shows   "VectorSpaceEnd smult V T"
proof (rule VectorSpaceEndI, rule VectorSpaceHom.intro)
  from assms show "ModuleHom smult V smult T"
    using ModuleEnd.axioms(1) by fast
  from assms show "T ` V \<subseteq>  V" using ModuleEnd.endomorph by fast
qed

context VectorSpace
begin

lemmas VectorSpaceEnd_inner_dirsum_el_decomp_nth =
  RModuleEnd_inner_dirsum_el_decomp_nth[
    THEN RModuleEnd_over_UNIV_is_ModuleEnd,
    THEN ModuleEnd_over_field_is_VectorSpaceEnd
  ]

abbreviation end_smult :: "'f \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v)" (infixr "\<cdot>\<cdot>" 70) 
  where "a \<cdot>\<cdot> T \<equiv> (\<lambda>v. a \<cdot> T v)"

abbreviation end_lincomb
  :: "'f list \<Rightarrow> (('v \<Rightarrow> 'v) list) \<Rightarrow> ('v \<Rightarrow> 'v)" (infixr "\<bullet>\<cdot>\<cdot>" 70)
  where "end_lincomb \<equiv> scalar_mult.lincomb end_smult"

lemma end_smult0: "a \<cdot>\<cdot> 0 = 0"
  using smult_zero by auto

lemma end_0smult: "range T \<subseteq> V \<Longrightarrow> 0 \<cdot>\<cdot> T = 0"
  using zero_smult by fastforce

lemma end_smult_distrib_left :
  assumes "range S \<subseteq> V" "range T \<subseteq> V"
  shows   "a \<cdot>\<cdot> (S + T) = a \<cdot>\<cdot> S + a \<cdot>\<cdot> T"
proof
  fix v from assms show "(a \<cdot>\<cdot> (S + T)) v = (a \<cdot>\<cdot> S  + a \<cdot>\<cdot> T) v"
    using smult_distrib_left[of a "S v" "T v"] by fastforce
qed

lemma end_smult_distrib_right :
  assumes "range T \<subseteq> V"
  shows   "(a+b) \<cdot>\<cdot> T = a \<cdot>\<cdot> T + b \<cdot>\<cdot> T"
proof
  fix v from assms show "((a+b) \<cdot>\<cdot> T) v = (a \<cdot>\<cdot> T + b \<cdot>\<cdot> T) v"
    using smult_distrib_right[of a b "T v"] by fastforce
qed

lemma end_smult_assoc :
  assumes "range T \<subseteq> V"
  shows   "a \<cdot>\<cdot> b \<cdot>\<cdot> T = (a * b) \<cdot>\<cdot> T"
proof
  fix v from assms show "(a \<cdot>\<cdot> b \<cdot>\<cdot> T) v = ((a * b) \<cdot>\<cdot> T) v"
    using smult_assoc[of a b "T v"] by fastforce
qed

lemma end_smult_comp_comm_left : "(a \<cdot>\<cdot> T) \<circ> S = a \<cdot>\<cdot> (T \<circ> S)"
  by auto

lemma end_idhom : "VEnd (id\<down>V)"
  by (rule VectorSpaceEnd.intro, rule VectorSpaceHom_idhom, unfold_locales) auto

lemma VectorSpaceEndSet_is_VectorSpaceHomSet :
  "VectorSpaceHomSet smult V smult V = {T. VEnd T}"
proof
  show "VectorSpaceHomSet smult V smult V \<subseteq> {T. VEnd T}"
    using VectorSpaceHomSetD_VectorSpaceHom VectorSpaceHomSetD_Im
          VectorSpaceEndI
    by    fast
  show "VectorSpaceHomSet smult V smult V \<supseteq> {T. VEnd T}"
    using VectorSpaceEnd.VectorSpaceHom[of smult V]
          VectorSpaceEnd.endomorph[of smult V]
          VectorSpaceHomSetI[of smult V smult _ V]
    by fast
qed

lemma VectorSpace_VectorSpaceEndSet : "VectorSpace end_smult VectorSpaceEndSet"
  using VectorSpace_axioms VectorSpace_VectorSpaceHomSet
        VectorSpaceEndSet_is_VectorSpaceHomSet
  by    fastforce

end (* context VectorSpace *)

context VectorSpaceEnd
begin

lemmas f_map                         = R_map
lemmas supp                          = supp
lemmas GroupEnd                      = ModuleEnd.GroupEnd[OF ModuleEnd]
lemmas idhom_left                    = idhom_left
lemmas range                         = GroupEnd.range[OF GroupEnd]
lemmas Ker0_imp_inj_on               = Ker0_imp_inj_on
lemmas inj_on_imp_Ker0               = inj_on_imp_Ker0
lemmas nonzero_Ker_el_imp_n_inj      = nonzero_Ker_el_imp_n_inj
lemmas VectorSpaceHom_composite_left
              = VectorSpaceHom_composite_left[OF endomorph]

lemma in_VEndSet : "T \<in> VectorSpaceEndSet"
  using VectorSpaceEnd_axioms by fast

lemma end_smult_comp_comm_right :
  "range S \<subseteq> V \<Longrightarrow> T \<circ> (a \<cdot>\<cdot> S) = a \<cdot>\<cdot> (T \<circ> S)"
  using f_map by fastforce

lemma VEnd_end_smult_VEnd : "VEnd (a \<cdot>\<cdot> T)"
  using in_VEndSet VectorSpace.smult_closed[OF VectorSpace_VectorSpaceEndSet]
  by    fast

lemma VEnd_composite_left :
  assumes "VEnd S"
  shows   "VEnd (S \<circ> T)"
  using endomorph VectorSpaceEnd.axioms(1)[OF assms] VectorSpaceHom_composite_left
        VectorSpaceEnd.endomorph[OF assms] VectorSpaceEndI[of smult V "S \<circ> T"]
  by    fastforce

lemma VEnd_composite_right : "VEnd S \<Longrightarrow> VEnd (T \<circ> S)"
  using VectorSpaceEnd_axioms VectorSpaceEnd.VEnd_composite_left by fast

end (* context VectorSpaceEnd *)

lemma (in VectorSpace) inj_comp_end :
  assumes "VEnd S" "inj_on S V" "VEnd T" "inj_on T V"
  shows   "inj_on (S \<circ> T) V"
proof-
  have "ker (S \<circ> T) \<inter> V \<subseteq> 0"
  proof
    fix v assume "v \<in> ker (S \<circ> T) \<inter> V"
    moreover hence "T v = 0" using kerD[of v "S \<circ> T"]
      using VectorSpaceEnd.endomorph[OF assms(3)] kerI[of S]
            VectorSpaceEnd.inj_on_imp_Ker0[OF assms(1,2)]
      by    auto
    ultimately show "v \<in> 0"
      using kerI[of T] VectorSpaceEnd.inj_on_imp_Ker0[OF assms(3,4)] by auto
  qed
  with assms(1,3) show ?thesis
    using VectorSpaceEnd.VEnd_composite_right VectorSpaceEnd.Ker0_imp_inj_on
    by    fast
qed

lemma (in VectorSpace) n_inj_comp_end : 
  "\<lbrakk> VEnd S; VEnd T; \<not> inj_on (S \<circ> T) V \<rbrakk> \<Longrightarrow> \<not> inj_on S V \<or> \<not> inj_on T V"
  using inj_comp_end by fast

subsubsection \<open>Polynomials of endomorphisms\<close>

context VectorSpaceEnd
begin

primrec endpow :: "nat \<Rightarrow> ('v\<Rightarrow>'v)"
  where endpow0:   "endpow 0 = id\<down>V"
  |     endpowSuc: "endpow (Suc n) = T \<circ> (endpow n)"

definition polymap :: "'f poly \<Rightarrow> ('v\<Rightarrow>'v)"
  where "polymap p \<equiv> (coeffs p) \<bullet>\<cdot>\<cdot> (map endpow [0..<Suc (degree p)])"

lemma VEnd_endpow : "VEnd (endpow n)"
proof (induct n)
  case 0 show ?case using end_idhom by simp
next
  case (Suc k)
  moreover have "VEnd T" ..
  ultimately have "VEnd (T \<circ> (endpow k))" using VEnd_composite_right by fast
  moreover have "endpow (Suc k) = T \<circ> (endpow k)" by simp
  ultimately show "VEnd (endpow (Suc k))" by simp
qed

lemma endpow_list_apply_closed :
  "v \<in> V \<Longrightarrow> set (map (\<lambda>S. S v) (map endpow [0..<k])) \<subseteq> V"
  using VEnd_endpow VectorSpaceEnd.endomorph by fastforce

lemma map_endpow_Suc :
  "map endpow [0..<Suc n] = (id\<down>V) # map ((\<circ>) T) (map endpow [0..<n])"
proof (induct n)
  case (Suc k)
  hence "map endpow [0..<Suc (Suc k)] = id \<down> V
              # map ((\<circ>) T) (map endpow [0..<k]) @ map ((\<circ>) T) [endpow k]"
    by auto
  also have "\<dots> = id \<down> V # map ((\<circ>) T) (map endpow ([0..<Suc k]))" by simp
  finally show ?case by fast
qed simp

lemma T_endpow_list_apply_commute :
  "map T (map (\<lambda>S. S v) (map endpow [0..<n]))
        = map (\<lambda>S. S v) (map ((\<circ>) T) (map endpow [0..<n]))"
  by (induct n) auto

lemma polymap0 : "polymap 0 = 0"
  using polymap_def scalar_mult.lincomb_Nil by force

lemma VEnd_polymap : "VEnd (polymap p)"
proof-
  have "set (map endpow [0..<Suc (degree p)]) \<subseteq> {S. VEnd S}"
    using VEnd_endpow by auto
  thus ?thesis
    using polymap_def VectorSpace_VectorSpaceEndSet VectorSpace.lincomb_closed
    by    fastforce
qed

lemma polymap_pCons : "polymap (pCons a p) = a \<cdot>\<cdot> (id\<down>V) + (T \<circ> (polymap p))"
proof cases
  assume p: "p = 0"
  show ?thesis
  proof cases
    assume "a = 0" with p show ?thesis
      using polymap0 VectorSpace_VectorSpaceEndSet VectorSpace.zero_smult end_idhom
            comp_zero
      by    fastforce
  next
    assume a: "a \<noteq> 0"
    define zmap where "zmap = (0::'v\<Rightarrow>'v)"
    from a p have "polymap (pCons a p) = a \<cdot>\<cdot> (endpow 0)" 
      using polymap_def scalar_mult.lincomb_singles by simp
    moreover have "a \<cdot>\<cdot> (id\<down>V) + (T \<circ> (polymap p)) = a \<cdot>\<cdot> (id\<down>V)"
      using p polymap0 comp_zero by simp
    ultimately show ?thesis by simp
  qed
next
  assume "p \<noteq> 0"
  hence "polymap (pCons a p)
              = (a # (coeffs p)) \<bullet>\<cdot>\<cdot> (map endpow [0..<Suc (Suc (degree p))])"
    using polymap_def by simp
  also have "\<dots> = (a # (coeffs p))
                   \<bullet>\<cdot>\<cdot> ((id\<down>V) # map ((\<circ>) T) (map endpow [0..<Suc (degree p)]))"
    using map_endpow_Suc[of "Suc (degree p)"] by fastforce
  also have "\<dots> = a \<cdot>\<cdot> (id\<down>V) + (coeffs p)
                  \<bullet>\<cdot>\<cdot> (map ((\<circ>) T) (map endpow [0..<Suc (degree p)]))"
    using scalar_mult.lincomb_Cons by simp
  also have "\<dots> = a \<cdot>\<cdot> (id\<down>V) + (\<Sum>(c,S)
                  \<leftarrow>zip (coeffs p) (map ((\<circ>) T) (map endpow [0..<Suc (degree p)])).
                      c \<cdot>\<cdot> S)"
    using scalar_mult.lincomb_def by simp
  finally have calc:
    "polymap (pCons a p) = a \<cdot>\<cdot> (id\<down>V)
      + (\<Sum>(c,k)\<leftarrow>zip (coeffs p) [0..<Suc (degree p)]. c \<cdot>\<cdot> (T \<circ> (endpow k)))"
    using sum_list_prod_map2[
            of "\<lambda>c S. c \<cdot>\<cdot> S" "coeffs p" "(\<circ>) T" "map endpow [0..<Suc (degree p)]"
          ]
          sum_list_prod_map2[
            of "\<lambda>c S. c \<cdot>\<cdot> (T \<circ> S)" "coeffs p" endpow "[0..<Suc (degree p)]"
          ]
    by    simp
  show ?thesis
  proof
    fix v show "polymap (pCons a p) v = ((a \<cdot>\<cdot> (id\<down>V)) + (T \<circ> (polymap p))) v"
    proof (cases "v \<in> V")
      case True
      with calc
        have "polymap (pCons a p) v = a \<cdot> v + (\<Sum>(c,k)
                    \<leftarrow>zip (coeffs p) [0..<Suc (degree p)]. c \<cdot> T (endpow k v))"
        using sum_list_prod_fun_apply[of "\<lambda>c k. c \<cdot>\<cdot> (T \<circ> (endpow k))"] by simp
      hence "polymap (pCons a p) v = a \<cdot> v + (coeffs p) \<bullet>\<cdot> (map T
                  (map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)])))"
        using sum_list_prod_map2[
                of "\<lambda>c S. c \<cdot> T (S v)" "coeffs p" endpow "[0..<Suc (degree p)]"
              ]
              sum_list_prod_map2[
                of "\<lambda>c u. c \<cdot> T u" "coeffs p" "\<lambda>S. S v" "map endpow [0..<Suc (degree p)]"
              ]
              sum_list_prod_map2[
                of "\<lambda>c u. c \<cdot> u" "coeffs p" T
                   "map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)])"
              ]
              lincomb_def
        by    simp
      also from True
        have  "\<dots> = a \<cdot> v + T ( (coeffs p)
                    \<bullet>\<cdot> (map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)])) )"
        using endpow_list_apply_closed[of v "Suc (degree p)"] distrib_lincomb
        by    simp
      finally show ?thesis
        using True lincomb_def
              sum_list_prod_map2[
                of "\<lambda>c u. c \<cdot> u" "coeffs p" "\<lambda>S. S v" "map endpow [0..<Suc (degree p)]"
              ]
              sum_list_prod_fun_apply[of "\<lambda>c S. c \<cdot>\<cdot> S"] polymap_def 
              scalar_mult.lincomb_def[of end_smult]
        by    simp
    next
      case False
      hence "polymap (pCons a p) v = 0"
        using VEnd_polymap VectorSpaceEnd.supp suppI_contra by fast
      moreover from False have "((a \<cdot>\<cdot> (id\<down>V)) + (T \<circ> (polymap p))) v = 0"
        using smult_zero VEnd_polymap[of p] VectorSpaceEnd.supp suppI_contra
              im_zero
        by    fastforce
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma polymap_plus : "polymap (p + q) = polymap p + polymap q"
proof (induct p q rule: pCons_induct2)
  case 00 show ?case using polymap0 by simp
  case lpCons show ?case using polymap0 by simp
  case rpCons show ?case using polymap0 by simp
next
  case (pCons2 a p b q)
  have "polymap (pCons a p + pCons b q) = a \<cdot>\<cdot> (id\<down>V) + b \<cdot>\<cdot> (id\<down>V)
              + (T \<circ> (polymap (p+q)))"
    using polymap_pCons end_idhom end_smult_distrib_right[OF VectorSpaceEnd.range]
    by    simp
  also from pCons2(3)
    have "\<dots> = a \<cdot>\<cdot> (id\<down>V) + b \<cdot>\<cdot> (id\<down>V) + (T \<circ> (polymap p + polymap q))"
    by   auto
  finally show ?case
    using pCons2(3) distrib_comp_sum_left[of "polymap p" "polymap q"] VEnd_polymap
          VectorSpaceEnd.range polymap_pCons
    by    fastforce
qed

lemma polymap_polysmult : "polymap (Polynomial.smult a p) = a \<cdot>\<cdot> polymap p"
proof (induct p)
  case 0 show "polymap (Polynomial.smult a 0) = a \<cdot>\<cdot> polymap 0"
    using polymap0 end_smult0 by simp
next
  case (pCons b p)
  hence "polymap (Polynomial.smult a (pCons b p))
              = a \<cdot>\<cdot> b \<cdot>\<cdot> (id\<down>V) + a \<cdot>\<cdot> (T \<circ> polymap p)"
    using polymap_pCons VectorSpaceEnd.range[OF VEnd_polymap]
          end_smult_comp_comm_right VectorSpaceEnd.range[OF end_idhom] end_smult_assoc
    by    simp
  thus "polymap (Polynomial.smult a (pCons b p)) = a \<cdot>\<cdot> (polymap (pCons b p))"
    using VectorSpaceEnd.VEnd_end_smult_VEnd[OF end_idhom, of b]
          VEnd_composite_right[OF VEnd_polymap, of p]
          end_smult_distrib_left[
            OF VectorSpaceEnd.range VectorSpaceEnd.range,
            of smult _ smult "T \<circ> polymap p"
          ]
          polymap_pCons
    by    simp
qed

lemma polymap_times : "polymap (p * q) = (polymap p) \<circ> (polymap q)"
proof (induct p)
  case 0 show ?case using polymap0 by auto
next
  case (pCons a p)
  have "polymap (pCons a p * q) = a \<cdot>\<cdot> polymap q + (T \<circ> (polymap (p*q)))"
    using polymap_plus polymap_polysmult polymap_pCons end_idhom
          end_0smult[OF VectorSpaceEnd.range]
    by    simp
  also from pCons(2)
    have "\<dots> = a \<cdot>\<cdot> ((id\<down>V) \<circ> polymap q) + (T \<circ> polymap p \<circ> polymap q)"
    using VectorSpaceEnd.endomorph[OF VEnd_polymap]
          VectorSpaceEnd.idhom_left[OF VEnd_polymap]
    by    auto
  finally show "polymap (pCons a p * q) = (polymap (pCons a p)) \<circ> (polymap q)"
    using end_smult_comp_comm_left
          distrib_comp_sum_right[of "a \<cdot>\<cdot> id \<down> V" _ "polymap q"]
          polymap_pCons
    by    simp
qed

lemma polymap_apply :
  assumes "v \<in> V"
  shows   "polymap p v = (coeffs p)
                \<bullet>\<cdot> (map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)]))"
proof (induct p)
  case 0 show ?case
    using lincomb_Nil scalar_mult.lincomb_Nil[of _ _ end_smult] polymap_def
    by    simp
next
  case (pCons a p)
  show ?case
  proof (cases "p = 0")
    case True
    moreover with pCons(1) have "polymap (pCons a p) = a \<cdot>\<cdot> id\<down>V"
      using polymap_pCons polymap0 comp_zero by simp
    ultimately show ?thesis using assms pCons(1) lincomb_singles by simp
  next
    case False
    from assms pCons(2)
      have "polymap (pCons a p) v = a \<cdot> v
                  + T (coeffs p \<bullet>\<cdot> map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)]))"
      using polymap_pCons by simp
    with assms pCons(1)
      have  1: "polymap (pCons a p) v = (coeffs (pCons a p)) \<bullet>\<cdot> (v #
                      map T (map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)])))"
      using endpow_list_apply_closed[of v "Suc (degree p)"] distrib_lincomb lincomb_Cons
      by    auto
    have 2: "map T (map (\<lambda>S. S v) (map endpow [0..<Suc (degree p)]))
                  = map (\<lambda>S. S v) (map ((\<circ>) T) (map endpow [0..<Suc (degree p)]))"
      using T_endpow_list_apply_commute[of v "Suc (degree p)"] by simp
    from 1 2
      have  "polymap (pCons a p) v = (coeffs (pCons a p)) \<bullet>\<cdot> (v #
                  map (\<lambda>S. S v) (map ((\<circ>) T) (map endpow [0..<Suc (degree p)])))"
      using subst[
              OF 2, of "\<lambda>x. polymap (pCons a p) v = (coeffs (pCons a p)) \<bullet>\<cdot> (v # x)"
            ]
      by    simp
    with assms
      have 3: "polymap (pCons a p) v = (coeffs (pCons a p))
                    \<bullet>\<cdot> (map (\<lambda>S. S v) (id\<down>V # map ((\<circ>) T)
                      (map endpow [0..<Suc (degree p)])))"
      by   simp
    from False pCons(1)
      have  4: "id \<down> V # map ((\<circ>) T) (map endpow [0..<Suc (degree p)])
                      = map endpow [0..<Suc (degree (pCons a p))]"
      using map_endpow_Suc[of "Suc (degree p)", THEN sym]
      by    simp
    from 3 show ?thesis
      using subst[
              OF 4,
              of "\<lambda>x. polymap (pCons a p) v
                        = (coeffs (pCons a p)) \<bullet>\<cdot> (map (\<lambda>S. S v) x)"
            ]
      by    simp
  qed
qed

lemma polymap_apply_linear : "v \<in> V \<Longrightarrow> polymap [:-c, 1:] v = T v - c \<cdot> v"
  using polymap_apply lincomb_def neg_smult endomorph by auto

lemma polymap_const_inj :
  assumes "degree p = 0" "p \<noteq> 0"
  shows   "inj_on (polymap p) V"
proof (rule inj_onI)
  fix u v assume uv: "u \<in> V" "v \<in> V" "polymap p u = polymap p v"
  from assms have p: "coeffs p = [coeff p 0]" unfolding coeffs_def by simp
  from uv assms have "(coeff p 0) \<cdot> u = (coeff p 0) \<cdot> v"
    using polymap_apply lincomb_singles unfolding coeffs_def by simp
  with assms uv(1,2) show "u = v"
    using const_poly_nonzero_coeff cancel_scalar by auto
qed

lemma n_inj_polymap_times :
  "\<not> inj_on (polymap (p * q)) V
        \<Longrightarrow> \<not> inj_on (polymap p) V \<or> \<not> inj_on (polymap q) V"
  using polymap_times VEnd_polymap n_inj_comp_end by fastforce

text \<open>In the following lemma, @{term "[:-c, 1:]"} is the linear polynomial @{term "x - c"}.\<close>

lemma n_inj_polymap_findlinear :
  assumes alg_closed: "\<And>p::'f poly. degree p > 0 \<Longrightarrow> \<exists>c. poly p c = 0"
  shows   "p \<noteq> 0 \<Longrightarrow> \<not> inj_on (polymap p) V
                \<Longrightarrow> \<exists>c. \<not> inj_on (polymap [:-c, 1:]) V"
proof (induct n \<equiv> "degree p" arbitrary: p)
  case (0 p) thus ?case using polymap_const_inj by simp
next
  case (Suc n p)
  from Suc(2) alg_closed obtain c where c: "poly p c = 0" by fastforce
  define q where "q = synthetic_div p c"
  with c have p_decomp: "p = [:-c, 1:] * q"
    using synthetic_div_correct'[of c p] by simp
  show ?case
  proof (cases "inj_on (polymap q) V")
    case True with Suc(4) show ?thesis
      using p_decomp n_inj_polymap_times by fast
  next
    case False
    then have "n = degree q"
      using degree_synthetic_div [of p c] q_def \<open>Suc n = degree p\<close>
      by auto
    moreover have "q \<noteq> 0"
      using \<open>p \<noteq> 0\<close> p_decomp
      by auto
    ultimately show ?thesis
      using False
      by (rule Suc.hyps)
  qed
qed

end (* context VectorSpaceEnd *)

subsubsection \<open>Existence of eigenvectors of endomorphisms of finite-dimensional vector spaces\<close>

lemma (in FinDimVectorSpace) endomorph_has_eigenvector :
  assumes alg_closed: "\<And>p::'a poly. degree p > 0 \<Longrightarrow> \<exists>c. poly p c = 0"
  and     dim       : "dim V > 0"
  and     endo      : "VectorSpaceEnd smult V T"
  shows   "\<exists>c u. u \<in> V \<and> u \<noteq> 0 \<and> T u = c \<cdot> u"
proof-
  define Tpolymap where "Tpolymap = VectorSpaceEnd.polymap smult V T"
  from dim obtain v where v: "v \<in> V" "v \<noteq> 0"
    using dim_nonzero nonempty by auto
  define Tpows where "Tpows = map (VectorSpaceEnd.endpow V T) [0..<Suc (dim V)]"
  define Tpows_v where "Tpows_v = map (\<lambda>S. S v) Tpows"
  with endo Tpows_def v(1) have Tpows_v_V: "set Tpows_v \<subseteq> V"
    using VectorSpaceEnd.endpow_list_apply_closed by fast
  moreover from Tpows_v_def Tpows_def Tpows_v_V have "\<not> lin_independent Tpows_v"
    using too_long_lin_dependent by simp
  ultimately obtain as
    where as: "set as \<noteq> 0" "length as = length Tpows_v" "as \<bullet>\<cdot> Tpows_v = 0"
    using lin_dependent_dependence_relation
    by    fast
  define p where "p = Poly as"
  with dim Tpows_def Tpows_v_def as(1,2) have p_n0: "p \<noteq> 0"
    using nonzero_coeffs_nonzero_poly[of as] by fastforce
  define Tpows' where "Tpows' = map (VectorSpaceEnd.endpow V T) [0..<Suc (degree p)]"
  define Tpows_v' where "Tpows_v' = map (\<lambda>S. S v) Tpows'"
  have "Tpows' = take (Suc (degree p)) Tpows"
  proof-
    from Tpows_def
      have  1: "take (Suc (degree p)) Tpows = map (VectorSpaceEnd.endpow V T)
                      (take (Suc (degree p)) [0..<Suc (dim V)])"
      using take_map[of _ _ "[0..<Suc (dim V)]"]
      by    simp
    from p_n0 p_def as(2) Tpows_v_def Tpows_def
      have  2: "take (Suc (degree p)) [0..<Suc (dim V)] = [0..<Suc (degree p)]"
      using length_coeffs_degree[of p] length_strip_while_le[of "(=) 0" as]
            take_upt[of 0 "Suc (degree p)" "Suc (dim V)"]
      by    simp
    from 1 Tpows'_def have "take (Suc (degree p)) Tpows = Tpows'"
      using subst[OF 2] by fast
    thus ?thesis by simp
  qed
  with Tpows_v_def Tpows_v'_def have "Tpows_v' = take (Suc (degree p)) Tpows_v"
    using take_map[of _ "\<lambda>S. S v" Tpows] by simp
  moreover from p_def Tpows_v_V as(3) Tpows_v'_def have "(coeffs p) \<bullet>\<cdot> Tpows_v = 0"
    using lincomb_strip_while_0coeffs by simp
  ultimately have "(coeffs p) \<bullet>\<cdot> Tpows_v' = 0"
    using p_n0 lincomb_conv_take_right[of "coeffs p"] length_coeffs_degree[of p] by simp
  with Tpolymap_def v(1) Tpows_v'_def Tpows'_def have "Tpolymap p v = 0"
    using VectorSpaceEnd.polymap_apply[OF endo] by simp
  with alg_closed Tpolymap_def v endo p_n0 obtain c
    where "\<not> inj_on (Tpolymap [:-c, 1:]) V"
    using VectorSpaceEnd.VEnd_polymap VectorSpaceEnd.nonzero_Ker_el_imp_n_inj
          VectorSpaceEnd.n_inj_polymap_findlinear[OF endo]
    by    fastforce
  with Tpolymap_def have "(GroupHom.Ker V (Tpolymap [:-c, 1:])) - 0 \<noteq> {}"
    using VectorSpaceEnd.VEnd_polymap[OF endo] VectorSpaceEnd.Ker0_imp_inj_on
    by    fast
  from this obtain u where "u \<in> V" "Tpolymap [:-c, 1:] u = 0" "u \<noteq> 0"
    using kerD by fastforce
  with Tpolymap_def show ?thesis
    using VectorSpaceEnd.polymap_apply_linear[OF endo] by auto
qed




section \<open>Modules Over a Group Ring\<close>

subsection \<open>Almost-everywhere-zero functions as scalars\<close>

locale aezfun_scalar_mult = scalar_mult smult
  for smult ::
    "('r::ring_1, 'g::group_add) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
begin

definition fsmult :: "'r \<Rightarrow> 'v \<Rightarrow> 'v" (infixr "\<sharp>\<cdot>" 70) where "a \<sharp>\<cdot> v \<equiv> (a \<delta>\<delta> 0) \<cdot> v"
abbreviation flincomb :: "'r list \<Rightarrow> 'v list \<Rightarrow> 'v" (infixr "\<bullet>\<sharp>\<cdot>" 70)
  where "as \<bullet>\<sharp>\<cdot> vs \<equiv> scalar_mult.lincomb fsmult as vs"
abbreviation f_lin_independent :: "'v list \<Rightarrow> bool"
  where "f_lin_independent \<equiv> scalar_mult.lin_independent fsmult"
abbreviation fSpan :: "'v list \<Rightarrow> 'v set" where "fSpan \<equiv> scalar_mult.Span fsmult"
definition Gmult :: "'g \<Rightarrow> 'v \<Rightarrow> 'v" (infixr "*\<cdot>" 70) where "g *\<cdot> v \<equiv> (1 \<delta>\<delta> g) \<cdot> v"

lemmas R_scalar_mult = R_scalar_mult

lemma fsmultD : "a \<sharp>\<cdot> v = (a \<delta>\<delta> 0) \<cdot> v"
  unfolding fsmult_def by fast

lemma GmultD : "g *\<cdot> v = (1 \<delta>\<delta> g) \<cdot> v"
  unfolding Gmult_def by fast

definition negGorbit_list :: "'g list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a list \<Rightarrow> 'v list list"
  where "negGorbit_list gs T as \<equiv> map (\<lambda>g. map (Gmult (-g) \<circ> T) as) gs"

lemma negGorbit_Cons :
  "negGorbit_list (g#gs) T as
        = (map (Gmult (-g) \<circ> T) as) # negGorbit_list gs T as"
  using negGorbit_list_def[of _ T as] by simp

lemma length_negGorbit_list : "length (negGorbit_list gs T as) = length gs"
  using negGorbit_list_def[of gs T] by simp

lemma length_negGorbit_list_sublist :
  "fs \<in> set (negGorbit_list gs T as) \<Longrightarrow> length fs = length as"
  using negGorbit_list_def[of gs T] by auto

lemma length_concat_negGorbit_list : 
  "length (concat (negGorbit_list gs T as)) = (length gs) * (length as)"
  using length_concat[of "negGorbit_list gs T as"]
        length_negGorbit_list_sublist[of _ gs T as]
        const_sum_list[of "negGorbit_list gs T as" length "length as"] length_negGorbit_list
  by    auto

lemma negGorbit_list_nth : 
  "\<And>i. i < length gs \<Longrightarrow> (negGorbit_list gs T as)!i = map (Gmult (-gs!i) \<circ> T) as"
proof (induct gs)
  case (Cons g gs) thus ?case using negGorbit_Cons[of _ _ T] by (cases i) auto
qed simp

end (* context aezfun_scalar_mult *)

subsection \<open>Locale and basic facts\<close>

locale FGModule = ActingGroup?: Group G
+ FGMod?: RModule ActingGroup.group_ring smult V
  for G     :: "'g::group_add set"
  and smult :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and V     :: "'v set"

sublocale FGModule < aezfun_scalar_mult proof- qed

lemma (in Group) trivial_FGModule :
  fixes   smult :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
  assumes smult_zero: "\<forall>a\<in>group_ring. smult a (0::'v) = 0"
  shows   "FGModule G smult (0::'v set)"
proof (rule FGModule.intro)
  from assms show "RModule group_ring  smult 0"
    using Ring1_RG trivial_RModule by fast
qed (unfold_locales)

context FGModule
begin

abbreviation FG :: "('f,'g) aezfun set" where "FG \<equiv> ActingGroup.group_ring"
abbreviation "FGSubmodule \<equiv> RSubmodule"
abbreviation "FG_proj     \<equiv> ActingGroup.RG_proj"

lemma GroupG: "Group G" ..

lemmas zero_closed            = zero_closed
lemmas neg_closed             = neg_closed
lemmas diff_closed            = diff_closed
lemmas zero_smult             = zero_smult
lemmas smult_zero             = smult_zero
lemmas AbGroup                = AbGroup
lemmas sum_closed          = AbGroup.sum_closed[OF AbGroup]
lemmas FGSubmoduleI           = RSubmoduleI
lemmas FG_proj_mult_leftdelta = ActingGroup.RG_proj_mult_leftdelta
lemmas FG_proj_mult_right     = ActingGroup.RG_proj_mult_right
lemmas FG_el_decomp           = ActingGroup.RG_el_decomp_aezdeltafun

lemma FG_n0: "FG \<noteq> 0" using ActingGroup.RG_n0 by fast

lemma FG_proj_in_FG : "FG_proj x \<in> FG"
  using ActingGroup.RG_proj_in_RG by fast

lemma FG_fddg_closed : "g \<in> G \<Longrightarrow> a \<delta>\<delta> g \<in> FG"
  using ActingGroup.RG_aezdeltafun_closed by fast

lemma FG_fdd0_closed : "a \<delta>\<delta> 0 \<in> FG"
  using ActingGroup.RG_aezdelta0fun_closed by fast

lemma Gmult_closed : "g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> g *\<cdot> v \<in> V"
  using FG_fddg_closed smult_closed GmultD by simp

lemma map_Gmult_closed :
  "g \<in> G \<Longrightarrow> set vs \<subseteq> V \<Longrightarrow> set (map ((*\<cdot>) g) vs) \<subseteq> V"
  using Gmult_def FG_fddg_closed map_smult_closed[of "1 \<delta>\<delta> g" vs] by auto

lemma Gmult0 :
  assumes "v \<in> V"
  shows   "0 *\<cdot> v = v"
proof-
  have "0 *\<cdot> v = (1 \<delta>\<delta> 0) \<cdot> v" using GmultD by fast
  moreover have "1 \<delta>\<delta> 0 = (1::('f,'g) aezfun)" using one_aezfun_transfer by fast
  ultimately have "0 *\<cdot> v = (1::('f,'g) aezfun) \<cdot> v" by simp
  with assms show ?thesis using one_smult by simp
qed

lemma Gmult_assoc :
  assumes "g \<in> G" "h \<in> G" "v \<in> V"
  shows   "g *\<cdot> h *\<cdot> v = (g + h) *\<cdot> v"
proof-
  define n where "n = (1::'f)"
  with assms have "g *\<cdot> h *\<cdot> v = ((n \<delta>\<delta> g) * (n \<delta>\<delta> h)) \<cdot> v"
    using FG_fddg_closed GmultD by simp
  moreover from n_def have "n \<delta>\<delta> g * (n \<delta>\<delta> h) = n \<delta>\<delta> (g + h)"
    using times_aezdeltafun_aezdeltafun[of n g n h] by simp
  ultimately show ?thesis using n_def GmultD by simp
qed

lemma Gmult_distrib_left :
  "\<lbrakk> g \<in> G; v \<in> V; v' \<in> V \<rbrakk> \<Longrightarrow> g *\<cdot> (v + v') = g *\<cdot> v + g *\<cdot> v'"
  using GmultD FG_fddg_closed by simp

lemma neg_Gmult : "g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> g *\<cdot> (- v) = - (g *\<cdot> v)"
  using GmultD FG_fddg_closed smult_neg by simp

lemma Gmult_neg_left : "g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> (- g) *\<cdot> g *\<cdot> v = v"
  using ActingGroup.neg_closed Gmult_assoc[of "- g" g] Gmult0 by simp

lemma fddg_smult_decomp : "g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> (f \<delta>\<delta> g) \<cdot> v = f \<sharp>\<cdot> g *\<cdot> v"
  using aezdeltafun_decomp[of f g] FG_fddg_closed FG_fdd0_closed GmultD
        fsmult_def
  by    simp

lemma sum_list_aezdeltafun_smult_distrib :
  assumes "v \<in> V" "set (map snd fgs) \<subseteq> G"
  shows   "(\<Sum>(f,g)\<leftarrow>fgs. f \<delta>\<delta> g) \<cdot> v = (\<Sum>(f,g)\<leftarrow>fgs. f \<sharp>\<cdot> g *\<cdot> v)"
proof-
  from assms(2) have "set (map (case_prod aezdeltafun) fgs) \<subseteq> FG"
    using FG_fddg_closed by auto
  with assms(1) have "(\<Sum>(f,g)\<leftarrow>fgs. f \<delta>\<delta> g) \<cdot> v =  (\<Sum>(f,g)\<leftarrow>fgs. (f \<delta>\<delta> g) \<cdot> v)"
    using sum_list_prod_map_smult_distrib by auto
  also have "\<dots> = (\<Sum>(f,g)\<leftarrow>fgs. f \<sharp>\<cdot> g *\<cdot> v)"
    using assms fddg_smult_decomp
          sum_list_prod_cong[of fgs "\<lambda> f g. (f \<delta>\<delta> g) \<cdot> v" "\<lambda> f g. f \<sharp>\<cdot> g *\<cdot> v"]
    by    fastforce
  finally show ?thesis by fast
qed

abbreviation "GSubspace \<equiv> RSubmodule"
abbreviation "GSpan     \<equiv> RSpan"
abbreviation "G_fingen  \<equiv> R_fingen"

lemma GSubspaceI : "FGModule G smult U \<Longrightarrow> U \<subseteq> V \<Longrightarrow> GSubspace U"
  using FGModule.axioms(2) by fast

lemma GSubspace_is_FGModule :
  assumes "GSubspace U"
  shows   "FGModule G smult U"
proof (rule FGModule.intro, rule GroupG)
  from assms show "RModule FG (\<cdot>) U" by fast
qed (unfold_locales)

lemma restriction_to_subgroup_is_module :
  fixes   H  :: "'g set"
  assumes subgrp: "Group.Subgroup G H"
  shows   "FGModule H smult V"
proof (rule FGModule.intro)
  from subgrp show "Group H" by fast
  from assms show "RModule (Group.group_ring H) (\<cdot>) V"
    using ActingGroup.Subgroup_imp_Subring SModule_restrict_scalars by fast
qed

lemma negGorbit_list_V :
  assumes "set gs \<subseteq> G" "T ` (set as) \<subseteq> V"
  shows   "set (concat (negGorbit_list gs T as)) \<subseteq> V"
proof-
  from assms(2)
    have  "set (concat (negGorbit_list gs T as)) \<subseteq> (\<Union>g\<in>set gs. (Gmult (-g)) ` V)"
    using set_concat negGorbit_list_def[of gs T as]
    by    force
  moreover from assms(1) have "\<And>g. g \<in> set gs \<Longrightarrow> (Gmult (-g)) ` V \<subseteq> V"
    using ActingGroup.neg_closed Gmult_closed by fast
  ultimately show ?thesis by fast    
qed

lemma negGorbit_list_Cons0 :
  "T ` (set as) \<subseteq> V
        \<Longrightarrow> negGorbit_list (0#gs) T as = (map T as) # (negGorbit_list gs T as)"
  using negGorbit_Cons[of 0 gs T as] Gmult0 by auto

end (* context FGModule *)

subsection \<open>Modules over a group ring as a vector spaces\<close>

context FGModule
begin

lemma fVectorSpace : "VectorSpace fsmult V"
proof (rule VectorSpaceI, unfold_locales)
  fix a::'f show "\<And>v. v \<in> V \<Longrightarrow> a \<sharp>\<cdot> v \<in> V"
    using fsmult_def smult_closed FG_fdd0_closed by simp
next
  fix a::'f show "\<And>u v. u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> a \<sharp>\<cdot> (u + v) = a \<sharp>\<cdot> u + a \<sharp>\<cdot> v"
    using fsmult_def FG_fdd0_closed by simp
next
  fix a b :: 'f and v :: 'v assume v: "v \<in> V"
  have "(a+b) \<sharp>\<cdot> v = (a \<delta>\<delta> 0 + b \<delta>\<delta> 0) \<cdot> v"
    using aezdeltafun_plus[of a b 0] arg_cong[of _ _ "\<lambda>r. r \<cdot> v"] fsmult_def by fastforce
  with v show "(a+b) \<sharp>\<cdot> v = a \<sharp>\<cdot> v + b \<sharp>\<cdot> v"
    using fsmult_def FG_fdd0_closed by simp
next
  fix a b :: 'f show "\<And>v. v \<in> V \<Longrightarrow> a \<sharp>\<cdot> (b \<sharp>\<cdot> v) = (a * b) \<sharp>\<cdot> v"
    using times_aezdeltafun_aezdeltafun[of a 0 b 0] arg_cong fsmult_def FG_fdd0_closed
    by    simp
next
  fix v :: 'v assume "v \<in> V" thus "1 \<sharp>\<cdot> v = v"
    using one_aezfun_transfer arg_cong[of "1 \<delta>\<delta> 0" 1 "\<lambda>a. a \<cdot> v"] fsmult_def by fastforce
qed

abbreviation "fSubspace  \<equiv> VectorSpace.Subspace fsmult V"
abbreviation "fbasis_for \<equiv> fscalar_mult.basis_for fsmult"
abbreviation "fdim       \<equiv> scalar_mult.dim fsmult V"

lemma VectorSpace_fSubspace : "fSubspace W \<Longrightarrow> VectorSpace fsmult W"
  using Module.intro VectorSpace.intro by fast

lemma fsmult_closed : "v \<in> V \<Longrightarrow> a \<sharp>\<cdot> v \<in> V"
  using FG_fdd0_closed smult_closed fsmult_def by simp

lemmas one_fsmult          [simp] = VectorSpace.one_smult   [OF fVectorSpace]
lemmas fsmult_assoc        [simp] = VectorSpace.smult_assoc [OF fVectorSpace]
lemmas fsmult_zero         [simp] = VectorSpace.smult_zero  [OF fVectorSpace]
lemmas fsmult_distrib_left [simp] = VectorSpace.smult_distrib_left
                                          [OF fVectorSpace]
lemmas flincomb_closed       = VectorSpace.lincomb_closed       [OF fVectorSpace]
lemmas fsmult_sum_distrib = VectorSpace.smult_sum_distrib [OF fVectorSpace]
lemmas sum_fsmult_distrib = VectorSpace.sum_smult_distrib [OF fVectorSpace]
lemmas flincomb_concat       = VectorSpace.lincomb_concat       [OF fVectorSpace]
lemmas fSpan_closed          = VectorSpace.Span_closed          [OF fVectorSpace]
lemmas flin_independentD_all_scalars
              = VectorSpace.lin_independentD_all_scalars[OF fVectorSpace]
lemmas in_fSpan_obtain_same_length_coeffs
              = VectorSpace.in_Span_obtain_same_length_coeffs [OF fVectorSpace]

lemma fsmult_smult_comm : "r \<in> FG \<Longrightarrow> v \<in> V \<Longrightarrow> a \<sharp>\<cdot> r \<cdot> v = r \<cdot> a \<sharp>\<cdot> v"
  using fsmultD FG_fdd0_closed smult_assoc aezdelta0fun_commutes[of r] by simp

lemma fsmult_Gmult_comm : "g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> a \<sharp>\<cdot> g *\<cdot> v = g *\<cdot> a \<sharp>\<cdot> v"
  using aezdeltafun_decomp[of a g] aezdeltafun_decomp'[of a g] FG_fddg_closed
        FG_fdd0_closed fsmult_def GmultD
  by    simp

lemma Gmult_flincomb_comm :
  assumes "g \<in> G" "set vs \<subseteq> V"
  shows   "g *\<cdot> as \<bullet>\<sharp>\<cdot> vs = as \<bullet>\<sharp>\<cdot> (map (Gmult g) vs)"
proof-
  have "g *\<cdot> as \<bullet>\<sharp>\<cdot> vs = (1 \<delta>\<delta> g) \<cdot> (\<Sum>(a,v)\<leftarrow>zip as vs. a \<sharp>\<cdot> v)"
    using Gmult_def scalar_mult.lincomb_def[of fsmult] by simp
  with assms have "g *\<cdot> as \<bullet>\<sharp>\<cdot> vs
                        = sum_list (map ((\<cdot>) (1 \<delta>\<delta> g) \<circ> (\<lambda>(x, y). x \<sharp>\<cdot> y)) (zip as vs))"
    using set_zip_rightD fsmult_closed FG_fddg_closed[of g "1::'f"]
          smult_sum_list_distrib[of "1 \<delta>\<delta> g" "map (case_prod (\<sharp>\<cdot>)) (zip as vs)"]
          map_map[of "(\<cdot>) (1 \<delta>\<delta> g)" "case_prod (\<sharp>\<cdot>)" "zip as vs"]
    by    fastforce
  moreover have "(\<cdot>) (1 \<delta>\<delta> g) \<circ> (\<lambda>(x, y). x \<sharp>\<cdot> y) = (\<lambda>(x,y). (1 \<delta>\<delta> g) \<cdot> (x \<sharp>\<cdot> y))"
    by auto
  ultimately have "g *\<cdot> as \<bullet>\<sharp>\<cdot> vs = sum_list (map (\<lambda>(x,y). g *\<cdot> x \<sharp>\<cdot> y) (zip as vs))"
    using Gmult_def by simp
  moreover from assms have "\<forall>(x,y) \<in> set (zip as vs). g *\<cdot> x \<sharp>\<cdot> y = x \<sharp>\<cdot> g *\<cdot> y"
    using set_zip_rightD fsmult_Gmult_comm by fastforce
  ultimately have "g *\<cdot> as \<bullet>\<sharp>\<cdot> vs
                        = sum_list (map (\<lambda>(x,y). x \<sharp>\<cdot> y) (zip as (map (Gmult g) vs)))"
    using sum_list_prod_cong sum_list_prod_map2[of "\<lambda>x y. x \<sharp>\<cdot> y" as "Gmult g"]
    by    force
  thus ?thesis using scalar_mult.lincomb_def[of fsmult] by simp
qed

lemma GSubspace_is_Subspace :
  "GSubspace U \<Longrightarrow> VectorSpace.Subspace fsmult V U"
  using GSubspace_is_FGModule FGModule.fVectorSpace VectorSpace.axioms
        Module.axioms
  by    fast


end (* context FGModule *)

subsection \<open>Homomorphisms of modules over a group ring\<close>

subsubsection \<open>Locales\<close>

locale FGModuleHom = ActingGroup?: Group G
+ RModHom?: RModuleHom ActingGroup.group_ring smult V smult' T
  for G      :: "'g::group_add set"
  and smult  :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and V      :: "'v set"
  and smult' :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and T      :: "'v \<Rightarrow> 'w"

sublocale FGModuleHom < FGModule ..

lemma (in FGModule) FGModuleHomI_fromaxioms :
  assumes "\<And>v v'. v \<in> V \<Longrightarrow> v' \<in> V \<Longrightarrow> T (v + v') = T v + T v'"
          "supp T \<subseteq> V" "\<And>r m. r \<in> FG \<Longrightarrow> m \<in> V \<Longrightarrow> T (r \<cdot> m) = smult' r (T m)"
  shows   "FGModuleHom G smult V smult' T"
  using   assms
  by      unfold_locales

locale FGModuleEnd = FGModuleHom G smult V smult T
  for G     :: "'g::group_add set"
  and FG    :: "('f::field,'g) aezfun set"
  and smult :: "('f, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and V     :: "'v set"
  and T     :: "'v \<Rightarrow> 'v"
+ assumes endomorph: "ImG \<subseteq> V"

locale FGModuleIso = FGModuleHom G smult V smult' T
  for   G      :: "'g::group_add set"
  and   smult  :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  and   V      :: "'v set"
  and   smult' :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and   T      :: "'v \<Rightarrow> 'w"
+ fixes W      :: "'w set"
  assumes bijective: "bij_betw T V W"

abbreviation (in FGModule) isomorphic ::
  "(('f,'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w) \<Rightarrow> 'w set \<Rightarrow> bool"
  where "isomorphic smult' W \<equiv> (\<exists> T. FGModuleIso G smult V smult' T W)"

subsubsection \<open>Basic facts\<close>

context FGModule
begin

lemma trivial_FGModuleHom :
  assumes "\<And>r. r \<in> FG \<Longrightarrow> smult' r 0 = 0"
  shows   "FGModuleHom G smult V smult' 0"
proof (rule FGModuleHom.intro)
  from assms show "RModuleHom FG (\<cdot>) V smult' 0"
    using trivial_RModuleHom by auto
qed (unfold_locales)

lemma FGModHom_idhom : "FGModuleHom G smult V smult (id\<down>V)"
proof (rule FGModuleHom.intro)
  show "RModuleHom FG smult V smult (id\<down>V)" using RModHom_idhom by fast
qed (unfold_locales)

lemma VecHom_GMap_is_FGModuleHom :
  fixes   smult'  :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     fsmult' :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70)
  and     Gmult'  :: "'g \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "*\<star>" 70)
  defines fsmult': "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
  and     Gmult' : "Gmult' \<equiv> aezfun_scalar_mult.Gmult smult'"
  assumes hom  : "VectorSpaceHom fsmult V fsmult' T"
  and     Im_W : "FGModule G smult' W" "T ` V \<subseteq> W"
  and     G_map : "\<And>g v. g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> T (g *\<cdot> v) = g *\<star> (T v)"
  shows   "FGModuleHom G smult V smult' T"
proof

  show "\<And>v v'. v \<in> V \<Longrightarrow> v' \<in> V \<Longrightarrow> T (v + v') = T v + T v'" 
    using VectorSpaceHom.GroupHom[OF hom] GroupHom.hom by auto

  from hom show "supp T \<subseteq> V" using VectorSpaceHom.supp by fast

  show "\<And>r v. r \<in> FG \<Longrightarrow> v \<in> V \<Longrightarrow> T (r \<cdot> v) = r \<star> T v"
  proof-
    fix r v assume r: "r \<in> FG" and v: "v \<in> V"
    from r obtain fgs
      where fgs: "set (map snd fgs) \<subseteq> G" "r = (\<Sum>(f,g)\<leftarrow>fgs. f \<delta>\<delta> g)"
      using FG_el_decomp
      by    fast
    from fgs v have "r \<cdot> v = (\<Sum>(f,g)\<leftarrow>fgs. f \<sharp>\<cdot> g *\<cdot> v)"
      using sum_list_aezdeltafun_smult_distrib by simp
    moreover from v fgs(1) have "set (map (\<lambda>(f,g). f \<sharp>\<cdot> g *\<cdot> v) fgs) \<subseteq> V"
      using Gmult_closed fsmult_closed by auto
    ultimately have "T (r \<cdot> v) = (\<Sum>(f,g)\<leftarrow>fgs. T (f \<sharp>\<cdot> g *\<cdot> v))"
      using hom VectorSpaceHom.im_sum_list_prod by auto
    moreover from hom G_map fgs(1) v
      have  "\<forall>(f,g) \<in> set fgs. T (f \<sharp>\<cdot> g *\<cdot> v) = f \<sharp>\<star> g *\<star> T v"
      using Gmult_closed VectorSpaceHom.f_map[of fsmult V fsmult' T]
      by    auto
    ultimately have "T (r \<cdot> v) = (\<Sum>(f,g)\<leftarrow>fgs. f \<sharp>\<star> g *\<star> T v)"
      using sum_list_prod_cong by simp
    with v fgs fsmult' Gmult' Im_W(2) show "T (r \<cdot> v) = r \<star> (T v)"
      using FGModule.sum_list_aezdeltafun_smult_distrib[OF Im_W(1)] by auto
  qed

qed

lemma VecHom_GMap_on_fbasis_is_FGModuleHom :
  fixes   smult'    :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     fsmult'   :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70)
  and     Gmult'    :: "'g \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "*\<star>" 70)
  and     flincomb' :: "'f list \<Rightarrow> 'w list \<Rightarrow> 'w" (infixr "\<bullet>\<sharp>\<star>" 70)
  defines fsmult'    : "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
  and     Gmult'     : "Gmult' \<equiv> aezfun_scalar_mult.Gmult smult'"
  and     flincomb'  : "flincomb' \<equiv> aezfun_scalar_mult.flincomb smult'"
  assumes fbasis     : "fbasis_for V vs"
  and     hom        : "VectorSpaceHom fsmult V fsmult' T"
  and     Im_W       : "FGModule G smult' W" "T ` V \<subseteq> W"
  and     G_map      : "\<And>g v. g \<in> G \<Longrightarrow> v \<in> set vs \<Longrightarrow> T (g *\<cdot> v) = g *\<star> (T v)"
  shows   "FGModuleHom G smult V smult' T"
proof (rule VecHom_GMap_is_FGModuleHom)
  from fsmult' hom
    show "VectorSpaceHom (\<sharp>\<cdot>) V (aezfun_scalar_mult.fsmult (\<star>)) T"
    by   fast
next
  fix g v assume g: "g \<in> G" and v: "v \<in> V"
  from v fbasis obtain cs where cs: "v = cs \<bullet>\<sharp>\<cdot> vs" 
    using VectorSpace.in_Span_obtain_same_length_coeffs[OF fVectorSpace] by fast
  with g(1) fbasis fsmult' flincomb'
    have  "T (g *\<cdot> v) = cs \<bullet>\<sharp>\<star> (map (T \<circ> (Gmult g)) vs)"
    using Gmult_flincomb_comm map_Gmult_closed
          VectorSpaceHom.distrib_lincomb[OF hom]
    by    auto
  moreover have "T \<circ> (Gmult g) = (\<lambda>v. T (g *\<cdot> v))" by auto
  ultimately have "T (g *\<cdot> v) = cs \<bullet>\<sharp>\<star> (map (\<lambda>v. g *\<star> (T v)) vs)"
    using fbasis g(1) G_map map_cong[of vs vs "\<lambda>v. T (g *\<cdot> v)"]
    by    simp
  moreover have "(\<lambda>v. g *\<star> (T v)) = (Gmult' g) \<circ> T" by auto
  ultimately have "T (g *\<cdot> v) = g *\<star> cs \<bullet>\<sharp>\<star> (map T vs)"
    using g(1) fbasis Im_W(2) Gmult' flincomb' 
          FGModule.Gmult_flincomb_comm[OF Im_W(1), of g "map T vs"]
    by    fastforce
  thus "T (g *\<cdot> v) = aezfun_scalar_mult.Gmult (\<star>) g (T v)"
    using fbasis fsmult' Gmult' flincomb' cs
          VectorSpaceHom.distrib_lincomb[OF hom]
    by auto
qed (rule Im_W(1), rule Im_W(2))

end (* context FGModule *)

context FGModuleHom
begin

abbreviation fsmult' :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70) 
  where "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
abbreviation Gmult' :: "'g \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "*\<star>" 70)
  where "Gmult' \<equiv> aezfun_scalar_mult.Gmult smult'"

lemmas supp                     = supp
lemmas additive                 = additive
lemmas FG_map                   = R_map
lemmas FG_fdd0_closed           = FG_fdd0_closed
lemmas fsmult_smult_domain_comm = fsmult_smult_comm
lemmas GSubspace_Ker            = RSubmodule_Ker
lemmas Ker_Im_iff               = Ker_Im_iff
lemmas Ker0_imp_inj_on          = Ker0_imp_inj_on
lemmas eq_im_imp_diff_in_Ker    = eq_im_imp_diff_in_Ker
lemmas im_submodule             = im_submodule
lemmas fsmultD'                 = aezfun_scalar_mult.fsmultD[of smult']
lemmas GmultD'                  = aezfun_scalar_mult.GmultD[of smult']

lemma f_map : "v \<in> V \<Longrightarrow> T (a \<sharp>\<cdot> v) = a \<sharp>\<star> T v"
  using fsmultD ActingGroup.RG_aezdelta0fun_closed[of a] FG_map fsmultD'
  by    simp

lemma G_map : "g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> T (g *\<cdot> v) = g *\<star> T v"
  using GmultD ActingGroup.RG_aezdeltafun_closed[of g 1] FG_map GmultD'
  by    simp

lemma VectorSpaceHom : "VectorSpaceHom fsmult V fsmult' T"
  by  (
        rule VectorSpace.VectorSpaceHomI, rule fVectorSpace, unfold_locales,
        rule f_map
      )

lemmas distrib_flincomb = VectorSpaceHom.distrib_lincomb[OF VectorSpaceHom]

lemma FGModule_Im : "FGModule G smult' ImG"
  by (rule FGModule.intro, rule GroupG, rule RModule_Im, unfold_locales)

lemma FGModHom_composite_left :
  assumes "FGModuleHom G smult' W smult'' S" "T ` V \<subseteq> W"
  shows   "FGModuleHom G smult V smult'' (S \<circ> T)"
proof (rule FGModuleHom.intro)
  from assms(2) show "RModuleHom FG smult V smult'' (S \<circ> T)"
    using FGModuleHom.axioms(2)[OF assms(1)] RModHom_composite_left[of W]
    by    fast
qed (rule GroupG, unfold_locales)

lemma restriction_to_subgroup_is_hom :
  fixes   H  :: "'g set"
  assumes subgrp: "Group.Subgroup G H"
  shows   "FGModuleHom H smult V smult' T"
proof (rule FGModule.FGModuleHomI_fromaxioms)
  have "FGModule G smult V" ..
  with assms show "FGModule H (\<cdot>) V"
    using FGModule.restriction_to_subgroup_is_module by fast
  from supp show "supp T \<subseteq> V" by fast
  from assms
    show  "\<And>r m. \<lbrakk> r \<in> (Group.group_ring H); m \<in> V \<rbrakk> \<Longrightarrow> T (r \<cdot> m) = r \<star> T m"
    using FG_map ActingGroup.Subgroup_imp_Subring by fast
qed (rule hom)

lemma FGModuleHom_restrict0_GSubspace :
  assumes "GSubspace U"
  shows   "FGModuleHom G smult U smult' (T \<down> U)"
proof (rule FGModuleHom.intro)
  from assms show "RModuleHom FG (\<cdot>) U (\<star>) (T \<down> U)"
    using RModuleHom_restrict0_submodule by fast
qed (unfold_locales)

lemma FGModuleHom_fscalar_mul :
  "FGModuleHom G smult V smult' (\<lambda>v. a \<sharp>\<star> T v)"
proof
  have vsphom: "VectorSpaceHom fsmult V fsmult' (\<lambda>v. a \<sharp>\<star> T v)"
    using VectorSpaceHom.VectorSpaceHom_scalar_mul[OF VectorSpaceHom]
    by    fast
  thus "\<And>v v'. v \<in> V \<Longrightarrow> v' \<in> V \<Longrightarrow> a \<sharp>\<star> T (v + v') = a \<sharp>\<star> T v + a \<sharp>\<star> T v'"
    using VectorSpaceHom.additive[of fsmult V] by auto
  from vsphom show "supp (\<lambda>v. a \<sharp>\<star> T v) \<subseteq> V"
    using VectorSpaceHom.supp by fast
next
  fix r v assume rv: "r \<in> FG" "v \<in> V"
  thus "a \<sharp>\<star> T (r \<cdot> v) = r \<star> a \<sharp>\<star> T v"
    using FG_map FGModule.fsmult_smult_comm[OF FGModule_Im] 
    by    auto
qed

end (* context FGModuleHom *)

lemma GSubspace_eigenspace :
  fixes   e     :: "'f::field"
  and     E     :: "'v::ab_group_add set"
  and     smult :: "('f::field, 'g::group_add) aezfun \<Rightarrow> 'v \<Rightarrow> 'v" (infixr "\<cdot>" 70)
  assumes FGModHom: "FGModuleHom G smult V smult T"
  defines E       : "E \<equiv> {v \<in> V. T v = aezfun_scalar_mult.fsmult smult e v}"
  shows   "FGModule.GSubspace G smult V E"
proof-
  have "FGModule.GSubspace G smult V {v \<in> V. T v = (e \<delta>\<delta> 0) \<cdot> v}"
    using FGModuleHom.axioms(2)[OF FGModHom]
  proof (rule RSubmodule_eigenspace)
    show "e \<delta>\<delta> 0 \<in> FGModule.FG G"
      using FGModuleHom.FG_fdd0_closed[OF FGModHom] by fast
    show "\<And>s v. s \<in> FGModule.FG G \<Longrightarrow> v \<in> V \<Longrightarrow> s \<cdot> (e \<delta>\<delta> 0) \<cdot> v = (e \<delta>\<delta> 0) \<cdot> s \<cdot> v"
      using FGModuleHom.fsmult_smult_domain_comm[OF FGModHom]
            aezfun_scalar_mult.fsmultD[of smult]
      by    simp
  qed
  with E show ?thesis using aezfun_scalar_mult.fsmultD[of smult] by simp
qed

subsubsection \<open>Basic facts about endomorphisms\<close>

lemma RModuleEnd_over_group_ring_is_FGModuleEnd :
  fixes   G     :: "'g::group_add set"
  and     smult :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
  assumes G : "Group G" and endo: "RModuleEnd (Group.group_ring G) smult V T"
  shows   "FGModuleEnd G smult V T"
proof (rule FGModuleEnd.intro, rule FGModuleHom.intro, rule G)
  from endo show "RModuleHom (Group.group_ring G) smult V smult T"
    using RModuleEnd.axioms(1) by fast
  from endo show "FGModuleEnd_axioms V T"
    using RModuleEnd.endomorph by unfold_locales
qed

lemma (in FGModule) VecEnd_GMap_is_FGModuleEnd :
  assumes endo : "VectorSpaceEnd fsmult V T"
  and     G_map: "\<And>g v. g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> T (g *\<cdot> v) = g *\<cdot> (T v)"
  shows   "FGModuleEnd G smult V T"
proof (rule FGModuleEnd.intro, rule VecHom_GMap_is_FGModuleHom)
  from endo show "VectorSpaceHom (\<sharp>\<cdot>) V (\<sharp>\<cdot>) T"
    using VectorSpaceEnd.axioms(1) by fast
  from endo show "T ` V \<subseteq> V" using VectorSpaceEnd.endomorph by fast
  from endo show "FGModuleEnd_axioms V T"
    using VectorSpaceEnd.endomorph by unfold_locales
qed (unfold_locales, rule G_map)

lemma (in FGModule) GEnd_inner_dirsum_el_decomp_nth :
  "\<lbrakk> \<forall>U\<in>set Us. GSubspace U; add_independentS Us; n < length Us \<rbrakk>
        \<Longrightarrow> FGModuleEnd G smult  (\<Oplus>U\<leftarrow>Us. U) (\<Oplus>Us\<down>n)"
  using GroupG RModuleEnd_inner_dirsum_el_decomp_nth
        RModuleEnd_over_group_ring_is_FGModuleEnd
  by    fast

context FGModuleEnd
begin

lemma RModuleEnd : "RModuleEnd ActingGroup.group_ring smult V T"
  using endomorph by unfold_locales

lemma VectorSpaceEnd : "VectorSpaceEnd fsmult V T"
  by  (
        rule VectorSpaceEnd.intro, rule VectorSpaceHom, unfold_locales,
        rule endomorph
      )

lemmas proj_decomp                     = RModuleEnd.proj_decomp[OF RModuleEnd]
lemmas GSubspace_Ker                   = GSubspace_Ker
lemmas FGModuleHom_restrict0_GSubspace = FGModuleHom_restrict0_GSubspace

end (* context FGModuleEnd *)

subsubsection \<open>Basic facts about isomorphisms\<close>

context FGModuleIso
begin

lemmas VectorSpaceHom = VectorSpaceHom

abbreviation "invT \<equiv> (the_inv_into V T) \<down> W"

lemma RModuleIso : "RModuleIso FG smult V smult' T W"
proof (rule RModuleIso.intro)
  show "RModuleHom FG (\<cdot>) V (\<star>) T"
    using FGModuleIso_axioms FGModuleIso.axioms(1) FGModuleHom.axioms(2)
    by    fast
qed (unfold_locales, rule bijective)

lemmas ImG = RModuleIso.ImG[OF RModuleIso]

lemma FGModuleIso_restrict0_GSubspace :
  assumes "GSubspace U"
  shows   "FGModuleIso G smult U smult' (T \<down> U) (T ` U)"
proof (rule FGModuleIso.intro)
  from assms show "FGModuleHom G (\<cdot>) U (\<star>) (T \<down> U)"
    using FGModuleHom_restrict0_GSubspace by fast
  show "FGModuleIso_axioms U (T \<down> U) (T ` U)"
  proof
    from assms bijective have "bij_betw T U (T ` U)"
      using subset_inj_on unfolding bij_betw_def by auto
    thus "bij_betw (T \<down> U) U (T ` U)" unfolding bij_betw_def inj_on_def by auto
  qed
qed

lemma inv : "FGModuleIso G smult' W smult invT V"
proof (rule FGModuleIso.intro, rule FGModuleHom.intro)
  show "RModuleHom FG (\<star>) W (\<cdot>) invT"
    using RModuleIso.inv[OF RModuleIso] RModuleIso.axioms(1) by fast
  show "FGModuleIso_axioms W invT V" 
    using RModuleIso.inv[OF RModuleIso] RModuleIso.bijective by unfold_locales
qed (unfold_locales)

lemma FGModIso_composite_left :
  assumes "FGModuleIso G smult' W smult'' S X"
  shows   "FGModuleIso G smult V smult'' (S \<circ> T) X"
proof (rule FGModuleIso.intro)
  from assms show "FGModuleHom G (\<cdot>) V smult'' (S \<circ> T)"
    using FGModuleIso.axioms(1) ImG FGModHom_composite_left by fast
  show "FGModuleIso_axioms V (S \<circ> T) X"
    using bijective FGModuleIso.bijective[OF assms] bij_betw_trans by unfold_locales
qed

lemma isomorphic_sym : "FGModule.isomorphic G smult' W smult V"
  using inv by fast

lemma isomorphic_trans :
  "FGModule.isomorphic G smult' W smult'' X
        \<Longrightarrow> FGModule.isomorphic G smult V smult'' X"
  using FGModIso_composite_left by fast

lemma isomorphic_to_zero_left : "V = 0 \<Longrightarrow> W = 0"
  using bijective bij_betw_imp_surj_on im_zero by fastforce

lemma isomorphic_to_zero_right : "W = 0 \<Longrightarrow> V = 0"
  using isomorphic_sym FGModuleIso.isomorphic_to_zero_left by fast

lemma isomorphic_to_irr_right' :
  assumes "\<And>U. FGModule.GSubspace G smult' W U \<Longrightarrow> U = 0 \<or> U = W"
  shows   "\<And>U. GSubspace U \<Longrightarrow> U = 0 \<or> U = V"
proof-
  fix U assume U: "GSubspace U"
  have "U \<noteq> V \<Longrightarrow> U = 0"
  proof-
    assume UV: "U \<noteq> V"
    from U bijective have "T ` U = T ` V \<Longrightarrow> U = V"
      using bij_betw_imp_inj_on[of T V W] inj_onD[of T V] by fast
    with UV bijective have "T ` U \<noteq> W" using bij_betw_imp_surj_on by fast
    moreover from U have "FGModule.GSubspace G smult' W (T ` U)"
      using ImG im_submodule by fast
    ultimately show "U = 0" 
      using assms U FGModuleIso_restrict0_GSubspace
            FGModuleIso.isomorphic_to_zero_right
      by    fast
  qed
  thus "U = 0 \<or> U = V" by fast
qed

end (* context FGModuleIso *)

context FGModule
begin

lemma isomorphic_sym :
  "isomorphic smult' W \<Longrightarrow> FGModule.isomorphic G smult' W smult V"
  using FGModuleIso.inv by fast

lemma isomorphic_trans : 
  "isomorphic smult' W \<Longrightarrow> FGModule.isomorphic G smult' W smult'' X
        \<Longrightarrow> isomorphic smult'' X"
  using FGModuleIso.FGModIso_composite_left by fast

lemma isomorphic_to_zero_left : "V = 0 \<Longrightarrow> isomorphic smult' W \<Longrightarrow> W = 0"
  using FGModuleIso.isomorphic_to_zero_left by fast

lemma isomorphic_to_zero_right : "isomorphic smult' 0 \<Longrightarrow> V = 0"
  using FGModuleIso.isomorphic_to_zero_right by fast

lemma FGModIso_idhom : "FGModuleIso G smult V smult (id\<down>V) V"
  using FGModHom_idhom
proof (rule FGModuleIso.intro)
  show "FGModuleIso_axioms V (id\<down>V) V"
    using bij_betw_id bij_betw_restrict0 by unfold_locales fast
qed

lemma isomorphic_refl : "isomorphic smult V" using FGModIso_idhom by fast

end (* context FGModule *)

subsubsection \<open>Hom-sets\<close>

definition FGModuleHomSet ::
  "'g::group_add set \<Rightarrow> (('f::field,'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow> 'v set
        \<Rightarrow> (('f,'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w) \<Rightarrow> 'w set
        \<Rightarrow> ('v \<Rightarrow> 'w) set"
  where "FGModuleHomSet G fgsmult V fgsmult' W
              \<equiv> {T. FGModuleHom G fgsmult V fgsmult' T} \<inter> {T. T ` V \<subseteq> W}"

lemma FGModuleHomSetI :
  "FGModuleHom G fgsmult V fgsmult' T \<Longrightarrow> T ` V \<subseteq> W
        \<Longrightarrow> T \<in> FGModuleHomSet G fgsmult V fgsmult' W"
  unfolding FGModuleHomSet_def by fast

lemma FGModuleHomSetD_FGModuleHom :
  "T \<in> FGModuleHomSet G fgsmult V fgsmult' W
        \<Longrightarrow> FGModuleHom G fgsmult V fgsmult' T"
  unfolding FGModuleHomSet_def by fast

lemma FGModuleHomSetD_Im :
  "T \<in> FGModuleHomSet G fgsmult V fgsmult' W \<Longrightarrow> T ` V \<subseteq> W"
  unfolding FGModuleHomSet_def by fast

context FGModule
begin

lemma FGModuleHomSet_is_Gmaps_in_VectorSpaceHomSet :
  fixes   smult'  :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     fsmult' :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70)
  and     Gmult'  :: "'g \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "*\<star>" 70)
  defines fsmult'  : "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
  and     Gmult'   : "Gmult' \<equiv> aezfun_scalar_mult.Gmult smult'"
  assumes FGModW   : "FGModule G smult' W"
  shows   "FGModuleHomSet G smult V smult' W
                = (VectorSpaceHomSet fsmult V fsmult' W)
                  \<inter> {T. \<forall>g\<in>G. \<forall>v\<in>V. T (g *\<cdot> v) = g *\<star> (T v)}"
proof
  from fsmult' Gmult'
    show  "FGModuleHomSet G smult V smult' W
                \<subseteq> (VectorSpaceHomSet fsmult V fsmult' W)
                  \<inter> {T. \<forall>g\<in>G. \<forall>v\<in>V. T (g *\<cdot> v) = g *\<star> T v}"
    using FGModuleHomSetD_FGModuleHom[of _ G smult V smult']
          FGModuleHom.VectorSpaceHom[of G smult V smult'] 
          FGModuleHomSetD_Im[of _ G smult V smult']
          VectorSpaceHomSetI[of fsmult V fsmult']
          FGModuleHom.G_map[of G smult V smult']
    by    auto
  show "FGModuleHomSet G smult V smult' W
              \<supseteq> (VectorSpaceHomSet fsmult V fsmult' W)
                \<inter> {T. \<forall>g\<in>G. \<forall>v\<in>V. T (g *\<cdot> v) = g *\<star> T v}"
  proof
    fix T
    assume T: "T \<in> (VectorSpaceHomSet fsmult V fsmult' W)
                    \<inter> {T. \<forall>g\<in>G. \<forall>v\<in>V. T (g *\<cdot> v) = g *\<star> T v}"
    show "T \<in> FGModuleHomSet G smult V smult' W"
    proof (rule FGModuleHomSetI, rule VecHom_GMap_is_FGModuleHom)
      from T fsmult'
        show  "VectorSpaceHom (\<sharp>\<cdot>) V (aezfun_scalar_mult.fsmult smult') T"
        using VectorSpaceHomSetD_VectorSpaceHom
        by    fast
      from T show "T ` V \<subseteq> W" using VectorSpaceHomSetD_Im by fast
      from T Gmult' 
        show  "\<And>g v. g \<in> G \<Longrightarrow> v \<in> V
                    \<Longrightarrow> T (g *\<cdot> v) = aezfun_scalar_mult.Gmult (\<star>) g (T v)" 
        by    fast
      from T show "T ` V \<subseteq> W" using VectorSpaceHomSetD_Im by fast
    qed (rule FGModW)
  qed
qed

lemma Group_FGModuleHomSet :
  fixes   smult'  :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     fsmult' :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70)
  and     Gmult'  :: "'g \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "*\<star>" 70)
  defines fsmult'  : "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
  and     Gmult'   : "Gmult' \<equiv> aezfun_scalar_mult.Gmult smult'"
  assumes FGModW   : "FGModule G smult' W"
  shows   "Group (FGModuleHomSet G smult V smult' W)"
proof
  from FGModW show "FGModuleHomSet G (\<cdot>) V smult' W \<noteq> {}"
    using FGModule.smult_zero trivial_FGModuleHom[of smult'] FGModule.zero_closed
          FGModuleHomSetI
    by    fastforce
next
  fix S T
  assume S: "S \<in> FGModuleHomSet G (\<cdot>) V smult' W"
    and  T: "T \<in> FGModuleHomSet G (\<cdot>) V smult' W"
  with assms
    have  ST: "S \<in> (VectorSpaceHomSet fsmult V fsmult' W)
                    \<inter> {T. \<forall>g\<in>G. \<forall>v\<in>V. T (g *\<cdot> v) = g *\<star> T v}"
              "T \<in> (VectorSpaceHomSet fsmult V fsmult' W)
                    \<inter> {T. \<forall>g\<in>G. \<forall>v\<in>V. T (g *\<cdot> v) = g *\<star> T v}"
    using FGModuleHomSet_is_Gmaps_in_VectorSpaceHomSet
    by    auto
  with fsmult' have "S - T \<in> VectorSpaceHomSet fsmult V fsmult' W"
    using FGModule.fVectorSpace[OF FGModW]
          VectorSpace.Group_VectorSpaceHomSet[OF fVectorSpace] Group.diff_closed
    by    fast
  moreover have "\<And>g v. g\<in>G \<Longrightarrow> v\<in>V \<Longrightarrow> (S-T) (g *\<cdot> v) = g *\<star> ((S-T) v)"
  proof-
    fix g v assume "g \<in> G" "v \<in> V"
    moreover with ST have "S v \<in> W" "T v \<in> W" "- T v \<in> W"
      using VectorSpaceHomSetD_Im[of S fsmult V fsmult']
            VectorSpaceHomSetD_Im[of T fsmult V fsmult']
            FGModule.neg_closed[OF FGModW]
      by    auto
    ultimately show "(S-T) (g *\<cdot> v) = g *\<star> ((S-T) v)"
      using ST Gmult' FGModule.neg_Gmult[OF FGModW]
            FGModule.Gmult_distrib_left[OF FGModW, of g "S v" "- T v"]
      by    auto
  qed
  ultimately show "S - T \<in> FGModuleHomSet G (\<cdot>) V smult' W"
    using fsmult' Gmult'
          FGModuleHomSet_is_Gmaps_in_VectorSpaceHomSet[OF FGModW]
    by    fast
qed

lemma Subspace_FGModuleHomSet :
  fixes   smult'     :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     fsmult'    :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70)
  and     Gmult'     :: "'g \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "*\<star>" 70)
  and     hom_fsmult :: "'f \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('v \<Rightarrow> 'w)" (infixr "\<sharp>\<star>\<cdot>" 70)
  defines fsmult'     : "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
  and     Gmult'      : "Gmult' \<equiv> aezfun_scalar_mult.Gmult smult'"
  defines hom_fsmult  : "hom_fsmult \<equiv> \<lambda>a T v. a \<sharp>\<star> T v"
  assumes FGModW      : "FGModule G smult' W"
  shows   "VectorSpace.Subspace hom_fsmult
                (VectorSpaceHomSet fsmult V fsmult' W)
                  (FGModuleHomSet G smult V smult' W)"
proof (rule VectorSpace.SubspaceI)
  from hom_fsmult fsmult'
    show  "VectorSpace (\<sharp>\<star>\<cdot>) (VectorSpaceHomSet (\<sharp>\<cdot>) V (\<sharp>\<star>) W)"
    using FGModule.fVectorSpace[OF FGModW]
          VectorSpace.VectorSpace_VectorSpaceHomSet[OF fVectorSpace]
    by    fast
  from fsmult' Gmult' FGModW
    show  "Group (FGModuleHomSet G (\<cdot>) V (\<star>) W)
                \<and> FGModuleHomSet G (\<cdot>) V (\<star>) W
                  \<subseteq> VectorSpaceHomSet (\<sharp>\<cdot>) V (\<sharp>\<star>) W"
    using Group_FGModuleHomSet FGModuleHomSet_is_Gmaps_in_VectorSpaceHomSet
    by    fast
next
  fix a T assume T: "T \<in> FGModuleHomSet G (\<cdot>) V (\<star>) W"
  from hom_fsmult fsmult' have "FGModuleHom G smult V smult' (a \<sharp>\<star>\<cdot> T)"
    using FGModuleHomSetD_FGModuleHom[OF T]
          FGModuleHomSetD_Im[OF T] 
          FGModuleHom.FGModuleHom_fscalar_mul
    by    simp
  moreover from hom_fsmult fsmult' have "(a \<sharp>\<star>\<cdot> T) ` V \<subseteq> W"
    using FGModuleHomSetD_Im[OF T] FGModule.fsmult_closed[OF FGModW]
    by    auto
  ultimately show "a \<sharp>\<star>\<cdot> T \<in> FGModuleHomSet G (\<cdot>) V (\<star>) W"
    using FGModuleHomSetI by fastforce
qed

lemma VectorSpace_FGModuleHomSet :
  fixes   smult'     :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and     fsmult'    :: "'f \<Rightarrow> 'w \<Rightarrow> 'w" (infixr "\<sharp>\<star>" 70)
  and     hom_fsmult :: "'f \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('v \<Rightarrow> 'w)" (infixr "\<sharp>\<star>\<cdot>" 70)
  defines "fsmult' \<equiv> aezfun_scalar_mult.fsmult smult'"
  defines "hom_fsmult \<equiv> \<lambda>a T v. a \<sharp>\<star> T v"
  assumes "FGModule G smult' W"
  shows   "VectorSpace hom_fsmult (FGModuleHomSet G smult V smult' W)"
  using   assms Subspace_FGModuleHomSet Module.intro VectorSpace.intro
  by      fast

end (* context FGModule *)

subsection \<open>Induced modules\<close>

subsubsection \<open>Additive function spaces\<close>

definition addfunset ::
  "'a::monoid_add set \<Rightarrow> 'm::monoid_add set \<Rightarrow> ('a \<Rightarrow> 'm) set"
  where "addfunset A M \<equiv> {f. supp f \<subseteq> A \<and> range f \<subseteq> M
              \<and> (\<forall>x\<in>A. \<forall>y\<in>A. f (x+y) = f x + f y) }"

lemma addfunsetI :
  "\<lbrakk> supp f \<subseteq> A; range f \<subseteq> M; \<forall>x\<in>A. \<forall>y\<in>A. f (x+y) = f x + f y \<rbrakk>
        \<Longrightarrow> f \<in> addfunset A M"
  unfolding addfunset_def by fast

lemma addfunsetD_supp : "f \<in> addfunset A M \<Longrightarrow> supp  f \<subseteq> A"
  unfolding addfunset_def by fast

lemma addfunsetD_range : "f \<in> addfunset A M \<Longrightarrow> range f \<subseteq> M"
  unfolding addfunset_def by fast

lemma addfunsetD_range' : "f \<in> addfunset A M \<Longrightarrow> f x \<in> M"
  using addfunsetD_range by fast

lemma addfunsetD_add :
  "\<lbrakk> f \<in> addfunset A M; x\<in>A; y\<in>A \<rbrakk> \<Longrightarrow> f (x+y) = f x + f y"
  unfolding addfunset_def by fast

lemma addfunset0 : "addfunset A (0::'m::monoid_add set) = 0"
proof
  show "addfunset A 0 \<subseteq> 0" using addfunsetD_range' by fastforce
  have "(0::'a\<Rightarrow>'m) \<in> addfunset A 0"
    using supp_zerofun_subset_any by (rule addfunsetI) auto
  thus "addfunset A (0::'m::monoid_add set) \<supseteq> 0" by simp
qed

lemma Group_addfunset :
  fixes   M::"'g::ab_group_add set"
  assumes "Group M"
  shows   "Group (addfunset R M)"
proof
  from assms show "addfunset R M \<noteq> {}"
    using addfunsetI[of 0 R M] supp_zerofun_subset_any Group.zero_closed
    by    fastforce
next
  fix g h assume gh: "g \<in> addfunset R M" "h \<in> addfunset R M"
  show "g - h \<in> addfunset R M"
  proof (rule addfunsetI)
    from gh show "supp (g - h) \<subseteq> R"
      using addfunsetD_supp supp_diff_subset_union_supp by fast
    from gh show "range (g - h) \<subseteq> M"
      using addfunsetD_range Group.diff_closed [OF assms]
        by (simp add: addfunsetD_range' image_subsetI)
    show "\<forall>x\<in>R. \<forall>y\<in>R. (g - h) (x + y) = (g - h) x + (g - h) y"
      using addfunsetD_add[OF gh(1)] addfunsetD_add[OF gh(2)] by simp
  qed
qed

subsubsection \<open>Spaces of functions which transform under scalar multiplication by
                 almost-everywhere-zero functions\<close>

context aezfun_scalar_mult
begin

definition smultfunset :: "'g set \<Rightarrow> ('r,'g) aezfun set \<Rightarrow> (('r,'g) aezfun \<Rightarrow> 'v) set"
  where "smultfunset G FH \<equiv> {f. (\<forall>a::'r. \<forall>g\<in>G. \<forall>x\<in>FH.
              f ( a \<delta>\<delta> g * x ) = (a \<delta>\<delta> g) \<cdot> (f x))}"

lemma smultfunsetD :
  "\<lbrakk>f \<in> smultfunset G FH; g\<in>G; x\<in>FH \<rbrakk> \<Longrightarrow> f ( a \<delta>\<delta> g * x ) = (a \<delta>\<delta> g) \<cdot> (f x)"
  unfolding smultfunset_def by fast

lemma smultfunsetI : 
  "\<forall>a::'r. \<forall>g\<in>G. \<forall>x\<in>FH. f ( a \<delta>\<delta> g * x ) = (a \<delta>\<delta> g) \<cdot> (f x)
        \<Longrightarrow> f \<in> smultfunset G FH"
  unfolding smultfunset_def by fast

end (* context aezfun_scalar_mult *)

subsubsection \<open>General induced spaces of functions on a group ring\<close>

context aezfun_scalar_mult
begin

definition indspace ::
  "'g set \<Rightarrow> ('r,'g) aezfun set \<Rightarrow> 'v set \<Rightarrow> (('r,'g) aezfun \<Rightarrow> 'v) set"
  where "indspace G FH V = addfunset FH V \<inter> smultfunset G FH"

lemma indspaceD :
  "f \<in> indspace G FH V \<Longrightarrow> f \<in> addfunset FH V \<inter> smultfunset G FH"
  using indspace_def by fast

lemma indspaceD_supp : "f \<in> indspace G FH V \<Longrightarrow> supp  f \<subseteq> FH"
  using indspace_def addfunsetD_supp by fast

lemma indspaceD_supp' : "f \<in> indspace G FH V \<Longrightarrow> x \<notin> FH \<Longrightarrow> f x = 0"
  using indspaceD_supp suppI_contra by fast

lemma indspaceD_range : "f \<in> indspace G FH V \<Longrightarrow> range f \<subseteq> V"
  using indspace_def addfunsetD_range by fast

lemma indspaceD_range': "f \<in> indspace G FH V \<Longrightarrow> f x \<in> V"
  using indspaceD_range by fast

lemma indspaceD_add :
  "\<lbrakk> f \<in> indspace G FH V; x\<in>FH; y\<in>FH \<rbrakk> \<Longrightarrow> f (x+y) = f x + f y"
  using indspace_def addfunsetD_add by auto

lemma indspaceD_transform : 
  "\<lbrakk>f \<in> indspace G FH V; g\<in>G; x\<in>FH \<rbrakk> \<Longrightarrow> f ( a \<delta>\<delta> g * x ) = (a \<delta>\<delta> g) \<cdot> (f x)"
  using indspace_def smultfunsetD by auto

lemma indspaceI :
  "f \<in> addfunset FH V \<Longrightarrow> f \<in> smultfunset G FH \<Longrightarrow> f \<in> indspace G FH V"
  using indspace_def by fast

lemma indspaceI' :
  "\<lbrakk> supp f \<subseteq> FH; range f \<subseteq> V; \<forall>x\<in>FH. \<forall>y\<in>FH. f (x+y) = f x + f y;
                \<forall>a::'r. \<forall>g\<in>G. \<forall>x\<in>FH. f ( a \<delta>\<delta> g * x ) = (a \<delta>\<delta> g) \<cdot> (f x) \<rbrakk>
                  \<Longrightarrow> f \<in> indspace G FH V"
  using smultfunsetI addfunsetI[of f] indspaceI by simp

lemma mono_indspace : "mono (indspace G FH)"
proof (rule monoI)
  fix U V :: "'v set" assume U_V: "U \<subseteq> V"
  show "indspace G FH U \<subseteq> indspace G FH V"
  proof
    fix f assume f: "f \<in> indspace G FH U"
    show "f \<in> indspace G FH V" using indspaceD_supp[OF f]
    proof (rule indspaceI')
      from f U_V show "range f \<subseteq> V" using indspaceD_range[of f G FH] by auto
      from f show "\<forall>x\<in>FH. \<forall>y\<in>FH. f (x+y) = f x + f y"
        using indspaceD_add by auto
      from f show "\<forall>a::'r. \<forall>g\<in>G. \<forall>x\<in>FH. f ( a \<delta>\<delta> g * x ) = (a \<delta>\<delta> g) \<cdot> (f x)" 
        using indspaceD_transform by auto
    qed
  qed
qed

end (* context aezfun_scalar_mult *)

context FGModule
begin

lemma zero_transforms : "0 \<in> smultfunset G FH"
  using smultfunsetI FG_fddg_closed smult_zero by simp

lemma indspace0 : "indspace G FH 0 = 0"
  using zero_transforms addfunset0 indspace_def by auto

lemma Group_indspace :
  assumes "Ring1 FH"
  shows   "Group (indspace G FH V)"
proof
  from zero_closed have "0 \<subseteq> V" by simp
  with mono_indspace [of G FH]
  have "indspace G FH 0 \<subseteq> indspace G FH V"
    by (auto dest!: monoD [of _ 0 V])
  then show "indspace G FH V \<noteq> {}"
    using indspace0 [of FH] by auto
next
  fix f1 f2 assume ff: "f1 \<in> indspace G FH V" "f2 \<in> indspace G FH V"
  hence "f1 - f2 \<in> addfunset FH V"
    using assms indspaceD indspaceD Group Group_addfunset Group.diff_closed
    by    fast
  moreover from ff have "f1 - f2 \<in> smultfunset G FH"
    using indspaceD_transform FG_fddg_closed indspaceD_range' smult_distrib_left_diff
          smultfunsetI
    by    simp
  ultimately show "f1 - f2 \<in> indspace G FH V" using indspaceI by fast
qed

end (* context FGModule *)

subsubsection \<open>The right regular action\<close>

context Ring1
begin

definition rightreg_scalar_mult :: 
  "'r::ring_1 \<Rightarrow> ('r \<Rightarrow> 'm::ab_group_add) \<Rightarrow> ('r \<Rightarrow> 'm)" (infixr "\<currency>" 70)
  where "rightreg_scalar_mult r f = (\<lambda>x. if x \<in> R then f (x*r) else 0)"

lemma rightreg_scalar_multD1 : "x \<in> R \<Longrightarrow> (r \<currency> f) x = f (x*r)"
  unfolding rightreg_scalar_mult_def by simp

lemma rightreg_scalar_multD2 : "x \<notin> R \<Longrightarrow> (r \<currency> f) x = 0"
  unfolding rightreg_scalar_mult_def by simp

lemma rrsmult_supp : "supp (r \<currency> f) \<subseteq> R"
  using rightreg_scalar_multD2 suppD_contra by force

lemma rrsmult_range : "range (r \<currency> f) \<subseteq> {0} \<union> range f"
proof (rule image_subsetI)
  fix x show "(r \<currency> f) x \<in> {0} \<union> range f"
    using rightreg_scalar_multD1[of x r f] image_eqI
          rightreg_scalar_multD2[of x r f]
    by    (cases "x \<in> R") auto
qed

lemma rrsmult_distrib_left : "r \<currency> (f + g) = r \<currency> f + r \<currency> g"
proof
  fix x show "(r \<currency> (f + g)) x = (r \<currency> f + r \<currency> g) x"
    unfolding rightreg_scalar_mult_def by (cases "x \<in> R") auto
qed

lemma rrsmult_distrib_right :
  assumes "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> f (x+y) = f x + f y" "r \<in> R" "s \<in> R"
  shows   "(r + s) \<currency> f = r \<currency> f + s \<currency> f"
proof
  fix x show "((r + s) \<currency> f) x = (r \<currency> f + s \<currency> f) x"
    using     assms mult_closed
    unfolding rightreg_scalar_mult_def
    by        (cases "x \<in> R") (auto simp add: distrib_left)
qed

lemma RModule_addfunset :
  fixes   M::"'g::ab_group_add set"
  assumes "Group M"
  shows   "RModule R rightreg_scalar_mult (addfunset R M)"
proof (rule RModuleI)

  from assms show "Group (addfunset R M)" using Group_addfunset by fast

  show "RModule_axioms R (\<currency>) (addfunset R M)"
  proof
    fix r f assume r: "r \<in> R" and f: "f \<in> addfunset R M"
    show "r \<currency> f \<in> addfunset R M"
    proof (rule addfunsetI)
      show "supp (r \<currency> f) \<subseteq> R"
        using rightreg_scalar_multD2 suppD_contra by force
      show "range (r \<currency> f) \<subseteq> M"
        using     addfunsetD_range[OF f] Group.zero_closed[OF assms]
        unfolding rightreg_scalar_mult_def
        by        fastforce
      from r show "\<forall>x\<in>R. \<forall>y\<in>R. (r \<currency> f) (x + y) = (r \<currency> f) x + (r \<currency> f) y"
        using     mult_closed add_closed addfunsetD_add[OF f]
        unfolding rightreg_scalar_mult_def
        by        (simp add: distrib_right)
    qed
  next
    show "\<And>r f g. r \<currency> (f + g) = r \<currency> f + r \<currency> g" using rrsmult_distrib_left by fast
  next
    fix r s f assume "r \<in> R" "s \<in> R" "f \<in> addfunset R M"
    thus "(r + s) \<currency> f = r \<currency> f + s \<currency> f"
      using addfunsetD_add[of f] rrsmult_distrib_right[of f] by simp
  next
    fix r s f assume r: "r \<in> R" and s: "s \<in> R" and f: "f \<in> addfunset R M"
    show "r \<currency> s \<currency> f = (r * s) \<currency> f"
    proof
      fix x from r show "(r \<currency> s \<currency> f) x = ((r * s) \<currency> f) x"
        using mult_closed unfolding rightreg_scalar_mult_def
        by    (cases "x \<in> R") (auto simp add: mult.assoc)
    qed
  next
    fix f assume f: "f \<in> addfunset R M"
    show "1 \<currency> f = f"
    proof
      fix x show "(1 \<currency> f) x = f x"
        unfolding rightreg_scalar_mult_def 
        using     addfunsetD_supp[OF f] suppI_contra[of x f]
                  contra_subsetD[of "supp f"]
        by        (cases "x \<in> R") auto
    qed
  qed

qed (unfold_locales)

end (* context Ring1 *)

subsubsection \<open>Locale and basic facts\<close>

text \<open>
  In the following locale, @{term G} is a subgroup of @{term H}, @{term V} is a module over the
  group ring for @{term G}, and the induced space @{term indV} will be shown to be a module over the
  group ring for @{term H} under the right regular scalar multiplication @{term rrsmult}.
\<close>

locale InducedFHModule = Supgroup?: Group H
+ BaseFGMod?    : FGModule G smult V
+ induced_smult?: aezfun_scalar_mult rrsmult
  for   H       :: "'g::group_add set"
  and   G       :: "'g set"
  and   FG      :: "('f::field, 'g) aezfun set"
  and   smult   :: "('f, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixl "\<cdot>" 70)
  and   V       :: "'v set"
  and   rrsmult :: "('f,'g) aezfun \<Rightarrow> (('f,'g) aezfun \<Rightarrow> 'v) \<Rightarrow> (('f,'g) aezfun \<Rightarrow> 'v)"
                                                                                    (infixl "\<currency>" 70)
+ fixes FH      :: "('f, 'g) aezfun set"
  and   indV    :: "(('f, 'g) aezfun \<Rightarrow> 'v) set"
  defines FH      : "FH \<equiv> Supgroup.group_ring"
  and     indV    : "indV \<equiv> BaseFGMod.indspace G FH V"
  assumes rrsmult : "rrsmult = Ring1.rightreg_scalar_mult FH"
  and     Subgroup: "Supgroup.Subgroup G"  (* G is a subgroup of H *)
begin

abbreviation indfsmult ::
  "'f \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v) \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v)" (infixl "\<currency>\<currency>" 70)
  where "indfsmult \<equiv> induced_smult.fsmult"
abbreviation indflincomb ::
  "'f list \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v) list \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v)" (infixl "\<bullet>\<currency>\<currency>" 70)
  where "indflincomb \<equiv> induced_smult.flincomb"
abbreviation Hmult ::
  "'g \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v) \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v)" (infixl "*\<currency>" 70)
  where "Hmult \<equiv> induced_smult.Gmult"

lemma Ring1_FH : "Ring1 FH" using FH Supgroup.Ring1_RG by fast

lemma FG_subring_FH : "Ring1.Subring1 FH BaseFGMod.FG"
  using FH Supgroup.Subgroup_imp_Subring[OF Subgroup] by fast

lemma rrsmultD1 : "x \<in> FH \<Longrightarrow> (r \<currency> f) x = f (x*r)"
  using Ring1.rightreg_scalar_multD1[OF Ring1_FH] rrsmult by simp

lemma rrsmultD2 : "x \<notin> FH \<Longrightarrow> (r \<currency> f) x = 0"
  using Ring1.rightreg_scalar_multD2[OF Ring1_FH] rrsmult by fast

lemma rrsmult_supp : "supp (r \<currency> f) \<subseteq> FH"
  using Ring1.rrsmult_supp[OF Ring1_FH] rrsmult by auto

lemma rrsmult_range : "range (r \<currency> f) \<subseteq> {0} \<union> range f"
  using Ring1.rrsmult_range[OF Ring1_FH] rrsmult by auto

lemma FHModule_addfunset : "FGModule H rrsmult (addfunset FH V)"
proof (rule FGModule.intro)
  from FH rrsmult show "RModule Supgroup.group_ring (\<currency>) (addfunset FH V)"
    using Group Supgroup.Ring1_RG Ring1.RModule_addfunset by fast
qed (unfold_locales)

lemma FHSubmodule_indspace :
  "FGModule.FGSubmodule H rrsmult (addfunset FH V) indV"
proof (rule FGModule.FGSubmoduleI[of H], rule FHModule_addfunset, rule conjI)
  from Ring1_FH indV show "Group indV" using Group_indspace by fast
  from indV show "indV \<subseteq> addfunset FH V"
    using BaseFGMod.indspaceD by fast
next
  fix r f assume rf: "r \<in> (Supgroup.group_ring :: ('f,'g) aezfun set)" "f \<in> indV"
  from rf(2) indV have rf2': "f \<in> BaseFGMod.indspace G FH V" by fast
  show "r \<currency> f \<in> indV"
    unfolding indV
  proof (rule BaseFGMod.indspaceI', rule rrsmult_supp)
    show "range (r \<currency> f) \<subseteq> V"
      using rrsmult_range BaseFGMod.indspaceD_range[OF rf2'] zero_closed
      by    force
    from FH rf(1) rf2'
      show  "\<forall>x\<in>FH. \<forall>y\<in>FH. (r \<currency> f) (x + y) = (r \<currency> f) x + (r \<currency> f) y"
      using Ring1.add_closed[OF Ring1_FH] rrsmultD1[of _ r f]
            Ring1.mult_closed[OF Ring1_FH] BaseFGMod.indspaceD_add
      by    (simp add: distrib_right)
    {
      fix a g x assume gx: "g\<in>G" "x\<in>FH"
      with FH have "a \<delta>\<delta> g * x \<in> FH"
        using FG_fddg_closed FG_subring_FH Ring1.mult_closed[OF Ring1_FH]
        by    fast
      with FH rf(1) gx(2) have "(r \<currency> f) (a \<delta>\<delta> g * x) = a \<delta>\<delta> g \<cdot> ((r \<currency> f) x)"
        using rrsmultD1[of _ r f] Ring1.mult_closed[OF Ring1_FH] 
              BaseFGMod.indspaceD_transform[OF rf2' gx(1)]
        by    (simp add: mult.assoc)
    }
    thus "\<forall>a. \<forall>g\<in>G. \<forall>x\<in>FH. (r \<currency> f) (a \<delta>\<delta> g * x) = a \<delta>\<delta> g \<cdot> (r \<currency> f) x" by fast
  qed
qed

lemma FHModule_indspace : "FGModule H rrsmult indV"
proof (rule FGModule.intro)
  show "RModule Supgroup.group_ring (\<currency>) indV" using FHSubmodule_indspace by fast
qed (unfold_locales)

lemmas fVectorSpace_indspace = FGModule.fVectorSpace[OF FHModule_indspace]
lemmas restriction_is_FGModule
              = FGModule.restriction_to_subgroup_is_module[OF FHModule_indspace]

definition induced_vector :: "'v \<Rightarrow> (('f, 'g) aezfun \<Rightarrow> 'v)"
  where "induced_vector v \<equiv> (if v \<in> V
              then (\<lambda>y. if y \<in> FH then (FG_proj y) \<cdot> v else 0) else 0)"

lemma induced_vector_apply1 :
  "v \<in> V \<Longrightarrow> x \<in> FH \<Longrightarrow> induced_vector v x = (FG_proj x) \<cdot> v"
  using induced_vector_def by simp

lemma induced_vector_apply2 : "v \<in> V \<Longrightarrow> x \<notin> FH \<Longrightarrow> induced_vector v x = 0"
  using induced_vector_def by simp

lemma induced_vector_indV :
  assumes v: "v \<in> V"
  shows   "induced_vector v \<in> indV"
  unfolding indV 
proof (rule BaseFGMod.indspaceI')

  from assms show "supp (induced_vector v) \<subseteq> FH"
    using induced_vector_def supp_restrict0[of FH "\<lambda>y. (FG_proj y) \<cdot> v"] by simp

  show "range (induced_vector v) \<subseteq> V"
  proof (rule image_subsetI)
    fix y
    from v show "(induced_vector v) y \<in> V"
      using     induced_vector_def zero_closed aezfun_setspan_proj_in_setspan[of G y]
                smult_closed ActingGroup.group_ringD
      by        auto
  qed

  {
    fix x y assume xy: "x \<in> FH" "y \<in> FH"
    with v have "(induced_vector v) (x + y)
                      = (induced_vector v) x + (induced_vector v) y"
      using Ring1_FH Ring1.add_closed aezfun_setspan_proj_add[of G x y] FG_proj_in_FG
            smult_distrib_left induced_vector_def
      by    auto
  }
  thus "\<forall>x\<in>FH. \<forall>y\<in>FH. induced_vector v (x + y)
              = induced_vector v x + induced_vector v y"
    by fast

  {
    fix a g x assume g: "g \<in> G" and x: "x \<in> FH"
    with v FH
      have  "(induced_vector v) (a \<delta>\<delta> g * x) = a \<delta>\<delta> g \<cdot> (induced_vector v) x"
      using FG_subring_FH FG_fddg_closed Ring1_FH
            Ring1.mult_closed[of FH "a \<delta>\<delta> g"] FG_proj_mult_leftdelta[of g a]
            FG_fddg_closed FG_proj_in_FG smult_assoc induced_vector_def
      by    fastforce
  }
  thus "\<forall>a. \<forall>g\<in>G. \<forall>x\<in>FH. induced_vector v (a \<delta>\<delta> g * x)
              = a \<delta>\<delta> g \<cdot> induced_vector v x"
    by fast

qed

lemma induced_vector_additive :
  "v \<in> V \<Longrightarrow> v' \<in> V
        \<Longrightarrow> induced_vector (v+v') = induced_vector v + induced_vector v'"
  using add_closed induced_vector_def FG_proj_in_FG smult_distrib_left by auto

lemma hom_induced_vector : "FGModuleHom G smult V rrsmult induced_vector"
proof

  show "\<And>v v'. v \<in> V \<Longrightarrow> v' \<in> V
              \<Longrightarrow> induced_vector (v + v') = induced_vector v + induced_vector v'"
    using induced_vector_additive by fast

  have "induced_vector = (\<lambda>v. if v\<in>V then \<lambda>y. if y \<in> FH
              then (FG_proj y) \<cdot> v else 0 else 0)"
    using induced_vector_def by fast
  thus "supp induced_vector \<subseteq> V" using supp_restrict0[of V] by fastforce

  show "\<And>x v. x \<in> BaseFGMod.FG \<Longrightarrow> v \<in> V
              \<Longrightarrow> induced_vector (x \<cdot> v) = x \<currency> induced_vector v"
  proof-
    fix x v assume xv: "x \<in> BaseFGMod.FG" "v \<in> V"
    show "induced_vector (x \<cdot> v) = x \<currency> induced_vector v"
    proof
      fix a
      from xv FH show "induced_vector (x \<cdot> v) a = (x \<currency> induced_vector v) a"
        using smult_closed induced_vector_def FG_proj_in_FG smult_assoc rrsmultD1
              FG_subring_FH Ring1.mult_closed[OF Ring1_FH] induced_vector_apply1
              FG_proj_mult_right[of x] smult_closed induced_vector_apply2 rrsmultD2
        by    auto
    qed
  qed

qed

lemma indspace_sum_list_fddh: 
  "\<lbrakk> fhs \<noteq> []; set (map snd fhs) \<subseteq> H; f \<in> indV \<rbrakk>
        \<Longrightarrow> f (\<Sum>(a,h)\<leftarrow>fhs. a \<delta>\<delta> h) = (\<Sum>(a,h)\<leftarrow>fhs. f (a \<delta>\<delta> h))"
proof (induct fhs rule: list_nonempty_induct)
  case (single fh) show ?case 
    using split_beta[of "\<lambda>a h. a \<delta>\<delta> h" fh] split_beta[of "\<lambda>a h. f (a \<delta>\<delta> h)" fh] by simp
next
  case (cons fh fhs)
  hence prevcase: "snd fh \<in> H" "set (map snd fhs) \<subseteq> H" "f \<in> indV"
                  "f (\<Sum>(a,h)\<leftarrow>fhs. a \<delta>\<delta> h) = (\<Sum>(a,h)\<leftarrow>fhs. f (a \<delta>\<delta> h))"
    by auto
  have "f (\<Sum>(a,h)\<leftarrow>fh#fhs. a \<delta>\<delta> h)
              = f ((fst fh) \<delta>\<delta> (snd fh) + (\<Sum>ah\<leftarrow>fhs. case_prod (\<lambda>a h. a \<delta>\<delta> h) ah))"
    using split_beta[of "\<lambda>a h. a \<delta>\<delta> h" fh] by simp
  moreover from prevcase(1) FH have "(fst fh) \<delta>\<delta> (snd fh) \<in> FH"
    using Supgroup.RG_aezdeltafun_closed by fast
  moreover from prevcase(2) FH
    have  "(\<Sum>ah\<leftarrow>fhs. case_prod (\<lambda>a h. a \<delta>\<delta> h) ah) \<in> FH"
    using Supgroup.RG_aezdeltafun_closed
          Ring1.sum_list_closed[OF Ring1_FH, of "\<lambda>ah. case_prod (\<lambda>a h. a \<delta>\<delta> h) ah" fhs]
    by    fastforce
  ultimately have "f (\<Sum>(a,h)\<leftarrow>fh#fhs. a \<delta>\<delta> h)
                              = f ((fst fh) \<delta>\<delta> (snd fh)) + f (\<Sum>(a,h)\<leftarrow>fhs. a \<delta>\<delta> h)"
    using indV prevcase(3) BaseFGMod.indspaceD_add by simp
  with prevcase(4) show ?case using split_beta[of "\<lambda>a h. f (a \<delta>\<delta> h)" fh] by simp
qed

lemma induced_fsmult_conv_fsmult_1ddh :
  "f \<in> indV \<Longrightarrow> h \<in> H \<Longrightarrow> (r \<currency>\<currency> f) (1 \<delta>\<delta> h) = r \<sharp>\<cdot> (f (1 \<delta>\<delta> h))"
  using FH indV induced_smult.fsmultD Supgroup.RG_aezdeltafun_closed[of h "1::'f"]
        rrsmultD1 aezdeltafun_decomp'[of r h]
        aezdeltafun_decomp[of r h] Supgroup.RG_aezdeltafun_closed[of h "1::'f"]
        Group.zero_closed[OF GroupG]
        BaseFGMod.indspaceD_transform[of f G FH V 0 "(1::'f) \<delta>\<delta> h" r]
        BaseFGMod.fsmultD
  by    simp

lemma indspace_el_eq_on_1ddh_imp_eq_on_rddh :
  assumes "HmodG \<subseteq> H" "H = (\<Union>h\<in>HmodG. G + {h})" "f \<in> indV" "f' \<in> indV" 
          "\<forall>h\<in>HmodG. f (1 \<delta>\<delta> h) = f' (1 \<delta>\<delta> h)" "h \<in> H"
  shows   "f (r \<delta>\<delta> h) = f' (r \<delta>\<delta> h)"
proof-
  from assms(2,6) obtain h' where h': "h' \<in> HmodG" "h \<in> G + {h'}" by fast
  from h'(2) obtain g where g: "g \<in> G" "h = g + h'"
    using set_plus_def[of G] by auto
  from g(2) have "r \<delta>\<delta> h = r \<delta>\<delta> 0 * (1 \<delta>\<delta> (g+h'))"
    using aezdeltafun_decomp by simp
  moreover have "(1::'f) \<delta>\<delta> (g+h') = 1 \<delta>\<delta> g * (1 \<delta>\<delta> h')"
    using times_aezdeltafun_aezdeltafun[of "1::'f", THEN sym] by simp
  ultimately have "r \<delta>\<delta> h = r \<delta>\<delta> g * (1 \<delta>\<delta> h')"
    using aezdeltafun_decomp[of r g]
    by    (simp add: algebra_simps)
  with indV FH assms(1,3,4) g(1) h'(1)
    have  "f (r \<delta>\<delta> h) = r \<delta>\<delta> g \<cdot> f (1 \<delta>\<delta> h')" "f' (r \<delta>\<delta> h) = r \<delta>\<delta> g \<cdot> f' (1 \<delta>\<delta> h')"
    using Supgroup.RG_aezdeltafun_closed[of h' 1]
          BaseFGMod.indspaceD_transform[of f G FH V g "1 \<delta>\<delta> h'" r]
          BaseFGMod.indspaceD_transform[of f' G FH V g "1 \<delta>\<delta> h'" r]
    by    auto
  thus "f (r \<delta>\<delta> h) = f' (r \<delta>\<delta> h)" using h'(1) assms(5) by simp
qed

lemma indspace_el_eq :
  assumes "HmodG \<subseteq> H" "H = (\<Union>h\<in>HmodG. G + {h})" "f \<in> indV" "f' \<in> indV" 
          "\<forall>h\<in>HmodG. f (1 \<delta>\<delta> h) = f' (1 \<delta>\<delta> h)"
  shows   "f = f'"
proof
  fix x show "f x = f' x"
  proof (cases "x = 0" "x \<in> FH" rule: conjcases)
    case BothTrue 
    hence "x = 0 \<delta>\<delta> 0" using zero_aezfun_transfer by simp
    with assms show ?thesis
      using indspace_el_eq_on_1ddh_imp_eq_on_rddh[of HmodG f f'] Supgroup.zero_closed
        by auto
  next
    case OneTrue with FH show ?thesis using Supgroup.RG_zero_closed by fast
  next
    case OtherTrue 
    with FH obtain rhs
      where rhs: "set (map snd rhs) \<subseteq> H" "x = (\<Sum>(r,h)\<leftarrow>rhs. r \<delta>\<delta> h)"
      using Supgroup.RG_el_decomp_aezdeltafun
      by    fast
    from OtherTrue rhs(2) have rhs_nnil: "rhs \<noteq> []" by auto
    with assms(3,4) rhs
      have  "f x = (\<Sum>(r,h)\<leftarrow>rhs. f (r \<delta>\<delta> h))" "f' x = (\<Sum>(r,h)\<leftarrow>rhs. f' (r \<delta>\<delta> h))"
      using indspace_sum_list_fddh
      by    auto
    moreover from rhs(1) assms have "\<forall>(r,h) \<in> set rhs. f (r \<delta>\<delta> h) = f' (r \<delta>\<delta> h)"
      using indspace_el_eq_on_1ddh_imp_eq_on_rddh[of HmodG f f'] by fastforce
    ultimately show ?thesis
      using sum_list_prod_cong[of rhs "\<lambda>r h. f (r \<delta>\<delta> h)"] by simp
  next
    case BothFalse
    with indV assms(3,4) show ?thesis
      using BaseFGMod.indspaceD_supp'[of f] BaseFGMod.indspaceD_supp'[of f']
      by    simp
  qed
qed

lemma indspace_el_eq' :
  assumes "set hs \<subseteq> H" "H = (\<Union>h\<in>set hs. G + {h})" "f \<in> indV" "f' \<in> indV"
          "\<forall>i<length hs. f (1 \<delta>\<delta> (hs!i)) = f' (1 \<delta>\<delta> (hs!i))"
  shows   "f = f'"
  using assms(1-4)
proof (rule indspace_el_eq[of "set hs"])
  have "\<And>h. h\<in>set hs \<Longrightarrow> f (1 \<delta>\<delta> h) = f' (1 \<delta>\<delta> h)"
  proof-
    fix h assume "h \<in> set hs"
    from this obtain i where "i < length hs" "h = hs!i"
      using in_set_conv_nth[of h] by fast
    with assms(5) show "f (1 \<delta>\<delta> h) = f' (1 \<delta>\<delta> h)" by simp
  qed
  thus "\<forall>h\<in>set hs. f (1 \<delta>\<delta> h) = f' (1 \<delta>\<delta> h)" by fast
qed

end (* context InducedFHModule *)




section \<open>Representations of Finite Groups\<close>

subsection \<open>Locale and basic facts\<close>

text \<open>
  Define a group representation to be a module over the group ring that is finite-dimensional as
  a vector space. The only restriction on the characteristic of the field is that it does not
  divide the order of the group. Also, we don't explicitly assume that the group is finite;
  instead, the \<open>good_char\<close> assumption implies that the cardinality of G is not zero, which
  implies G is finite. (See lemma \<open>good_card_imp_finite\<close>.)
\<close>

locale FinGroupRepresentation = FGModule G smult V
  for G     :: "'g::group_add set"
  and smult :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixl "\<cdot>" 70)
  and V     :: "'v set"
+
  assumes good_char: "of_nat (card G) \<noteq> (0::'f)"
  and     findim   : "fscalar_mult.findim fsmult V"

lemma (in Group) trivial_FinGroupRep :
  fixes   smult     :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
  assumes good_char  : "of_nat (card G) \<noteq> (0::'f)"
  and     smult_zero : "\<forall>a\<in>group_ring. smult a (0::'v) = 0"
  shows   "FinGroupRepresentation G smult (0::'v set)"
proof (rule FinGroupRepresentation.intro)
  from smult_zero show "FGModule G smult (0::'v set)"
    using trivial_FGModule by fast

  have "fscalar_mult.findim (aezfun_scalar_mult.fsmult smult) 0"
    by auto (metis R_scalar_mult.RSpan.simps(1) aezfun_scalar_mult.R_scalar_mult empty_set empty_subsetI set_zero)

  with good_char show "FinGroupRepresentation_axioms G smult 0" by unfold_locales
qed

context FinGroupRepresentation
begin

abbreviation ordG :: 'f where "ordG \<equiv> of_nat (card G)"
abbreviation "GRepHom \<equiv> FGModuleHom G smult V"
abbreviation "GRepIso \<equiv> FGModuleIso G smult V"
abbreviation "GRepEnd \<equiv> FGModuleEnd G smult V"

lemmas zero_closed              = zero_closed
lemmas Group                    = Group
lemmas GSubmodule_GSpan_single  = RSubmodule_RSpan_single
lemmas GSpan_single_nonzero     = RSpan_single_nonzero

lemma finiteG: "finite G"
  using good_char good_card_imp_finite by fast

lemma FinDimVectorSpace: "FinDimVectorSpace fsmult V"
  using findim fVectorSpace VectorSpace.FinDimVectorSpaceI by fast

lemma GSubspace_is_FinGroupRep :
  assumes "GSubspace U"
  shows   "FinGroupRepresentation G smult U"
proof (
  rule FinGroupRepresentation.intro, rule GSubspace_is_FGModule[OF assms], unfold_locales
)
  from assms show "fscalar_mult.findim fsmult U"
    using FinDimVectorSpace GSubspace_is_Subspace FinDimVectorSpace.Subspace_is_findim
    by    fast
qed (rule good_char)

lemma isomorphic_imp_GRep :
  assumes "isomorphic smult' W"
  shows   "FinGroupRepresentation G smult' W"
proof (rule FinGroupRepresentation.intro)
  from assms show "FGModule G smult' W"
    using FGModuleIso.ImG FGModuleHom.FGModule_Im[OF FGModuleIso.axioms(1)]
    by    fast
  from assms have "fscalar_mult.findim (aezfun_scalar_mult.fsmult smult') W"
    using FGModuleIso.ImG findim FGModuleIso.VectorSpaceHom
          VectorSpaceHom.findim_domain_findim_image
    by    fastforce
  with good_char show "FinGroupRepresentation_axioms G smult' W" by unfold_locales
qed

end (* context FinGroupRepresentation *)


subsection \<open>Irreducible representations\<close>

locale IrrFinGroupRepresentation = FinGroupRepresentation
+ assumes irr: "GSubspace U \<Longrightarrow> U = 0 \<or> U = V"
begin

lemmas AbGroup = AbGroup

lemma zero_isomorphic_to_FG_zero :
  assumes "V = 0"
  shows   "isomorphic (*) (0::('b,'a) aezfun set)"
proof
  show "GRepIso (*) 0 0"
  proof (rule FGModuleIso.intro)
    show "GRepHom (*) 0" using trivial_FGModuleHom[of "(*)"] by simp
    show "FGModuleIso_axioms V 0 0"
    proof
      from assms show "bij_betw 0 V 0" unfolding bij_betw_def inj_on_def by simp
    qed
  qed
qed

lemma eq_GSpan_single : "v \<in> V \<Longrightarrow> v \<noteq> 0 \<Longrightarrow> V = GSpan [v]"
  using irr RSubmodule_RSpan_single RSpan_single_nonzero by fast

end (* context IrrFinGroupRepresentation *)

lemma (in Group) trivial_IrrFinGroupRepI :
  fixes   smult :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
  assumes "of_nat (card G) \<noteq> (0::'f)"
  and     "\<forall>a\<in>group_ring. smult a (0::'v) = 0"
  shows   "IrrFinGroupRepresentation G smult (0::'v set)"
proof (rule IrrFinGroupRepresentation.intro)
  from assms show "FinGroupRepresentation G smult 0"
    using trivial_FinGroupRep by fast
  show "IrrFinGroupRepresentation_axioms G smult 0"
    using RModule.zero_closed by unfold_locales auto
qed

lemma (in Group) trivial_IrrFinGroupRepresentation_in_FG :
  "of_nat (card G) \<noteq> (0::'f::field)
        \<Longrightarrow> IrrFinGroupRepresentation G (*) (0::('f,'g) aezfun set)"
  using trivial_IrrFinGroupRepI[of "(*)"] by simp

context FinGroupRepresentation
begin

lemma IrrFinGroupRep_trivialGSubspace :
  "IrrFinGroupRepresentation G smult (0::'v set)"
proof-
  have "ordG \<noteq> (0::'f)" using good_char by fast
  moreover have "\<forall>a\<in>FG. a \<cdot> 0 = 0" using smult_zero by simp
  ultimately show ?thesis
    using ActingGroup.trivial_IrrFinGroupRepI[of smult] by fast
qed

lemma IrrI :
  assumes "\<And>U. FGModule.GSubspace G smult V U \<Longrightarrow> U = 0 \<or> U = V"
  shows   "IrrFinGroupRepresentation G smult V"
  using assms IrrFinGroupRepresentation.intro by unfold_locales

lemma notIrr :
  "\<not> IrrFinGroupRepresentation G smult V
        \<Longrightarrow> \<exists>U. GSubspace U \<and> U \<noteq> 0 \<and> U \<noteq> V"
  using IrrI by fast

end (* context FinGroupRepresentation *)


subsection \<open>Maschke's theorem\<close>

subsubsection \<open>Averaged projection onto a G-subspace\<close>

context FinGroupRepresentation
begin

lemma avg_proj_eq_id_on_right :
  assumes "VectorSpace fsmult W" "add_independentS [W,V]" "v \<in> V"
  defines P : "P \<equiv> (\<Oplus>[W,V]\<down>1)"
  defines CP: "CP \<equiv> (\<lambda>g. Gmult (- g) \<circ> P \<circ> Gmult g)"
  defines T : "T \<equiv> fsmult (1/ordG) \<circ> (\<Sum>g\<in>G. CP g)"
  shows   "T v = v"
proof-
  from P assms(2,3) have "\<And>g. g \<in> G \<Longrightarrow> P (g *\<cdot> v) = g *\<cdot> v"
    using Gmult_closed VectorSpace.AbGroup[OF assms(1)] AbGroup 
          AbGroup_inner_dirsum_el_decomp_nth_id_on_nth[of "[W,V]"]
    by    simp
  with CP assms(3) have "\<And>g. g \<in> G \<Longrightarrow> CP g v = v"
    using Gmult_neg_left by simp
  with assms(3) good_char T show "T v = v"
    using finiteG sum_fun_apply[of G CP] sum_fsmult_distrib[of v G "\<lambda>x. 1"]
          fsmult_assoc[of _ ordG v]
    by    simp
qed

lemma avg_proj_onto_right :
  assumes "VectorSpace fsmult W" "GSubspace U" "add_independentS [W,U]"
          "V = W \<oplus> U"
  defines P : "P \<equiv> (\<Oplus>[W,U]\<down>1)"
  defines CP: "CP \<equiv> (\<lambda>g. Gmult (- g) \<circ> P \<circ> Gmult g)"
  defines T : "T \<equiv> fsmult (1/ordG) \<circ> (\<Sum>g\<in>G. CP g)"
  shows   "T ` V = U"
proof
  from assms(2) have U: "FGModule G smult U"
    using GSubspace_is_FGModule by fast
  show "T ` V \<subseteq> U"
  proof (rule image_subsetI)
    fix v assume v: "v \<in> V"
    with assms(1,3,4) P U have "\<And>g. g \<in> G \<Longrightarrow> P (g *\<cdot> v) \<in> U"
      using Gmult_closed VectorSpace.AbGroup FGModule.AbGroup
            AbGroup_inner_dirsum_el_decomp_nth_onto_nth[of "[W,U]" 1]
      by    fastforce
    with U CP have "\<And>g. g \<in> G \<Longrightarrow> CP g v \<in> U"
      using FGModule.Gmult_closed GroupG Group.neg_closed by fastforce
    with assms(2) U T show "T v \<in> U"
      using finiteG FGModule.sum_closed[of G smult U G "\<lambda>g. CP g v"]
            sum_fun_apply[of G CP] FGModule.fsmult_closed[of G smult U]
      by    fastforce
  qed
  show "T ` V \<supseteq> U"
  proof
    fix u assume u: "u \<in> U"
    with u T CP P assms(1,2,3) have "T u = u"
      using GSubspace_is_FinGroupRep FinGroupRepresentation.avg_proj_eq_id_on_right
      by    fast
    from this[THEN sym] assms(1-4) u show "u \<in> T ` V"
      using Module.AbGroup RModule.AbGroup AbGroup_subset_inner_dirsum
      by    fast
  qed
qed

lemma FGModuleEnd_avg_proj_right :
  assumes "fSubspace W" "GSubspace U" "add_independentS [W,U]" "V = W \<oplus> U"
  defines P : "P \<equiv> (\<Oplus>[W,U]\<down>1)"
  defines CP: "CP \<equiv> (\<lambda>g. Gmult (- g) \<circ> P \<circ> Gmult g)"
  defines T : "T \<equiv> (fsmult (1/ordG) \<circ> (\<Sum>g\<in>G. CP g))\<down>V"
  shows   "FGModuleEnd G smult V T"
proof (rule VecEnd_GMap_is_FGModuleEnd)

  from T have T_apply: "\<And>v. v\<in>V \<Longrightarrow> T v = (1/ordG) \<sharp>\<cdot> (\<Sum>g\<in>G. CP g v)"
    using finiteG sum_fun_apply[of G CP] by simp

  from assms(1-4) P have Pgv: "\<And>g v. g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> P ( g *\<cdot> v ) \<in> V"
    using Gmult_closed VectorSpace_fSubspace VectorSpace.AbGroup[of fsmult W]
          RModule.AbGroup[of FG smult U]
          GroupEnd_inner_dirsum_el_decomp_nth[of "[W,U]" 1]
          GroupEnd.endomorph[of V]
    by force

  have im_CP_V: "\<And>v. v \<in> V \<Longrightarrow> (\<lambda>g. CP g v) ` G \<subseteq> V"
  proof-
    fix v assume "v \<in> V" thus "(\<lambda>g. CP g v) ` G \<subseteq> V"
      using CP Pgv[of _ v] ActingGroup.neg_closed Gmult_closed finiteG by auto
  qed

  have sumCP_V: "\<And>v. v \<in> V \<Longrightarrow> (\<Sum>g\<in>G. CP g v) \<in> V"
    using finiteG im_CP_V sum_closed by force

  show "VectorSpaceEnd (\<sharp>\<cdot>) V T"
  proof (
    rule VectorSpaceEndI, rule VectorSpace.VectorSpaceHomI, rule fVectorSpace
  )

    show "GroupHom V T"
    proof
      fix v v' assume vv': "v \<in> V" "v' \<in> V"
      with T_apply have "T (v + v') = (1/ordG) \<sharp>\<cdot> (\<Sum>g\<in>G. CP g (v + v'))"
        using add_closed by fast
      moreover have "\<And>g. g \<in> G \<Longrightarrow> CP g (v + v') = CP g v + CP g v'"
      proof-
        fix g assume g: "g \<in> G"
        with CP P vv' assms(1-4)
          have  "CP g (v + v') = (- g) *\<cdot> ( P ( g *\<cdot> v ) + P ( g *\<cdot> v' ) )"
          using Gmult_distrib_left Gmult_closed VectorSpace_fSubspace
                VectorSpace.AbGroup[of fsmult W] RModule.AbGroup[of FG smult U]
                GroupEnd_inner_dirsum_el_decomp_nth[of "[W,U]" 1]
                GroupEnd.hom[of V P]
          by    simp
        with g vv' have "CP g (v + v')
                              = (- g) *\<cdot> P ( g *\<cdot> v ) + (- g) *\<cdot> P ( g *\<cdot> v' )"
          using Pgv ActingGroup.neg_closed Gmult_distrib_left by simp
        thus "CP g (v + v') = CP g v + CP g v'" using CP by simp
      qed
      ultimately show "T (v + v') = T v + T v'"
        using vv' sumCP_V[of v] sumCP_V[of v'] sum.distrib[of "\<lambda>g. CP g v"]
              T_apply
        by    simp
    next
      from T show "supp T \<subseteq> V" using supp_restrict0 by fast
    qed

    show "\<And>a v. v \<in> V \<Longrightarrow> T (a \<sharp>\<cdot> v) = a \<sharp>\<cdot> T v"
    proof-
      fix a::'f and v assume v: "v \<in> V"
      with T_apply have "T (a \<sharp>\<cdot> v) = (1/ordG) \<sharp>\<cdot> (\<Sum>g\<in>G. CP g (a \<sharp>\<cdot> v))"
        using fsmult_closed by fast
      moreover have "\<And>g. g \<in> G \<Longrightarrow> CP g (a \<sharp>\<cdot> v) = a \<sharp>\<cdot> CP g v"
      proof-
        fix g assume "g \<in> G"
        with assms(1-4) CP P v show "CP g (a \<sharp>\<cdot> v) = a \<sharp>\<cdot> CP g v"
          using fsmult_Gmult_comm GSubspace_is_Subspace Gmult_closed fVectorSpace
                VectorSpace.VectorSpaceEnd_inner_dirsum_el_decomp_nth[of fsmult]
                VectorSpaceEnd.f_map[of fsmult "(\<Oplus>N\<leftarrow>[W, U]. N)" P a "g *\<cdot> v"]
                ActingGroup.neg_closed Pgv
          by    simp
      qed
      ultimately show "T (a \<sharp>\<cdot> v) = a \<sharp>\<cdot> T v"
        using v im_CP_V sumCP_V T_apply finiteG
              fsmult_sum_distrib[of a G "\<lambda>g. CP g v"]
              fsmult_assoc[of "1/ordG" a "(\<Sum>g\<in>G. CP g v)"]
        by    simp
    qed

    show "T ` V \<subseteq> V" using sumCP_V fsmult_closed T_apply image_subsetI by auto

  qed

  show "\<And>g v. g \<in> G \<Longrightarrow> v \<in> V \<Longrightarrow> T (g *\<cdot> v) = g *\<cdot> T v"
  proof-
    fix g v assume g: "g \<in> G" and v: "v \<in> V"
    with T_apply have "T (g *\<cdot> v) = (1/ordG) \<sharp>\<cdot> (\<Sum>h\<in>G. CP h (g *\<cdot> v))"
      using Gmult_closed by fast
    with g have "T (g *\<cdot> v) = (1/ordG) \<sharp>\<cdot> (\<Sum>h\<in>G. CP (h + - g) (g *\<cdot> v))"
      using GroupG Group.neg_closed
            Group.right_translate_sum[of G "- g" "\<lambda>h. CP h (g *\<cdot> v)"]
      by    fastforce
    moreover from CP
      have  "\<And>h. h \<in> G \<Longrightarrow> CP (h + - g) (g *\<cdot> v) = g *\<cdot> CP h v"
      using g v Gmult_closed[of g v] ActingGroup.neg_closed
            Gmult_assoc[of _ "- g" "g *\<cdot> v", THEN sym]
            Gmult_neg_left minus_add[of _ "- g"] Pgv Gmult_assoc
      by    simp
    ultimately show "T (g *\<cdot> v) = g *\<cdot> T v"
      using g v GmultD finiteG FG_fddg_closed im_CP_V sumCP_V
            smult_sum_distrib[of "1 \<delta>\<delta> g" G]
            fsmult_Gmult_comm[of g "\<Sum>h\<in>G. (CP h v)"] T_apply
      by    simp
  qed

qed

lemma avg_proj_is_proj_right :
  assumes "VectorSpace fsmult W" "GSubspace U" "add_independentS [W,U]"
          "V = W \<oplus> U" "v \<in> V"
  defines P : "P \<equiv> (\<Oplus>[W,U]\<down>1)"
  defines CP: "CP \<equiv> (\<lambda>g. Gmult (- g) \<circ> P \<circ> Gmult g)"
  defines T : "T \<equiv> fsmult (1/ordG) \<circ> (\<Sum>g\<in>G. CP g)"
  shows   "T (T v) = T v"
  using   assms avg_proj_onto_right GSubspace_is_FinGroupRep
          FinGroupRepresentation.avg_proj_eq_id_on_right
  by      fast

end (* context FinGroupRepresentation *)

subsubsection \<open>The theorem\<close>

context FinGroupRepresentation
begin

theorem Maschke :
  assumes "GSubspace U"
  shows   "\<exists>W. GSubspace W \<and> V = W \<oplus> U"
proof (cases "V = 0")
  case True
  moreover from assms True have "U = 0" using RModule.zero_closed by auto
  ultimately have "V = 0 + U" using set_plus_def by fastforce
  moreover have "add_independentS [0,U]" by simp
  ultimately have "V = 0 \<oplus> U" using inner_dirsum_doubleI by fast
  moreover have "GSubspace 0" using trivial_RSubmodule zero_closed by auto
  ultimately show "\<exists>W. GSubspace W \<and> V = W \<oplus> U" by fast
next
  case False
  from assms obtain W'
    where W': "VectorSpace.Subspace fsmult V W' \<and> V = W' \<oplus> U"
    using GSubspace_is_Subspace FinDimVectorSpace FinDimVectorSpace.semisimple
    by    force
  hence vsp_W': "VectorSpace fsmult W'" and dirsum: "V = W' \<oplus> U"
    using VectorSpace.SubspaceD1[OF fVectorSpace] by auto
  from False dirsum have indS: "add_independentS [W',U]"
    using inner_dirsumD2 by fastforce
  define P where "P  = (\<Oplus>[W',U]\<down>1)"
  define CP where "CP = (\<lambda>g. Gmult (- g) \<circ> P \<circ> Gmult g)"
  define S where "S = fsmult (1/ordG) \<circ> (\<Sum>g\<in>G. CP g)"
  define W where "W = GroupHom.Ker V (S\<down>V)"
  from assms W' indS S_def CP_def P_def have endo: "GRepEnd (S\<down>V)"
    using FGModuleEnd_avg_proj_right by fast
  moreover from S_def CP_def P_def have "\<And>v. v \<in> V \<Longrightarrow> (S\<down>V) ((S\<down>V) v) = (S\<down>V) v"
      using endo FGModuleEnd.endomorph
            avg_proj_is_proj_right[OF vsp_W' assms indS dirsum]
      by    fastforce
  moreover have "(S\<down>V) ` V = U"
  proof-
    from assms indS P_def CP_def S_def dirsum vsp_W' have "S ` V = U"
      using avg_proj_onto_right by fast
    moreover have "(S\<down>V) ` V = S ` V" by auto
    ultimately show ?thesis by fast
  qed
  ultimately have "V = W \<oplus> U" "GSubspace W"
    using W_def FGModuleEnd.proj_decomp[of G smult V "S\<down>V"]
          FGModuleEnd.GSubspace_Ker
    by    auto
  thus ?thesis by fast
qed

corollary Maschke_proper :
  assumes "GSubspace U" "U \<noteq> 0" "U \<noteq> V"
  shows   "\<exists>W. GSubspace W \<and> W \<noteq> 0 \<and> W \<noteq> V \<and> V = W \<oplus> U"
proof-
  from assms(1) obtain W where W: "GSubspace W" "V = W \<oplus> U"
    using Maschke by fast
  from assms(3) W(2) have "W \<noteq> 0" using inner_dirsum_double_left0 by fast
  moreover from assms(1,2) W have "W \<noteq> V"
    using Subgroup_RSubmodule Group.nonempty
          inner_dirsum_double_leftfull_imp_right0[of W U]
    by    fastforce
  ultimately show ?thesis using W by fast
qed

end (* context FinGroupRepresentation *)

subsubsection \<open>Consequence: complete reducibility\<close>

lemma (in FinGroupRepresentation) notIrr_decompose :
  "\<not> IrrFinGroupRepresentation G smult V
        \<Longrightarrow> \<exists>U W. GSubspace U \<and> U \<noteq> 0 \<and> U \<noteq> V \<and> GSubspace W \<and> W \<noteq> 0
          \<and> W \<noteq> V \<and> V = U \<oplus> W"
  using notIrr Maschke_proper by blast

text \<open>
  In the following decomposition lemma, we do not need to explicitly include the condition that all
  @{term U} in @{term "set Us"} are subsets of @{term V}. (See lemma \<open>AbGroup_subset_inner_dirsum\<close>.)
\<close>

lemma FinGroupRepresentation_reducible' :
  fixes n::nat
  shows "\<And>V. FinGroupRepresentation G fgsmult V
              \<and> n = FGModule.fdim fgsmult V
                \<Longrightarrow> (\<exists>Us. Ball (set Us) (IrrFinGroupRepresentation G fgsmult)
                  \<and> (0 \<notin> set Us) \<and> V = (\<Oplus>U\<leftarrow>Us. U) )"
proof (induct n rule: full_nat_induct)
  fix n V
  define GRep IGRep GSubspace GSpan fdim
    where "GRep = FinGroupRepresentation G fgsmult"
      and "IGRep = IrrFinGroupRepresentation G fgsmult"
      and "GSubspace = FGModule.GSubspace G fgsmult V"
      and "GSpan = FGModule.GSpan G fgsmult"
      and "fdim = FGModule.fdim fgsmult"
  assume "\<forall>m. Suc m \<le> n \<longrightarrow> (\<forall>x. GRep x \<and> m = fdim x \<longrightarrow> ( \<exists>Us.
              Ball (set Us) IGRep \<and> (0 \<notin> set Us) \<and> x = (\<Oplus>U\<leftarrow>Us. U)) )"
  hence prev_case:
    "\<And>m. m < n \<Longrightarrow> (\<And>W. GRep W \<Longrightarrow> m = fdim W \<Longrightarrow> ( \<exists>Us.
            Ball (set Us) IGRep \<and> (0 \<notin> set Us) \<and> W = (\<Oplus>U\<leftarrow>Us. U)))"
    using Suc_le_eq by auto
  show "GRep V \<and> n = fdim V \<Longrightarrow> ( \<exists>Us.
          Ball (set Us) IGRep \<and> (0 \<notin> set Us) \<and> V = (\<Oplus>U\<leftarrow>Us. U) )"
  proof-
    assume V: "GRep V \<and> n = fdim V"
    show "(\<exists>Us. Ball (set Us) IGRep \<and> (0 \<notin> set Us) \<and> V = (\<Oplus>U\<leftarrow>Us. U))"
    proof (cases "IGRep V" "V = 0" rule: conjcases)
      case BothTrue
      moreover have "Ball (set []) IGRep" "\<forall>U\<in>set []. U \<noteq> 0" by auto
      ultimately show ?thesis using inner_dirsum_Nil by fast
    next
      case OneTrue
      with V GRep_def obtain v where v: "v \<in> V" "v \<noteq> 0" 
        using FinGroupRepresentation.Group[of G fgsmult] Group.obtain_nonzero
        by    auto
      from v(1) V GRep_def GSpan_def GSubspace_def have GSub: "GSubspace (GSpan [v])"
        using FinGroupRepresentation.GSubmodule_GSpan_single by fast
      moreover from v V GRep_def GSpan_def have nzero: "GSpan [v] \<noteq> 0"
        using FinGroupRepresentation.GSpan_single_nonzero by fast
      ultimately have "V = GSpan [v]"
        using OneTrue GSpan_def GSubspace_def IGRep_def IrrFinGroupRepresentation.irr
        by    fast
      with OneTrue
        have  "Ball (set [GSpan [v]]) IGRep" "0 \<notin> set [GSpan [v]]"
              "V = (\<Oplus>U\<leftarrow>[GSpan [v]]. U)"
        using nzero GSub inner_dirsum_singleD
        by    auto
      thus ?thesis by fast
    next
      case OtherTrue with V GRep_def IGRep_def show ?thesis
        using FinGroupRepresentation.IrrFinGroupRep_trivialGSubspace by fast
    next
      case BothFalse
      with V GRep_def IGRep_def GSubspace_def obtain U W
        where U: "GSubspace U" "U \<noteq> 0" "U \<noteq> V"
        and   W: "GSubspace W" "W \<noteq> 0" "W \<noteq> V"
        and   Vdecompose: "V = U \<oplus> W"
        using FinGroupRepresentation.notIrr_decompose[of G fgsmult V]
        by    auto
      from U(1,3) W(1,3) V GRep_def GSubspace_def fdim_def
        have  "fdim U < fdim V" "fdim W < fdim V"
        using FinGroupRepresentation.axioms(1)
              FGModule.GSubspace_is_Subspace[of G fgsmult V U]
              FGModule.GSubspace_is_Subspace[of G fgsmult V W]
              FinGroupRepresentation.FinDimVectorSpace[of G fgsmult V]
              FinDimVectorSpace.Subspace_dim_lt[
                of "aezfun_scalar_mult.fsmult fgsmult" V U
              ]
              FinDimVectorSpace.Subspace_dim_lt[
                of "aezfun_scalar_mult.fsmult fgsmult" V W
              ]
        by    auto
      from this U(1) W(1) V GSubspace_def obtain Us Ws
        where "Ball (set Us) IGRep \<and> (0 \<notin> set Us) \<and> U = (\<Oplus>X\<leftarrow>Us. X)"
        and   "Ball (set Ws) IGRep \<and> (0 \<notin> set Ws) \<and> W = (\<Oplus>X\<leftarrow>Ws. X)"
        using prev_case[of "fdim U"] prev_case[of "fdim W"] GRep_def
              FinGroupRepresentation.GSubspace_is_FinGroupRep[
                of G fgsmult V U
              ]
              FinGroupRepresentation.GSubspace_is_FinGroupRep[
                of G fgsmult V W
              ]
        by    fastforce
      hence Us: "Ball (set Us) IGRep" "0 \<notin> set Us" "U = (\<Oplus>X\<leftarrow>Us. X)"
        and Ws: "Ball (set Ws) IGRep" "0 \<notin> set Ws" "W = (\<Oplus>X\<leftarrow>Ws. X)"
        by  auto
      from Us(1) Ws(1) have "Ball (set (Us@Ws)) IGRep" by auto
      moreover from Us(2) Ws(2) have "0 \<notin> set (Us@Ws)" by auto
      moreover have "V = (\<Oplus>X\<leftarrow>(Us@Ws). X)"
      proof-
        from U(2) Us(3) W(2) Ws(3)
          have  indUs: "add_independentS Us"
          and   indWs: "add_independentS Ws"
          using inner_dirsumD2
          by    auto
        moreover from IGRep_def Us(1) have "Ball (set Us) ((\<in>) 0)"
          using IrrFinGroupRepresentation.axioms(1)[of G fgsmult]
                FinGroupRepresentation.zero_closed[of G fgsmult]
          by    fast
        moreover from Us(3) Ws(3) BothFalse Vdecompose indUs indWs
          have "add_independentS [(\<Sum>X\<leftarrow>Us. X),(\<Sum>X\<leftarrow>Ws. X)]"
          using inner_dirsumD2[of "[U,W]"] inner_dirsumD[of Us]
                inner_dirsumD[of Ws]
          by    auto
        ultimately have "add_independentS (Us@Ws)" 
          using add_independentS_double_sum_conv_append by auto
        moreover from W(1) Ws(3) indWs have "0 \<in> (\<Sum>X\<leftarrow>Ws. X)"
          using inner_dirsumD GSubspace_def RModule.zero_closed by fast
        ultimately show ?thesis
          using Vdecompose Us(3) Ws(3) inner_dirsum_append by fast
      qed
      ultimately show ?thesis by fast
    qed
  qed
qed

theorem (in FinGroupRepresentation) reducible :
  "\<exists>Us. (\<forall>U\<in>set Us. IrrFinGroupRepresentation G smult U) \<and> (0 \<notin> set Us) 
        \<and> V = (\<Oplus>U\<leftarrow>Us. U)"
  using FinGroupRepresentation_axioms FinGroupRepresentation_reducible' by fast

subsubsection \<open>Consequence: decomposition relative to a homomomorphism\<close>

lemma (in FinGroupRepresentation) GRepHom_decomp :
  fixes   T   :: "'v \<Rightarrow> 'w::ab_group_add"
  defines KerT : "KerT \<equiv> (ker T \<inter> V)"
  assumes hom  : "GRepHom smult' T" and nonzero: "V \<noteq> 0"
  shows   "\<exists>U. GSubspace U \<and> V = U \<oplus> KerT
                \<and> FGModule.isomorphic G smult U smult' (T ` V)"
proof-
  from KerT have KerT': "GSubspace KerT"
    using FGModuleHom.GSubspace_Ker[OF hom] by fast
  from this obtain U where U: "GSubspace U" "V = U \<oplus> KerT"
    using Maschke[of KerT] by fast
  from nonzero U(2) have indep: "add_independentS [U,KerT]"
    using inner_dirsumD2 by fastforce
  have "FGModuleIso G smult U smult' (T \<down> U) (T ` V)"
  proof (rule FGModuleIso.intro)
    from U(1) show "FGModuleHom G (\<cdot>) U smult' (T \<down> U)"
      using FGModuleHom.FGModuleHom_restrict0_GSubspace[OF hom] by fast
    show "FGModuleIso_axioms U (T \<down> U) (T ` V)"
      unfolding FGModuleIso_axioms_def bij_betw_def
    proof (rule conjI, rule inj_onI)
      show "(T \<down> U) ` U = T ` V"
      proof
        from U(1) show "(T \<down> U) ` U \<subseteq> T ` V" by auto
        show "(T \<down> U) ` U \<supseteq> T ` V"
        proof (rule image_subsetI)
          fix v assume "v \<in> V"
          with U(2) obtain u k where uk: "u \<in> U" "k \<in> KerT" "v = u + k"
            using inner_dirsum_doubleD[OF indep] set_plus_def[of U KerT] by fast
          with KerT U(1) have "T v = (T \<down> U) u"
            using kerD FGModuleHom.additive[OF hom] by force
          with uk(1) show "T v \<in> (T \<down> U) ` U" by fast
        qed
      qed
    next
      fix x y assume xy: "x \<in> U" "y \<in> U" "(T \<down> U) x = (T \<down> U) y"
      with U(1) KerT have "x - y \<in> U \<inter> KerT"
        using FGModuleHom.eq_im_imp_diff_in_Ker[OF hom]
              GSubspace_is_FGModule FGModule.diff_closed[of G smult U x y]
        by    auto
      moreover from U(1) have "AbGroup U" using RModule.AbGroup by fast
      moreover from KerT' have "AbGroup KerT"
        using RModule.AbGroup by fast
      ultimately show "x = y" 
        using indep AbGroup_inner_dirsum_pairwise_int0_double[of U KerT]
        by    force
    qed
  qed
  with U show ?thesis by fast
qed


subsection \<open>Schur's lemma\<close>

lemma (in IrrFinGroupRepresentation) Schur_Ker :
  "GRepHom smult' T \<Longrightarrow> T ` V \<noteq> 0 \<Longrightarrow> inj_on T V"
  using irr FGModuleHom.GSubspace_Ker[of G smult V smult' T] 
        FGModuleHom.Ker_Im_iff[of G smult V smult' T]
        FGModuleHom.Ker0_imp_inj_on[of G smult V smult' T]
  by    auto

lemma (in FinGroupRepresentation) Schur_Im :
  assumes "IrrFinGroupRepresentation G smult' W" "GRepHom smult' T"
          "T ` V \<subseteq> W"
          "T ` V \<noteq> 0"
  shows   "T ` V = W"
proof-
  have "FGModule.GSubspace G smult' W (T ` V)"
  proof
    from assms(2) show "RModule FG smult' (T ` V)"
      using FGModuleHom.axioms(2)[of G]
            RModuleHom.RModule_Im[of FG smult V smult' T]
      by    fast
    from assms(3) show "T ` V \<subseteq> W" by fast
  qed
  with assms(1,4) show ?thesis using IrrFinGroupRepresentation.irr by fast
qed

theorem (in IrrFinGroupRepresentation) Schur1 :
  assumes   "IrrFinGroupRepresentation G smult' W" 
            "GRepHom smult' T" "T ` V \<subseteq> W" "T ` V \<noteq> 0"
  shows     "GRepIso smult' T W"
proof (rule FGModuleIso.intro, rule assms(2), unfold_locales)
  show "bij_betw T V W"
    using     IrrFinGroupRepresentation_axioms assms
              IrrFinGroupRepresentation.axioms(1)[of G]
              FinGroupRepresentation.Schur_Im[of G]
              IrrFinGroupRepresentation.Schur_Ker[of G smult V smult' T]
    unfolding bij_betw_def
    by        fast
qed

theorem (in IrrFinGroupRepresentation) Schur2 :
  assumes GRep      : "GRepEnd T"
  and     fdim       : "fdim > 0"
  and     alg_closed: "\<And>p::'b poly. degree p > 0 \<Longrightarrow> \<exists>c. poly p c = 0"
  shows   "\<exists>c. \<forall>v \<in> V. T v = c \<sharp>\<cdot> v"
proof-
  from fdim alg_closed obtain e u where eu: "u \<in> V" "u \<noteq> 0" "T u = e \<sharp>\<cdot> u"
    using FGModuleEnd.VectorSpaceEnd[OF GRep]
          FinDimVectorSpace.endomorph_has_eigenvector[
            OF FinDimVectorSpace, of T
          ]
    by    fast
  define U where "U = {v \<in> V. T v = e \<sharp>\<cdot> v}"
  moreover from eu U_def have "U \<noteq> 0" by auto
  ultimately have "\<forall>v \<in> V. T v = e \<sharp>\<cdot> v"
    using GRep irr FGModuleEnd.axioms(1)[of G smult V T]
          GSubspace_eigenspace[of G smult]
    by    fast
  thus ?thesis by fast
qed


subsection \<open>The group ring as a representation space\<close>

subsubsection \<open>The group ring is a representation space\<close>

lemma (in Group) FGModule_FG :
  defines FG: "FG \<equiv> group_ring :: ('f::field, 'g) aezfun set"
  shows   "FGModule G (*) FG"
proof (rule FGModule.intro, rule Group_axioms, rule RModuleI)
  show 1: "Ring1 group_ring" using Ring1_RG by fast
  from 1 FG show "Group FG" using Ring1.axioms(1) by fast
  from 1 FG show "RModule_axioms group_ring (*) FG"
    using Ring1.mult_closed
    by    unfold_locales (auto simp add: algebra_simps)
qed

theorem (in Group) FinGroupRepresentation_FG :
  defines FG: "FG \<equiv> group_ring :: ('f::field, 'g) aezfun set"
  assumes good_char: "of_nat (card G) \<noteq> (0::'f)"
  shows   "FinGroupRepresentation G (*) FG"
proof (rule FinGroupRepresentation.intro)
  from FG show "FGModule G (*) FG" using FGModule_FG by fast
  show "FinGroupRepresentation_axioms G (*) FG"
  proof
    from FG good_char obtain gs
      where gs: "set gs = G"
                "\<forall>f\<in> FG. \<exists>bs. length bs = length gs
                      \<and> f = (\<Sum>(b,g)\<leftarrow>zip bs gs. (b \<delta>\<delta> 0) * (1 \<delta>\<delta> g))"
      using good_card_imp_finite FinGroupI FinGroup.group_ring_spanning_set
      by    fast
    define xs where "xs = map ((\<delta>\<delta>) (1::'f)) gs"
    with FG gs(1) have 1: "set xs \<subseteq> FG" using RG_aezdeltafun_closed by auto
    moreover have "aezfun_scalar_mult.fSpan (*) xs = FG"
    proof
      from 1 FG show "aezfun_scalar_mult.fSpan (*) xs \<subseteq> FG"
        using FGModule_FG FGModule.fSpan_closed by fast
      show "aezfun_scalar_mult.fSpan (*) xs \<supseteq> FG"
      proof
        fix x assume "x \<in> FG"
        from this gs(2) obtain bs
          where bs: "length bs = length gs"
                    "x = (\<Sum>(b,g)\<leftarrow>zip bs gs. (b \<delta>\<delta> 0) * (1 \<delta>\<delta> g))"
          by    fast
        from bs(2) xs_def have "x = (\<Sum>(b,a)\<leftarrow>zip bs xs. (b \<delta>\<delta> 0) * a)"
          using sum_list_prod_map2[THEN sym] by fast
        with bs(1) xs_def show "x \<in> aezfun_scalar_mult.fSpan (*) xs"
          using aezfun_scalar_mult.fsmultD[of "(*)", THEN sym]
                sum_list_prod_cong[
                  of "zip bs xs" "\<lambda>b a. (b \<delta>\<delta> 0) * a"
                     "\<lambda>b a. aezfun_scalar_mult.fsmult (*) b a"
                ]
                scalar_mult.lincomb_def[of "aezfun_scalar_mult.fsmult (*)" bs xs]
                scalar_mult.SpanD_lincomb[of "aezfun_scalar_mult.fsmult (*)"]
          by    force
      qed
    qed
    ultimately show "\<exists>xs. set xs \<subseteq> FG \<and> aezfun_scalar_mult.fSpan (*) xs = FG"
      by fast
  qed (rule good_char)
qed

lemma (in FinGroupRepresentation) FinGroupRepresentation_FG :
  "FinGroupRepresentation G (*) FG"
  using good_char ActingGroup.FinGroupRepresentation_FG by fast

lemma (in Group) FG_reducible :
  assumes "of_nat (card G) \<noteq> (0::'f::field)"
  shows   "\<exists>Us::('f,'g) aezfun set list.
                (\<forall>U\<in>set Us. IrrFinGroupRepresentation G (*) U) \<and> 0 \<notin> set Us
                  \<and> group_ring = (\<Oplus>U\<leftarrow>Us. U)"
  using   assms FinGroupRepresentation_FG FinGroupRepresentation.reducible
  by      fast

subsubsection \<open>Irreducible representations are constituents of the group ring\<close>

lemma (in FGModuleIso) isomorphic_to_irr_right :
  assumes "IrrFinGroupRepresentation G smult' W"
  shows   "IrrFinGroupRepresentation G smult V"
proof (rule FinGroupRepresentation.IrrI)
  from assms show "FinGroupRepresentation G (\<cdot>) V"
    using IrrFinGroupRepresentation.axioms(1) isomorphic_sym
          FinGroupRepresentation.isomorphic_imp_GRep
    by    fast
  from assms show "\<And>U. GSubspace U \<Longrightarrow> U = 0 \<or> U = V"
    using IrrFinGroupRepresentation.irr isomorphic_to_irr_right' by fast
qed

lemma (in FinGroupRepresentation) IrrGSubspace_iso_constituent :
  assumes nonzero : "V \<noteq> 0"
  and     subsp   : "W \<subseteq> V" "W \<noteq> 0" "IrrFinGroupRepresentation G smult W"
  and     V_decomp: "\<forall>U\<in>set Us. IrrFinGroupRepresentation G smult U"
                    "0 \<notin> set Us" "V = (\<Oplus>U\<leftarrow>Us. U)"
  shows   "\<exists>U\<in>set Us. FGModule.isomorphic G smult W smult U"
proof-
  from V_decomp(1) have abGrp: "\<forall>U\<in>set Us. AbGroup U"
    using IrrFinGroupRepresentation.AbGroup by fast
  from nonzero V_decomp(3) have indep: "add_independentS Us"
    using inner_dirsumD2 by fast
  with V_decomp (3) have "\<forall>U\<in>set Us. U \<subseteq> V"
    using abGrp AbGroup_subset_inner_dirsum by fast
  with subsp(1,3) V_decomp(1)
    have  GSubspaces: "GSubspace W" "\<forall>U\<in> set Us. GSubspace U"
    using IrrFinGroupRepresentation.axioms(1)[of G smult]
          FinGroupRepresentation.axioms(1)[of G smult] GSubspaceI
    by    auto
  have "\<And>i. i < length Us \<Longrightarrow> (\<Oplus>Us\<down>i) ` W \<noteq> 0
              \<Longrightarrow> FGModuleIso G smult W smult ( (\<Oplus>Us\<down>i) \<down> W ) (Us!i)"
  proof-
    fix i assume i: "i < length Us" "(\<Oplus>Us\<down>i) ` W \<noteq> 0"
    from i(1) V_decomp(3) have "GRepEnd (\<Oplus>Us\<down>i)"
      using GSubspaces(2) indep GEnd_inner_dirsum_el_decomp_nth by fast
    hence "FGModuleHom G smult W smult ( (\<Oplus>Us\<down>i) \<down> W )"
      using GSubspaces(1) FGModuleEnd.FGModuleHom_restrict0_GSubspace
      by    fast
    moreover have "( (\<Oplus>Us\<down>i) \<down> W ) ` W \<subseteq> Us!i"
    proof-
      from V_decomp(3) i(1) subsp(1,3) have "(\<Oplus>Us\<down>i) ` W \<subseteq> Us!i"
        using indep abGrp AbGroup_inner_dirsum_el_decomp_nth_onto_nth by fast
      thus ?thesis by auto
    qed
    moreover from i(1) V_decomp(1)
      have "IrrFinGroupRepresentation G smult (Us!i)"
      by   simp
    ultimately show "FGModuleIso G smult W smult ( (\<Oplus>Us\<down>i) \<down> W ) (Us!i)"
      using i(2)
            IrrFinGroupRepresentation.Schur1[
              OF subsp(3), of smult "Us!i" "(\<Oplus>Us\<down>i) \<down> W "
            ]
      by    auto
  qed
  moreover from nonzero V_decomp(3)
    have  "\<forall>i<length Us. (\<Oplus>Us\<down>i) ` W = 0 \<Longrightarrow> W = 0"
    using inner_dirsum_Nil abGrp subsp(1) indep
          AbGroup_inner_dirsum_subset_proj_eq_0[of Us W]
    by    fastforce
  ultimately have "\<exists>i<length Us.  FGModuleIso G smult W smult
                        ( (\<Oplus>Us\<down>i) \<down> W ) (Us!i)"
    using subsp(2) by auto
  thus ?thesis using set_conv_nth[of Us] by auto
qed

theorem (in IrrFinGroupRepresentation) iso_FG_constituent :
  assumes nonzero  : "V \<noteq> 0"
  and     FG_decomp: "\<forall>U\<in>set Us. IrrFinGroupRepresentation G (*) U"
                     "0 \<notin> set Us" "FG = (\<Oplus>U\<leftarrow>Us. U)"
  shows   "\<exists>U\<in>set Us. isomorphic (*) U"
proof-
  from nonzero obtain v where v: "v \<in> V" "v \<noteq> 0" using nonempty by auto
  define T where "T = (\<lambda>x. x \<cdot> v)\<down>FG"
  have "FGModuleHom G (*) FG smult T"
  proof (rule FGModule.FGModuleHomI_fromaxioms)
    show "FGModule G (*) FG"
      using ActingGroup.FGModule_FG by fast
    from T_def v(1) show "\<And>v v'. v \<in> FG \<Longrightarrow> v' \<in> FG \<Longrightarrow> T (v + v') = T v + T v'"
      using Ring1.add_closed[OF Ring1] smult_distrib_right by auto
    from T_def show "supp T \<subseteq> FG" using supp_restrict0 by fast
    from T_def v(1) show "\<And>r m. r \<in> FG \<Longrightarrow> m \<in> FG \<Longrightarrow> T (r * m) = r \<cdot> T m"
      using ActingGroup.RG_mult_closed by auto
  qed
  then obtain W
    where W: "FGModule.GSubspace G (*) FG W" "FG = W \<oplus> (ker T \<inter> FG)"
             "FGModule.isomorphic G (*) W smult (T ` FG)"
    using FG_n0
          FinGroupRepresentation.GRepHom_decomp[
            OF FinGroupRepresentation_FG
          ]
    by    fast
  from T_def v have "T ` FG = V" using eq_GSpan_single RSpan_single by auto
  with W(3) have W': "FGModule.isomorphic G (*) W smult V" by fast
  with W(1) nonzero have "W \<noteq> 0"
    using FGModule.GSubspace_is_FGModule[OF ActingGroup.FGModule_FG]
          FGModule.isomorphic_to_zero_left
    by    fastforce
  moreover from W' have "IrrFinGroupRepresentation G (*) W"
    using IrrFinGroupRepresentation_axioms FGModuleIso.isomorphic_to_irr_right
    by    fast
  ultimately have "\<exists>U\<in>set Us. FGModule.isomorphic G (*) W (*) U"
    using FG_decomp W(1) good_char FG_n0
          FinGroupRepresentation.IrrGSubspace_iso_constituent[
            OF ActingGroup.FinGroupRepresentation_FG, of W
          ]
    by    simp
  with W(1) W' show ?thesis
    using FGModule.GSubspace_is_FGModule[OF ActingGroup.FGModule_FG]
          FGModule.isomorphic_sym[of G "(*)" W smult] isomorphic_trans
    by    fast
qed


subsection \<open>Isomorphism classes of irreducible representations\<close>

text \<open>
  We have already demonstrated that the relation \<open>FGModule.isomorphic\<close> is reflexive
  (lemma \<open>FGModule.isomorphic_refl\<close>), symmetric (lemma \<open>FGModule.isomorphic_sym\<close>),
  and transitive (lemma \<open>FGModule.isomorphic_trans\<close>). In this section, we provide a finite
  set of representatives for the resulting isomorphism classes of irreducible representations.
\<close>

context Group
begin

primrec remisodups :: "('f::field,'g) aezfun set list \<Rightarrow> ('f,'g) aezfun set list" where
  "remisodups [] = []"
| "remisodups (U # Us) = (if
        (\<exists>W\<in>set Us. FGModule.isomorphic G (*) U (*) W)
          then remisodups Us else U # remisodups Us)"

lemma set_remisodups : "set (remisodups Us) \<subseteq> set Us"
  by (induct Us) auto

lemma isodistinct_remisodups :
  "\<lbrakk> \<forall>U\<in>set Us. FGModule G (*) U; V \<in> set (remisodups Us);
        W \<in> set (remisodups Us); V \<noteq> W \<rbrakk>
          \<Longrightarrow> \<not> (FGModule.isomorphic G (*) V (*) W)"
proof (induct Us arbitrary: V W)
  case (Cons U Us)
  show ?case
  proof (cases "\<exists>X\<in>set Us. FGModule.isomorphic G (*) U (*) X")
    case True with Cons show ?thesis by simp
  next
    case False show ?thesis
    proof (cases "V=U" "W=U" rule: conjcases)
      case BothTrue with Cons(5) show ?thesis by fast
    next
      case OneTrue with False Cons(4,5) show ?thesis
        using set_remisodups by auto
    next
      case OtherTrue with False Cons(2,3) show ?thesis
        using set_remisodups FGModule.isomorphic_sym[of G "(*)" V "(*)" W]
        by    fastforce
    next
      case BothFalse with Cons False show ?thesis by simp
    qed
  qed
qed simp

definition "FG_constituents \<equiv> SOME Us.
                  (\<forall>U\<in>set Us. IrrFinGroupRepresentation G (*) U)
                    \<and> 0 \<notin> set Us \<and> group_ring = (\<Oplus>U\<leftarrow>Us. U)"

lemma FG_constituents_irr :
  "of_nat (card G) \<noteq> (0::'f::field)
        \<Longrightarrow> \<forall>U\<in>set (FG_constituents::('f,'g) aezfun set list). 
          IrrFinGroupRepresentation G (*) U"
  using someI_ex[OF FG_reducible] unfolding FG_constituents_def by fast

lemma FG_consitutents_n0:
  "of_nat (card G) \<noteq> (0::'f::field)
        \<Longrightarrow> 0 \<notin> set (FG_constituents::('f,'g) aezfun set list)"
  using someI_ex[OF FG_reducible] unfolding FG_constituents_def by fast

lemma FG_constituents_constituents :
  "of_nat (card G) \<noteq> (0::'f::field)
        \<Longrightarrow> (group_ring::('f,'g) aezfun set) = (\<Oplus>U\<leftarrow>FG_constituents. U)"
  using someI_ex[OF FG_reducible] unfolding FG_constituents_def by fast

definition "GIrrRep_repset \<equiv> 0 \<union> set (remisodups FG_constituents)"

lemma finite_GIrrRep_repset : "finite GIrrRep_repset"
  unfolding GIrrRep_repset_def by simp

lemma all_irr_GIrrRep_repset :
  assumes "of_nat (card G) \<noteq> (0::'f::field)"
  shows "\<forall>U\<in>(GIrrRep_repset::('f,'g) aezfun set set).
              IrrFinGroupRepresentation G (*) U"
proof
  fix U :: "('f,'g) aezfun set" assume "U \<in> GIrrRep_repset"
  with assms show "IrrFinGroupRepresentation G (*) U"
    using trivial_IrrFinGroupRepresentation_in_FG GIrrRep_repset_def
          set_remisodups FG_constituents_irr
    by    (cases "U = 0") auto
qed

lemma isodistinct_GIrrRep_repset :
  defines "GIRRS \<equiv> GIrrRep_repset :: ('f::field,'g) aezfun set set"
  assumes "of_nat (card G) \<noteq> (0::'f)" "V \<in> GIRRS" "W \<in> GIRRS" "V \<noteq> W"
  shows   "\<not> (FGModule.isomorphic G (*) V (*) W)"
proof (cases "V = 0" "W = 0" rule: conjcases)
  case BothTrue with assms(5) show ?thesis by fast
next
  case OneTrue with assms(1,2,4,5) show ?thesis
    using GIrrRep_repset_def set_remisodups FG_consitutents_n0
          trivial_FGModule[of "(*)"] FGModule.isomorphic_to_zero_left[of G "(*)"]
    by    fastforce
next
  case OtherTrue
  moreover with assms(1,3) have "V \<in> set FG_constituents"
    using GIrrRep_repset_def set_remisodups by auto
  ultimately show ?thesis
    using assms(2) FG_consitutents_n0 FG_constituents_irr
          IrrFinGroupRepresentation.axioms(1)
          FinGroupRepresentation.axioms(1)
          FGModule.isomorphic_to_zero_right[of G "(*)" V "(*)"]
    by    fastforce
next
  case BothFalse
  with assms(1,3,4) have "V \<in> set (remisodups FG_constituents)"
                         "W \<in> set (remisodups FG_constituents)"
    using GIrrRep_repset_def by auto
  with assms(2,5) show ?thesis
    using FG_constituents_irr IrrFinGroupRepresentation.axioms(1)
          FinGroupRepresentation.axioms(1) isodistinct_remisodups
    by    fastforce
qed

end (* context Group *)

lemma (in FGModule) iso_in_list_imp_iso_in_remisodups :
  "\<exists>U\<in>set Us. isomorphic (*) U
        \<Longrightarrow> \<exists>U\<in>set (ActingGroup.remisodups Us). isomorphic (*) U"
proof (induct Us)
  case (Cons U Us)
  from Cons(2) obtain W where W: "W \<in> set (U#Us)" "isomorphic (*) W"
    by fast
  show ?case
  proof (
    cases "W = U" "\<exists>X\<in>set Us. FGModule.isomorphic G (*) U (*) X"
    rule: conjcases
  )
    case BothTrue with W(2) Cons(1) show ?thesis
      using isomorphic_trans[of "(*)" W] by force
  next
    case OneTrue with W(2) show ?thesis by simp
  next
    case OtherTrue with Cons(1) W show ?thesis by auto
  next
    case BothFalse with Cons(1) W show ?thesis by auto
  qed
qed simp

lemma (in IrrFinGroupRepresentation) iso_to_GIrrRep_rep :
  "\<exists>U\<in>ActingGroup.GIrrRep_repset. isomorphic (*) U"
  using zero_isomorphic_to_FG_zero ActingGroup.GIrrRep_repset_def
        good_char ActingGroup.FG_constituents_irr
        ActingGroup.FG_consitutents_n0 ActingGroup.FG_constituents_constituents
        iso_FG_constituent iso_in_list_imp_iso_in_remisodups
        ActingGroup.GIrrRep_repset_def
  by    (cases "V = 0") auto

theorem (in Group) iso_class_reps :
  defines "GIRRS \<equiv> GIrrRep_repset :: ('f::field,'g) aezfun set set"
  assumes "of_nat (card G) \<noteq> (0::'f)"
  shows "finite GIRRS"
        "\<forall>U\<in>GIRRS. IrrFinGroupRepresentation G (*) U"
        "\<And>U W. \<lbrakk> U \<in> GIRRS; W \<in> GIRRS; U \<noteq> W \<rbrakk>
              \<Longrightarrow> \<not> (FGModule.isomorphic G (*) U (*) W)"
        "\<And>fgsmult V. IrrFinGroupRepresentation G fgsmult V
              \<Longrightarrow> \<exists>U\<in>GIRRS. FGModule.isomorphic G fgsmult V (*) U"
  using assms finite_GIrrRep_repset all_irr_GIrrRep_repset
        isodistinct_GIrrRep_repset IrrFinGroupRepresentation.iso_to_GIrrRep_rep
  by    auto


subsection \<open>Induced representations\<close>

subsubsection \<open>Locale and basic facts\<close>

locale InducedFinGroupRepresentation = Supgroup?: Group H
+ BaseRep?: FinGroupRepresentation G smult V
+ induced_smult?: aezfun_scalar_mult rrsmult
  for   H       :: "'g::group_add set"
  and   G       :: "'g set"
  and   smult   :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixl "\<cdot>" 70)
  and   V       :: "'v set"
  and   rrsmult :: "('f,'g) aezfun \<Rightarrow> (('f,'g) aezfun \<Rightarrow>'v)
                          \<Rightarrow> (('f,'g) aezfun \<Rightarrow>'v)" (infixl "\<currency>" 70)
+ fixes FH      :: "('f, 'g) aezfun set"
  and   indV    :: "(('f, 'g) aezfun \<Rightarrow> 'v) set"
  defines FH            : "FH \<equiv> Supgroup.group_ring"
  and     indV          : "indV \<equiv> BaseRep.indspace G FH V"
  assumes rrsmult       : "rrsmult = Ring1.rightreg_scalar_mult FH"
  and     good_ordSupgrp: "of_nat (card H) \<noteq> (0::'f)"  (* this implies H is finite *)
  and     Subgroup      : "Supgroup.Subgroup G"  (* G is a subgroup of H *)

sublocale InducedFinGroupRepresentation < InducedFHModule 
  using FH indV rrsmult Subgroup by unfold_locales fast

context InducedFinGroupRepresentation
begin

abbreviation ordH :: 'f where "ordH \<equiv> of_nat (card H)"
abbreviation "is_Vfbasis \<equiv> fbasis_for V"
abbreviation "GRepHomSet \<equiv> FGModuleHomSet G smult V"
abbreviation "HRepHom    \<equiv> FGModuleHom H rrsmult indV"
abbreviation "HRepHomSet \<equiv> FGModuleHomSet H rrsmult indV"

lemma finiteSupgroup: "finite H"
  using good_ordSupgrp good_card_imp_finite by fast

lemma FinGroupSupgroup : "FinGroup H"
  using finiteSupgroup Supgroup.FinGroupI by fast

lemmas fVectorSpace          = fVectorSpace
lemmas FinDimVectorSpace     = FinDimVectorSpace
lemmas ex_rcoset_replist_hd0
              = FinGroup.ex_rcoset_replist_hd0[OF FinGroupSupgroup Subgroup]

end (* context InducedFinGroupRepresentation *)

subsubsection \<open>A basis for the induced space\<close>

context InducedFinGroupRepresentation
begin

abbreviation "negHorbit_list \<equiv> induced_smult.negGorbit_list"

lemmas ex_rcoset_replist
              = FinGroup.ex_rcoset_replist[OF FinGroupSupgroup Subgroup]
lemmas length_negHorbit_list         = induced_smult.length_negGorbit_list
lemmas length_negHorbit_list_sublist = induced_smult.length_negGorbit_list_sublist
lemmas negHorbit_list_indV           = FGModule.negGorbit_list_V[OF FHModule_indspace]

lemma flincomb_Horbit_induced_veclist_reduce :
  fixes   vs         :: "'v list"
  and     hs         :: "'g list"
  defines hfvss       : "hfvss \<equiv> negHorbit_list hs induced_vector vs"
  assumes vs          : "set vs \<subseteq> V" and i: "i < length hs"
  and     scalars     : "list_all2 (\<lambda>rs ms. length rs = length ms) css hfvss"
  and     rcoset_reps : "Supgroup.is_rcoset_replist G hs"
  shows   "((concat css) \<bullet>\<currency>\<currency> (concat hfvss)) (1 \<delta>\<delta> (hs!i)) = (css!i) \<bullet>\<sharp>\<cdot> vs"
proof-
  have mostly_zero:
    "\<And>k j. k < length hs \<Longrightarrow> j < length hs 
          \<Longrightarrow> ((css!j) \<bullet>\<currency>\<currency> (hfvss!j)) (1 \<delta>\<delta> hs!k)
            = (if j = k then (css!k) \<bullet>\<sharp>\<cdot> vs else 0)"
  proof-
    fix k j assume k: "k < length hs" and j: "j < length hs"
    hence hsk_H: "hs!k \<in> H" and hsj_H: "hs!j \<in> H"
      using Supgroup.is_rcoset_replistD_set[OF rcoset_reps] by auto
    define LHS where "LHS = ((css!j) \<bullet>\<currency>\<currency> (hfvss!j)) (1 \<delta>\<delta> hs!k)"
    with hfvss
      have "LHS = (\<Sum>(r,m)\<leftarrow>zip (css!j) (hfvss!j). (r \<currency>\<currency> m) (1 \<delta>\<delta> hs!k))"
      using length_negHorbit_list scalar_mult.lincomb_def[of induced_smult.fsmult]
            sum_list_prod_fun_apply
      by    simp
    moreover have "\<forall>(r,m) \<in> set (zip (css!j) (hfvss!j)).
                        (induced_smult.fsmult r m) (1 \<delta>\<delta> hs!k) = r \<sharp>\<cdot> m (1 \<delta>\<delta> hs!k)"
    proof (rule prod_ballI)
      fix r m assume "(r,m) \<in> set (zip (css!j) (hfvss!j))"
      with k j vs hfvss
        show "(induced_smult.fsmult r m) (1 \<delta>\<delta> hs!k) = r \<sharp>\<cdot> m (1 \<delta>\<delta> hs!k)"
        using Supgroup.is_rcoset_replistD_set[OF rcoset_reps] set_zip_rightD
              set_concat length_negHorbit_list[of hs induced_vector vs]
              nth_mem[of j hfvss] hsk_H induced_fsmult_conv_fsmult_1ddh[of m "hs!k" r]
              induced_vector_indV negHorbit_list_indV[of hs induced_vector vs]
        by    force
    qed
    ultimately have
      "LHS = (\<Sum>(r,v)\<leftarrow>zip (css!j) vs.
            r \<sharp>\<cdot> (induced_vector v) (1 \<delta>\<delta> hs!k * (1 \<delta>\<delta> - hs!j)))"
      using FH j hfvss induced_smult.negGorbit_list_def[of hs induced_vector vs]
            sum_list_prod_cong[of _ "\<lambda>r m. (induced_smult.fsmult r m) (1 \<delta>\<delta> hs!k)"]
            sum_list_prod_map2[of
              "\<lambda>r m. r \<sharp>\<cdot> m (1 \<delta>\<delta> hs!k)" _ "Hmult (- hs!j)" "map induced_vector vs"
            ]
            sum_list_prod_map2[of "\<lambda>r v. r \<sharp>\<cdot> (Hmult (-hs!j) v) (1 \<delta>\<delta> hs!k)"]
            induced_smult.GmultD hsk_H
            Supgroup.RG_aezdeltafun_closed[of "hs!k" "1::'f"]
            rrsmultD1[of "1 \<delta>\<delta> (hs!k)"]
      by    force
    moreover have "(1::'f) \<delta>\<delta> hs!k * (1 \<delta>\<delta> - hs!j) = 1 \<delta>\<delta> (hs!k - hs!j)"
      using times_aezdeltafun_aezdeltafun[of "1::'f" "hs!k" 1 "-(hs!j)"]
      by (simp add: algebra_simps)
    ultimately have "LHS = (\<Sum>(r,v)\<leftarrow>zip (css!j) vs.
                          r \<sharp>\<cdot> (induced_vector v) (1 \<delta>\<delta> (hs!k - hs!j)))"
      using sum_list_prod_map2 by simp
    moreover from FH vs
      have "\<forall>(r,v) \<in> set (zip (css!j) vs). r \<sharp>\<cdot> (induced_vector v) (1 \<delta>\<delta> (hs!k - hs!j))
                  = r \<sharp>\<cdot> (FG_proj (1 \<delta>\<delta> (hs!k - hs!j)) \<cdot> v)"
      using set_zip_rightD induced_vector_def hsk_H hsj_H Supgroup.diff_closed
            Supgroup.RG_aezdeltafun_closed[of _ "1::'f"]
      by    fastforce
    ultimately have calc: "LHS = (\<Sum>(r,v)\<leftarrow>zip (css!j) vs.
                                r \<sharp>\<cdot> (FG_proj (1 \<delta>\<delta> (hs!k - hs!j)) \<cdot> v) )"
      using sum_list_prod_cong by force
    show "LHS = (if j = k then (css!k) \<bullet>\<sharp>\<cdot> vs else 0)"
    proof (cases "j = k")
      case True
      with calc have "LHS = (\<Sum>(r,v)\<leftarrow>zip (css!k) vs. r \<sharp>\<cdot> 1 \<sharp>\<cdot> v)"
        using Group.zero_closed[OF GroupG]
              aezfun_setspan_proj_aezdeltafun[of G "1::'f"]
              BaseRep.fsmult_def
        by    simp
      moreover from vs have "\<forall>(r,v) \<in> set (zip (css!k) vs). r \<sharp>\<cdot> 1 \<sharp>\<cdot> v = r \<sharp>\<cdot> v"
        using set_zip_rightD BaseRep.fsmult_assoc by fastforce
      ultimately show ?thesis
        using True sum_list_prod_cong[of _ "\<lambda>r v. r \<sharp>\<cdot> 1 \<sharp>\<cdot> v"]
              scalar_mult.lincomb_def[of BaseRep.fsmult]
        by    simp
    next
      case False
      with k j calc have "LHS = (\<Sum>(r,v)\<leftarrow>zip (css!j) vs. r \<sharp>\<cdot> (0 \<cdot> v))"
        using Supgroup.is_rcoset_replist_imp_nrelated_nth[OF Subgroup rcoset_reps]
              aezfun_setspan_proj_aezdeltafun[of G "1::'f"]
        by    simp
      moreover from vs have "\<forall>(r,v) \<in> set (zip (css!j) vs). r \<sharp>\<cdot> (0 \<cdot> v) = 0"
        using set_zip_rightD BaseRep.zero_smult by fastforce
      ultimately have "LHS = (\<Sum>(r,v)\<leftarrow>zip (css!j) vs. (0::'v))"
        using sum_list_prod_cong[of _ "\<lambda>r v. r \<sharp>\<cdot> (0 \<cdot> v)"] by simp
      hence "LHS = (\<Sum>rv\<leftarrow>zip (css!j) vs. case_prod (\<lambda>r v. (0::'v)) rv)" by fastforce
      with False show ?thesis by simp
    qed
  qed

  define terms LHS
    where "terms = map (\<lambda>a. case_prod (\<lambda>cs hfvs. (cs \<bullet>\<currency>\<currency> hfvs) (1 \<delta>\<delta> hs!i)) a) (zip css hfvss)"
      and "LHS = ((concat css) \<bullet>\<currency>\<currency> (concat hfvss)) (1 \<delta>\<delta> (hs!i))"
  hence "LHS = sum_list terms"
    using scalars
          VectorSpace.lincomb_concat[OF fVectorSpace_indspace, of css hfvss]
          sum_list_prod_fun_apply
    by    simp
  hence "LHS = (\<Sum>j\<in>{0..<length terms}. terms!j)"
    using sum_list_sum_nth[of terms] by simp
  moreover from terms_def
    have "\<forall>j\<in>{0..<length terms}. terms!j = ((css!j) \<bullet>\<currency>\<currency> (hfvss!j)) (1 \<delta>\<delta> hs!i)"
    by   simp
  ultimately show "LHS = (css!i) \<bullet>\<sharp>\<cdot> vs"
    using terms_def sum.cong scalars list_all2_lengthD[of _ css hfvss] hfvss 
          length_negHorbit_list[of hs induced_vector vs] i mostly_zero
          sum_single_nonzero[
            of "{0..<length hs}" "\<lambda>i j. ((css!j) \<bullet>\<currency>\<currency> (hfvss!j)) (1 \<delta>\<delta> (hs!i))"
               "\<lambda>i. (css!i) \<bullet>\<sharp>\<cdot> vs"
          ]
    by    simp

qed

lemma indspace_fspanning_set :
  fixes   vs         :: "'v list"
  and     hs         :: "'g list"
  defines hfvss       : "hfvss \<equiv> negHorbit_list hs induced_vector vs"
  assumes base_spset  : "set vs \<subseteq> V" "V = BaseRep.fSpan vs"
  and     rcoset_reps : "Supgroup.is_rcoset_replist G hs"
  shows   "indV = induced_smult.fSpan (concat hfvss)"
proof (rule VectorSpace.SpanI[OF fVectorSpace_indspace])
  from base_spset(1) hfvss show "set (concat hfvss) \<subseteq> indV"
    using Supgroup.is_rcoset_replistD_set[OF rcoset_reps]
          induced_vector_indV negHorbit_list_indV
    by    fast
  show "indV \<subseteq> R_scalar_mult.RSpan UNIV (aezfun_scalar_mult.fsmult (\<currency>))
              (concat hfvss)"
  proof

    fix f assume f: "f \<in> indV"
    hence "\<forall>h \<in> set hs. f (1 \<delta>\<delta> h) \<in> V"
      using indV BaseRep.indspaceD_range by fast
    with base_spset(2)
      have  coeffs_exist: "\<forall>h \<in> set hs. \<exists>ahs. length ahs = length vs
                                \<and> f (1 \<delta>\<delta> h) = ahs \<bullet>\<sharp>\<cdot> vs"
      using BaseRep.in_fSpan_obtain_same_length_coeffs
      by    fast
    define f_coeffs
      where "f_coeffs h = (SOME ahs. length ahs = length vs \<and> f (1 \<delta>\<delta> h) = ahs \<bullet>\<sharp>\<cdot> vs)" for h
    define ahss where "ahss = map f_coeffs hs"
    hence len_ahss: "length ahss = length hs" by simp
    with hfvss have len_zip_ahss_hfvss: "length (zip ahss hfvss) = length hs"
      using length_negHorbit_list[of hs induced_vector vs] by simp
    have len_ahss_el: "\<forall>ahs\<in>set ahss. length ahs = length vs"
    proof
      fix ahs assume "ahs \<in> set ahss"
      from this ahss_def obtain h where h: "h \<in> set hs" "ahs = f_coeffs h"
        using set_map by auto
      from h(1) have "\<exists>ahs. length ahs = length vs \<and> f (1 \<delta>\<delta> h) = ahs \<bullet>\<sharp>\<cdot> vs"
        using coeffs_exist by fast
      with h(2) show "length ahs = length vs"
        unfolding f_coeffs_def
        using someI_ex[of "\<lambda>ahs. length ahs = length vs \<and> f (1 \<delta>\<delta> h) = ahs \<bullet>\<sharp>\<cdot> vs"]
        by    fast
    qed
    have "\<forall>(ahs,hfvs)\<in>set (zip ahss hfvss). length ahs = length hfvs"
    proof
      fix x assume x: "x \<in> set (zip ahss hfvss)"
      show "case x of (ahs, hfvs) \<Rightarrow> length ahs = length hfvs"
      proof
        fix ahs hfvs assume "x = (ahs,hfvs)"
        with x hfvss have "length ahs = length vs" "length hfvs = length vs"
          using set_zip_leftD[of ahs hfvs] len_ahss_el set_zip_rightD[of ahs hfvs]
                length_negHorbit_list_sublist[of _ hs induced_vector]
          by    auto
        thus "length ahs = length hfvs" by simp
      qed
    qed
    with hfvss have list_all2_len_ahss_hfvss:
      "list_all2 (\<lambda>rs ms. length rs = length ms) ahss hfvss"
      using len_ahss length_negHorbit_list[of hs induced_vector vs]
            list_all2I[of ahss hfvss]
      by    auto

    define f' where "f' = (concat ahss) \<bullet>\<currency>\<currency> (concat hfvss)"
    have "f = f'"
      using Supgroup.is_rcoset_replistD_set[OF rcoset_reps]
            Supgroup.group_eq_subgrp_rcoset_un[OF Subgroup rcoset_reps]
            f
    proof (rule indspace_el_eq'[of hs])
      from f'_def hfvss base_spset(1) show "f' \<in> indV"
        using Supgroup.is_rcoset_replistD_set[OF rcoset_reps]
              induced_vector_indV negHorbit_list_indV[of hs induced_vector vs]
              FGModule.flincomb_closed[OF FHModule_indspace]
        by    fast
      have "\<And>i. i<length hs \<Longrightarrow> f (1 \<delta>\<delta> (hs!i)) = f' (1 \<delta>\<delta> (hs!i))"
      proof-
        fix i assume i: "i < length hs"
        with f_coeffs_def have "f (1 \<delta>\<delta> (hs!i)) = (f_coeffs (hs!i)) \<bullet>\<sharp>\<cdot> vs"
          using coeffs_exist
                someI_ex[of "\<lambda>ahs. length ahs = length vs \<and> f (1 \<delta>\<delta> hs!i) = ahs \<bullet>\<sharp>\<cdot> vs"]
          by    auto
        moreover from i hfvss f'_def base_spset(1) rcoset_reps ahss_def
          have  "f' (1 \<delta>\<delta> (hs!i)) = (f_coeffs (hs!i)) \<bullet>\<sharp>\<cdot> vs"
          using list_all2_len_ahss_hfvss flincomb_Horbit_induced_veclist_reduce
          by    simp
        ultimately show "f (1 \<delta>\<delta> (hs!i)) = f' (1 \<delta>\<delta> (hs!i))" by simp
      qed
      thus "\<forall>i<length hs. f (1 \<delta>\<delta> (hs!i)) = f' (1 \<delta>\<delta> (hs!i))" by fast
    qed
    with f'_def hfvss base_spset(1) show "f \<in> induced_smult.fSpan (concat hfvss)"
      using Supgroup.is_rcoset_replistD_set[OF rcoset_reps]
            induced_vector_indV negHorbit_list_indV[of hs induced_vector vs]
            VectorSpace.SpanI_lincomb_arb_len_coeffs[OF fVectorSpace_indspace]
      by    fast
  
  qed
qed

lemma indspace_basis :
  fixes   vs         :: "'v list"
  and     hs         :: "'g list"
  defines hfvss       : "hfvss \<equiv> negHorbit_list hs induced_vector vs"
  assumes base_spset  : "BaseRep.fbasis_for V vs"
  and     rcoset_reps : "Supgroup.is_rcoset_replist G hs"
  shows   "fscalar_mult.basis_for induced_smult.fsmult indV (concat hfvss)"
proof-
  from assms
    have  1: "set (concat hfvss) \<subseteq> indV"
      and    "indV = induced_smult.fSpan (concat hfvss)"
    using Supgroup.is_rcoset_replistD_set[OF rcoset_reps]
          induced_vector_indV negHorbit_list_indV[of hs induced_vector vs]
          indspace_fspanning_set[of vs hs]
    by    auto
  moreover have "induced_smult.f_lin_independent (concat hfvss)"
  proof (
    rule VectorSpace.lin_independentI_concat_all_scalars[OF fVectorSpace_indspace],
    rule 1
  )
    fix rss
    assume rss: "list_all2 (\<lambda>xs ys. length xs = length ys) rss hfvss"
                "(concat rss) \<bullet>\<currency>\<currency> (concat hfvss) = 0"
    from rss(1) have len_rss_hfvsss: "length rss = length hfvss"
      using list_all2_lengthD by fast
    with hfvss have len_rss_hs: "length rss = length hs"
      using length_negHorbit_list by fastforce
    show "\<forall>rs\<in>set rss. set rs \<subseteq> 0"
    proof
      fix rs assume "rs \<in> set rss"
      from this obtain i where i: "i < length rss" "rs = rss!i"
        using in_set_conv_nth[of rs] by fast
      with hfvss rss(1) have "length rs = length vs"
        using list_all2_nthD len_rss_hfvsss in_set_conv_nth[of _ hfvss]
              length_negHorbit_list_sublist
        by    fastforce
      moreover from hfvss rss i base_spset(1) rcoset_reps have "rs \<bullet>\<sharp>\<cdot> vs = 0"
        using len_rss_hs flincomb_Horbit_induced_veclist_reduce by force
      ultimately show "set rs \<subseteq> 0"
        using base_spset flin_independentD_all_scalars by force
    qed
  qed
  ultimately show ?thesis by fast
qed

lemma induced_vector_decomp :
  fixes   vs         :: "'v list"
  and     hs         :: "'g list"
  and     cs         :: "'f list"
  defines hfvss       : "hfvss \<equiv> negHorbit_list (0#hs) induced_vector vs"
  and     extrazeros  : "extrazeros \<equiv> replicate ((length hs)*(length vs)) 0"
  assumes base_spset  : "BaseRep.fbasis_for V vs"
  and     rcoset_reps : "Supgroup.is_rcoset_replist G (0#hs)"
  and     cs          : "length cs = length vs"
  and     v           : "v = cs \<bullet>\<sharp>\<cdot> vs"
  shows   "induced_vector v = (cs@extrazeros) \<bullet>\<currency>\<currency> (concat hfvss)"
proof-
  from hfvss base_spset
    have  "hfvss = (map induced_vector vs) # (negHorbit_list hs induced_vector vs)"
    using induced_vector_indV
          FGModule.negGorbit_list_Cons0[OF FHModule_indspace]
    by    fastforce
  with cs extrazeros base_spset rcoset_reps v
    show  "induced_vector v = (cs@extrazeros) \<bullet>\<currency>\<currency> (concat hfvss)"
    using scalar_mult.lincomb_append[of cs _ induced_smult.fsmult]
          Supgroup.is_rcoset_replistD_set induced_vector_indV
          negHorbit_list_indV[of hs induced_vector vs]
          VectorSpace.lincomb_replicate0_left[OF fVectorSpace_indspace]
          FGModuleHom.VectorSpaceHom[OF hom_induced_vector]
          VectorSpaceHom.distrib_lincomb
    by    fastforce
qed

end (* context InducedFinGroupRepresentation *)

subsubsection \<open>The induced space is a representation space\<close>

context InducedFinGroupRepresentation
begin

lemma indspace_findim :
  "fscalar_mult.findim induced_smult.fsmult indV"
proof-
  from BaseRep.findim obtain vs where vs: "set vs \<subseteq> V" "V = BaseRep.fSpan vs"
    by fast
  obtain hs where hs: "Supgroup.is_rcoset_replist G hs"
    using ex_rcoset_replist by fast
  define hfvss where "hfvss = negHorbit_list hs induced_vector vs"
  with vs hs
    have  "set (concat hfvss) \<subseteq> indV" "indV = induced_smult.fSpan (concat hfvss)"
    using Supgroup.is_rcoset_replistD_set[OF hs] induced_vector_indV
          negHorbit_list_indV[of hs induced_vector vs] indspace_fspanning_set
    by    auto
  thus ?thesis by fast
qed

theorem FinGroupRepresentation_indspace :
  "FinGroupRepresentation H rrsmult indV"
  using FHModule_indspace
proof (rule FinGroupRepresentation.intro)
  from good_ordSupgrp show "FinGroupRepresentation_axioms H (\<currency>) indV" 
    using indspace_findim by unfold_locales fast
qed

end (* context InducedFinGroupRepresentation *)


subsection \<open>Frobenius reciprocity\<close>

subsubsection \<open>Locale and basic facts\<close>

text \<open>There are a number of defined objects and lemmas concerning those objects leading up to the
        theorem of Frobenius reciprocity, so we create a locale to contain it all.\<close>

locale FrobeniusReciprocity
= GRep?: InducedFinGroupRepresentation H G smult V rrsmult
+ HRep?: FinGroupRepresentation H smult' W
  for H       :: "'g::group_add set"
  and G       :: "'g set"
  and smult   :: "('f::field, 'g) aezfun \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v" (infixl "\<cdot>" 70)
  and V       :: "'v set"
  and rrsmult :: "('f,'g) aezfun \<Rightarrow> (('f,'g) aezfun \<Rightarrow> 'v)
                        \<Rightarrow> (('f,'g) aezfun \<Rightarrow> 'v)" (infixl "\<currency>" 70)
  and smult'  :: "('f, 'g) aezfun \<Rightarrow> 'w::ab_group_add \<Rightarrow> 'w" (infixr "\<star>" 70)
  and W       :: "'w set"
begin

abbreviation fsmult'   :: "'f \<Rightarrow> 'w \<Rightarrow> 'w"           (infixr "\<sharp>\<star>" 70)
  where "fsmult' \<equiv> HRep.fsmult"
abbreviation flincomb' :: "'f list \<Rightarrow> 'w list \<Rightarrow> 'w" (infixr "\<bullet>\<sharp>\<star>" 70) 
  where "flincomb' \<equiv> HRep.flincomb"
abbreviation Hmult'    :: "'g \<Rightarrow> 'w \<Rightarrow> 'w"           (infixr "*\<star>" 70)
  where "Hmult' \<equiv> HRep.Gmult"

definition Tsmult1 :: 
  "'f \<Rightarrow> ((('f, 'g) aezfun \<Rightarrow> 'v)\<Rightarrow>'w) \<Rightarrow> ((('f, 'g) aezfun \<Rightarrow> 'v)\<Rightarrow>'w)" (infixr "\<star>\<currency>" 70)
  where "Tsmult1 \<equiv> \<lambda>a T. \<lambda>f. a \<sharp>\<star> (T f)"

definition Tsmult2 :: "'f \<Rightarrow> ('v\<Rightarrow>'w) \<Rightarrow> ('v\<Rightarrow>'w)" (infixr "\<star>\<cdot>" 70) 
  where "Tsmult2 \<equiv> \<lambda>a T. \<lambda>v. a \<sharp>\<star> (T v)"

lemma FHModuleW : "FGModule H (\<star>) W" ..

lemma FGModuleW: "FGModule G smult' W"
 using FHModuleW Subgroup HRep.restriction_to_subgroup_is_module
 by    fast

text \<open>
  In order to build an inverse for the required isomorphism of Hom-sets, we will need a basis for
  the induced @{term H}-space.
\<close>

definition Vfbasis :: "'v list" where "Vfbasis \<equiv> (SOME vs. is_Vfbasis vs)"

lemma Vfbasis : "is_Vfbasis Vfbasis"
  using Vfbasis_def FinDimVectorSpace.basis_ex[OF GRep.FinDimVectorSpace] someI_ex
  by    simp

lemma Vfbasis_V : "set Vfbasis \<subseteq> V"
  using Vfbasis by fast

definition nonzero_H_rcoset_reps :: "'g list"
  where "nonzero_H_rcoset_reps \<equiv> (SOME hs. Group.is_rcoset_replist H G (0#hs))"

definition H_rcoset_reps :: "'g list" where "H_rcoset_reps \<equiv> 0 # nonzero_H_rcoset_reps"

lemma H_rcoset_reps : "Group.is_rcoset_replist H G H_rcoset_reps"
  using H_rcoset_reps_def nonzero_H_rcoset_reps_def GRep.ex_rcoset_replist_hd0 someI_ex
  by    simp

lemma H_rcoset_reps_H : "set H_rcoset_reps \<subseteq> H"
  using H_rcoset_reps Group.is_rcoset_replistD_set[OF HRep.GroupG] by fast

lemma nonzero_H_rcoset_reps_H : "set nonzero_H_rcoset_reps \<subseteq> H"
  using H_rcoset_reps_H H_rcoset_reps_def by simp

abbreviation negHorbit_homVfbasis :: "('v \<Rightarrow> 'w) \<Rightarrow> 'w list list"
  where "negHorbit_homVfbasis T \<equiv> HRep.negGorbit_list H_rcoset_reps T Vfbasis"

lemma negHorbit_Hom_indVfbasis_W :
  "T ` V \<subseteq> W \<Longrightarrow> set (concat (negHorbit_homVfbasis T)) \<subseteq> W"
  using H_rcoset_reps_H Vfbasis_V
        HRep.negGorbit_list_V[of H_rcoset_reps T Vfbasis]
  by    fast

lemma negHorbit_HomSet_indVfbasis_W :  
  "T \<in> GRepHomSet smult' W \<Longrightarrow> set (concat (negHorbit_homVfbasis T)) \<subseteq> W"
  using FGModuleHomSetD_Im negHorbit_Hom_indVfbasis_W by fast

definition indVfbasis :: "(('f, 'g) aezfun \<Rightarrow> 'v) list list"
  where "indVfbasis \<equiv> GRep.negHorbit_list H_rcoset_reps induced_vector Vfbasis"

lemma indVfbasis :
  "fscalar_mult.basis_for induced_smult.fsmult indV (concat indVfbasis)"
  using Vfbasis H_rcoset_reps indVfbasis_def indspace_basis[of Vfbasis H_rcoset_reps]
  by    auto

lemma indVfbasis_indV : "hfvs \<in> set indVfbasis \<Longrightarrow> set hfvs \<subseteq> indV"
  using indVfbasis by auto

end (* context FrobeniusReciprocity *)

subsubsection \<open>The required isomorphism of Hom-sets\<close>

context FrobeniusReciprocity
begin

text \<open>The following function will demonstrate the required isomorphism of Hom-sets (as vector
        spaces).\<close>

definition \<phi> :: "((('f, 'g) aezfun \<Rightarrow> 'v) \<Rightarrow> 'w) \<Rightarrow> ('v \<Rightarrow> 'w)"
  where "\<phi> \<equiv> restrict0 (\<lambda>T. T \<circ> GRep.induced_vector) (HRepHomSet smult' W)"

lemma \<phi>_im : "\<phi> ` HRepHomSet (\<star>) W \<subseteq> GRepHomSet (\<star>) W"
proof (rule image_subsetI)

  fix T assume T: "T \<in> HRepHomSet (\<star>) W"
  show "\<phi> T \<in> GRepHomSet (\<star>) W"
  proof (rule FGModuleHomSetI)

    from T have "FGModuleHom G rrsmult indV smult' T"
      using FGModuleHomSetD_FGModuleHom GRep.Subgroup
            FGModuleHom.restriction_to_subgroup_is_hom
      by    fast
    thus "BaseRep.GRepHom (\<star>) (\<phi> T)"
      using T \<phi>_def GRep.hom_induced_vector GRep.induced_vector_indV
            FGModuleHom.FGModHom_composite_left
      by    fastforce

      show "\<phi> T ` V \<subseteq> W"
        using T \<phi>_def GRep.induced_vector_indV FGModuleHomSetD_Im by fastforce

  qed

qed

end (* context FrobeniusReciprocity *)

subsubsection \<open>The inverse map of Hom-sets\<close>

text \<open>In this section we build an inverse for the required isomorphism, @{term "\<phi>"}.\<close>

context FrobeniusReciprocity
begin

definition \<psi>_condition :: "('v \<Rightarrow> 'w) \<Rightarrow> ((('f, 'g) aezfun \<Rightarrow> 'v) \<Rightarrow> 'w) \<Rightarrow> bool"
  where "\<psi>_condition T S
              \<equiv> VectorSpaceHom induced_smult.fsmult indV fsmult' S 
                \<and> map (map S) indVfbasis = negHorbit_homVfbasis T"

lemma inverse_im_exists' :
  assumes "T \<in> GRepHomSet (\<star>) W"
  shows   "\<exists>! S. VectorSpaceHom induced_smult.fsmult indV fsmult' S
                \<and> map S (concat indVfbasis) = concat (negHorbit_homVfbasis T)"
proof (
  rule VectorSpace.basis_im_defines_hom, rule fVectorSpace_indspace,
  rule HRep.fVectorSpace, rule indVfbasis
)
  from  assms show "set (concat (negHorbit_homVfbasis T)) \<subseteq> W"
    using negHorbit_HomSet_indVfbasis_W by fast
  show  "length (concat (negHorbit_homVfbasis T)) = length (concat indVfbasis)"
    using length_concat_negGorbit_list indVfbasis_def
          induced_smult.length_concat_negGorbit_list[of H_rcoset_reps induced_vector]
    by    simp
qed

lemma inverse_im_exists :
  assumes "T \<in> GRepHomSet (\<star>) W"
  shows   "\<exists>! S. \<psi>_condition T S"
proof-
  have "\<exists> S. \<psi>_condition T S"
  proof-
    from assms obtain S
      where S: "VectorSpaceHom induced_smult.fsmult indV fsmult' S" 
               "map S (concat indVfbasis) = concat (negHorbit_homVfbasis T)"
      using inverse_im_exists'
      by    fast
    from S(2) have "concat (map (map S) indVfbasis)
                          = concat (negHorbit_homVfbasis T)"
      using map_concat[of S] by simp
    moreover have "list_all2 (\<lambda>xs ys. length xs = length ys)
                        (map (map S) indVfbasis) (negHorbit_homVfbasis T)"
    proof (rule iffD2[OF list_all2_iff], rule conjI)
      show "length (map (map S) indVfbasis) = length (negHorbit_homVfbasis T)"
        using indVfbasis_def induced_smult.length_negGorbit_list
              HRep.length_negGorbit_list[of H_rcoset_reps T]
        by    auto
      show "\<forall>(xs,ys)\<in>set (zip (map (map S) indVfbasis)
                  (negHorbit_homVfbasis T)). length xs = length ys"
      proof (rule prod_ballI)
        fix xs ys
        assume xsys: "(xs,ys) \<in> set (zip (map (map S) indVfbasis)
                            (negHorbit_homVfbasis T))"
        from this obtain zs where zs: "zs \<in> set indVfbasis" "xs = map S zs"
          using set_zip_leftD by fastforce
        with xsys show "length xs = length ys"
          using indVfbasis_def set_zip_rightD[of xs ys]
                HRep.length_negGorbit_list_sublist[of ys H_rcoset_reps T Vfbasis]
                induced_smult.length_negGorbit_list_sublist
          by    simp
      qed
    qed
    ultimately have "map (map S) indVfbasis = negHorbit_homVfbasis T"
      using concat_eq[of "map (map S) indVfbasis"] by fast
    with S(1) show ?thesis using \<psi>_condition_def by fast
  qed
  moreover have "\<And>S U. \<psi>_condition T S \<Longrightarrow> \<psi>_condition T U \<Longrightarrow> S = U"
  proof-
    fix S U assume "\<psi>_condition T S" "\<psi>_condition T U"
    hence "VectorSpaceHom induced_smult.fsmult indV fsmult' S"
          "map S (concat indVfbasis) = concat (negHorbit_homVfbasis T)"
          "VectorSpaceHom induced_smult.fsmult indV fsmult' U"
          "map U (concat indVfbasis) = concat (negHorbit_homVfbasis T)"
      using \<psi>_condition_def map_concat[of S] map_concat[of U] by auto
    with assms show "S = U" using inverse_im_exists' by fast
  qed
  ultimately show ?thesis by fast
qed

definition \<psi> :: "('v \<Rightarrow> 'w) \<Rightarrow> ((('f, 'g) aezfun \<Rightarrow> 'v) \<Rightarrow> 'w)"
  where "\<psi> \<equiv> restrict0 (\<lambda>T. THE S. \<psi>_condition T S) (GRepHomSet (\<star>) W)"

lemma \<psi>D : "T \<in> GRepHomSet (\<star>) W \<Longrightarrow> \<psi>_condition T (\<psi> T)"
  using \<psi>_def inverse_im_exists[of T] theI'[of "\<lambda>S. \<psi>_condition T S"] by simp

lemma \<psi>D_VectorSpaceHom :
  "T \<in> GRepHomSet (\<star>) W
        \<Longrightarrow> VectorSpaceHom induced_smult.fsmult indV fsmult' (\<psi> T)"
  using \<psi>D \<psi>_condition_def by fast

lemma \<psi>D_im :
  "T \<in> GRepHomSet (\<star>) W \<Longrightarrow> map (map (\<psi> T)) indVfbasis
        = aezfun_scalar_mult.negGorbit_list (\<star>) H_rcoset_reps T Vfbasis"
  using \<psi>D \<psi>_condition_def by fast

lemma \<psi>D_im_single :
  assumes "T \<in> GRepHomSet (\<star>) W" "h \<in> set H_rcoset_reps" "v \<in> set Vfbasis"
  shows   "\<psi> T ((- h) *\<currency> (induced_vector v)) = (-h) *\<star> (T v)"
proof-
  from assms(2,3) obtain i j
    where i: "i < length H_rcoset_reps" "h = H_rcoset_reps!i"
    and   j: "j < length Vfbasis" "v = Vfbasis!j"
    using set_conv_nth[of H_rcoset_reps] set_conv_nth[of Vfbasis] by auto
  moreover
    hence "map (map (\<psi> T)) indVfbasis !i !j = \<psi> T ((-h) *\<currency> (induced_vector v))"
    using indVfbasis_def
          aezfun_scalar_mult.length_negGorbit_list[
            of rrsmult H_rcoset_reps induced_vector
          ]
          aezfun_scalar_mult.negGorbit_list_nth[
            of i H_rcoset_reps rrsmult induced_vector
          ]
    by    auto
  ultimately show ?thesis
    using assms(1) HRep.negGorbit_list_nth[of i H_rcoset_reps T] \<psi>D_im by simp
qed

lemma \<psi>T_W :
  assumes "T \<in> GRepHomSet (\<star>) W"
  shows   "\<psi> T ` indV \<subseteq> W"
proof (rule image_subsetI)
  from assms have T: "VectorSpaceHom induced_smult.fsmult indV fsmult' (\<psi> T)"
    using \<psi>D_VectorSpaceHom by fast
  fix f assume "f \<in> indV"
  from this obtain cs 
    where cs:"length cs = length (concat indVfbasis)" "f = cs \<bullet>\<currency>\<currency> (concat indVfbasis)"
    using indVfbasis scalar_mult.in_Span_obtain_same_length_coeffs
    by    fast
  from cs(1) obtain css
    where css: "cs = concat css" "list_all2 (\<lambda>xs ys. length xs = length ys) css indVfbasis"
    using match_concat
    by    fast
  from assms cs(2) css
    have "\<psi> T f = \<psi> T (\<Sum>(cs,hfvs)\<leftarrow>zip css indVfbasis. cs \<bullet>\<currency>\<currency> hfvs)"
    using VectorSpace.lincomb_concat[OF fVectorSpace_indspace] by simp
  also have "\<dots> = (\<Sum>(cs,hfvs)\<leftarrow>zip css indVfbasis. \<psi> T  (cs \<bullet>\<currency>\<currency> hfvs))"
    using set_zip_rightD[of _ _ css indVfbasis] indVfbasis_indV
          VectorSpace.lincomb_closed[OF GRep.fVectorSpace_indspace]
          VectorSpaceHom.im_sum_list_prod[OF T]
    by    force
  finally have "\<psi> T f = (\<Sum>(cs,\<psi>Thfvs)\<leftarrow>zip css (map (map (\<psi> T)) indVfbasis).
                      cs \<bullet>\<sharp>\<star> \<psi>Thfvs)"
    using set_zip_rightD[of _ _ css indVfbasis] indVfbasis_indV
          VectorSpaceHom.distrib_lincomb[OF T] 
          sum_list_prod_cong[of
            "zip css indVfbasis" "\<lambda>cs hfvs. \<psi> T (cs \<bullet>\<currency>\<currency> hfvs)" 
            "\<lambda>cs hfvs. cs \<bullet>\<sharp>\<star> (map (\<psi> T) hfvs)"
          ]
          sum_list_prod_map2[of "\<lambda>cs \<psi>Thfvs. cs \<bullet>\<sharp>\<star> \<psi>Thfvs" css "map (\<psi> T)"]
    by    fastforce
  moreover from css(2)
    have "list_all2 (\<lambda>xs ys. length xs = length ys) css (map (map (\<psi> T)) indVfbasis)"
    using list_all2_iff[of _ css indVfbasis] set_zip_map2
          list_all2_iff[of _ css "map (map (\<psi> T)) indVfbasis"]
    by    force
  ultimately have "\<psi> T f = (concat css) \<bullet>\<sharp>\<star> (concat (negHorbit_homVfbasis T))"
    using HRep.flincomb_concat map_concat[of "\<psi> T"] \<psi>D_im[OF assms]
    by    simp
  thus "\<psi> T f \<in> W"
    using assms negHorbit_HomSet_indVfbasis_W HRep.flincomb_closed by simp
qed

lemma \<psi>T_Hmap_on_indVfbasis :
  assumes "T \<in> GRepHomSet (\<star>) W"
  shows   "\<And>x f. x \<in> H \<Longrightarrow> f \<in> set (concat indVfbasis)
                \<Longrightarrow> \<psi> T (x *\<currency> f) = x *\<star> (\<psi> T f)"
proof-
  fix x f assume x: "x \<in> H" and f: "f \<in> set (concat indVfbasis)"
  from f obtain i where i: "i < length indVfbasis" "f \<in> set (indVfbasis!i)"
    using set_concat set_conv_nth[of indVfbasis] by auto
  from i(1) have i': "i < length H_rcoset_reps"
    using indVfbasis_def
          aezfun_scalar_mult.length_negGorbit_list[
            of rrsmult H_rcoset_reps induced_vector
          ]
    by    simp
  define hi where "hi = H_rcoset_reps!i"
  with i' have hi_H: "hi \<in> H" using set_conv_nth H_rcoset_reps_H by fast
  from hi_def i(2) have "f \<in> set (map (Hmult (-hi) \<circ> induced_vector) Vfbasis)"
    using indVfbasis_def i'
          aezfun_scalar_mult.negGorbit_list_nth[
            of i H_rcoset_reps rrsmult induced_vector
          ]
    by    simp
  from this obtain v where v: "v \<in> set Vfbasis" "f = (-hi) *\<currency> (induced_vector v)"
    by auto
  from v(1) have v_V: "v \<in> V" and Tv_W: "T v \<in> W"
    using Vfbasis_V FGModuleHomSetD_Im[OF assms] by auto
  from x have "hi - x \<in> H" using hi_H Supgroup.diff_closed by fast
  from this obtain j
    where j: "j < length H_rcoset_reps" "hi - x \<in> G + {H_rcoset_reps!j}"
    using set_conv_nth[of H_rcoset_reps] H_rcoset_reps
          Group.group_eq_subgrp_rcoset_un[OF HRep.GroupG Subgroup H_rcoset_reps]
    by    force
  from j(1) have j': "j < length indVfbasis"
    using indVfbasis_def
          aezfun_scalar_mult.length_negGorbit_list[
            of rrsmult H_rcoset_reps induced_vector
          ]
    by    simp
  define hj where "hj = H_rcoset_reps!j"
  with j(1) have hj_H: "hj \<in> H" using set_conv_nth H_rcoset_reps_H by fast
  from hj_def j(2) obtain g where g: "g \<in> G" "hi - x = g + hj"
    unfolding set_plus_def by fast
  from g(2) have x_hi: "x - hi = - hj + - g"
    using minus_diff_eq[of hi x] minus_add[of g] by simp
  from g(1) have "-g *\<cdot> v \<in> V"
    using v_V ActingGroup.neg_closed BaseRep.Gmult_closed by fast
  from this obtain cs
    where cs: "length cs = length Vfbasis" "-g *\<cdot> v = cs \<bullet>\<sharp>\<cdot> Vfbasis"
    using Vfbasis
          VectorSpace.in_Span_obtain_same_length_coeffs[OF GRep.fVectorSpace]
    by    fast

  from v(2) x have "\<psi> T (x *\<currency> f) = \<psi> T ((x-hi) *\<currency> (induced_vector v))"
    using hi_H Supgroup.neg_closed v_V induced_vector_indV
          FGModule.Gmult_assoc[OF GRep.FHModule_indspace]
    by    (simp add: algebra_simps)
  also from g(1) have "\<dots> = \<psi> T ((-hj) *\<currency> (induced_vector (-g *\<cdot> v)))"
    using x_hi hj_H Subgroup Supgroup.neg_closed v_V induced_vector_indV
          FGModule.Gmult_assoc[OF GRep.FHModule_indspace]
          ActingGroup.neg_closed
          FGModuleHom.G_map[OF hom_induced_vector]
    by    auto
  also from cs(2) hj_def j(1) have "\<dots> = \<psi> T (cs \<bullet>\<currency>\<currency> (indVfbasis!j))"
    using hj_H Vfbasis_V FGModuleHom.distrib_flincomb[OF hom_induced_vector]
          indVfbasis_def Supgroup.neg_closed[of hj] induced_vector_indV
          FGModule.Gmult_flincomb_comm[
            OF GRep.FHModule_indspace,
            of "-hj" "map induced_vector Vfbasis"
          ]
          aezfun_scalar_mult.negGorbit_list_nth[
            of j H_rcoset_reps rrsmult induced_vector
          ]
    by    fastforce
  also have "\<dots> = cs \<bullet>\<sharp>\<star> ((map (map (\<psi> T)) indVfbasis)!j)"
    using \<psi>D_VectorSpaceHom[OF assms] indVfbasis_indV j' set_conv_nth
          VectorSpaceHom.distrib_lincomb[of induced_smult.fsmult indV fsmult']
    by    simp
  also from j(1) hj_def have "\<dots> = (- hj) *\<star> cs \<bullet>\<sharp>\<star> (map T Vfbasis)"
    using \<psi>D_im[OF assms]
          aezfun_scalar_mult.negGorbit_list_nth[of j H_rcoset_reps smult' T] hj_H
          Group.neg_closed[OF HRep.GroupG]
          Vfbasis_V FGModuleHomSetD_Im[OF assms]
          HRep.Gmult_flincomb_comm[of "- hj" "map T Vfbasis"]
    by    fastforce
  also from cs(2) g(1) have "\<dots> = (- hj) *\<star> (-g) *\<star> (T v)"
    using v_V FGModuleHomSetD_FGModuleHom[OF assms] Vfbasis_V
          FGModuleHom.distrib_flincomb[of G smult V smult']
          ActingGroup.neg_closed
          FGModuleHom.G_map[of G smult V smult' T "-g" v]
    by    auto
  also from g(1) v(1) have "\<dots> = (x - hi) *\<star> (T v)"
    using FGModuleHomSetD_FGModuleHom[OF assms] Vfbasis_V Supgroup.neg_closed
          hj_H Subgroup FGModuleHomSetD_Im[OF assms]
          HRep.Gmult_assoc[of "-hj" "-g" "T v"] x_hi
    by    auto
  also from x(1) have "\<dots> = x *\<star> (- hi) *\<star> (T v)"
    using hi_H Supgroup.neg_closed Tv_W HRep.Gmult_assoc
    by    (simp add: algebra_simps)
  finally show "\<psi> T (x *\<currency> f) = x *\<star> (\<psi> T f)"
    using assms(1) v hi_def i' set_conv_nth[of H_rcoset_reps] \<psi>D_im_single by fastforce
qed

lemma \<psi>T_hom :
  assumes "T \<in> GRepHomSet (\<star>) W"
  shows   "HRepHom (\<star>) (\<psi> T)"
  using indVfbasis \<psi>D_VectorSpaceHom[OF assms] FHModuleW
proof (
  rule FGModule.VecHom_GMap_on_fbasis_is_FGModuleHom[
    OF GRep.FHModule_indspace
  ]
)
  show "\<psi> T ` indV \<subseteq> W" using indVfbasis \<psi>T_W[OF assms] by fast
  show "\<And>g v. g \<in> H \<Longrightarrow> v \<in> set (concat indVfbasis)
              \<Longrightarrow> \<psi> T (g *\<currency> v) = g *\<star> \<psi> T v"
    using \<psi>T_Hmap_on_indVfbasis[OF assms] by fast
qed

lemma \<psi>_im : "\<psi> ` GRepHomSet (\<star>) W \<subseteq> HRepHomSet (\<star>) W"
  using \<psi>T_W \<psi>T_hom FGModuleHomSetI by fastforce

end (* context FrobeniusReciprocity *)

subsubsection \<open>Demonstration of bijectivity\<close>

text \<open>Now we demonstrate that @{term "\<phi>"} is bijective via the inverse @{term "\<psi>"}.\<close>

context FrobeniusReciprocity
begin

lemma \<phi>\<psi> :
  assumes "T \<in> GRepHomSet smult' W"
  shows   "(\<phi> \<circ> \<psi>) T = T"
proof
  fix v show "(\<phi> \<circ> \<psi>) T v = T v"
  proof (cases "v \<in> V")
    case True
    from this obtain cs where cs: "length cs = length Vfbasis" "v = cs \<bullet>\<sharp>\<cdot> Vfbasis"
      using Vfbasis
            VectorSpace.in_Span_obtain_same_length_coeffs[OF GRep.fVectorSpace]
      by    fast
    define extrazeros
      where "extrazeros = replicate ((length nonzero_H_rcoset_reps)*(length Vfbasis)) (0::'f)"
    with cs have "GRep.induced_vector v = (cs@extrazeros) \<bullet>\<currency>\<currency> (concat indVfbasis)"
      using     H_rcoset_reps induced_vector_decomp[OF Vfbasis]
      unfolding H_rcoset_reps_def indVfbasis_def
      by        auto
    with assms
      have  "(\<phi> \<circ> \<psi>) T v = (cs@extrazeros) \<bullet>\<sharp>\<star> (map (\<psi> T) (concat indVfbasis))"
      using \<psi>_im \<phi>_def indVfbasis
            VectorSpaceHom.distrib_lincomb[OF \<psi>D_VectorSpaceHom]
      by    auto
    also have "\<dots> = (cs@extrazeros) \<bullet>\<sharp>\<star> (map T Vfbasis
                    @ concat (HRep.negGorbit_list nonzero_H_rcoset_reps T Vfbasis))"
      using map_concat[of "\<psi> T"] \<psi>D_im[OF assms] H_rcoset_reps_def
            FGModuleHomSetD_Im[OF assms] Vfbasis_V HRep.negGorbit_list_Cons0
      by    fastforce
    also from cs(1)
      have  "\<dots> = cs \<bullet>\<sharp>\<star> (map T Vfbasis) + extrazeros
                  \<bullet>\<sharp>\<star> (concat (HRep.negGorbit_list nonzero_H_rcoset_reps T Vfbasis))"
      using scalar_mult.lincomb_append[of cs _ fsmult']
      by    simp
    also have "\<dots> = cs \<bullet>\<sharp>\<star> (map T Vfbasis)"
      using nonzero_H_rcoset_reps_H Vfbasis FGModuleHomSetD_Im[OF assms]
            HRep.negGorbit_list_V
            VectorSpace.lincomb_replicate0_left[OF HRep.fVectorSpace]
      unfolding extrazeros_def
      by    force
    also from cs(2) have "\<dots> = T v"
      using FGModuleHomSetD_FGModuleHom[OF assms]
            FGModuleHom.VectorSpaceHom Vfbasis
            VectorSpaceHom.distrib_lincomb[of "aezfun_scalar_mult.fsmult smult"]
      by    fastforce
    finally show ?thesis by fast
  next
    case False
    with assms show ?thesis
      using \<psi>_im \<phi>_def GRep.induced_vector_def \<psi>D_VectorSpaceHom
            VectorSpaceHom.im_zero
            FGModuleHomSetD_FGModuleHom[of T G smult V]
            FGModuleHom.supp suppI_contra
      by    fastforce
  qed
qed

lemma \<phi>_inverse_im : "\<phi> ` HRepHomSet (\<star>) W \<supseteq> GRepHomSet (\<star>) W"
  using \<phi>\<psi> \<psi>_im by force

lemma bij_\<phi> : "bij_betw \<phi> (HRepHomSet (\<star>) W) (GRepHomSet (\<star>) W)"
  unfolding bij_betw_def
proof

  have "\<And> S T. \<lbrakk> S \<in> HRepHomSet (\<star>) W; T \<in> HRepHomSet (\<star>) W;
            \<phi> S = \<phi> T \<rbrakk> \<Longrightarrow> S = T"
  proof (rule VectorSpaceHom.same_image_on_spanset_imp_same_hom)
    fix S T
    assume ST: "S \<in> HRepHomSet (\<star>) W" "T \<in> HRepHomSet (\<star>) W" "\<phi> S = \<phi> T"
    from ST(1,2) have ST': "HRepHom smult' S" "HRepHom smult' T"
      using FGModuleHomSetD_FGModuleHom[of _ H rrsmult] by auto

    from ST'
      show  "VectorSpaceHom induced_smult.fsmult indV fsmult' S"
            "VectorSpaceHom induced_smult.fsmult indV fsmult' T"
      using FGModuleHom.VectorSpaceHom[of H rrsmult indV smult']
      by    auto

    show "indV = induced_smult.fSpan (concat indVfbasis)"
         "set (concat indVfbasis) \<subseteq> indV"
      using indVfbasis by auto

    show "\<forall>f\<in>set (concat indVfbasis). S f = T f"
    proof
      fix f assume "f \<in> set (concat indVfbasis)"
      from this obtain hfvs where hfvs: "hfvs \<in> set indVfbasis" "f \<in> set hfvs"
        using set_concat by fast
      from hfvs(1) obtain h
        where h: "h \<in> set H_rcoset_reps"
                 "hfvs = map (Hmult (-h) \<circ> induced_vector) Vfbasis"
        using indVfbasis_def
              induced_smult.negGorbit_list_def[of H_rcoset_reps induced_vector]
        by    auto
      from hfvs(2) h(2) obtain v
        where v: "v \<in> set Vfbasis" "f = (-h) *\<currency> (induced_vector v)"
        by    auto
      from v h(1) ST(1) have "S f = (-h) *\<star> (\<phi> S v)"
        using ST'(1) H_rcoset_reps_H Group.neg_closed[OF HRep.GroupG]
              GRep.induced_vector_indV Vfbasis_V \<phi>_def FGModuleHom.G_map
        by    fastforce
      moreover from v h(1) ST(2) have "T f = (-h) *\<star> (\<phi> T v)"
        using ST'(2) H_rcoset_reps_H Group.neg_closed[OF HRep.GroupG] GRep.induced_vector_indV
              Vfbasis_V \<phi>_def FGModuleHom.G_map
        by    fastforce
      ultimately show "S f = T f" using ST(3) by simp

    qed
  qed
  thus "inj_on \<phi> (HRepHomSet (\<star>) W)" unfolding inj_on_def by fast

  show "\<phi> ` HRepHomSet (\<star>) W = GRepHomSet (\<star>) W"
    using \<phi>_im \<phi>_inverse_im by fast

qed

end (* context FrobeniusReciprocity *)

subsubsection \<open>The theorem\<close>

text \<open>
  Finally we demonstrate that @{term "\<phi>"} is an isomorphism of vector spaces between the two
  hom-sets, leading to Frobenius reciprocity.
\<close>

context FrobeniusReciprocity
begin

lemma VectorSpaceIso_\<phi> :
  "VectorSpaceIso Tsmult1 (HRepHomSet (\<star>) W) Tsmult2 \<phi>
        (GRepHomSet (\<star>) W)"
proof (rule VectorSpaceIso.intro, rule VectorSpace.VectorSpaceHomI_fromaxioms)

  from Tsmult1_def show "VectorSpace Tsmult1 (HRepHomSet (\<star>) W)"
    using FHModule_indspace FHModuleW
          FGModule.VectorSpace_FGModuleHomSet
    by    simp

  from \<phi>_def show "supp \<phi> \<subseteq> HRepHomSet (\<star>) W"
    using suppD_contra[of \<phi>] by fastforce

  have "bij_betw \<phi> (HRepHomSet (\<star>) W) (GRepHomSet (\<star>) W)"
    using bij_\<phi> by fast
  thus "VectorSpaceIso_axioms (HRepHomSet (\<star>) W) \<phi> (GRepHomSet (\<star>) W)"
    by unfold_locales

next    
  fix S T assume "S \<in> HRepHomSet (\<star>) W" "T \<in> HRepHomSet (\<star>) W"
  thus "\<phi> (S + T) = \<phi> S + \<phi> T"
    using \<phi>_def Group.add_closed
          FGModule.Group_FGModuleHomSet[OF FHModule_indspace FHModuleW]
    by    auto

next
  fix a T assume T: "T \<in> HRepHomSet (\<star>) W"
  moreover with Tsmult1_def have aT: "a \<star>\<currency> T \<in> HRepHomSet (\<star>) W"
    using FGModule.VectorSpace_FGModuleHomSet[
            OF FHModule_indspace FHModuleW
          ]
          VectorSpace.smult_closed
    by    simp
  ultimately show "\<phi> (a \<star>\<currency> T) = a \<star>\<cdot> (\<phi> T)"
    using \<phi>_def Tsmult1_def Tsmult2_def by auto

qed

theorem FrobeniusReciprocity :
  "VectorSpace.isomorphic Tsmult1 (HRepHomSet smult' W) Tsmult2
        (GRepHomSet smult' W)"
  using VectorSpaceIso_\<phi> by fast

end (* context FrobeniusReciprocity *)


end (* theory *)
