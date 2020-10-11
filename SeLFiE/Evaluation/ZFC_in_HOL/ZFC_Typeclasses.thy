section \<open>Type Classes for ZFC\<close>

theory ZFC_Typeclasses
  imports ZFC_Cardinals Complex_Main

begin



subsection\<open>The class of embeddable types\<close>

class embeddable =
  assumes ex_inj: "\<exists>V_of :: 'a \<Rightarrow> V. inj V_of"

context countable
begin

subclass embeddable
proof -
  have "inj (ord_of_nat \<circ> to_nat)" if "inj to_nat"
    for to_nat :: "'a \<Rightarrow> nat"
    using that by (simp add: inj_compose inj_ord_of_nat)
  then show "class.embeddable TYPE('a)"
    by intro_classes (meson local.ex_inj)
qed

end

instance unit :: embeddable ..
instance bool :: embeddable ..
instance nat :: embeddable ..
instance int :: embeddable ..
instance rat :: embeddable ..
instance char :: embeddable ..
instance String.literal :: embeddable ..
instance typerep :: embeddable ..


lemma embeddable_classI:
  fixes f :: "'a \<Rightarrow> V"
  assumes "\<And>x y. f x = f y \<Longrightarrow> x = y"
  shows "OFCLASS('a, embeddable_class)"
proof (intro_classes, rule exI)
  show "inj f"
    by (rule injI [OF assms]) assumption
qed

instance V :: embeddable
  by (rule embeddable_classI [where f=id]) auto

instance prod :: (embeddable,embeddable) embeddable
proof -
  have "inj (\<lambda>(x,y). \<langle>V_of1 x, V_of2 y\<rangle>)" if "inj V_of1" "inj V_of2"
    for V_of1 :: "'a \<Rightarrow> V" and V_of2 :: "'b \<Rightarrow> V"
    using that by (auto simp: inj_on_def)
  then show "OFCLASS('a \<times> 'b, embeddable_class)"
    by intro_classes (meson embeddable_class.ex_inj)
qed

instance sum :: (embeddable,embeddable) embeddable
proof -
  have "inj (case_sum (Inl \<circ> V_of1) (Inr \<circ> V_of2))" if "inj V_of1" "inj V_of2"
    for V_of1 :: "'a \<Rightarrow> V" and V_of2 :: "'b \<Rightarrow> V"
    using that by (auto simp: inj_on_def split: sum.split_asm)
  then show "OFCLASS('a + 'b, embeddable_class)"
    by intro_classes (meson embeddable_class.ex_inj)
qed

instance option :: (embeddable) embeddable
proof -
  have "inj (case_option 0 (\<lambda>x. ZFC_in_HOL.set{V_of x}))" if "inj V_of"
    for V_of :: "'a \<Rightarrow> V"
    using that by (auto simp: inj_on_def split: option.split_asm)
  then show "OFCLASS('a option, embeddable_class)"
    by intro_classes (meson embeddable_class.ex_inj)
qed

primrec V_of_list where
  "V_of_list V_of Nil = 0"
| "V_of_list V_of (x#xs) = \<langle>V_of x, V_of_list V_of xs\<rangle>"

lemma inj_V_of_list:
  assumes "inj V_of"
  shows "inj (V_of_list V_of)"
proof -
  note inj_eq [OF assms, simp]
  have "x = y" if "V_of_list V_of x = V_of_list V_of y" for x y
    using that
  proof (induction x arbitrary: y)
    case Nil
    then show ?case
      by (cases y) auto
  next
    case (Cons a x)
    then show ?case
      by (cases y) auto
  qed
  then show ?thesis
    by (auto simp: inj_on_def)
qed

instance list :: (embeddable) embeddable
proof -
  have "inj (rec_list 0 (\<lambda>x xs r. \<langle>V_of x, r\<rangle>))" (is "inj ?f")
    if V_of: "inj V_of" for V_of :: "'a \<Rightarrow> V"
  proof -
    note inj_eq [OF V_of, simp]
    have "x = y" if "?f x = ?f y" for x y
      using that
    proof (induction x arbitrary: y)
      case Nil
      then show ?case
        by (cases y) auto
    next
      case (Cons a x)
      then show ?case
        by (cases y) auto
    qed
    then show ?thesis
      by (auto simp: inj_on_def)
  qed
  then show "OFCLASS('a list, embeddable_class)"
    by intro_classes (meson embeddable_class.ex_inj)
qed


subsection\<open>The class of small types\<close>

class small =
  assumes small: "small (UNIV::'a set)"
begin

subclass embeddable
  by intro_classes (meson local.small small_def)

lemma TC_small [iff]:
  fixes A :: "'a set"
  shows "small A"
  using small smaller_than_small by blast

end

context countable
begin

subclass small
proof -
  have *: "inj (ord_of_nat \<circ> to_nat)" if "inj to_nat"
    for to_nat :: "'a \<Rightarrow> nat"
    using that by (simp add: inj_compose inj_ord_of_nat)
  then show "class.small TYPE('a)"
    by intro_classes (metis small_image_nat local.ex_inj the_inv_into_onto)
qed

end

lemma lepoll_UNIV_imp_small: "X \<lesssim> (UNIV::'a::small set) \<Longrightarrow> small X"
  by (meson lepoll_iff replacement small smaller_than_small)

lemma lepoll_imp_small:
  fixes A :: "'a::small set"
  assumes "X \<lesssim> A"
  shows "small X"
  by (metis lepoll_UNIV_imp_small UNIV_I assms lepoll_def subsetI)

instance unit :: small ..
instance bool :: small ..
instance nat :: small ..
instance int :: small ..
instance rat :: small ..
instance char :: small ..
instance String.literal :: small ..
instance typerep :: small ..

instance prod :: (small,small) small
proof -
  have "inj (\<lambda>(x,y). \<langle>V_of1 x, V_of2 y\<rangle>)"
       "range (\<lambda>(x,y). \<langle>V_of1 x, V_of2 y\<rangle>) \<le> elts (VSigma A (\<lambda>x. B))"
    if "inj V_of1" "inj V_of2" "range V_of1 \<le> elts A" "range V_of2 \<le> elts B"
    for V_of1 :: "'a \<Rightarrow> V" and V_of2 :: "'b \<Rightarrow> V" and A B
    using that by (auto simp: inj_on_def)
  with small [where 'a='a] small [where 'a='b]
  show "OFCLASS('a \<times> 'b, small_class)"
    apply intro_classes
    unfolding small_def
    apply clarify
    by (metis down_raw dual_order.refl)
qed

instance sum :: (small,small) small
proof -
  have "inj (case_sum (Inl \<circ> V_of1) (Inr \<circ> V_of2))"
       "range (case_sum (Inl \<circ> V_of1) (Inr \<circ> V_of2)) \<le> elts (A \<Uplus> B)"
    if "inj V_of1" "inj V_of2" "range V_of1 \<le> elts A" "range V_of2 \<le> elts B"
    for V_of1 :: "'a \<Rightarrow> V" and V_of2 :: "'b \<Rightarrow> V" and A B
    using that by (force simp: inj_on_def split: sum.split)+
  with small [where 'a='a] small [where 'a='b]
  show "OFCLASS('a + 'b, small_class)"
    apply intro_classes
    unfolding small_def
    apply clarify
    by (metis down_raw dual_order.refl)
qed

instance option :: (small) small
proof -
  have "inj (\<lambda>x. case x of None \<Rightarrow> 0 | Some x \<Rightarrow> ZFC_in_HOL.set {V_of x})"
       "range (\<lambda>x. case x of None \<Rightarrow> 0 | Some x \<Rightarrow> ZFC_in_HOL.set {V_of x}) \<le> insert 0 (elts (VPow A))"
    if "inj V_of" "range V_of \<le> elts A"
    for V_of :: "'a \<Rightarrow> V" and A
    using that  by (auto simp: inj_on_def split: option.split_asm)
  with small [where 'a='a]
  show "OFCLASS('a option, small_class)"
    apply intro_classes
    unfolding small_def
    apply clarify
    by (metis down_raw elts_vinsert subset_insertI)
qed

instance list :: (small) small
proof -
  have "small (range (V_of_list V_of))"
    if "inj V_of" "range V_of \<le> elts A"
    for V_of :: "'a \<Rightarrow> V" and A
  proof -
    have "range (V_of_list V_of) \<approx> (UNIV :: 'a list set)"
      using that by (simp add: inj_V_of_list)
    also have "\<dots> \<approx> lists (UNIV :: 'a set)"
      by simp
    also have "\<dots> \<lesssim> (UNIV :: 'a set) \<times> (UNIV :: nat set)"
    proof (cases "finite (range (V_of::'a \<Rightarrow> V))")
      case True
      then have "lists (UNIV :: 'a set) \<lesssim> (UNIV :: nat set)"
        using countable_iff_lepoll countable_image_inj_on that(1) uncountable_infinite by blast
      then show ?thesis
        by (blast intro: lepoll_trans [OF _ lepoll_times2])
    next
      case False
      then have "lists (UNIV :: 'a set) \<lesssim> (UNIV :: 'a set)"
        using \<open>infinite (range V_of)\<close> eqpoll_imp_lepoll infinite_eqpoll_lists by blast
      then show ?thesis
        using lepoll_times1 lepoll_trans by fastforce
    qed
    finally show ?thesis
      by (simp add: lepoll_imp_small)
  qed
  with small [where 'a='a]
  show "OFCLASS('a list, small_class)"
    apply intro_classes
    unfolding small_def
    apply clarify
    by (metis inj_V_of_list order_refl small_def small_iff_range)
qed

instance "fun" :: (small,embeddable) embeddable
proof -
  have "inj (\<lambda>f. VLambda A (\<lambda>x. V_of2 (f (inv V_of1 x))))"
    if *: "inj V_of1" "inj V_of2" "range V_of1 \<le> elts A"
    for V_of1 :: "'a \<Rightarrow> V" and V_of2 :: "'b \<Rightarrow> V" and A
  proof -
    have "f u = f' u"
      if "VLambda A (\<lambda>u. V_of2 (f (inv V_of1 u))) = VLambda A (\<lambda>x. V_of2 (f' (inv V_of1 x)))"
      for f f' :: "'a \<Rightarrow> 'b" and u
      by (metis inv_f_f rangeI subsetD VLambda_eq_D2 [OF that, of "V_of1 u"] *)
    then show ?thesis
      by (auto simp: inj_on_def)
  qed
  then show "OFCLASS('a \<Rightarrow> 'b, embeddable_class)"
    by intro_classes (metis embeddable_class.ex_inj small order_refl replacement small_iff)
qed

instance "fun" :: (small,small) small
proof -
  have "inj (\<lambda>f. VLambda A (\<lambda>x. V_of2 (f (inv V_of1 x))))"   (is "inj ?\<phi>")
       "range (\<lambda>f. VLambda A (\<lambda>x. V_of2 (f (inv V_of1 x)))) \<le> elts (VPi A (\<lambda>x. B))"
    if *: "inj V_of1" "inj V_of2" "range V_of1 \<le> elts A" and "range V_of2 \<le> elts B"
    for V_of1 :: "'a \<Rightarrow> V" and V_of2 :: "'b \<Rightarrow> V" and A B
  proof -
    have "f u = f' u"
      if "VLambda A (\<lambda>u. V_of2 (f (inv V_of1 u))) = VLambda A (\<lambda>x. V_of2 (f' (inv V_of1 x)))"
      for f f' :: "'a \<Rightarrow> 'b" and u
      by (metis inv_f_f rangeI subsetD VLambda_eq_D2 [OF that, of "V_of1 u"] *)
    then show "inj ?\<phi>"
      by (auto simp: inj_on_def)
    show "range ?\<phi> \<le> elts (VPi A (\<lambda>x. B))"
      using that by (simp add: VPi_I subset_eq)
  qed
  with small [where 'a='a] small [where 'a='b]
  show "OFCLASS('a \<Rightarrow> 'b, small_class)"
    apply intro_classes
    unfolding small_def
    apply clarify
    by (metis down_raw dual_order.refl)
qed

instance set :: (small) small 
proof -
  have 1: "inj (\<lambda>x. ZFC_in_HOL.set (V_of ` x))"
    if "inj V_of" for V_of :: "'a \<Rightarrow> V" 
    by (simp add: inj_on_def inj_image_eq_iff [OF that])
  have 2: "range (\<lambda>x. ZFC_in_HOL.set (V_of ` x)) \<le> elts (VPow A)"
    if "range V_of \<le> elts A" for V_of :: "'a \<Rightarrow> V" and A
    using that by (auto simp: inj_on_def image_subset_iff)
  from small [where 'a='a]
  show "OFCLASS('a set, small_class)"
    apply intro_classes
    unfolding small_def
    apply clarify
    by (metis 1 2 down_raw subsetI)
qed

instance real :: small 
proof -
  have "small (range (Rep_real))"
    by simp
  then show "OFCLASS(real, small_class)"
    by intro_classes (metis Rep_real_inverse image_inv_f_f inj_on_def replacement)
qed

instance complex :: small 
proof -
  have "\<And>c. c \<in> range (\<lambda>(x,y). Complex x y)"
    by (metis case_prod_conv complex.exhaust_sel rangeI)
  then show "OFCLASS(complex, small_class)"
    by intro_classes (meson TC_small replacement smaller_than_small subset_eq)
qed


end
