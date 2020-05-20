theory Xor imports 
  "HOL-Algebra.Complete_Lattice" 
  "CryptHOL.Misc_CryptHOL" 
begin

(* disable lattice syntax for type class lattices *)
no_notation
  bot_class.bot ("\<bottom>") and
  top_class.top ("\<top>") and 
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) 

context bounded_lattice begin

lemma top_join [simp]: "x \<in> carrier L \<Longrightarrow> \<top> \<squnion> x = \<top>"
  using eq_is_equal top_join by auto

lemma join_top [simp]: "x \<in> carrier L \<Longrightarrow> x \<squnion> \<top> = \<top>"
  using le_iff_meet by blast

lemma bot_join [simp]: "x \<in> carrier L \<Longrightarrow> \<bottom> \<squnion> x = x"
  using le_iff_meet by blast

lemma join_bot [simp]: "x \<in> carrier L \<Longrightarrow> x \<squnion> \<bottom> = x"
  by (metis bot_join join_comm)

lemma bot_meet [simp]: "x \<in> carrier L \<Longrightarrow> \<bottom> \<sqinter> x = \<bottom>"
  using bottom_meet by auto

lemma meet_bot [simp]: "x \<in> carrier L \<Longrightarrow> x \<sqinter> \<bottom> = \<bottom>"
  by (metis bot_meet meet_comm)

lemma top_meet [simp]: "x \<in> carrier L \<Longrightarrow> \<top> \<sqinter> x = x"
  by (metis le_iff_join meet_comm top_closed top_higher)

lemma meet_top [simp]: "x \<in> carrier L \<Longrightarrow> x \<sqinter> \<top> = x"
  by (metis meet_comm top_meet)

lemma join_idem [simp]: "x \<in> carrier L \<Longrightarrow> x \<squnion> x = x"
  using le_iff_meet by blast

lemma meet_idem [simp]: "x \<in> carrier L \<Longrightarrow> x \<sqinter> x = x"
  using le_iff_join le_refl by presburger

lemma meet_leftcomm: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)" if "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  by (metis meet_assoc meet_comm that)

lemma join_leftcomm: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)" if "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  by (metis join_assoc join_comm that)

lemmas meet_ac = meet_assoc meet_comm meet_leftcomm
lemmas join_ac = join_assoc join_comm join_leftcomm

end

record 'a boolean_algebra = "'a gorder" +
  compl :: "'a \<Rightarrow> 'a" ("\<^bold>-\<index>" 1000)

definition xor :: "('a, 'b) boolean_algebra_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<oplus>\<index>" 100) where
  "x \<oplus> y = (x \<squnion> y) \<sqinter> (\<^bold>- (x \<sqinter> y))" for L (structure)

locale boolean_algebra = bounded_lattice L
  for L (structure) +
  assumes compl_closed [intro, simp]: "x \<in> carrier L \<Longrightarrow> \<^bold>- x \<in> carrier L"
    and meet_compl_bot [simp]: "x \<in> carrier L \<Longrightarrow> \<^bold>- x \<sqinter> x = \<bottom>"
    and join_compl_top [simp]: "x \<in> carrier L \<Longrightarrow> \<^bold>- x \<squnion> x = \<top>"
    and join_meet_distrib1: "\<lbrakk> x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
begin

lemma join_meet_distrib2: "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  if "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  by (simp add: join_comm join_meet_distrib1 that)

lemma meet_join_distrib1: "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  if [simp]: "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
proof -
  have "x \<sqinter> (y \<squnion> z) = (x \<sqinter> (x \<squnion> z)) \<sqinter> (y \<squnion> z)"
    using join_left le_iff_join by auto
  also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))"
    by (simp add: join_comm join_meet_distrib1 meet_assoc)
  also have "\<dots> = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)"
    by (metis join_comm le_iff_meet meet_closed meet_left that(1) that(2))
  also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
    by (simp add: join_meet_distrib1)
  finally show ?thesis .
qed

lemma meet_join_distrib2: "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
  if [simp]: "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  by (simp add: meet_comm meet_join_distrib1)

lemmas join_meet_distrib = join_meet_distrib1 join_meet_distrib2

lemmas meet_join_distrib = meet_join_distrib1 meet_join_distrib2

lemmas distrib = join_meet_distrib meet_join_distrib

lemma meet_compl2_bot [simp]: "x \<in> carrier L \<Longrightarrow> x \<sqinter> \<^bold>- x = \<bottom>"
  by (metis meet_comm meet_compl_bot)

lemma join_compl2_top [simp]: "x \<in> carrier L \<Longrightarrow> x \<squnion> \<^bold>- x = \<top>"
  by (metis join_comm join_compl_top)

lemma compl_unique:
  assumes "x \<sqinter> y = \<bottom>"
    and "x \<squnion> y = \<top>"
    and [simp]: "x \<in> carrier L" "y \<in> carrier L"
  shows "\<^bold>- x = y"
proof -
  have "(x \<sqinter> \<^bold>- x) \<squnion> (\<^bold>- x \<sqinter> y) = (x \<sqinter> y) \<squnion> (\<^bold>- x \<sqinter> y)"
    using inf_compl_bot assms(1) by simp
  then have "(\<^bold>- x \<sqinter> x) \<squnion> (\<^bold>- x \<sqinter> y) = (y \<sqinter> x) \<squnion> (y \<sqinter> \<^bold>- x)"
    by (simp add: meet_comm)
  then have "\<^bold>- x \<sqinter> (x \<squnion> y) = y \<sqinter> (x \<squnion> \<^bold>- x)"
    using assms(3) assms(4) compl_closed meet_join_distrib1 by presburger
  then have "\<^bold>- x \<sqinter> \<top> = y \<sqinter> \<top>"
    by (simp add: assms(2))
  then show "\<^bold>- x = y"
    using le_iff_join top_higher by auto
qed

lemma double_compl [simp]: "\<^bold>- (\<^bold>- x) = x" if [simp]: "x \<in> carrier L"
  by(rule compl_unique)(simp_all)

lemma compl_eq_compl_iff [simp]: "\<^bold>- x = \<^bold>- y \<longleftrightarrow> x = y" if "x \<in> carrier L" "y \<in> carrier L"
  by (metis double_compl that that)

lemma compl_bot_eq [simp]: "\<^bold>- \<bottom> = \<top>"
  using le_iff_join le_iff_meet local.compl_unique top_higher by auto

lemma compl_top_eq [simp]: "\<^bold>- \<top> = \<bottom>"
  by (metis bottom_closed compl_bot_eq double_compl)

lemma compl_inf [simp]: "\<^bold>- (x \<sqinter> y) = \<^bold>- x \<squnion> \<^bold>- y" if [simp]: "x \<in> carrier L" "y \<in> carrier L"
proof (rule compl_unique)
  have "(x \<sqinter> y) \<sqinter> (\<^bold>- x \<squnion> \<^bold>- y) = (y \<sqinter> (x \<sqinter> \<^bold>- x)) \<squnion> (x \<sqinter> (y \<sqinter> \<^bold>- y))"
    by (smt compl_closed meet_assoc meet_closed meet_comm meet_join_distrib1 that)
  then show "(x \<sqinter> y) \<sqinter> (\<^bold>- x \<squnion> \<^bold>- y) = \<bottom>"
    by (metis bottom_closed bottom_lower le_iff_join le_iff_meet meet_comm meet_compl2_bot that)
next
  have "(x \<sqinter> y) \<squnion> (\<^bold>- x \<squnion> \<^bold>- y) = (\<^bold>- y \<squnion> (x \<squnion> \<^bold>- x)) \<sqinter> (\<^bold>- x \<squnion> (y \<squnion> \<^bold>- y))"
    by (smt compl_closed join_meet_distrib2 join_assoc join_comm local.boolean_algebra_axioms that join_closed)
  then show "(x \<sqinter> y) \<squnion> (\<^bold>- x \<squnion> \<^bold>- y) = \<top>"
    by (metis compl_closed join_compl2_top join_right le_iff_join le_iff_meet that top_closed)
qed simp_all

lemma compl_sup [simp]: "\<^bold>- (x \<squnion> y) = \<^bold>- x \<sqinter> \<^bold>- y" if "x \<in> carrier L" "y \<in> carrier L"
  by (metis compl_closed compl_inf double_compl meet_closed that)

lemma compl_mono:
  assumes "x \<sqsubseteq> y"
    and "x \<in> carrier L" "y \<in> carrier L"
  shows "\<^bold>- y \<sqsubseteq> \<^bold>- x"
  by (metis assms(1) assms(2) assms(3) compl_closed join_comm le_iff_join le_iff_meet compl_inf)

lemma compl_le_compl_iff [simp]: "\<^bold>- x \<sqsubseteq> \<^bold>- y \<longleftrightarrow> y \<sqsubseteq> x" if "x \<in> carrier L" "y \<in> carrier L"
  using that by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<sqsubseteq> \<^bold>- x" "x \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubseteq> \<^bold>- y"
  by (metis assms compl_closed compl_le_compl_iff double_compl)

lemma compl_le_swap2:
  assumes "\<^bold>- y \<sqsubseteq> x" "x \<in> carrier L" "y \<in> carrier L"
  shows "\<^bold>- x \<sqsubseteq> y"
  by (metis assms compl_closed compl_le_compl_iff double_compl)

lemma join_compl_top_left1 [simp]: "\<^bold>- x \<squnion> (x \<squnion> y) = \<top>" if [simp]: "x \<in> carrier L" "y \<in> carrier L"
  by (simp add: join_assoc[symmetric])

lemma join_compl_top_left2 [simp]: "x \<squnion> (\<^bold>- x \<squnion> y) = \<top>" if [simp]: "x \<in> carrier L" "y \<in> carrier L"
  using join_compl_top_left1[of "\<^bold>- x" y] by simp

lemma meet_compl_bot_left1 [simp]: "\<^bold>- x \<sqinter> (x \<sqinter> y) = \<bottom>" if [simp]: "x \<in> carrier L" "y \<in> carrier L"
  by (simp add: meet_assoc[symmetric])

lemma meet_compl_bot_left2 [simp]: "x \<sqinter> (\<^bold>- x \<sqinter> y) = \<bottom>" if [simp]: "x \<in> carrier L" "y \<in> carrier L"
  using meet_compl_bot_left1[of "\<^bold>- x" y] by simp

lemma meet_compl_bot_right [simp]: "x \<sqinter> (y \<sqinter> \<^bold>- x) = \<bottom>" if [simp]: "x \<in> carrier L" "y \<in> carrier L"
  by (metis meet_compl_bot_left2 meet_comm that)

lemma xor_closed [intro, simp]: "\<lbrakk> x \<in> carrier L; y \<in> carrier L \<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrier L"
  by(simp add: xor_def)

lemma xor_comm: "\<lbrakk> x \<in> carrier L; y \<in> carrier L \<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
  by(simp add: xor_def meet_join_distrib join_comm)

lemma xor_assoc: "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  if [simp]: "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  by(simp add: xor_def)(simp add: meet_join_distrib meet_ac join_ac)

lemma xor_left_comm: "x \<oplus> (y \<oplus> z) = y \<oplus> (x \<oplus> z)" if "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  using that xor_assoc xor_comm by auto

lemma [simp]:
  assumes "x \<in> carrier L"
  shows xor_bot: "x \<oplus> \<bottom> = x"
  and bot_xor: "\<bottom> \<oplus> x = x"
  and xor_top: "x \<oplus> \<top> = \<^bold>- x"
  and top_xor: "\<top> \<oplus> x = \<^bold>- x"
  by(simp_all add: xor_def assms)

lemma xor_inverse [simp]: "x \<oplus> x = \<bottom>" if "x \<in> carrier L"
  by(simp add: xor_def that)

lemma xor_left_inverse [simp]: "x \<oplus> x \<oplus> y = y" if "x \<in> carrier L" "y \<in> carrier L"
  using that xor_assoc by fastforce

lemmas xor_ac = xor_assoc xor_comm xor_left_comm

lemma inj_on_xor: "inj_on ((\<oplus>) x) (carrier L)" if "x \<in> carrier L"
  by(rule inj_onI)(metis that xor_left_inverse)

lemma surj_xor: "(\<oplus>) x ` carrier L = carrier L" if [simp]: "x \<in> carrier L"
proof(rule Set.set_eqI, rule iffI)
  fix y
  assume [simp]: "y \<in> carrier L"
  have "x \<oplus> y \<in> carrier L" by(simp)
  moreover have "y = x \<oplus> (x \<oplus> y)" by simp
  ultimately show "y \<in> (\<oplus>) x ` carrier L" by(rule rev_image_eqI)
qed auto

lemma one_time_pad: "map_spmf ((\<oplus>) x) (spmf_of_set (carrier L)) = spmf_of_set (carrier L)"
  if "x \<in> carrier L"
  apply(subst map_spmf_of_set_inj_on)
   apply(rule inj_on_xor[OF that])
  by(simp add: surj_xor that)

end

end