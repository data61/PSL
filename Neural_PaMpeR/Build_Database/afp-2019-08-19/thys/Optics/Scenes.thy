section \<open> Scenes \<close>

theory Scenes
  imports Lens_Instances
begin

text \<open> Like lenses, scenes characterise a region of a source type. However, unlike lenses, scenes
  do not explicitly assign a view type to this region, and consequently they have just one type
  parameter. This means they can be more flexibly composed, and in particular it is possible to
  show they form nice algebraic structures in Isabelle/HOL. They are mainly of use in characterising
  sets of variables, where, of course, we do not care about the types of those variables and
  therefore representing them as lenses is inconvenient. \<close>

subsection \<open> Overriding Functions \<close>

text \<open> Overriding functions provide an abstract way of replacing a region of an existing source
  with the corresponding region of another source. \<close>

locale overrider =
  fixes F :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<triangleright>" 65)
  assumes 
    ovr_overshadow_left: "x \<triangleright> y \<triangleright> z = x \<triangleright> z" and
    ovr_overshadow_right: "x \<triangleright> (y \<triangleright> z) = x \<triangleright> z"
begin
  lemma ovr_assoc: "x \<triangleright> (y \<triangleright> z) = x \<triangleright> y \<triangleright> z"
    by (simp add: ovr_overshadow_left ovr_overshadow_right)
end

locale idem_overrider = overrider +
  assumes ovr_idem: "x \<triangleright> x = x"

declare overrider.ovr_overshadow_left [simp]
declare overrider.ovr_overshadow_right [simp]
declare idem_overrider.ovr_idem [simp]

subsection \<open> Scene Type \<close>

typedef 's scene = "{F :: 's \<Rightarrow> 's \<Rightarrow> 's. overrider F}"
  by (rule_tac x="\<lambda> x y. x" in exI, simp, unfold_locales, simp_all)

setup_lifting type_definition_scene

lift_definition idem_scene :: "'s scene \<Rightarrow> bool" is idem_overrider .

lift_definition region :: "'s scene \<Rightarrow> 's rel" 
is "\<lambda> F. {(s\<^sub>1, s\<^sub>2). (\<forall> s. F s s\<^sub>1 = F s s\<^sub>2)}" .

lift_definition coregion :: "'s scene \<Rightarrow> 's rel" 
is "\<lambda> F. {(s\<^sub>1, s\<^sub>2). (\<forall> s. F s\<^sub>1 s = F s\<^sub>2 s)}" .

lemma equiv_region: "equiv UNIV (region X)"
  apply (transfer)
  apply (rule equivI)
    apply (rule refl_onI)
     apply (auto)
   apply (rule symI)
   apply (auto)
  apply (rule transI)
  apply (auto)
  done

lemma equiv_coregion: "equiv UNIV (coregion X)"
  apply (transfer)
  apply (rule equivI)
    apply (rule refl_onI)
     apply (auto)
   apply (rule symI)
   apply (auto)
  apply (rule transI)
  apply (auto)
  done

lemma region_coregion_Id:
  "idem_scene X \<Longrightarrow> region X \<inter> coregion X = Id"
  by (transfer, auto, metis idem_overrider.ovr_idem)

lemma state_eq_iff: "idem_scene S \<Longrightarrow> x = y \<longleftrightarrow> (x, y) \<in> region S \<and> (x, y) \<in> coregion S"
  by (metis IntE IntI pair_in_Id_conv region_coregion_Id)

lift_definition scene_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('a scene) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>S _ on _" [95,0,96] 95)
is "\<lambda> s\<^sub>1 s\<^sub>2 F. F s\<^sub>1 s\<^sub>2" .

lemma scene_override_idem [simp]: "idem_scene X \<Longrightarrow> s \<oplus>\<^sub>S s on X = s"
  by (transfer, simp)

lemma scene_override_overshadow_left [simp]:
  "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on X = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on X"
  by (transfer, simp)

lemma scene_override_overshadow_right [simp]:
  "S\<^sub>1 \<oplus>\<^sub>S (S\<^sub>2 \<oplus>\<^sub>S S\<^sub>3 on X) on X = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on X"
  by (transfer, simp)

lift_definition scene_indep :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix "\<bowtie>\<^sub>S" 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. G (F s\<^sub>1 s\<^sub>2) s\<^sub>3 = F (G s\<^sub>1 s\<^sub>3) s\<^sub>2)" .

lemma scene_indep_override:
  "X \<bowtie>\<^sub>S Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y \<oplus>\<^sub>S s\<^sub>2 on X)"
  by (transfer, auto)

lemma scene_indep_sym:
  "X \<bowtie>\<^sub>S Y \<Longrightarrow> Y \<bowtie>\<^sub>S X"
  by (transfer, auto)

text \<open> Compatibility is a weaker notion than independence; the scenes can overlap but they must
  agree when they do. \<close>
                                                  
lift_definition scene_compat :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix "##\<^sub>S" 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2 = F (G s\<^sub>1 s\<^sub>2) s\<^sub>2)" .

lemma scene_indep_compat [simp]: "X \<bowtie>\<^sub>S Y \<Longrightarrow> X ##\<^sub>S Y"
  by (transfer, auto)

lemma scene_compat_refl: "X ##\<^sub>S X"
  by (transfer, simp)

lemma scene_compat_sym: "X ##\<^sub>S Y \<Longrightarrow> Y ##\<^sub>S X"
  by (transfer, simp)

lemma scene_override_commute_indep:
  assumes "X \<bowtie>\<^sub>S Y"
  shows "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on Y = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on Y \<oplus>\<^sub>S S\<^sub>2 on X"
  using assms
  by (transfer, auto)

instantiation scene :: (type) "{bot, top, uminus, sup, inf}"
begin
  lift_definition bot_scene    :: "'s scene" is "\<lambda> x y. x" by (unfold_locales, simp_all)
  lift_definition top_scene    :: "'s scene" is "\<lambda> x y. y" by (unfold_locales, simp_all)
  lift_definition uminus_scene :: "'s scene \<Rightarrow> 's scene" is "\<lambda> F x y. F y x"
    by (unfold_locales, simp_all)
  text \<open> Scene union requires that the two scenes are at least compatible. If they are not, the
        result is the bottom scene. \<close>
  lift_definition sup_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" 
    is "\<lambda> F G. if (\<forall> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2 = F (G s\<^sub>1 s\<^sub>2) s\<^sub>2) then (\<lambda> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2) else (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1)"
    by (unfold_locales, auto, metis overrider.ovr_overshadow_right)
  definition inf_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" where
    "inf_scene X Y = - (sup (- X) (- Y))"
  instance ..
end

abbreviation union_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" (infixl "\<squnion>\<^sub>S" 65)
where "union_scene \<equiv> sup"

abbreviation inter_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" (infixl "\<sqinter>\<^sub>S" 70)
where "inter_scene \<equiv> inf"

abbreviation top_scene :: "'s scene" ("\<top>\<^sub>S")
where "top_scene \<equiv> top"

abbreviation bot_scene :: "'s scene" ("\<bottom>\<^sub>S")
where "bot_scene \<equiv> bot"

lemma uminus_scene_twice: "- (- (X :: 's scene)) = X"
  by (transfer, simp)

lemma scene_override_id [simp]: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on \<top>\<^sub>S = S\<^sub>2"
  by (transfer, simp)

lemma scene_override_unit [simp]: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on \<bottom>\<^sub>S = S\<^sub>1"
  by (transfer, simp)

lemma scene_override_commute: "S\<^sub>2 \<oplus>\<^sub>S S\<^sub>1 on (- X) = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X"
  by (transfer, simp)

lemma scene_union_incompat: "\<not> X ##\<^sub>S Y \<Longrightarrow> X \<squnion>\<^sub>S Y = \<bottom>\<^sub>S"
  by (transfer, auto)

lemma scene_override_union: "X ##\<^sub>S Y \<Longrightarrow> S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on (X \<squnion>\<^sub>S Y) = (S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X) \<oplus>\<^sub>S S\<^sub>2 on Y"
  by (transfer, auto)

lemma scene_union_unit: "X \<squnion>\<^sub>S \<bottom>\<^sub>S = X"
  by (transfer, simp)

lemma scene_union_annhil: "idem_scene X \<Longrightarrow> X \<squnion>\<^sub>S \<top>\<^sub>S = \<top>\<^sub>S"
  by (transfer, simp)

lemma scene_union_assoc: 
  assumes "X ##\<^sub>S Y" "X ##\<^sub>S Z" "Y ##\<^sub>S Z"
  shows "X \<squnion>\<^sub>S (Y \<squnion>\<^sub>S Z) = (X \<squnion>\<^sub>S Y) \<squnion>\<^sub>S Z"
  using assms
  by (transfer, auto)

lemma scene_union_idem: "X \<squnion>\<^sub>S X = X"
  by (transfer, simp)

lemma scene_union_compl: "idem_scene X \<Longrightarrow> X \<squnion>\<^sub>S - X = \<top>\<^sub>S"
  by (transfer, auto)

lemma scene_inter_idem: "X \<sqinter>\<^sub>S X = X"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_union_commute: "X \<squnion>\<^sub>S Y = Y \<squnion>\<^sub>S X"
  by (transfer, auto)
  
lemma scene_inter_compl: "idem_scene X \<Longrightarrow> X \<sqinter>\<^sub>S - X = \<bottom>\<^sub>S"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_demorgan1: "-(X \<squnion>\<^sub>S Y) = -X \<sqinter>\<^sub>S -Y"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_demorgan2: "-(X \<sqinter>\<^sub>S Y) = -X \<squnion>\<^sub>S -Y"
  by (simp add: inf_scene_def, transfer, auto)

instantiation scene :: (type) ord
begin
  text \<open> $X$ is a subscene of $Y$ provided that overriding with first $Y$ and then $X$ can
         be rewritten using the complement of $X$. \<close>
  definition less_eq_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "less_eq_scene X Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on Y \<oplus>\<^sub>S s\<^sub>3 on X = s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>2 \<oplus>\<^sub>S s\<^sub>3 on X) on Y)"
  definition less_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "less_scene x y = (x \<le> y \<and> \<not> y \<le> x)"
instance ..
end

abbreviation subscene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix "\<subseteq>\<^sub>S" 55)
where "subscene X Y \<equiv> X \<le> Y"

lemma subscene_refl: "X \<subseteq>\<^sub>S X"
  by (simp add: less_eq_scene_def)

lemma subscene_trans: "\<lbrakk> idem_scene Y; X \<subseteq>\<^sub>S Y; Y \<subseteq>\<^sub>S Z \<rbrakk> \<Longrightarrow> X \<subseteq>\<^sub>S Z"
  by (simp add: less_eq_scene_def, transfer, auto, metis (no_types, hide_lams) idem_overrider.ovr_idem)

lemma subscene_antisym: "\<lbrakk> idem_scene Y; X \<subseteq>\<^sub>S Y; Y \<subseteq>\<^sub>S X \<rbrakk> \<Longrightarrow> X = Y"
  apply (simp add: less_eq_scene_def, transfer, auto)
  apply (rule ext)
  apply (rule ext)
  apply (metis (full_types) idem_overrider.ovr_idem overrider.ovr_overshadow_left)
  done

lemma subscene_eliminate:
  "\<lbrakk> idem_scene Y; X \<le> Y \<rbrakk> \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y"
  by (metis less_eq_scene_def scene_override_overshadow_left scene_override_idem)
    
lemma scene_bot_least: "\<bottom>\<^sub>S \<le> X"
  unfolding less_eq_scene_def by (transfer, auto)

lemma scene_top_greatest: "X \<le> \<top>\<^sub>S"
  unfolding less_eq_scene_def by (transfer, auto)

lemma scene_union_ub: "\<lbrakk> idem_scene Y; X \<bowtie>\<^sub>S Y \<rbrakk> \<Longrightarrow> X \<le> (X \<squnion>\<^sub>S Y)"
  by (simp add: less_eq_scene_def, transfer, auto)
     (metis (no_types, hide_lams) idem_overrider.ovr_idem overrider.ovr_overshadow_right)

subsection \<open> Linking Scenes and Lenses \<close>

text \<open> The following function extracts a scene from a very well behaved lens \<close>

lift_definition lens_scene :: "('v \<Longrightarrow> 's) \<Rightarrow> 's scene" ("\<lbrakk>_\<rbrakk>\<^sub>\<sim>") is
"\<lambda> X s\<^sub>1 s\<^sub>2. if (mwb_lens X) then s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X else s\<^sub>1"
  by (unfold_locales, auto simp add: lens_override_def)

lemma vwb_impl_idem_scene [simp]:
  "vwb_lens X \<Longrightarrow> idem_scene \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (transfer, unfold_locales, auto simp add: lens_override_overshadow_left lens_override_overshadow_right)

lemma idem_scene_impl_vwb:
  "\<lbrakk> mwb_lens X; idem_scene \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> vwb_lens X"
  apply (cases "mwb_lens X")
   apply (transfer, unfold idem_overrider_def overrider_def, auto)
  apply (simp add: idem_overrider_axioms_def override_idem_implies_vwb)
  done

text \<open> Next we show some important congruence properties \<close>

lemma zero_lens_scene: "\<lbrakk>0\<^sub>L\<rbrakk>\<^sub>\<sim> = \<bottom>\<^sub>S"
  by (transfer, simp)

lemma one_lens_scene: "\<lbrakk>1\<^sub>L\<rbrakk>\<^sub>\<sim> = \<top>\<^sub>S"
  by (transfer, simp)

lemma lens_scene_override: 
  "mwb_lens X \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on \<lbrakk>X\<rbrakk>\<^sub>\<sim> = s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X"
  by (transfer, simp)

lemma lens_indep_scene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "(X \<bowtie> Y) \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  using assms
  by (auto, (simp add: scene_indep_override, transfer, simp add: lens_indep_override_def)+)

lemma lens_indep_impl_scene_indep [simp]:
  "(X \<bowtie> Y) \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: lens_indep_comm lens_override_def)

lemma lens_plus_scene:
  "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: lens_override_plus lens_indep_override_def lens_indep_overrideI plus_vwb_lens)

lemma subscene_implies_sublens': "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim> \<longleftrightarrow> X \<subseteq>\<^sub>L' Y"
  by (simp add: lens_defs less_eq_scene_def, transfer, simp add: lens_override_def)

lemma sublens'_implies_subscene: "\<lbrakk> vwb_lens X; vwb_lens Y; X \<subseteq>\<^sub>L' Y \<rbrakk> \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (simp add: lens_defs less_eq_scene_def, auto simp add: lens_override_def lens_scene_override)

lemma sublens_iff_subscene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "X \<subseteq>\<^sub>L Y \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (simp add: assms sublens_iff_sublens' subscene_implies_sublens')

text \<open> Equality on scenes is sound and complete with respect to lens equivalence. \<close>

lemma lens_equiv_scene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "X \<approx>\<^sub>L Y \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
proof
  assume a: "X \<approx>\<^sub>L Y"
  show "\<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
    by (meson a assms lens_equiv_def sublens_iff_subscene subscene_antisym vwb_impl_idem_scene)
next
  assume b: "\<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  show "X \<approx>\<^sub>L Y"
    by (simp add: assms b lens_equiv_def sublens_iff_subscene subscene_refl)
qed

text \<open> Membership operations. These have slightly hacky definitions at the moment in order to
  cater for @{term mwb_lens}. See if they can be generalised? \<close>

definition lens_member :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b scene \<Rightarrow> bool" (infix "\<in>\<^sub>S" 50) where
[lens_defs]:
"lens_member x A = ((\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on A \<oplus>\<^sub>L s\<^sub>3 on x = s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>2 \<oplus>\<^sub>L s\<^sub>3 on x) on A) \<and>
                      (\<forall> b b'. get\<^bsub>x\<^esub> (b \<oplus>\<^sub>S b' on A) = get\<^bsub>x\<^esub> b'))"

lemma lens_member_top: "x \<in>\<^sub>S \<top>\<^sub>S"
  by (auto simp add: lens_member_def)

abbreviation lens_not_member :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b scene \<Rightarrow> bool" (infix "\<notin>\<^sub>S" 50) where
"x \<notin>\<^sub>S A \<equiv> (x \<in>\<^sub>S - A)" 

lemma lens_member_get_override [simp]: "x \<in>\<^sub>S a \<Longrightarrow> get\<^bsub>x\<^esub> (b \<oplus>\<^sub>S b' on a) = get\<^bsub>x\<^esub> b'"
  by (simp add: lens_member_def)

lemma lens_not_member_get_override [simp]: "x \<notin>\<^sub>S a \<Longrightarrow> get\<^bsub>x\<^esub> (b \<oplus>\<^sub>S b' on a) = get\<^bsub>x\<^esub> b"
  by (simp add: lens_member_def scene_override_commute)

text \<open> Hide implementation details for scenes \<close>

lifting_update scene.lifting
lifting_forget scene.lifting

end