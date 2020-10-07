theory FS_Set
imports
  Nominal2.Nominal2
begin

section \<open>Finitely Supported Sets\<close>

text \<open>We define the type of finitely supported sets (over some permutation type~@{typ "'a::pt"}).

Note that we cannot more generally define the (sub-)type of finitely supported elements for
arbitrary permutation types~@{typ "'a::pt"}: there is no guarantee that this type is non-empty.\<close>

typedef 'a fs_set = "{x::'a::pt set. finite (supp x)}"
  by (simp add: exI[where x="{}"] supp_set_empty)

setup_lifting type_definition_fs_set

text \<open>Type~@{typ "'a fs_set"} is a finitely supported permutation type.\<close>

instantiation fs_set :: (pt) pt
begin

  lift_definition permute_fs_set :: "perm \<Rightarrow> 'a fs_set \<Rightarrow> 'a fs_set" is permute
    by (metis permute_finite supp_eqvt)

  instance
   apply (intro_classes)
    apply (metis (mono_tags) permute_fs_set.rep_eq Rep_fs_set_inverse permute_zero)
   apply (metis (mono_tags) permute_fs_set.rep_eq Rep_fs_set_inverse permute_plus)
  done

end

instantiation fs_set :: (pt) fs
begin

  instance
  proof (intro_classes)
    fix x :: "'a fs_set"
    from Rep_fs_set have "finite (supp (Rep_fs_set x))" by simp
    hence "finite {a. infinite {b. (a \<rightleftharpoons> b) \<bullet> Rep_fs_set x \<noteq> Rep_fs_set x}}" by (unfold supp_def)
    hence "finite {a. infinite {b. ((a \<rightleftharpoons> b) \<bullet> x) \<noteq>  x}}" by transfer
    thus "finite (supp x)" by (fold supp_def)
  qed

end

text \<open>Set membership.\<close>

lift_definition member_fs_set :: "'a::pt \<Rightarrow> 'a fs_set \<Rightarrow> bool" is "(\<in>)" .

notation
  member_fs_set ("'(\<in>\<^sub>f\<^sub>s')") and
  member_fs_set ("(_/ \<in>\<^sub>f\<^sub>s _)" [51, 51] 50)

lemma member_fs_set_permute_iff [simp]: "p \<bullet> x \<in>\<^sub>f\<^sub>s p \<bullet> X \<longleftrightarrow> x \<in>\<^sub>f\<^sub>s X"
by transfer (simp add: mem_permute_iff)

lemma member_fs_set_eqvt [eqvt]: "x \<in>\<^sub>f\<^sub>s X \<Longrightarrow> p \<bullet> x \<in>\<^sub>f\<^sub>s p \<bullet> X"
by simp

end
