theory "HOLCF-Join-Classes"
imports "HOLCF-Join"
begin

class Finite_Join_cpo = cpo +
  assumes all_compatible: "compatible x y"

lemmas join_mono = join_mono[OF all_compatible all_compatible ]
lemmas join_above1[simp] = all_compatible[THEN join_above1]
lemmas join_above2[simp] = all_compatible[THEN join_above2]
lemmas join_below[simp] = all_compatible[THEN join_below]
lemmas join_below_iff = all_compatible[THEN join_below_iff]
lemmas join_assoc[simp] = join_assoc[OF all_compatible all_compatible all_compatible]
lemmas join_comm[simp] = all_compatible[THEN join_commute]

lemma join_lc[simp]: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> (z::'a::Finite_Join_cpo))"
  by (metis join_assoc join_comm)
  
lemma join_cont': "chain Y \<Longrightarrow> (\<Squnion> i. Y i) \<squnion> y = (\<Squnion> i. Y i \<squnion> (y::'a::Finite_Join_cpo))"
by (metis all_compatible join_cont1)

lemma join_cont1:
  fixes y :: "'a :: Finite_Join_cpo"
  shows "cont (\<lambda>x. (x \<squnion> y))"
  apply (rule contI2)
  apply (rule monofunI)
  apply (metis below_refl join_mono)
  apply (rule eq_imp_below)
  apply (rule join_cont')
  apply assumption
  done

lemma join_cont2: 
  fixes x :: "'a :: Finite_Join_cpo"
  shows "cont (\<lambda>y. (x \<squnion> y))"
  by (simp only: join_comm) (rule join_cont1)

lemma join_cont[cont2cont,simp]:"cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. (f x \<squnion> (g x::'a::Finite_Join_cpo)))"
  apply (rule cont2cont_case_prod[where g = "\<lambda> x. (f x, g x)" and f = "\<lambda> p x y . x \<squnion> y", simplified])
  apply (rule join_cont2)
  apply (metis cont2cont_Pair)
  done

instantiation "fun" :: (type, Finite_Join_cpo) Finite_Join_cpo
begin
  definition fun_join :: "('a \<Rightarrow> 'b) \<rightarrow> ('a \<Rightarrow> 'b) \<rightarrow> ('a \<Rightarrow> 'b)"
    where "fun_join = (\<Lambda> f g . (\<lambda> x. (f x) \<squnion> (g x)))"
  lemma [simp]: "(fun_join\<cdot>f\<cdot>g) x = (f x) \<squnion> (g x)"
    unfolding fun_join_def
      apply (subst beta_cfun, intro cont2cont cont2cont_lambda cont2cont_fun)+
      ..
  instance
  apply standard
  proof(intro compatibleI exI conjI strip)
    fix x y
    show "x \<sqsubseteq> fun_join\<cdot>x\<cdot>y"  by (auto simp add: fun_below_iff)
    show "y \<sqsubseteq> fun_join\<cdot>x\<cdot>y"  by (auto simp add: fun_below_iff)
    fix z
    assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    thus "fun_join\<cdot>x\<cdot>y \<sqsubseteq> z" by (auto simp add: fun_below_iff)
  qed
end

instantiation "cfun" :: (cpo, Finite_Join_cpo) Finite_Join_cpo
begin
  definition cfun_join :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)"
    where "cfun_join = (\<Lambda> f g  x. (f \<cdot> x) \<squnion> (g \<cdot> x))"
  lemma [simp]: "cfun_join\<cdot>f\<cdot>g\<cdot>x = (f \<cdot> x) \<squnion> (g \<cdot> x)"
    unfolding cfun_join_def
      apply (subst beta_cfun, intro cont2cont cont2cont_lambda cont2cont_fun)+
      ..
  instance
  apply standard
  proof(intro compatibleI exI conjI strip)
    fix x y
    show "x \<sqsubseteq> cfun_join\<cdot>x\<cdot>y"  by (auto simp add: cfun_below_iff)
    show "y \<sqsubseteq> cfun_join\<cdot>x\<cdot>y"  by (auto simp add: cfun_below_iff)
    fix z
    assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    thus "cfun_join\<cdot>x\<cdot>y \<sqsubseteq> z" by (auto simp add: cfun_below_iff)
  qed
end

lemma bot_lub[simp]: "S <<| \<bottom> \<longleftrightarrow>  S \<subseteq> {\<bottom>}"
  by (auto dest!: is_lubD1 is_ubD intro: is_lubI is_ubI)

lemma compatible_up[simp]: "compatible (up\<cdot>x) (up\<cdot>y) \<longleftrightarrow> compatible x y"
proof
  assume "compatible (up\<cdot>x) (up\<cdot>y)"
  then obtain z' where z': "{up\<cdot>x,up\<cdot>y} <<| z'" unfolding compatible_def by auto
  then obtain z where  "{up\<cdot>x,up\<cdot>y} <<| up\<cdot>z" by (cases z') auto
  hence "{x,y} <<| z"
    unfolding is_lub_def
    apply auto
    by (metis up_below)
  thus "compatible x y"  unfolding compatible_def..
next
  assume "compatible x y"
  then obtain z where z: "{x,y} <<| z" unfolding compatible_def by auto
  hence  "{up\<cdot>x,up\<cdot>y} <<| up\<cdot>z"  unfolding is_lub_def
    apply auto
    by (metis not_up_less_UU upE up_below)
  thus "compatible (up\<cdot>x) (up\<cdot>y)"  unfolding compatible_def..
qed


instance u :: (Finite_Join_cpo) Finite_Join_cpo
proof
  fix x y :: "'a\<^sub>\<bottom>"
  show "compatible x y"
  apply (cases x, simp)
  apply (cases y, simp)
  apply (simp add: all_compatible)
  done
qed

class is_unit = fixes unit assumes is_unit: "\<And> x. x = unit"

instantiation unit :: is_unit
begin

definition "unit \<equiv> ()"

instance
  by standard auto

end

instance lift :: (is_unit) Finite_Join_cpo
proof
  fix x y :: "'a lift"
  show "compatible x y"
  apply (cases x, simp)
  apply (cases y, simp)
  apply (simp add: all_compatible)
  apply (subst is_unit)
  apply (subst is_unit) back
  apply simp
  done
qed

instance prod :: (Finite_Join_cpo, Finite_Join_cpo) Finite_Join_cpo
proof
  fix x y :: "('a \<times> 'b)"
  let ?z = "(fst x \<squnion> fst y, snd x \<squnion> snd y)"
  show "compatible x y"
  proof(rule compatibleI)
    show "x \<sqsubseteq> ?z" by (cases x, auto)
    show "y \<sqsubseteq> ?z" by (cases y, auto)
    fix z'
    assume "x \<sqsubseteq> z'" and "y \<sqsubseteq> z'" thus "?z \<sqsubseteq> z'"
      by (cases z', cases x, cases y, auto)
  qed
qed

lemma prod_join: 
    fixes x y :: "'a::Finite_Join_cpo \<times> 'b::Finite_Join_cpo" 
    shows "x \<squnion> y = (fst x \<squnion> fst y, snd x \<squnion> snd y)"
  apply (rule is_joinI)
  apply (cases x, auto)[1]
  apply (cases y, auto)[1]
  apply (cases x, cases y, case_tac a, auto)[1]
  done

lemma 
  fixes x y :: "'a::Finite_Join_cpo \<times> 'b::Finite_Join_cpo" 
  shows fst_join[simp]: "fst (x \<squnion> y) = fst x \<squnion> fst y"
  and snd_join[simp]: "snd (x \<squnion> y) = snd x \<squnion> snd y" 
  unfolding prod_join by simp_all

lemma fun_meet_simp[simp]: "(f \<squnion> g) x = f x \<squnion> (g x::'a::Finite_Join_cpo)"
proof-
  have "f \<squnion> g = (\<lambda> x. f x \<squnion> g x)"
  by (rule is_joinI)(auto simp add: fun_below_iff)
  thus ?thesis by simp
qed

lemma fun_upd_meet_simp[simp]: "(f \<squnion> g) (x := y) = f (x := y)  \<squnion> g (x := y::'a::Finite_Join_cpo)"
  by auto

lemma cfun_meet_simp[simp]: "(f \<squnion> g) \<cdot> x = f \<cdot> x \<squnion> (g \<cdot> x::'a::Finite_Join_cpo)"
proof-
  have "f \<squnion> g = (\<Lambda> x. f \<cdot> x \<squnion> g \<cdot> x)"
  by (rule is_joinI)(auto simp add: cfun_below_iff)
  thus ?thesis by simp
qed

lemma cfun_join_below:
  fixes f :: "('a::Finite_Join_cpo) \<rightarrow> ('b::Finite_Join_cpo)"
  shows "f\<cdot>x \<squnion> f\<cdot>y \<sqsubseteq> f\<cdot>(x \<squnion> y)"
  by (intro join_below monofun_cfun_arg join_above1 join_above2)
  
lemma join_self_below[iff]:
  "x = x \<squnion> y \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "x = y \<squnion> x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "x \<squnion> y = x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "y \<squnion> x = x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "x \<squnion> y \<sqsubseteq> x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "y \<squnion> x \<sqsubseteq> x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  apply (metis join_above2 larger_is_join1)
  apply (metis join_above1 larger_is_join2)
  apply (metis join_above2 larger_is_join1)
  apply (metis join_above1 larger_is_join2)
  apply (metis join_above1 join_above2 below_antisym larger_is_join1)
  apply (metis join_above2 join_above1 below_antisym larger_is_join2)
  done

lemma join_bottom_iff[iff]:
  "x \<squnion> y = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> (y::'a::{Finite_Join_cpo,pcpo}) = \<bottom>"
  by (metis all_compatible join_bottom(2) join_comm join_idem)

class Join_cpo = cpo +
  assumes exists_lub: "\<exists>u. S <<| u"

context Join_cpo
begin
  subclass Finite_Join_cpo
    apply standard
    unfolding compatible_def
    apply (rule exists_lub)
  done
end

lemma below_lubI[intro, simp]:
  fixes x :: "'a :: Join_cpo"
  shows  "x \<in> S \<Longrightarrow> x \<sqsubseteq> lub S"
by (metis exists_lub is_ub_thelub_ex)

lemma lub_belowI[intro, simp]:
  fixes x :: "'a :: Join_cpo"
  shows  "(\<And> y. y \<in> S \<Longrightarrow> y \<sqsubseteq> x) \<Longrightarrow> lub S \<sqsubseteq> x"
by (metis exists_lub is_lub_thelub_ex is_ub_def)

(* subclass (in Join_cpo)  pcpo *)
instance Join_cpo \<subseteq> pcpo
  apply standard
  apply (rule exI[where x = "lub {}"])
  apply auto
  done

lemma lub_empty_set[simp]:
  "lub {} = (\<bottom>::'a::Join_cpo)"
  by (rule lub_eqI) simp


lemma lub_insert[simp]:
  fixes x :: "'a :: Join_cpo"
  shows "lub (insert x S) = x \<squnion> lub S"
by (rule lub_eqI) (auto intro: below_trans[OF _ join_above2] simp add: join_below_iff is_ub_def is_lub_def)


end
