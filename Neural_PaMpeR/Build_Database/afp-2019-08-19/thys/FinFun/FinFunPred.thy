(*  Author:     Andreas Lochbihler *)

section \<open>Predicates modelled as FinFuns\<close>

theory FinFunPred
imports FinFun
begin

unbundle finfun_syntax

text \<open>Instantiate FinFun predicates just like predicates\<close>

type_synonym 'a pred\<^sub>f = "'a \<Rightarrow>f bool"

instantiation "finfun" :: (type, ord) ord
begin

definition le_finfun_def [code del]: "f \<le> g \<longleftrightarrow> (\<forall>x. f $ x \<le> g $ x)"

definition [code del]: "(f::'a \<Rightarrow>f 'b) < g \<longleftrightarrow> f \<le> g \<and> \<not> g \<le> f"

instance ..

lemma le_finfun_code [code]:
  "f \<le> g \<longleftrightarrow> finfun_All ((\<lambda>(x, y). x \<le> y) \<circ>$ ($f, g$))"
by(simp add: le_finfun_def finfun_All_All o_def)

end

instance "finfun" :: (type, preorder) preorder
  by(intro_classes)(auto simp add: less_finfun_def le_finfun_def intro: order_trans)

instance "finfun" :: (type, order) order
by(intro_classes)(auto simp add: le_finfun_def order_antisym_conv intro: finfun_ext)

instantiation "finfun" :: (type, order_bot) order_bot begin
definition "bot = finfun_const bot"
instance by(intro_classes)(simp add: bot_finfun_def le_finfun_def)
end

lemma bot_finfun_apply [simp]: "($) bot = (\<lambda>_. bot)"
by(auto simp add: bot_finfun_def)

instantiation "finfun" :: (type, order_top) order_top begin
definition "top = finfun_const top"
instance by(intro_classes)(simp add: top_finfun_def le_finfun_def)
end

lemma top_finfun_apply [simp]: "($) top = (\<lambda>_. top)"
by(auto simp add: top_finfun_def)

instantiation "finfun" :: (type, inf) inf begin
definition [code]: "inf f g = (\<lambda>(x, y). inf x y) \<circ>$ ($f, g$)"
instance ..
end

lemma inf_finfun_apply [simp]: "($) (inf f g) = inf (($) f) (($) g)"
by(auto simp add: inf_finfun_def o_def inf_fun_def)

instantiation "finfun" :: (type, sup) sup begin
definition [code]: "sup f g = (\<lambda>(x, y). sup x y) \<circ>$ ($f, g$)"
instance ..
end

lemma sup_finfun_apply [simp]: "($) (sup f g) = sup (($) f) (($) g)"
by(auto simp add: sup_finfun_def o_def sup_fun_def)

instance "finfun" :: (type, semilattice_inf) semilattice_inf
by(intro_classes)(simp_all add: inf_finfun_def le_finfun_def)

instance "finfun" :: (type, semilattice_sup) semilattice_sup
by(intro_classes)(simp_all add: sup_finfun_def le_finfun_def)

instance "finfun" :: (type, lattice) lattice ..

instance "finfun" :: (type, bounded_lattice) bounded_lattice
by(intro_classes)

instance "finfun" :: (type, distrib_lattice) distrib_lattice
by(intro_classes)(simp add: sup_finfun_def inf_finfun_def expand_finfun_eq o_def sup_inf_distrib1)

instantiation "finfun" :: (type, minus) minus begin
definition "f - g = case_prod (-) \<circ>$ ($f, g$)"
instance ..
end

lemma minus_finfun_apply [simp]: "($) (f - g) = ($) f - ($) g"
by(simp add: minus_finfun_def o_def fun_diff_def)

instantiation "finfun" :: (type, uminus) uminus begin
definition "- A = uminus \<circ>$ A"
instance ..
end

lemma uminus_finfun_apply [simp]: "($) (- g) = - ($) g"
by(simp add: uminus_finfun_def o_def fun_Compl_def)

instance "finfun" :: (type, boolean_algebra) boolean_algebra
by(intro_classes)
  (simp_all add: uminus_finfun_def inf_finfun_def expand_finfun_eq sup_fun_def inf_fun_def fun_Compl_def o_def inf_compl_bot sup_compl_top diff_eq)

text \<open>
  Replicate predicate operations for FinFuns
\<close>

abbreviation finfun_empty :: "'a pred\<^sub>f" ("{}\<^sub>f")
where "{}\<^sub>f \<equiv> bot"

abbreviation finfun_UNIV :: "'a pred\<^sub>f" 
where "finfun_UNIV \<equiv> top"

definition finfun_single :: "'a \<Rightarrow> 'a pred\<^sub>f"
where [code]: "finfun_single x = finfun_empty(x $:= True)"

lemma finfun_single_apply [simp]:
  "finfun_single x $ y \<longleftrightarrow> x = y"
by(simp add: finfun_single_def finfun_upd_apply)

lemma [iff]:
  shows finfun_single_neq_bot: "finfun_single x \<noteq> bot" 
  and bot_neq_finfun_single: "bot \<noteq> finfun_single x"
by(simp_all add: expand_finfun_eq fun_eq_iff)

lemma finfun_leI [intro!]: "(!!x. A $ x \<Longrightarrow> B $ x) \<Longrightarrow> A \<le> B"
by(simp add: le_finfun_def)

lemma finfun_leD [elim]: "\<lbrakk> A \<le> B; A $ x \<rbrakk> \<Longrightarrow> B $ x"
by(simp add: le_finfun_def)

text \<open>Bounded quantification.
  Warning: \<open>finfun_Ball\<close> and \<open>finfun_Ex\<close> may raise an exception, they should not be used for quickcheck
\<close>

definition finfun_Ball_except :: "'a list \<Rightarrow> 'a pred\<^sub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Ball_except xs A P = (\<forall>a. A $ a \<longrightarrow> a \<in> set xs \<or> P a)"

lemma finfun_Ball_except_const:
  "finfun_Ball_except xs (K$ b) P \<longleftrightarrow> \<not> b \<or> set xs = UNIV \<or> Code.abort (STR ''finfun_ball_except'') (\<lambda>u. finfun_Ball_except xs (K$ b) P)"
by(auto simp add: finfun_Ball_except_def)

lemma finfun_Ball_except_const_finfun_UNIV_code [code]:
  "finfun_Ball_except xs (K$ b) P \<longleftrightarrow> \<not> b \<or> is_list_UNIV xs \<or> Code.abort (STR ''finfun_ball_except'') (\<lambda>u. finfun_Ball_except xs (K$ b) P)"
by(auto simp add: finfun_Ball_except_def is_list_UNIV_iff)

lemma finfun_Ball_except_update:
  "finfun_Ball_except xs (A(a $:= b)) P = ((a \<in> set xs \<or> (b \<longrightarrow> P a)) \<and> finfun_Ball_except (a # xs) A P)"
by(fastforce simp add: finfun_Ball_except_def finfun_upd_apply split: if_split_asm)

lemma finfun_Ball_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_Ball_except xs (finfun_update_code f a b) P = ((a \<in> set xs \<or> (b \<longrightarrow> P a)) \<and> finfun_Ball_except (a # xs) f P)"
by(simp add: finfun_Ball_except_update)

definition finfun_Ball :: "'a pred\<^sub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Ball A P = Ball {x. A $ x} P"

lemma finfun_Ball_code [code]: "finfun_Ball = finfun_Ball_except []"
by(auto intro!: ext simp add: finfun_Ball_except_def finfun_Ball_def)


definition finfun_Bex_except :: "'a list \<Rightarrow> 'a pred\<^sub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Bex_except xs A P = (\<exists>a. A $ a \<and> a \<notin> set xs \<and> P a)"

lemma finfun_Bex_except_const:
  "finfun_Bex_except xs (K$ b) P \<longleftrightarrow> b \<and> set xs \<noteq> UNIV \<and> Code.abort (STR ''finfun_Bex_except'') (\<lambda>u. finfun_Bex_except xs (K$ b) P)"
by(auto simp add: finfun_Bex_except_def)

lemma finfun_Bex_except_const_finfun_UNIV_code [code]:
  "finfun_Bex_except xs (K$ b) P \<longleftrightarrow> b \<and> \<not> is_list_UNIV xs \<and> Code.abort (STR ''finfun_Bex_except'') (\<lambda>u. finfun_Bex_except xs (K$ b) P)"
by(auto simp add: finfun_Bex_except_def is_list_UNIV_iff)

lemma finfun_Bex_except_update: 
  "finfun_Bex_except xs (A(a $:= b)) P \<longleftrightarrow> (a \<notin> set xs \<and> b \<and> P a) \<or> finfun_Bex_except (a # xs) A P"
by(fastforce simp add: finfun_Bex_except_def finfun_upd_apply dest: bspec split: if_split_asm)

lemma finfun_Bex_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_Bex_except xs (finfun_update_code f a b) P \<longleftrightarrow> ((a \<notin> set xs \<and> b \<and> P a) \<or> finfun_Bex_except (a # xs) f P)"
by(simp add: finfun_Bex_except_update)

definition finfun_Bex :: "'a pred\<^sub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Bex A P = Bex {x. A $ x} P"

lemma finfun_Bex_code [code]: "finfun_Bex = finfun_Bex_except []"
by(auto intro!: ext simp add: finfun_Bex_except_def finfun_Bex_def)


text \<open>Automatically replace predicate operations by finfun predicate operations where possible\<close>

lemma iso_finfun_le [code_unfold]:
  "($) A \<le> ($) B \<longleftrightarrow> A \<le> B"
by (metis le_finfun_def le_funD le_funI)

lemma iso_finfun_less [code_unfold]:
  "($) A < ($) B \<longleftrightarrow> A < B"
by (metis iso_finfun_le less_finfun_def less_fun_def)

lemma iso_finfun_eq [code_unfold]:
  "($) A = ($) B \<longleftrightarrow> A = B"
by(simp only: expand_finfun_eq)

lemma iso_finfun_sup [code_unfold]:
  "sup (($) A) (($) B) = ($) (sup A B)"
by(simp)

lemma iso_finfun_disj [code_unfold]:
  "A $ x \<or> B $ x \<longleftrightarrow> sup A B $ x"
by(simp add: sup_fun_def)

lemma iso_finfun_inf [code_unfold]:
  "inf (($) A) (($) B) = ($) (inf A B)"
by(simp)

lemma iso_finfun_conj [code_unfold]:
  "A $ x \<and> B $ x \<longleftrightarrow> inf A B $ x"
by(simp add: inf_fun_def)

lemma iso_finfun_empty_conv [code_unfold]:
  "(\<lambda>_. False) = ($) {}\<^sub>f"
by simp

lemma iso_finfun_UNIV_conv [code_unfold]:
  "(\<lambda>_. True) = ($) finfun_UNIV"
by simp

lemma iso_finfun_upd [code_unfold]:
  fixes A :: "'a pred\<^sub>f"
  shows "(($) A)(x := b) = ($) (A(x $:= b))"
by(simp add: fun_eq_iff)

lemma iso_finfun_uminus [code_unfold]:
  fixes A :: "'a pred\<^sub>f"
  shows "- ($) A = ($) (- A)"
by(simp)

lemma iso_finfun_minus [code_unfold]:
  fixes A :: "'a pred\<^sub>f"
  shows "($) A - ($) B = ($) (A - B)"
by(simp)

text \<open>
  Do not declare the following two theorems as \<open>[code_unfold]\<close>,
  because this causes quickcheck to fail frequently when bounded quantification is used which raises an exception.
  For code generation, the same problems occur, but then, no randomly generated FinFun is usually around.
\<close>

lemma iso_finfun_Ball_Ball:
  "(\<forall>x. A $ x \<longrightarrow> P x) \<longleftrightarrow> finfun_Ball A P"
by(simp add: finfun_Ball_def)

lemma iso_finfun_Bex_Bex:
  "(\<exists>x. A $ x \<and> P x) \<longleftrightarrow> finfun_Bex A P"
by(simp add: finfun_Bex_def)

text \<open>Test code setup\<close>

notepad begin
have "inf ((\<lambda>_ :: nat. False)(1 := True, 2 := True)) ((\<lambda>_. True)(3 := False)) \<le> 
      sup ((\<lambda>_. False)(1 := True, 5 := True)) (- ((\<lambda>_. True)(2 := False, 3 := False)))"
  by eval
end

declare iso_finfun_Ball_Ball[code_unfold]
notepad begin
have "(\<forall>x. ((\<lambda>_ :: nat. False)(1 := True, 2 := True)) x \<longrightarrow> x < 3)"
  by eval
end
declare iso_finfun_Ball_Ball[code_unfold del]

end
