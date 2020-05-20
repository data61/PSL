(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Propositional Hoare Logic\<close>

theory PHL_KAT
  imports KAT Kleene_Algebra.PHL_KA
begin

text \<open>We define a class of pre-dioids with notions of assertions, tests and iteration. The above rules of PHL are derivable in that class.\<close>

class at_pre_dioid = pre_dioid_one +
  fixes alpha :: "'a \<Rightarrow> 'a" ("\<alpha>")
  and tau :: "'a \<Rightarrow> 'a" ("\<tau>")
  assumes at_pres: "\<alpha> x \<cdot> \<tau> y \<le> \<tau> y \<cdot> \<alpha> x \<cdot> \<tau> y"
  and as_left_supdistl: "\<alpha> x \<cdot> (y + z) \<le> \<alpha> x \<cdot> y + \<alpha> x \<cdot> z"

begin

text \<open>Only the conditional and the iteration rule need to be considered (in addition to the export laws. 
In this context, they no longer depend on external assumptions. The other ones do not depend on any assumptions anyway.\<close>

lemma at_phl_cond: 
assumes "\<alpha> u \<cdot> \<tau> v \<cdot> x \<le> x \<cdot> z" and "\<alpha> u \<cdot> \<tau> w \<cdot> y \<le> y \<cdot> z" 
shows "\<alpha> u \<cdot> (\<tau> v \<cdot> x + \<tau> w \<cdot> y) \<le> (\<tau> v \<cdot> x + \<tau> w \<cdot> y) \<cdot> z"
  using assms as_left_supdistl at_pres phl_cond by blast

lemma ht_at_phl_cond: 
assumes "\<lbrace>\<alpha> u \<cdot> \<tau> v\<rbrace> x \<lbrace>z\<rbrace>" and "\<lbrace>\<alpha> u \<cdot> \<tau> w\<rbrace> y \<lbrace>z\<rbrace>" 
shows "\<lbrace>\<alpha> u\<rbrace> (\<tau> v \<cdot> x + \<tau> w \<cdot> y) \<lbrace>z\<rbrace>"
  using assms by (fact at_phl_cond)

lemma  ht_at_phl_export1: 
assumes "\<lbrace>\<alpha> x \<cdot> \<tau> y\<rbrace> z \<lbrace>w\<rbrace>"
shows "\<lbrace>\<alpha> x\<rbrace> \<tau> y \<cdot> z \<lbrace>w\<rbrace>"
  by (simp add: assms at_pres ht_phl_export1)

lemma ht_at_phl_export2: 
assumes "\<lbrace>x\<rbrace> y \<lbrace>\<alpha> z\<rbrace>"
shows "\<lbrace>x\<rbrace> y \<cdot> \<tau> w \<lbrace>\<alpha> z \<cdot> \<tau> w\<rbrace>"
  using assms at_pres ht_phl_export2 by auto

end

class at_it_pre_dioid = at_pre_dioid + it_pre_dioid
begin

lemma at_phl_while:  
assumes "\<alpha> p \<cdot> \<tau> s \<cdot> x \<le> x \<cdot> \<alpha> p"
shows "\<alpha> p \<cdot> (it (\<tau> s \<cdot> x) \<cdot> \<tau> w)  \<le> it (\<tau> s \<cdot> x) \<cdot> \<tau> w \<cdot> (\<alpha> p \<cdot> \<tau> w)"
  by (simp add: assms at_pres it_simr phl_while)

lemma ht_at_phl_while:  
assumes "\<lbrace>\<alpha> p \<cdot> \<tau> s\<rbrace> x \<lbrace>\<alpha> p\<rbrace>"
shows "\<lbrace>\<alpha> p\<rbrace> it (\<tau> s \<cdot> x) \<cdot> \<tau> w \<lbrace>\<alpha> p \<cdot> \<tau> w\<rbrace>"
  using assms by (fact at_phl_while)

end

text \<open>The following statements show that pre-Conway algebras, Kleene algebras with tests
and demonic refinement algebras form pre-dioids with test and assertions. This automatically
generates propositional Hoare logics for these structures.\<close>

sublocale test_pre_dioid_zerol < phl: at_pre_dioid where alpha = t and tau = t
proof 
  show "\<And>x y. t x \<cdot> t y \<le> t y \<cdot> t x \<cdot> t y"
    by (simp add: n_mult_comm mult_assoc)
  show "\<And>x y z. t x \<cdot> (y + z) \<le> t x \<cdot> y + t x \<cdot> z"
    by (simp add: n_left_distrib)
qed

sublocale test_pre_conway < phl: at_it_pre_dioid where alpha = t and tau = t and it = dagger ..

sublocale kat_zerol < phl: at_it_pre_dioid where alpha = t and tau = t and it = star ..

context test_pre_dioid_zerol begin

abbreviation if_then_else :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi \<equiv> (p \<cdot> x + !p \<cdot> y)"
 
lemma phl_n_cond: 
  "\<lbrace>n v \<cdot> n w\<rbrace> x \<lbrace>z\<rbrace> \<Longrightarrow> \<lbrace>n v \<cdot> t w\<rbrace> y \<lbrace>z\<rbrace> \<Longrightarrow> \<lbrace>n v\<rbrace> n w \<cdot> x + t w \<cdot> y \<lbrace>z\<rbrace>"
  by (metis phl.ht_at_phl_cond t_n_closed)

lemma phl_test_cond: 
  assumes "test p" and "test b"
  and "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>q\<rbrace>" and "\<lbrace>p \<cdot> !b\<rbrace> y \<lbrace>q\<rbrace>" 
  shows "\<lbrace>p\<rbrace> b \<cdot> x + !b \<cdot> y \<lbrace>q\<rbrace>"
  by (metis assms local.test_double_comp_var phl_n_cond)

lemma phl_cond_syntax: 
  assumes "test p" and "test b"
  and "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>q\<rbrace>" and "\<lbrace>p \<cdot> !b\<rbrace> y \<lbrace>q\<rbrace>" 
  shows "\<lbrace>p\<rbrace> if b then x else y fi \<lbrace>q\<rbrace>"
  using assms by (fact phl_test_cond)

lemma phl_cond_syntax_iff: 
  assumes "test p" and "test b"
  shows "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>q\<rbrace> \<and> \<lbrace>p \<cdot> !b\<rbrace> y \<lbrace>q\<rbrace> \<longleftrightarrow> \<lbrace>p\<rbrace> if b then x else y fi \<lbrace>q\<rbrace>"
proof
  assume a: "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>q\<rbrace> \<and> \<lbrace>p \<cdot> !b\<rbrace> y \<lbrace>q\<rbrace>"
  show "\<lbrace>p\<rbrace> if b then x else y fi \<lbrace>q\<rbrace>"
    using a assms(1) assms(2) phl_test_cond by auto
next
  assume a: "\<lbrace>p\<rbrace> if b then x else y fi \<lbrace>q\<rbrace>"
  have "p \<cdot> b \<cdot> x \<le> b \<cdot> p \<cdot> (b \<cdot> x + !b \<cdot> y)"
    by (metis assms(1) assms(2) local.mult.assoc local.subdistl local.test_preserve)
  also have "... \<le> b \<cdot> (b \<cdot> x + !b \<cdot> y) \<cdot> q"
    using a local.mult_isol mult_assoc by auto
  also have "...  = (b \<cdot> b \<cdot> x + b \<cdot> !b \<cdot> y) \<cdot> q"
    using assms(2) local.n_left_distrib_var mult_assoc by presburger
  also have "... = b \<cdot> x \<cdot> q"
    by (simp add: assms(2))
  finally have b: "p \<cdot> b \<cdot> x \<le> x \<cdot> q"
    by (metis assms(2) local.order_trans local.test_restrictl mult_assoc)
  have "p \<cdot> !b \<cdot> y = !b \<cdot> p \<cdot> !b \<cdot> y"
    by (simp add: assms(1) assms(2) local.test_preserve)
  also have "... \<le> !b \<cdot> p \<cdot> (b \<cdot> x + !b \<cdot> y)"
    by (simp add: local.mult_isol mult_assoc)
  also have "... \<le> !b \<cdot> (b \<cdot> x + !b \<cdot> y) \<cdot> q"
    using a local.mult_isol mult_assoc by auto
  also have "... = (!b \<cdot> b \<cdot> x + !b \<cdot> !b \<cdot> y) \<cdot> q"
    using local.n_left_distrib mult_assoc by presburger
  also have "... = !b \<cdot> y \<cdot> q"
    by (simp add: assms(2))
  finally have c: "p \<cdot> !b \<cdot> y \<le> y \<cdot> q"
    by (metis local.dual_order.trans local.n_restrictl mult_assoc)
  show "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>q\<rbrace> \<and> \<lbrace>p \<cdot> !b\<rbrace> y \<lbrace>q\<rbrace>"
    using b c by auto
qed

end

context test_pre_conway
begin

lemma  phl_n_while: 
  assumes "\<lbrace>n x \<cdot>  n y\<rbrace> z \<lbrace>n x\<rbrace>"
  shows "\<lbrace>n x\<rbrace> (n y \<cdot> z)\<^sup>\<dagger> \<cdot> t y \<lbrace>n x \<cdot> t y\<rbrace>"
  by (metis assms phl.ht_at_phl_while t_n_closed)

end

context kat_zerol
begin

abbreviation while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while b do x od \<equiv> (b \<cdot> x)\<^sup>\<star> \<cdot> !b"

lemma  phl_n_while: 
  assumes "\<lbrace>n x \<cdot>  n y\<rbrace> z \<lbrace>n x\<rbrace>"
  shows "\<lbrace>n x\<rbrace> (n y \<cdot> z)\<^sup>\<star> \<cdot> t y \<lbrace>n x \<cdot> t y\<rbrace>"
  by (metis assms phl.ht_at_phl_while t_n_closed)

lemma phl_test_while: 
  assumes "test p" and "test b" 
  and "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>p\<rbrace>"
  shows "\<lbrace>p\<rbrace> (b \<cdot> x)\<^sup>\<star> \<cdot> !b \<lbrace>p \<cdot> !b\<rbrace>"
  by (metis assms phl_n_while test_double_comp_var)

lemma phl_while_syntax: 
  assumes "test p" and "test b" and "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>p\<rbrace>"
  shows "\<lbrace>p\<rbrace> while b do x od \<lbrace>p \<cdot> !b\<rbrace>"
  by (metis assms phl_test_while)

end

lemma (in kat) "test p \<Longrightarrow> p \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> p \<Longrightarrow> p \<cdot> x \<le> x \<cdot> p"
  oops

lemma (in kat) "test p \<Longrightarrow> test b \<Longrightarrow> p \<cdot> (b \<cdot> x)\<^sup>\<star> \<cdot> !b \<le> (b \<cdot> x)\<^sup>\<star> \<cdot> !b \<cdot> p \<cdot> !b \<Longrightarrow> p \<cdot> b \<cdot> x \<le> x \<cdot> p"
  oops

lemma (in kat) "test p \<Longrightarrow> test q \<Longrightarrow>  p \<cdot> x \<cdot> y \<le> x \<cdot> y \<cdot> q \<Longrightarrow>(\<exists>r. test r \<and> p \<cdot> x \<le> x \<cdot> r \<and> r \<cdot> y  \<le> y \<cdot> q)"
  (* nitpick *)  oops

lemma (in kat) "test p \<Longrightarrow> test q \<Longrightarrow>  p \<cdot> x \<cdot> y \<cdot> !q = 0 \<Longrightarrow>(\<exists>r. test r \<and> p \<cdot> x \<cdot> !r = 0 \<and> r \<cdot> y \<cdot> !q = 0)"
  (* nitpick *) oops

text \<open>The following facts should be moved. They show that the rules of Hoare logic based on Tarlecki triples are invertible.\<close>

abbreviation (in near_dioid) tt :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lparr>_\<rparr>_\<lparr>_\<rparr>") where
  "\<lparr>x\<rparr> y \<lparr>z\<rparr> \<equiv> x \<cdot> y \<le> z" 

lemma (in near_dioid_one) tt_skip: "\<lparr>p\<rparr> 1 \<lparr>p\<rparr>"
  by simp

lemma (in near_dioid) tt_cons1: "(\<exists>q'. \<lparr>p\<rparr> x \<lparr>q'\<rparr> \<and> q'\<le> q) \<longleftrightarrow> \<lparr>p\<rparr> x \<lparr>q\<rparr>"
  using local.order_trans by blast

lemma (in near_dioid) tt_cons2:  "(\<exists>p'. \<lparr>p'\<rparr> x \<lparr>q\<rparr> \<and> p \<le> p') \<longleftrightarrow> \<lparr>p\<rparr> x \<lparr>q\<rparr>"
  using local.dual_order.trans local.mult_isor by blast

lemma (in near_dioid) tt_seq: "(\<exists>r. \<lparr>p\<rparr> x \<lparr>r\<rparr> \<and> \<lparr>r\<rparr> y \<lparr>q\<rparr>) \<longleftrightarrow> \<lparr>p\<rparr> x \<cdot> y \<lparr>q\<rparr>"
  by (metis local.tt_cons2 mult_assoc)

lemma (in dioid) tt_cond: "\<lparr>p \<cdot> v\<rparr> x \<lparr>q\<rparr> \<and> \<lparr>p \<cdot> w\<rparr> y \<lparr>q\<rparr> \<longleftrightarrow> \<lparr>p\<rparr> (v \<cdot> x + w \<cdot> y)\<lparr>q\<rparr>"
  by (simp add: local.distrib_left mult_assoc)

lemma (in kleene_algebra) tt_while: "w \<le> 1 \<Longrightarrow> \<lparr>p \<cdot> v\<rparr> x \<lparr>p\<rparr> \<Longrightarrow> \<lparr>p\<rparr> (v \<cdot> x)\<^sup>\<star> \<cdot> w \<lparr>p\<rparr>"
  by (metis local.star_inductr_var_equiv local.star_subid local.tt_seq local.tt_skip mult_assoc)

text \<open>The converse implication can be refuted. The situation is similar to the ht case.\<close>

lemma (in kat) tt_while: "test v \<Longrightarrow>  \<lparr>p\<rparr> (v \<cdot> x)\<^sup>\<star> \<cdot> !v \<lparr>p\<rparr> \<Longrightarrow> \<lparr>p \<cdot> v\<rparr> x \<lparr>p\<rparr>"
  (* nitpick *) oops

lemma (in kat) tt_while: "test v \<Longrightarrow>  \<lparr>p\<rparr> (v \<cdot> x)\<^sup>\<star>  \<lparr>p\<rparr> \<Longrightarrow> \<lparr>p \<cdot> v\<rparr> x \<lparr>p\<rparr>"
  using local.star_inductr_var_equiv mult_assoc by auto

text \<open>Perhaps this holds with possibly infinite loops in DRA...\<close>

text \<open>wlp in KAT\<close>

lemma (in kat) "test y \<Longrightarrow> (\<exists> z. test z \<and> z \<cdot> x \<cdot> !y = 0)"
  by (metis local.annil local.test_zero_var)

end                                                                                             

