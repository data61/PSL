(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Chain
  imports "HOL-Nominal.Nominal"
begin

lemma pt_set_nil: 
  fixes Xs :: "'a set"
  assumes pt: "pt TYPE('a) TYPE ('x)"
  and     at: "at TYPE('x)"

  shows "([]::'x prm)\<bullet>Xs = Xs"
by(auto simp add: perm_set_def pt1[OF pt])

lemma pt_set_append: 
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   Xs  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE ('x)"
  and     at: "at TYPE('x)"

  shows "(pi1@pi2)\<bullet>Xs = pi1\<bullet>(pi2\<bullet>Xs)"
by(auto simp add: perm_set_def pt2[OF pt])

lemma pt_set_prm_eq: 
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   Xs  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE ('x)"
  and     at: "at TYPE('x)"

  shows "pi1 \<triangleq> pi2  \<Longrightarrow> pi1\<bullet>Xs = pi2\<bullet>Xs"
by(auto simp add: perm_set_def pt3[OF pt])

lemma pt_set_inst:
  assumes pt: "pt TYPE('a) TYPE ('x)"
  and     at: "at TYPE('x)"

  shows "pt TYPE('a set) TYPE('x)"
apply(simp add: pt_def pt_set_nil[OF pt, OF at] pt_set_append[OF pt, OF at])
apply(clarify)
by(rule pt_set_prm_eq[OF pt, OF at])

lemma pt_ball_eqvt:
  fixes pi :: "'a prm"
  and   Xs :: "'b set"
  and   P :: "'b \<Rightarrow> bool"

  assumes pt: "pt TYPE('b) TYPE('a)"
  and     at: "at TYPE('a)"

  shows "(pi \<bullet> (\<forall>x \<in> Xs. P x)) = (\<forall>x \<in> (pi \<bullet> Xs). pi \<bullet> P (rev pi \<bullet> x))"
apply(auto simp add: perm_bool)
apply(drule_tac pi="rev pi" in pt_set_bij2[OF pt, OF at])
apply(simp add: pt_rev_pi[OF pt_set_inst[OF pt, OF at], OF at])
apply(drule_tac pi="pi" in pt_set_bij2[OF pt, OF at])
apply(erule_tac x="pi \<bullet> x" in ballE)
apply(simp add: pt_rev_pi[OF pt, OF at])
by simp

lemma perm_cart_prod:
  fixes Xs :: "'b set"
  and   Ys :: "'c set"
  and   p  :: "'a prm"

  assumes pt1: "pt TYPE('b) TYPE('a)"
  and     pt2: "pt TYPE('c) TYPE('a)"
  and     at:  "at TYPE('a)"

  shows "(p \<bullet> (Xs \<times> Ys)) = (((p \<bullet> Xs) \<times> (p \<bullet> Ys))::(('b \<times> 'c) set))"
by(auto simp add: perm_set_def)

lemma supp_member:
  fixes Xs :: "'b set"
  and   x  :: 'a

  assumes pt: "pt TYPE('b) TYPE('a)"
  and     at: "at TYPE('a)"
  and     fs: "fs TYPE('b) TYPE('a)"
  and     "finite Xs"
  and     "x \<in> ((supp Xs)::'a set)"

  obtains X where "(X::'b) \<in> Xs" and "x \<in> supp X"
proof -
  from \<open>finite Xs\<close> \<open>x \<in> supp Xs\<close> have "\<exists>X::'b. (X \<in> Xs) \<and> (x \<in> (supp X))"
  proof(induct rule: finite_induct)
    case empty
    from \<open>x \<in> ((supp {})::'a set)\<close> have False
      by(simp add: supp_set_empty)
    thus ?case by simp
  next
    case(insert y Xs)
    show ?case
    proof(case_tac "x \<in> supp y")
      assume "x \<in> supp y"
      thus ?case by force
    next
      assume "x \<notin> supp y"
      with \<open>x \<in> supp(insert y Xs)\<close> have "x \<in> supp Xs"
        by(simp add: supp_fin_insert[OF pt, OF at, OF fs, OF \<open>finite Xs\<close>])
      with \<open>x \<in> supp Xs \<Longrightarrow> \<exists>X. X \<in> Xs \<and> x \<in> supp X\<close>
      show ?case by force
    qed
  qed
  with that show ?thesis by blast
qed

lemma supp_cart_prod_empty[simp]:
  fixes Xs :: "'b set"

  shows "supp (Xs \<times> {}) = ({}::'a set)"
  and   "supp ({} \<times> Xs) = ({}::'a set)"
by(auto simp add: supp_set_empty)

lemma supp_cart_prod:
  fixes Xs :: "'b set"
  and   Ys :: "'c set"

  assumes pt1: "pt TYPE('b) TYPE('a)"
  and     pt2: "pt TYPE('c) TYPE('a)"
  and     fs1: "fs TYPE('b) TYPE('a)"
  and     fs2: "fs TYPE('c) TYPE('a)"
  and     at:  "at TYPE('a)"
  and     f1:  "finite Xs"
  and     f2:  "finite Ys"
  and     a:   "Xs \<noteq> {}"
  and     b:   "Ys \<noteq> {}"

  shows "((supp (Xs \<times> Ys))::'a set) = ((supp Xs) \<union> (supp Ys))"
proof -
  from f1 f2 have f3: "finite(Xs \<times> Ys)" by simp
  show ?thesis
    apply(simp add: supp_of_fin_sets[OF pt_prod_inst[OF pt1, OF pt2], OF at, OF fs_prod_inst[OF fs1, OF fs2], OF f3] supp_prod)
    apply(rule equalityI)
    using Union_included_in_supp[OF pt1, OF at, OF fs1, OF f1] Union_included_in_supp[OF pt2, OF at, OF fs2, OF f2]
    apply(force simp add: supp_prod)
    using a b
    apply(auto simp add: supp_prod)
    using supp_member[OF pt1, OF at, OF fs1, OF f1]
    apply blast
    using supp_member[OF pt2, OF at, OF fs2, OF f2]
    by blast
qed

lemma fresh_cart_prod:
  fixes x  :: 'a
  and   Xs :: "'b set"
  and   Ys :: "'c set"

  assumes pt1: "pt TYPE('b) TYPE('a)"
  and     pt2: "pt TYPE('c) TYPE('a)"
  and     fs1: "fs TYPE('b) TYPE('a)"
  and     fs2: "fs TYPE('c) TYPE('a)"
  and     at:  "at TYPE('a)"
  and     f1:  "finite Xs"
  and     f2:  "finite Ys"
  and     a:   "Xs \<noteq> {}"
  and     b:   "Ys \<noteq> {}"

  shows "(x \<sharp> (Xs \<times> Ys)) = (x \<sharp> Xs \<and> x \<sharp> Ys)"
using assms
by(simp add: supp_cart_prod fresh_def)

lemma fresh_star_cart_prod:
  fixes Zs   :: "'a set"
  and   xvec :: "'a list"
  and   Xs   :: "'b set"
  and   Ys   :: "'c set"

  assumes pt1: "pt TYPE('b) TYPE('a)"
  and     pt2: "pt TYPE('c) TYPE('a)"
  and     fs1: "fs TYPE('b) TYPE('a)"
  and     fs2: "fs TYPE('c) TYPE('a)"
  and     at:  "at TYPE('a)"
  and     f1:  "finite Xs"
  and     f2:  "finite Ys"
  and     a:   "Xs \<noteq> {}"
  and     b:   "Ys \<noteq> {}"

  shows "(Zs \<sharp>* (Xs \<times> Ys)) = (Zs \<sharp>* Xs \<and> Zs \<sharp>* Ys)"
  and   "(xvec \<sharp>* (Xs \<times> Ys)) = (xvec \<sharp>* Xs \<and> xvec \<sharp>* Ys)"
using assms
by(force simp add: fresh_cart_prod fresh_star_def)+

lemma permCommute:
  fixes p  :: "'a prm"
  and   q  :: "'a prm"
  and   P  :: 'x
  and   Xs :: "'a set"
  and   Ys :: "'a set"

  assumes pt: "pt TYPE('x) TYPE('a)"
  and     at: "at TYPE('a)"
  and     a: "(set p) \<subseteq> Xs \<times> Ys"
  and     b: "Xs \<sharp>* q"
  and     c: "Ys \<sharp>* q"

  shows "p \<bullet> q \<bullet> P = q \<bullet> p \<bullet> P"
proof -
  have "p \<bullet> q \<bullet> P = (p \<bullet> q) \<bullet> p \<bullet> P"
    by(rule pt_perm_compose[OF pt, OF at])
  moreover from at have "pt TYPE('a) TYPE('a)"
    by(rule at_pt_inst)
  hence "pt TYPE(('a \<times> 'a) list) TYPE('a)"
    by(force intro: pt_prod_inst pt_list_inst)
  hence "p \<bullet> q = q" using at a b c
    by(rule pt_freshs_freshs)
  ultimately show ?thesis by simp
qed


definition
  distinctPerm :: "'a prm \<Rightarrow> bool" where
  "distinctPerm p \<equiv> distinct((map fst p)@(map snd p))"

lemma at_set_avoiding_aux':
  fixes Xs::"'a set"
  and   As::"'a set"
  assumes at: "at TYPE('a)"
  and     a: "finite Xs"
  and     b: "Xs \<subseteq> As"
  and     c: "finite As"
  and     d: "finite ((supp c)::'a set)"
  shows "\<exists>(Ys::'a set) (pi::'a prm). Ys\<sharp>*c \<and> Ys \<inter> As = {} \<and> (pi\<bullet>Xs=Ys) \<and> 
          set pi \<subseteq> Xs \<times> Ys \<and> finite Ys \<and> (distinctPerm pi)"
using a b c
proof (induct)
  case empty
  have "({}::'a set)\<sharp>*c" by (simp add: fresh_star_def)
  moreover
  have "({}::'a set) \<inter> As = {}" by simp
  moreover
  have "([]::'a prm)\<bullet>{} = ({}::'a set)"
    by(rule pt1) (metis Nominal.pt_set_inst at at_pt_inst)
  moreover
  have "set ([]::'a prm) \<subseteq> {} \<times> {}" by simp
  moreover 
  have "finite ({}::'a set)" by simp
  moreover have "distinctPerm([]::'a prm)"
    by(simp add: distinctPerm_def)
  ultimately show ?case by blast
next
  case (insert x Xs)
  then have ih: "\<exists>Ys pi. Ys\<sharp>*c \<and> Ys \<inter> As = {} \<and> pi\<bullet>Xs = Ys \<and> set pi \<subseteq> Xs \<times> Ys \<and> finite Ys \<and> distinctPerm pi" by simp
  then obtain Ys pi where a1: "Ys\<sharp>*c" and a2: "Ys \<inter> As = {}" and a3: "(pi::'a prm)\<bullet>Xs = Ys" and 
                          a4: "set pi \<subseteq> Xs \<times> Ys" and a5: "finite Ys" 
                      and a6: "distinctPerm pi" by blast
  have b: "x\<notin>Xs" by fact
  have d1: "finite As" by fact
  have d2: "finite Xs" by fact
  have d3: "insert x Xs \<subseteq> As" by fact
  have d4: "finite((supp pi)::'a set)"
    by(induct pi)
      (auto simp add: supp_list_nil supp_prod at_fin_set_supp[OF at]
                      supp_list_cons at_supp[OF at])
  have "\<exists>y::'a. y\<sharp>(c,x,Ys,As,pi)" using d d1 a5 d4
    by (rule_tac at_exists_fresh'[OF at])
       (simp add: supp_prod at_supp[OF at] at_fin_set_supp[OF at])
  then obtain y::"'a" where  e: "y\<sharp>(c,x,Ys,As,pi)" by blast
  have "({y}\<union>Ys)\<sharp>*c" using a1 e by (simp add: fresh_star_def)
  moreover
  have "({y}\<union>Ys)\<inter>As = {}" using a2 d1 e by (simp add: fresh_prod at_fin_set_fresh[OF at])
  moreover
  have "(((pi\<bullet>x,y)#pi)\<bullet>(insert x Xs)) = {y}\<union>Ys"
  proof -
    have eq: "[(pi\<bullet>x,y)]\<bullet>Ys = Ys" 
    proof -
      have "(pi\<bullet>x)\<sharp>Ys" using a3[symmetric] b d2
        by(simp add: pt_fresh_bij[OF pt_set_inst, OF at_pt_inst[OF at], OF at, OF at]
                     at_fin_set_fresh[OF at d2])
      moreover
      have "y\<sharp>Ys" using e by simp
      ultimately show "[(pi\<bullet>x,y)]\<bullet>Ys = Ys" 
        by (simp add: pt_fresh_fresh[OF pt_set_inst, OF at_pt_inst[OF at], OF at, OF at])
    qed
    have "(((pi\<bullet>x,y)#pi)\<bullet>({x}\<union>Xs)) = ([(pi\<bullet>x,y)]\<bullet>(pi\<bullet>({x}\<union>Xs)))"
      by (simp add: pt2[symmetric, OF pt_set_inst, OF at_pt_inst[OF at], OF at])
    also have "\<dots> = {y}\<union>([(pi\<bullet>x,y)]\<bullet>(pi\<bullet>Xs))" 
      by (simp only: union_eqvt perm_set_def at_calc[OF at])(auto)
    also have "\<dots> = {y}\<union>([(pi\<bullet>x,y)]\<bullet>Ys)" using a3 by simp
    also have "\<dots> = {y}\<union>Ys" using eq by simp
    finally show "(((pi\<bullet>x,y)#pi)\<bullet>(insert x Xs)) = {y}\<union>Ys" by auto
  qed
  moreover
  have "pi\<bullet>x=x" using a4 b a2 a3 d3 by (rule_tac at_prm_fresh2[OF at]) (auto)
  then have "set ((pi\<bullet>x,y)#pi) \<subseteq> (insert x Xs) \<times> ({y}\<union>Ys)" using a4 by auto
  moreover 
  have "finite ({y}\<union>Ys)" using a5 by simp
  moreover from \<open>Ys \<inter> As = {}\<close> \<open>(insert x Xs) \<subseteq> As\<close> \<open>finite Ys\<close> have "x \<notin> Ys"
    by(auto simp add: fresh_def at_fin_set_supp[OF at])
  with a6 \<open>pi \<bullet> x = x\<close> \<open>x \<notin> Xs\<close> \<open>(set pi) \<subseteq> Xs \<times> Ys\<close> e have "distinctPerm((pi \<bullet> x, y)#pi)"
    apply(auto simp add: distinctPerm_def fresh_prod at_fresh[OF at])
    proof -
      fix a b
      assume "b \<sharp> pi" and "(a, b) \<in> set pi"
      thus False
        by(induct pi)
          (auto simp add: supp_list_cons supp_prod at_supp[OF at] fresh_list_cons fresh_prod at_fresh[OF at])
    next
      fix a b
      assume "a \<sharp> pi" and "(a, b) \<in> set pi"
      thus False
        by(induct pi)
          (auto simp add: supp_list_cons supp_prod at_supp[OF at] fresh_list_cons fresh_prod at_fresh[OF at])
    qed
  ultimately 
  show ?case by blast
qed

lemma at_set_avoiding:
  fixes Xs::"'a set"
  assumes at: "at TYPE('a)"
  and     a: "finite Xs"
  and     b: "finite ((supp c)::'a set)"
  obtains pi::"'a prm" where "(pi \<bullet> Xs) \<sharp>* c" and "set pi \<subseteq> Xs \<times> (pi \<bullet> Xs)" and "distinctPerm pi"
  using a b
  by (frule_tac As="Xs" in at_set_avoiding_aux'[OF at]) auto

lemma pt_swap:
  fixes x :: 'a
  and a :: 'x
  and b :: 'x

  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"

  shows "[(a, b)] \<bullet> x = [(b, a)] \<bullet> x"
proof -
  show ?thesis by(simp add: pt3[OF pt] at_ds5[OF at])
qed


atom_decl name

lemma supp_subset:
  fixes Xs :: "'a::fs_name set"
  and   Ys :: "'a::fs_name set"

  assumes "Xs \<subseteq> Ys"
  and     "finite Xs"
  and     "finite Ys"

  shows "(supp Xs) \<subseteq> ((supp Ys)::name set)"
proof(rule subsetI)
  fix x
  assume "x \<in> ((supp Xs)::name set)"
  with \<open>finite Xs\<close> obtain X where "X \<in> Xs" and "x \<in> supp X"
    by(rule supp_member[OF pt_name_inst, OF at_name_inst, OF fs_name_inst])
  from \<open>X \<in> Xs\<close> \<open>Xs \<subseteq> Ys\<close> have "X \<in> Ys" by auto
  with \<open>finite Ys\<close> \<open>x \<in> supp X\<close> show "x \<in> supp Ys"
    by(induct rule: finite_induct)
      (auto simp add: supp_fin_insert[OF pt_name_inst, OF at_name_inst, OF fs_name_inst])
qed

abbreviation mem_def :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" ("_ mem _" [80, 80] 80)  where
  "x mem xs \<equiv> x \<in> set xs"

lemma memFresh:
  fixes x :: name
  and   p :: "'a::fs_name"
  and   l :: "('a::fs_name) list"

  assumes "x \<sharp> l"
  and     "p mem l"
  
  shows "x \<sharp> p"
using assms
by(induct l, auto simp add: fresh_list_cons)

lemma memFreshChain:
  fixes xvec :: "name list"
  and   p    :: "'a::fs_name"
  and   l    :: "'a::fs_name list"
  and   Xs   :: "name set"

  assumes "p mem l"
  
  shows "xvec \<sharp>* l \<Longrightarrow> xvec \<sharp>* p"
  and   "Xs \<sharp>* l \<Longrightarrow> Xs \<sharp>* p"
using assms
by(auto simp add: fresh_star_def intro: memFresh)

lemma fresh_star_list_append[simp]:
  fixes A :: "name list"
  and   B :: "name list"
  and   C :: "name list"

  shows "(A \<sharp>* (B @ C)) = ((A \<sharp>* B) \<and> (A \<sharp>* C))"
by(auto simp add: fresh_star_def fresh_list_append)

lemma unionSimps[simp]:
  fixes Xs :: "name set"
  and   Ys :: "name set"
  and   C  :: "'a::fs_name"

  shows "((Xs \<union> Ys) \<sharp>* C) = ((Xs \<sharp>* C) \<and> (Ys \<sharp>* C))"
by(auto simp add: fresh_star_def)

lemma substFreshAux[simp]:
  fixes C    :: "'a::fs_name"
  and   xvec :: "name list"

  shows "xvec \<sharp>* (supp C - set xvec)"
by(auto simp add: fresh_star_def fresh_def at_fin_set_supp[OF at_name_inst] fs_name1)

lemma fresh_star_perm_app[simp]:
  fixes Xs :: "name set"
  and   xvec :: "name list"
  and   p  :: "name prm"
  and   C  :: "'d::fs_name"

  shows "\<lbrakk>Xs \<sharp>* p; Xs \<sharp>* C\<rbrakk> \<Longrightarrow> Xs \<sharp>* (p \<bullet> C)"
  and   "\<lbrakk>xvec \<sharp>* p; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> xvec \<sharp>* (p \<bullet> C)"
by(auto simp add: fresh_star_def fresh_perm_app)

lemma freshSets[simp]:
  fixes x    :: name
  and   y    :: name
  and   xvec :: "name list"
  and   X    :: "name set"
  and   C    :: 'a

  shows "([]::name list) \<sharp>* C"
  and   "([]::name list) \<sharp>* [y].C"
  and   "({}::name set) \<sharp>* C"
  and   "({}::name set) \<sharp>* [y].C"
  and   "((x#xvec) \<sharp>* C) = (x \<sharp> C \<and> xvec \<sharp>* C)"
  and   "((x#xvec) \<sharp>* ([y].C)) = (x \<sharp> ([y].C) \<and> xvec \<sharp>* ([y].C))"
  and   "((insert x X) \<sharp>* C) = (x \<sharp> C \<and> X \<sharp>* C)"
  and   "((insert x X) \<sharp>* ([y].C)) = (x \<sharp> ([y].C) \<and> X \<sharp>* ([y].C))"
by(auto simp add: fresh_star_def)

lemma freshStarAtom[simp]: "(xvec::name list) \<sharp>* (x::name) = x \<sharp> xvec"
by(induct xvec)
  (auto simp add: fresh_list_nil fresh_list_cons fresh_atm)

lemma name_list_set_fresh[simp]:
  fixes xvec :: "name list"
  and   x    :: "'a::fs_name"

  shows "(set xvec) \<sharp>* x = xvec \<sharp>* x"
by(auto simp add: fresh_star_def)

lemma name_list_supp:
  fixes xvec :: "name list"

  shows "set xvec = supp xvec"
proof -
  have "set xvec = supp(set xvec)"
    by(simp add: at_fin_set_supp[OF at_name_inst])
  moreover have "\<dots> = supp xvec"
    by(simp add: pt_list_set_supp[OF pt_name_inst, OF at_name_inst, OF fs_name_inst])
  ultimately show ?thesis
    by simp
qed

lemma abs_fresh_list_star:
  fixes xvec :: "name list"
  and   a    :: name
  and   P    :: "'a::fs_name"

  shows "(xvec \<sharp>* [a].P) = ((set xvec) - {a}) \<sharp>* P"
by(induct xvec) (auto simp add: fresh_star_def abs_fresh)

lemma abs_fresh_set_star:
  fixes X :: "name set"
  and   a :: name
  and   P :: "'a::fs_name"

  shows "(X \<sharp>* [a].P) = (X - {a}) \<sharp>* P"
by(auto simp add: fresh_star_def abs_fresh)

lemmas abs_fresh_star = abs_fresh_list_star abs_fresh_set_star

lemma abs_fresh_list_star'[simp]:
  fixes xvec :: "name list"
  and   a    :: name
  and   P    :: "'a::fs_name"

  assumes "a \<sharp> xvec"

  shows "xvec \<sharp>* [a].P = xvec \<sharp>* P"
using assms
by(induct xvec) (auto simp add: abs_fresh fresh_list_cons fresh_atm)

lemma freshChainSym[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  
  shows   "xvec \<sharp>* yvec = yvec \<sharp>* xvec"
by(auto simp add: fresh_star_def fresh_def name_list_supp)

lemmas [eqvt] = perm_cart_prod[OF pt_name_inst, OF pt_name_inst, OF at_name_inst]

lemma name_set_avoiding:
  fixes c :: "'a::fs_name"
  and   X :: "name set"
  
  assumes "finite X"
  and     "\<And>pi::name prm. \<lbrakk>(pi \<bullet> X) \<sharp>* c; distinctPerm pi; set pi \<subseteq> X \<times> (pi \<bullet> X)\<rbrakk> \<Longrightarrow> thesis"

  shows thesis
using assms
by(rule_tac c=c in at_set_avoiding[OF at_name_inst]) (simp_all add: fs_name1)

lemmas simps[simp] = fresh_atm fresh_prod
                     pt3[OF pt_name_inst, OF at_ds1, OF at_name_inst]
                     pt_fresh_fresh[OF pt_name_inst, OF at_name_inst]
                     pt_rev_pi[OF pt_name_inst, OF at_name_inst]
                     pt_pi_rev[OF pt_name_inst, OF at_name_inst]

lemmas name_supp_cart_prod = supp_cart_prod[OF pt_name_inst, OF pt_name_inst, OF fs_name_inst, OF fs_name_inst, OF at_name_inst]
lemmas name_fresh_cart_prod = fresh_cart_prod[OF pt_name_inst, OF pt_name_inst, OF fs_name_inst, OF fs_name_inst, OF at_name_inst]
lemmas name_fresh_star_cart_prod = fresh_star_cart_prod[OF pt_name_inst, OF pt_name_inst, OF fs_name_inst, OF fs_name_inst, OF at_name_inst]


lemmas name_swap_bij[simp] = pt_swap_bij[OF pt_name_inst, OF at_name_inst]
lemmas name_swap = pt_swap[OF pt_name_inst, OF at_name_inst]
lemmas name_set_fresh_fresh[simp] = pt_freshs_freshs[OF pt_name_inst, OF at_name_inst]
lemmas list_fresh[simp] = fresh_list_nil fresh_list_cons fresh_list_append

definition  eqvt :: "'a::fs_name set \<Rightarrow> bool" where
                  "eqvt X \<equiv> \<forall>x \<in> X. \<forall>p::name prm. p \<bullet> x \<in> X"

lemma eqvtUnion[intro]:
  fixes Rel  :: "('d::fs_name) set"
  and   Rel' :: "'d set"

  assumes EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "eqvt (Rel \<union> Rel')"
using assms
by(force simp add: eqvt_def)

lemma eqvtPerm[simp]: 
  fixes X :: "('d::fs_name) set"
  and   x :: name
  and   y :: name

  assumes "eqvt X"

  shows "([(x, y)] \<bullet> X) = X"
using assms
apply(auto simp add: eqvt_def)
apply(erule_tac x="[(x, y)] \<bullet> xa" in ballE)
apply(erule_tac x="[(x, y)]" in allE)
apply simp
apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply simp
apply(erule_tac x=xa in ballE)
apply(erule_tac x="[(x, y)]" in allE)
apply(drule_tac pi="[(x, y)]" and x="[(x, y)] \<bullet> xa" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply simp
by simp

lemma eqvtI:
  fixes X :: "'d::fs_name set"
  and   x :: 'd
  and   p :: "name prm"
  
  assumes "eqvt X"
  and     "x \<in> X"
 
  shows "(p \<bullet> x) \<in> X"
using assms
by(unfold eqvt_def) auto

lemma fresh_star_list_nil[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  
  shows "xvec \<sharp>* []"
  and   "Xs \<sharp>* []"
by(auto simp add: fresh_star_def)

lemma fresh_star_list_cons[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   x    :: "'a::fs_name"
  and   xs   :: "'a list"

  shows "(xvec \<sharp>* (x#xs)) = ((xvec \<sharp>* x) \<and> xvec \<sharp>* xs)"
  and   "(Xs \<sharp>* (x#xs)) = ((Xs \<sharp>* x) \<and> (Xs \<sharp>* xs))"
by(auto simp add: fresh_star_def)

lemma freshStarPair[simp]:
  fixes X    :: "name set"
  and   xvec :: "name list"
  and   x    :: "'a::fs_name"
  and   y    :: "'b::fs_name"

  shows "(X \<sharp>* (x, y)) = (X \<sharp>* x \<and> X \<sharp>* y)"
  and   "(xvec \<sharp>* (x, y)) = (xvec \<sharp>* x \<and> xvec \<sharp>* y)"
by(auto simp add: fresh_star_def)
lemma name_list_avoiding:
  fixes c    :: "'a::fs_name"
  and   xvec :: "name list"
  
  assumes "\<And>pi::name prm. \<lbrakk>(pi \<bullet> xvec) \<sharp>* c; distinctPerm pi; set pi \<subseteq> (set xvec) \<times> (set (pi \<bullet> xvec))\<rbrakk> \<Longrightarrow> thesis"

  shows thesis
proof -
  have "finite(set xvec)" by simp
  thus ?thesis using assms
    by(rule name_set_avoiding) (auto simp add: eqvts fresh_star_def)
qed

lemma distinctPermSimps[simp]:
  fixes p :: "name prm"
  and   a :: name
  and   b :: name

  shows "distinctPerm([]::name prm)"
  and   "(distinctPerm((a, b)#p)) = (distinctPerm p \<and> a \<noteq> b \<and> a \<sharp> p \<and> b \<sharp> p)"
apply(simp add: distinctPerm_def)
apply(induct p)
apply(unfold distinctPerm_def)
apply(clarsimp)
apply(rule iffI, erule iffE)
by(clarsimp)+

lemma map_eqvt[eqvt]:
  fixes p   :: "name prm"
  and   lst :: "'a::pt_name list"

  shows "(p \<bullet> (map f lst)) = map (p \<bullet> f) (p \<bullet> lst)"
apply(induct lst, auto) 
by(simp add: pt_fun_app_eq[OF pt_name_inst, OF at_name_inst])

lemma consPerm:
  fixes x :: name
  and   y :: name
  and   p :: "name prm"
  and   C :: "'a::pt_name"

  shows "((x, y)#p) \<bullet> C = [(x, y)] \<bullet> p \<bullet> C"
by(simp add: pt2[OF pt_name_inst, THEN sym])

simproc_setup consPerm ("((x, y)#p) \<bullet> C") = \<open>
  fn _ => fn _ => fn ct => 
    case Thm.term_of ct of 
      Const (@{const_name perm}, _ ) $ (Const (@{const_name Cons}, _) $ _ $ p) $ _ =>
        (case p of
          Const (@{const_name Nil}, _) => NONE
        | _ => SOME(mk_meta_eq @{thm consPerm}))
    | _ => NONE
\<close>

lemma distinctEqvt[eqvt]:
  fixes p  :: "name prm"
  and   xs :: "'a::pt_name list"

  shows "(p \<bullet> (distinct xs)) = distinct (p \<bullet> xs)"
by(induct xs) (auto simp add: eqvts)

lemma distinctClosed[simp]:
  fixes p  :: "name prm"
  and   xs :: "'a::pt_name list"

  shows "distinct (p \<bullet> xs) = distinct xs"
apply(induct xs)
apply(auto simp add: eqvts)
apply(drule_tac pi=p in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: eqvts)
apply(drule_tac pi="rev p" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by(simp add: eqvts)

lemma lengthEqvt[eqvt]:
  fixes p  :: "name prm"
  and   xs :: "'a::pt_name list"
  
  shows "p \<bullet> (length xs) = length (p \<bullet> xs)"
by(induct xs) (auto simp add: eqvts)

lemma lengthClosed[simp]:
  fixes p  :: "name prm"
  and   xs :: "'a::pt_name list"
  
  shows "length (p \<bullet> xs) = length xs"
by(induct xs) (auto simp add: eqvts)

lemma subsetEqvt[eqvt]:
  fixes p :: "name prm"
  and   S :: "('a::pt_name) set"
  and   T :: "('a::pt_name) set"

  shows "(p \<bullet> (S \<subseteq> T)) = ((p \<bullet> S) \<subseteq> (p \<bullet> T))"
by(rule pt_subseteq_eqvt[OF pt_name_inst, OF at_name_inst])

lemma subsetClosed[simp]:
  fixes p :: "name prm"
  and   S :: "('a::pt_name) set"
  and   T :: "('a::pt_name) set"

  shows "((p \<bullet> S) \<subseteq> (p \<bullet> T)) = (S \<subseteq> T)"
apply auto
apply(drule_tac pi=p in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(insert pt_set_bij[OF pt_name_inst, OF at_name_inst])
apply auto
apply(drule_tac pi="rev p" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply auto
apply(subgoal_tac "rev p \<bullet> x \<in> T")
apply auto
apply(drule_tac pi="p" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply auto
apply(drule_tac pi="p" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by auto

lemma subsetClosed'[simp]:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   P    :: "'a::fs_name"

  shows "(set (p \<bullet> xvec) \<subseteq> supp (p \<bullet> P)) = (set xvec \<subseteq> supp P)"
by(simp add: eqvts[THEN sym])

lemma memEqvt[eqvt]:
  fixes p  :: "name prm"
  and   x  :: "'a::pt_name"
  and   xs :: "('a::pt_name) list"

  shows "(p \<bullet> (x mem xs)) = ((p \<bullet> x) mem (p \<bullet> xs))"
by(induct xs)
  (auto simp add: pt_bij[OF pt_name_inst, OF at_name_inst] eqvts)

lemma memClosed[simp]:
  fixes p  :: "name prm"
  and   x  :: "'a::pt_name"
  and   xs :: "('a::pt_name) list"

  shows "(p \<bullet> x) mem (p \<bullet> xs) = (x mem xs)"
proof -
  have "x mem xs = p \<bullet> (x mem xs)"
    by(case_tac "x mem xs") auto
  thus ?thesis by(simp add: eqvts)
qed

lemma memClosed'[simp]:
  fixes p  :: "name prm"
  and   x  :: "'a::pt_name"
  and   y  :: "'b::pt_name"
  and   xs :: "('a \<times>  'b) list" 

  shows "((p \<bullet> x, p \<bullet> y) mem (p \<bullet> xs)) = ((x, y) mem xs)"
apply(subgoal_tac "((x, y) mem xs) = (p \<bullet> (x, y)) mem (p \<bullet> xs)")
apply force
by(force simp del: eqvts)


lemma freshPerm:
  fixes x :: name
  and   p :: "name prm"

  assumes "x \<sharp> p"

  shows "p \<bullet> x = x"
using assms
apply(rule_tac pt_pi_fresh_fresh[OF pt_name_inst, OF at_name_inst])
by(induct p, auto simp add: fresh_list_cons fresh_prod)

lemma freshChainPermSimp:
  fixes xvec :: "name list"
  and   p    :: "name prm"

  assumes "xvec \<sharp>* p"

  shows "p \<bullet> xvec = xvec"
  and   "rev p \<bullet> xvec = xvec"
using assms
by(induct xvec) (auto simp add: freshPerm pt_bij1[OF pt_name_inst, OF at_name_inst, THEN sym])

lemma freshChainAppend[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   C    :: "'a::fs_name"
  
  shows "(xvec@yvec) \<sharp>* C = ((xvec \<sharp>* C) \<and> (yvec \<sharp>* C))"
by(force simp add: fresh_star_def)

lemma subsetFresh:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   C    :: "'d::fs_name"

  assumes "set xvec \<subseteq> set yvec"
  and     "yvec \<sharp>* C"

  shows "xvec \<sharp>* C"
using assms
by(auto simp add: fresh_star_def)

lemma distinctPermCancel[simp]:
  fixes p :: "name prm"
  and   T :: "'a::pt_name"

  assumes "distinctPerm p"

  shows "(p \<bullet> (p \<bullet> T)) = T"
using assms
proof(induct p)
  case Nil
  show ?case by simp
next
  case(Cons a p)
  thus ?case
  proof(case_tac a, auto)
    fix a b
    assume "(a::name) \<sharp> (p::name prm)" "b \<sharp> p" "p \<bullet> p \<bullet> T = T" "a \<noteq> b"
    thus "[(a, b)] \<bullet> p \<bullet> [(a, b)] \<bullet> p \<bullet> T = T"
      by(subst pt_perm_compose[OF pt_name_inst, OF at_name_inst]) simp
  qed
qed

fun composePerm :: "name list \<Rightarrow> name list \<Rightarrow> name prm"
where
  Base:  "composePerm [] [] = []"
| Step:  "composePerm (x#xs) (y#ys) = (x, y)#(composePerm xs ys)"
| Empty: "composePerm _ _= []"

lemma composePermInduct[consumes 1, case_names cBase cStep]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   P    :: "name list \<Rightarrow> name list \<Rightarrow> bool"

  assumes L: "length xvec = length yvec"
  and     rBase: "P [] []"
  and     rStep: "\<And>x xvec y yvec. \<lbrakk>length xvec = length yvec; P xvec yvec\<rbrakk> \<Longrightarrow> P (x # xvec) (y # yvec)"

  shows "P xvec yvec"
using assms
by(induct rule: composePerm.induct) auto

lemma composePermEqvt[eqvt]:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   yvec :: "name list"

  shows "(p \<bullet> (composePerm xvec yvec)) = composePerm (p \<bullet> xvec) (p \<bullet> yvec)"
by(induct xvec yvec rule: composePerm.induct) auto

abbreviation
  composePermJudge ("[_ _] \<bullet>\<^sub>v _" [80, 80, 80] 80) where "[xvec yvec] \<bullet>\<^sub>v p \<equiv> (composePerm xvec yvec) \<bullet> p"

abbreviation
  composePermInvJudge ("[_ _]\<^sup>- \<bullet>\<^sub>v _" [80, 80, 80] 80) where "[xvec yvec]\<^sup>- \<bullet>\<^sub>v p \<equiv> (rev (composePerm xvec yvec)) \<bullet> p"

lemma permChainSimps[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   perm :: "name prm"
  and   p    :: "'a::pt_name"

  shows "((composePerm xvec yvec) @ perm) \<bullet> p = [xvec yvec] \<bullet>\<^sub>v (perm \<bullet> p)"
by(simp add: pt2[OF pt_name_inst])

lemma permChainEqvt[eqvt]:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   x    :: "'a::pt_name"

  shows "(p \<bullet> ([xvec yvec] \<bullet>\<^sub>v x)) = [(p \<bullet> xvec) (p \<bullet> yvec)] \<bullet>\<^sub>v (p \<bullet> x)"
  and   "(p \<bullet> ([xvec yvec]\<^sup>- \<bullet>\<^sub>v x)) = [(p \<bullet> xvec) (p \<bullet> yvec)]\<^sup>- \<bullet>\<^sub>v (p \<bullet> x)"
by(subst pt_perm_compose[OF pt_name_inst, OF at_name_inst], simp add: eqvts rev_eqvt)+

lemma permChainBij:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   p    :: "'a::pt_name"
  and   q    :: "'a::pt_name"

  assumes "length xvec = length yvec"

  shows "(([xvec yvec] \<bullet>\<^sub>v p) = ([xvec yvec] \<bullet>\<^sub>v q)) = (p = q)"
  and   "(([xvec yvec]\<^sup>- \<bullet>\<^sub>v p) = ([xvec yvec]\<^sup>- \<bullet>\<^sub>v q)) = (p = q)"
using assms
by(induct rule: composePermInduct)
  (auto simp add: pt_bij[OF pt_name_inst, OF at_name_inst])

lemma permChainAppend:
  fixes xvec1 :: "name list"
  and   yvec1 :: "name list"
  and   xvec2 :: "name list"
  and   yvec2 :: "name list"
  and   p     :: "'a::pt_name"
  
  assumes "length xvec1 = length yvec1"

  shows "([(xvec1@xvec2) (yvec1@yvec2)] \<bullet>\<^sub>v p) = [xvec1 yvec1] \<bullet>\<^sub>v [xvec2 yvec2] \<bullet>\<^sub>v p"
  and   "([(xvec1@xvec2) (yvec1@yvec2)]\<^sup>- \<bullet>\<^sub>v p) = [xvec2 yvec2]\<^sup>- \<bullet>\<^sub>v [xvec1 yvec1]\<^sup>- \<bullet>\<^sub>v p"
using assms
by(induct arbitrary: p rule: composePermInduct, auto) (simp add: pt2[OF pt_name_inst])

lemma calcChainAtom:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   x    :: name

  assumes "length xvec = length yvec"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "[xvec yvec] \<bullet>\<^sub>v x = x"
using assms
by(induct rule: composePermInduct, auto)

lemma calcChainAtomRev:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   x    :: name

  assumes "length xvec = length yvec"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "[xvec yvec]\<^sup>- \<bullet>\<^sub>v x = x"
using assms
by(induct rule: composePermInduct, auto)
  (auto simp add: pt2[OF pt_name_inst] fresh_list_cons calc_atm)

lemma permChainFresh[simp]:
  fixes x    :: name
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   p    :: "'a::pt_name"

  assumes "x \<sharp> xvec"
  and     "x \<sharp> yvec"
  and     "length xvec = length yvec"

  shows "x \<sharp> [xvec yvec] \<bullet>\<^sub>v p = x \<sharp> p"
  and   "x \<sharp> [xvec yvec]\<^sup>- \<bullet>\<^sub>v p = x \<sharp> p"
using assms
by(auto simp add: fresh_left calcChainAtomRev calcChainAtom)

lemma chainFreshFresh:
  fixes x    :: name
  and   y    :: name
  and   xvec :: "name list"
  and   p    :: "'a::pt_name"

  assumes "x \<sharp> xvec"
  and     "y \<sharp> xvec"

  shows "xvec \<sharp>* ([(x, y)] \<bullet> p) = (xvec \<sharp>* p)"
using assms
by(induct xvec) (auto simp add: fresh_list_cons fresh_left)

lemma permChainFreshFresh:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   p    :: "'a::pt_name"

  assumes "xvec \<sharp>* p"
  and     "yvec \<sharp>* p"
  and     "length xvec = length yvec"

  shows "[xvec yvec] \<bullet>\<^sub>v p = p"
  and   "[xvec yvec]\<^sup>- \<bullet>\<^sub>v p = p"
using assms
by(induct rule: composePerm.induct, auto) (simp add: pt2[OF pt_name_inst])

lemma setFresh[simp]:
  fixes x    :: name
  and   xvec :: "name list"

  shows "x \<notin> set xvec = x \<sharp> xvec"
by(simp add: name_list_supp fresh_def)
  
lemma calcChain:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  
  assumes "yvec \<sharp>* xvec"
  and     "length xvec = length yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  shows "[xvec yvec] \<bullet>\<^sub>v xvec = yvec"
using assms
by(induct xvec yvec rule: composePerm.induct, auto)
  (subst consPerm, simp add: calcChainAtom calc_atm name_list_supp fresh_def[symmetric])+

lemma freshChainPerm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   x    :: name
  and   C    :: "'a::pt_name"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* C"
  and     "xvec \<sharp>* yvec"
  and     "x mem xvec"
  and     "distinct yvec"

  shows "x \<sharp> [xvec yvec] \<bullet>\<^sub>v C"
using assms
proof(induct rule: composePermInduct)
  case cBase
  have "x mem []" by fact
  hence False by simp
  thus ?case by simp
next
  case(cStep x' xvec y yvec)
  have "(y # yvec) \<sharp>* C" by fact
  hence yFreshC: "y \<sharp> C" and yvecFreshp: "yvec \<sharp>* C" by simp+
  have "(x' # xvec) \<sharp>* (y # yvec)" by fact
  hence x'ineqy: "x' \<noteq> y" and xvecFreshyvec: "xvec \<sharp>* yvec"
    and x'Freshyvec: "x' \<sharp> yvec" and yFreshxvec: "y \<sharp> xvec"
    by(auto simp add: fresh_list_cons)
  have "distinct (y#yvec)" by fact
  hence yFreshyvec: "y \<sharp> yvec" and yvecDist: "distinct yvec"
    by simp+
  have L: "length xvec = length yvec" by fact
  have "x \<sharp> [(x', y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v C"
  proof(case_tac "x = x'")
    assume xeqx': "x = x'"
    moreover from yFreshxvec yFreshyvec yFreshC L have "y \<sharp> [xvec yvec] \<bullet>\<^sub>v C"
      by simp
    hence "([(x, y)] \<bullet> y) \<sharp> [(x, y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v C"
      by(rule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
    with x'ineqy xeqx' show ?thesis by(simp add: calc_atm)
  next
    assume xineqx': "x \<noteq> x'"
    have "x mem (x' # xvec)" by fact
    with xineqx' have xmemxvec: "x mem xvec" by simp
    moreover have "\<lbrakk>yvec \<sharp>* C; xvec \<sharp>* yvec; x mem xvec; distinct yvec\<rbrakk> \<Longrightarrow> x \<sharp> [xvec yvec] \<bullet>\<^sub>v C" by fact
    ultimately have "x \<sharp> [xvec yvec] \<bullet>\<^sub>v C" using yvecFreshp xvecFreshyvec yvecDist
      by simp
    hence "([(x', y)] \<bullet> x) \<sharp> [(x', y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v C"
      by(rule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
    moreover from xmemxvec yFreshxvec have "x \<noteq> y"
      by(induct xvec) (auto simp add: fresh_list_cons)
    ultimately show ?thesis using xineqx' x'ineqy by(simp add: calc_atm)
  qed
  thus ?case by simp
qed

lemma memFreshSimp[simp]:
  fixes y    :: name
  and   yvec :: "name list"

  shows "(\<not>(y mem yvec)) = y \<sharp> yvec"
by(induct yvec)
  (auto simp add: fresh_list_nil fresh_list_cons)

lemma freshChainPerm':
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   p    :: "'a::pt_name"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* p"
  and     "xvec \<sharp>* yvec"
  and     "distinct yvec"

  shows "xvec \<sharp>* ([xvec yvec] \<bullet>\<^sub>v p)"
using assms
proof(induct rule: composePermInduct)
  case cBase
  show ?case by simp
next
  case(cStep x xvec y yvec)
  have "(y # yvec) \<sharp>* p" by fact
  hence yFreshp: "y \<sharp> p" and yvecFreshp: "yvec \<sharp>* p"
    by simp+
  moreover have "(x # xvec) \<sharp>* (y # yvec)" by fact
  hence xineqy: "x \<noteq> y" and xvecFreshyvec: "xvec \<sharp>* yvec"
    and xFreshyvec: "x \<sharp> yvec" and yFreshxvec: "y \<sharp> xvec"
    by(auto simp add: fresh_list_cons)
  have "distinct (y # yvec)" by fact
  hence yFreshyvec: "y \<sharp> yvec" and yvecDist: "distinct yvec"
    by simp+
  have L: "length xvec = length yvec" by fact
  have "\<lbrakk>yvec \<sharp>* p; xvec \<sharp>* yvec; distinct yvec\<rbrakk> \<Longrightarrow> xvec \<sharp>* ([xvec yvec] \<bullet>\<^sub>v p)" by fact
  with yvecFreshp xvecFreshyvec yvecDist have IH: "xvec \<sharp>* ([xvec yvec] \<bullet>\<^sub>v p)" by simp
  show ?case
  proof(auto)
    from L yFreshp yvecFreshp xineqy xvecFreshyvec yvecDist yFreshyvec yFreshxvec xFreshyvec
    have "x \<sharp> [(x # xvec) (y # yvec)] \<bullet>\<^sub>v p"
      by(rule_tac freshChainPerm) (auto simp add: fresh_list_cons)
    thus "x \<sharp> [(x, y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v p" by simp
  next
    show "xvec \<sharp>* ([(x, y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v p)"
    proof(case_tac "x mem xvec")
      assume "x mem xvec"
      with L yvecFreshp xvecFreshyvec yvecDist xFreshyvec
      have"x \<sharp> [xvec yvec] \<bullet>\<^sub>v p"
        by(rule_tac freshChainPerm) (auto simp add: fresh_list_cons)
      moreover from yFreshxvec yFreshyvec yFreshp L
      have "y \<sharp> [xvec yvec] \<bullet>\<^sub>v p" by simp
      ultimately show ?thesis using IH
        by(subst consPerm) (simp add: perm_fresh_fresh)
    next
      assume "\<not>(x mem xvec)"
      hence xFreshxvec: "x \<sharp> xvec" by simp
      from IH have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v p)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with xFreshxvec yFreshxvec show ?thesis by simp
    qed
  qed
qed

lemma permSym:
  fixes x    :: name
  and   y    :: name
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   p    :: "'a::pt_name"
  
  assumes "x \<sharp> xvec"
  and     "x \<sharp> yvec"
  and     "y \<sharp> xvec"
  and     "y \<sharp> yvec"
  and     "length xvec = length yvec"

  shows "([(x, y)] \<bullet> [xvec yvec] \<bullet>\<^sub>v p) = [xvec yvec] \<bullet>\<^sub>v [(x, y)] \<bullet> p"
using assms
apply(induct rule: composePerm.induct, auto)
by(subst pt_perm_compose[OF pt_name_inst, OF at_name_inst]) simp

lemma distinctPermClosed[simp]:
  fixes p :: "name prm"
  and   q :: "name prm"

  assumes "distinctPerm p"

  shows "distinctPerm(q \<bullet> p)"
using assms
by(induct p) (auto simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst] dest: pt_bij4[OF pt_name_inst, OF at_name_inst])

lemma freshStarSimps:
  fixes x  :: name
  and   Xs :: "name set"
  and   Ys :: "name set"
  and   C  :: "'a::fs_name"
  and   p  :: "name prm"
  
  assumes "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* x"
  and     "Ys \<sharp>* x"

  shows "x \<sharp> (p \<bullet> C) = x \<sharp> C"
using assms
by(subst  pt_fresh_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ C p]) simp

lemma freshStarChainSimps:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   Ys   :: "name set"
  and   C    :: "'a::fs_name"
  and   p    :: "name prm"

  assumes "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* xvec"
  and     "Ys \<sharp>* xvec"

  shows   "xvec \<sharp>* (p \<bullet> C) = xvec \<sharp>* C"
using assms
by(induct xvec) (auto simp add: freshStarSimps)

lemma permStarFresh:
  fixes xvec :: "name list"
  and   p    :: "name prm"
  and   T    :: "'a::pt_name"

  assumes "xvec \<sharp>* p"

  shows "xvec \<sharp>* (p \<bullet> T) = xvec \<sharp>* T"
using assms
by(induct p) (auto simp add: chainFreshFresh)

lemma swapStarFresh:
  fixes x :: name
  and   p :: "name prm"
  and   T :: "'a::pt_name"

  assumes "x \<sharp> p"

  shows "x \<sharp> (p \<bullet> T) = x \<sharp> T"
proof -
  from assms have "[x] \<sharp>* (p \<bullet> T) = [x] \<sharp>* T"
    by(rule_tac permStarFresh) auto
  thus ?thesis by simp
qed

lemmas freshChainSimps = freshStarSimps freshStarChainSimps permStarFresh swapStarFresh chainFreshFresh freshPerm subsetFresh

lemma freshAlphaPerm:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   Ys   :: "name set"
  and   p    :: "name prm"

  assumes S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* xvec"
  and     "Ys \<sharp>* xvec"

  shows "xvec \<sharp>* p"
using assms
apply(induct p)
by auto (simp add: fresh_star_def fresh_def name_list_supp supp_list_nil)+

lemma freshAlphaSwap:
  fixes x  :: name
  and   Xs :: "name set"
  and   Ys :: "name set"
  and   p  :: "name prm"

  assumes S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* x"
  and     "Ys \<sharp>* x"

  shows "x \<sharp> p"
proof -
  from assms have "[x] \<sharp>* p" 
    apply(rule_tac freshAlphaPerm)
    apply assumption
    by auto
  thus ?thesis by simp
qed

lemma setToListFresh[simp]:
  fixes xvec :: "name list"
  and   C    :: "'a::fs_name"
  and   yvec :: "name list"
  and   Xs   :: "name set"
  and   x    :: name

  shows "xvec \<sharp>* (set yvec) = xvec \<sharp>* yvec"
  and   "Xs \<sharp>* (set yvec) = Xs \<sharp>* yvec"
  and   "x \<sharp> (set yvec) = x \<sharp> yvec"
  and   "set xvec \<sharp>* Xs = xvec \<sharp>* Xs"
by(auto simp add: fresh_star_def name_list_supp fresh_def fs_name1 at_fin_set_supp[OF at_name_inst])

end
