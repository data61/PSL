(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Subst_Term
  imports Chain
begin

locale substType =
  fixes subst :: "'a::fs_name \<Rightarrow> name list \<Rightarrow> 'b::fs_name list \<Rightarrow> 'a" ("_[_::=_]" [80, 80 ,80] 130)

  assumes eq[eqvt]: "\<And>p::name prm. (p \<bullet> (M[xvec::=Tvec])) = ((p \<bullet> M)[(p \<bullet> xvec)::=(p \<bullet> Tvec)])"
(*  and subst1:       "\<And>xvec Tvec T x. \<lbrakk>length xvec = length Tvec; distinct xvec; (x::name) \<sharp> T[xvec::=Tvec]; x \<sharp> xvec\<rbrakk> \<Longrightarrow> x \<sharp> T"
  and subst2:       "\<And>xvec Tvec T x. \<lbrakk>length xvec = length Tvec; distinct xvec; (x::name) \<sharp> T; x \<sharp> Tvec\<rbrakk> \<Longrightarrow> x \<sharp> T[xvec::=Tvec]"*)
  and subst3:       "\<And>xvec Tvec T x. \<lbrakk>length xvec = length Tvec; distinct xvec; set(xvec) \<subseteq> supp(T); (x::name) \<sharp> T[xvec::=Tvec]\<rbrakk> \<Longrightarrow> x \<sharp> Tvec"
(*  and subst4:       "\<And>xvec Tvec T. \<lbrakk>length xvec = length Tvec; distinct xvec; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> T[xvec::=Tvec] = T"
  and subst5:       "\<And>xvec Tvec yvec Tvec' T. \<lbrakk>length xvec = length Tvec; distinct xvec; length yvec = length Tvec'; distinct yvec; yvec \<sharp>* xvec; yvec \<sharp>* Tvec\<rbrakk> \<Longrightarrow>
                                                T[(xvec@yvec)::=(Tvec@Tvec')] = (T[xvec::=Tvec])[yvec::=Tvec']"*)
  and renaming:     "\<And>xvec Tvec p T. \<lbrakk>length xvec = length Tvec; (set p) \<subseteq> set xvec \<times> set (p \<bullet> xvec);
                                      distinctPerm p; (p \<bullet> xvec) \<sharp>* T\<rbrakk> \<Longrightarrow>
                                      T[xvec::=Tvec] = (p \<bullet> T)[(p \<bullet> xvec)::=Tvec]"
begin

lemma suppSubst:
  fixes M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  shows "(supp(M[xvec::=Tvec])::name set) \<subseteq> ((supp M) \<union> (supp xvec) \<union> (supp Tvec))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> M)[([(x, y)] \<bullet> xvec)::=([(x, y)] \<bullet> Tvec)] \<noteq> M[xvec::=Tvec]"
  let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> (M::'a)"
  let ?R = "\<lambda>y xvec. ([(x, y)] \<bullet> xvec) \<noteq> (xvec::name list)"
  let ?S = "\<lambda>y Tvec. ([(x, y)] \<bullet> Tvec) \<noteq> (Tvec::'b list)"
  assume A: "finite {y. ?Q y M}" and B: "finite {y. ?R y xvec}" and C: "finite {y. ?S y Tvec}" and D: "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y M}  - {y. ?R y xvec}  - {y. ?S y Tvec})" 
    by(auto intro: Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?R y xvec) \<and> \<not> (?S y Tvec)})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?R y xvec) \<and> \<not> (?S y Tvec)} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma subst2[intro]:
  fixes x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  assumes "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> Tvec"

  shows "x \<sharp> M[xvec::=Tvec]"
using assms suppSubst
by(auto simp add: fresh_def)

lemma subst2Chain[intro]:
  fixes yvec :: "name list"
  and   M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  assumes "yvec \<sharp>* M"
  and     "yvec \<sharp>* xvec"
  and     "yvec \<sharp>* Tvec"

  shows "yvec \<sharp>* M[xvec::=Tvec]"
using assms
by(induct yvec) auto

lemma fs[simp]: "finite ((supp subst)::name set)"
by(simp add: supp_def perm_fun_def eqvts)
(*
lemma subst1Chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   Xs   :: "name set"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "Xs \<sharp>* T[xvec::=Tvec]"
  and     "Xs \<sharp>* xvec"

  shows "Xs \<sharp>* T"
using assms
by(auto intro: subst1 simp add: fresh_star_def)
*)
lemma subst3Chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   Xs   :: "name set"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "set xvec \<subseteq> supp T"
  and     "Xs \<sharp>* T[xvec::=Tvec]"

  shows "Xs \<sharp>* Tvec"
using assms
by(auto intro: subst3 simp add: fresh_star_def)

lemma subst4Chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "xvec \<sharp>* Tvec"

  shows "xvec \<sharp>* T[xvec::=Tvec]"
proof -
  obtain p where "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* T" and "(p \<bullet> xvec) \<sharp>* xvec"
             and S: "(set p) \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
             and "distinctPerm p"
    by(rule_tac xvec=xvec and c="(T, xvec)" in name_list_avoiding) auto 

  from \<open>length xvec = length Tvec\<close> have "length(p \<bullet> xvec) = length Tvec" by simp
  moreover from \<open>(p \<bullet> xvec) \<sharp>* T\<close> have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> T)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>distinctPerm p\<close> have "xvec \<sharp>* (p \<bullet> T)" by simp
  ultimately have "(set xvec) \<sharp>* (p \<bullet> T)[(p \<bullet> xvec)::=Tvec]" using \<open>xvec \<sharp>* Tvec\<close> \<open>(p \<bullet> xvec) \<sharp>* xvec\<close>
    by auto

  thus ?thesis using \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> S \<open>(p \<bullet> xvec) \<sharp>* T\<close> \<open>distinctPerm p\<close>
    by(simp add: renaming)
qed

definition seqSubst :: "'a \<Rightarrow> (name list \<times> 'b list) list \<Rightarrow> 'a" ("_[<_>]" [80, 80] 130)
  where "M[<\<sigma>>] \<equiv> foldl (\<lambda>N. \<lambda>(xvec, Tvec). N[xvec::=Tvec]) M \<sigma>"

lemma seqSubstNil[simp]:
  "seqSubst M [] = M"
by(simp add: seqSubst_def)

lemma seqSubstCons[simp]:
  shows "seqSubst M ((xvec, Tvec)#\<sigma>) = seqSubst(M[xvec::=Tvec]) \<sigma>"
  by(simp add: seqSubst_def)

lemma seqSubstTermAppend[simp]:
  shows "seqSubst M (\<sigma>@\<sigma>') = seqSubst (seqSubst M \<sigma>) \<sigma>'"
by(induct \<sigma>) (auto simp add: seqSubst_def)

definition wellFormedSubst :: "(('d::fs_name) list \<times> ('e::fs_name) list) list \<Rightarrow> bool" where "wellFormedSubst \<sigma> = ((filter (\<lambda>(xvec, Tvec). \<not>(length xvec = length Tvec \<and> distinct xvec)) \<sigma>) = [])"

lemma wellFormedSubstEqvt[eqvt]:
  fixes \<sigma> :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   p :: "name prm"

  shows "p \<bullet> (wellFormedSubst \<sigma>) = wellFormedSubst(p \<bullet> \<sigma>)"
by(induct \<sigma> arbitrary: p) (auto simp add: eqvts wellFormedSubst_def)

lemma wellFormedSimp[simp]:
  fixes \<sigma> :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   p :: "name prm"
  
  shows "wellFormedSubst(p \<bullet> \<sigma>) = wellFormedSubst \<sigma>"
by(induct \<sigma>) (auto simp add: eqvts wellFormedSubst_def)

lemma wellFormedNil[simp]:
  "wellFormedSubst []"
by(simp add: wellFormedSubst_def)

lemma wellFormedCons[simp]:
  shows "wellFormedSubst((xvec, Tvec)#\<sigma>) = (length xvec = length Tvec \<and> distinct xvec \<and> wellFormedSubst \<sigma>)"
by(simp add: wellFormedSubst_def) auto

lemma wellFormedAppend[simp]:
  fixes \<sigma>  :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   \<sigma>' :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"

  shows "wellFormedSubst(\<sigma>@\<sigma>') = (wellFormedSubst \<sigma> \<and> wellFormedSubst \<sigma>')"
by(simp add: wellFormedSubst_def)

lemma seqSubst2[intro]:
  fixes \<sigma> :: "(name list \<times> 'b list) list"
  and   T :: 'a
  and   x :: name

  assumes "x \<sharp> \<sigma>"
  and     "x \<sharp> T"

  shows "x \<sharp> T[<\<sigma>>]"
using assms
by(induct \<sigma> arbitrary: T) (clarsimp |  blast)+

lemma seqSubst2Chain[intro]:
  fixes \<sigma>    :: "(name list \<times> 'b list) list"
  and   T    :: 'a
  and   xvec :: "name list"

  assumes "xvec \<sharp>* \<sigma>"
  and     "xvec \<sharp>* T"

  shows "xvec \<sharp>* T[<\<sigma>>]"
using assms
by(induct xvec) auto

end

end
