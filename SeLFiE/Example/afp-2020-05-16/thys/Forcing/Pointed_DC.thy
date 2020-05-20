section\<open>A pointed version of DC\<close>
theory Pointed_DC imports ZF.AC

begin
txt\<open>This proof of DC is from Moschovakis "Notes on Set Theory"\<close>

consts dc_witness :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
primrec
  wit0   : "dc_witness(0,A,a,s,R) = a"
  witrec :"dc_witness(succ(n),A,a,s,R) = s`{x\<in>A. \<langle>dc_witness(n,A,a,s,R),x\<rangle>\<in>R }"

lemma witness_into_A [TC]:
  assumes "a\<in>A"
    "(\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X)"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0" "n\<in>nat"
  shows "dc_witness(n, A, a, s, R)\<in>A"
  using \<open>n\<in>nat\<close>
proof(induct n)
  case 0
  then show ?case using \<open>a\<in>A\<close> by simp
next
  case (succ x)
  then
  show ?case using assms by auto
qed

lemma witness_related :
  assumes "a\<in>A"
    "(\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X)"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0" "n\<in>nat"
  shows "\<langle>dc_witness(n, A, a, s, R),dc_witness(succ(n), A, a, s, R)\<rangle>\<in>R"
proof -
  from assms
  have "dc_witness(n, A, a, s, R)\<in>A" (is "?x \<in> A")
    using witness_into_A[of _ _ s R n] by simp
  with assms
  show ?thesis by auto
qed

lemma witness_funtype:
  assumes "a\<in>A"
    "(\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X)"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0"
  shows "(\<lambda>n\<in>nat. dc_witness(n, A, a, s, R)) \<in> nat \<rightarrow> A" (is "?f \<in> _ \<rightarrow> _")
proof -
  have "?f \<in> nat \<rightarrow> {dc_witness(n, A, a, s, R). n\<in>nat}" (is "_ \<in> _ \<rightarrow> ?B")
    using lam_funtype assms by simp
  then
  have "?B \<subseteq> A"
    using witness_into_A assms by auto
  with \<open>?f \<in> _\<close>
  show ?thesis
    using fun_weaken_type
    by simp
qed

lemma witness_to_fun:   assumes "a\<in>A"
  "(\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X)"
  "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0"
shows "\<exists>f \<in> nat\<rightarrow>A. \<forall>n\<in>nat. f`n =dc_witness(n,A,a,s,R)"
  using assms bexI[of _ "\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)"] witness_funtype
  by simp

theorem pointed_DC  :
  assumes "(\<forall>x\<in>A. \<exists>y\<in>A. \<langle>x,y\<rangle>\<in> R)"
  shows "\<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>R))"
proof -
  have 0:"\<forall>y\<in>A. {x \<in> A . \<langle>y, x\<rangle> \<in> R} \<noteq> 0"
    using assms by auto
  from AC_func_Pow[of A]
  obtain g
    where 1: "g \<in> Pow(A) - {0} \<rightarrow> A"
      "\<forall>X. X \<noteq> 0 \<and> X \<subseteq> A \<longrightarrow> g ` X \<in> X"
    by auto
  let ?f ="\<lambda>a.\<lambda>n\<in>nat. dc_witness(n,A,a,g,R)"
  {
    fix a
    assume "a\<in>A"
    from \<open>a\<in>A\<close>
    have f0: "?f(a)`0 = a" by simp
    with \<open>a\<in>A\<close>
    have "\<langle>?f(a) ` n, ?f(a) ` succ(n)\<rangle> \<in> R" if "n\<in>nat" for n
      using witness_related[OF \<open>a\<in>A\<close> 1(2) 0] beta that by simp
    then
    have "\<exists>f\<in>nat \<rightarrow> A. f ` 0 = a \<and> (\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> R)" (is "\<exists>x\<in>_ .?P(x)")
      using f0 witness_funtype 0 1 \<open>a\<in>_\<close> by blast
  }
  then show ?thesis by auto
qed

lemma aux_DC_on_AxNat2 : "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R \<Longrightarrow>
                  \<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> {\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  by (rule ballI, erule_tac x="x" in ballE, simp_all)

lemma infer_snd : "c\<in> A\<times>B \<Longrightarrow> snd(c) = k \<Longrightarrow> c=\<langle>fst(c),k\<rangle>"
  by auto

corollary DC_on_A_x_nat :
  assumes "(\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R)" "a\<in>A"
  shows "\<exists>f \<in> nat\<rightarrow>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>\<langle>f`n,n\<rangle>,\<langle>f`succ(n),succ(n)\<rangle>\<rangle>\<in>R)" (is "\<exists>x\<in>_.?P(x)")
proof -
  let ?R'="{\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  from assms(1)
  have "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> ?R'"
    using aux_DC_on_AxNat2 by simp
  with \<open>a\<in>_\<close>
  obtain f where
    F:"f\<in>nat\<rightarrow>A\<times>nat" "f ` 0 = \<langle>a,0\<rangle>"  "\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> ?R'"
    using pointed_DC[of "A\<times>nat" ?R'] by blast
  let ?f="\<lambda>x\<in>nat. fst(f`x)"
  from F
  have "?f\<in>nat\<rightarrow>A" "?f ` 0 = a" by auto
  have 1:"n\<in> nat \<Longrightarrow> f`n= \<langle>?f`n, n\<rangle>" for n
  proof(induct n set:nat)
    case 0
    then show ?case using F by simp
  next
    case (succ x)
    then
    have "\<langle>f`x, f`succ(x)\<rangle> \<in> ?R'" "f`x \<in> A\<times>nat" "f`succ(x)\<in>A\<times>nat"
      using F by simp_all
    then
    have "snd(f`succ(x)) = succ(snd(f`x))" by simp
    with succ \<open>f`x\<in>_\<close>
    show ?case using infer_snd[OF \<open>f`succ(_)\<in>_\<close>] by auto
  qed
  have "\<langle>\<langle>?f`n,n\<rangle>,\<langle>?f`succ(n),succ(n)\<rangle>\<rangle> \<in> R" if "n\<in>nat" for n
    using that 1[of "succ(n)"] 1[OF \<open>n\<in>_\<close>] F(3) by simp
  with \<open>f`0=\<langle>a,0\<rangle>\<close>
  show ?thesis using rev_bexI[OF \<open>?f\<in>_\<close>] by simp
qed

lemma aux_sequence_DC :
  assumes "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n"
    "R={\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle> \<in> (A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  shows "\<forall> x\<in>A\<times>nat . \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R"
  using assms Pair_fst_snd_eq by auto

lemma aux_sequence_DC2 : "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n \<Longrightarrow>
        \<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> {\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle>\<in>(A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  by auto

lemma sequence_DC:
  assumes "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n"
  shows "\<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>S`succ(n)))"
  by (rule ballI,insert assms,drule aux_sequence_DC2, drule DC_on_A_x_nat, auto)

end