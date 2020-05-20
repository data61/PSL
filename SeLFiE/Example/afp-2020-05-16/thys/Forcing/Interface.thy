section\<open>Interface between set models and Constructibility\<close>

text\<open>This theory provides an interface between Paulson's
relativization results and set models of ZFC. In particular,
it is used to prove that the locale \<^term>\<open>forcing_data\<close> is
a sublocale of all relevant locales in ZF-Constructibility
(\<^term>\<open>M_trivial\<close>, \<^term>\<open>M_basic\<close>, \<^term>\<open>M_eclose\<close>, etc).\<close>

theory Interface
  imports
    Nat_Miscellanea
    Relative_Univ
    Synthetic_Definition
begin

syntax
  "_sats"  :: "[i, i, i] \<Rightarrow> o"  ("(_, _ \<Turnstile> _)" [36,36,36] 60)
translations
  "(M,env \<Turnstile> \<phi>)" \<rightleftharpoons> "CONST sats(M,\<phi>,env)"

abbreviation
  dec10  :: i   ("10") where "10 \<equiv> succ(9)"

abbreviation
  dec11  :: i   ("11") where "11 \<equiv> succ(10)"

abbreviation
  dec12  :: i   ("12") where "12 \<equiv> succ(11)"

abbreviation
  dec13  :: i   ("13") where "13 \<equiv> succ(12)"

abbreviation
  dec14  :: i   ("14") where "14 \<equiv> succ(13)"


definition
  infinity_ax :: "(i \<Rightarrow> o) \<Rightarrow> o" where
  "infinity_ax(M) \<equiv>
      (\<exists>I[M]. (\<exists>z[M]. empty(M,z) \<and> z\<in>I) \<and> (\<forall>y[M]. y\<in>I \<longrightarrow> (\<exists>sy[M]. successor(M,y,sy) \<and> sy\<in>I)))"

definition
  choice_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
  "choice_ax(M) \<equiv> \<forall>x[M]. \<exists>a[M]. \<exists>f[M]. ordinal(M,a) \<and> surjection(M,a,x,f)"

context M_basic begin

lemma choice_ax_abs :
  "choice_ax(M) \<longleftrightarrow> (\<forall>x[M]. \<exists>a[M]. \<exists>f[M]. Ord(a) \<and> f \<in> surj(a,x))"
  unfolding choice_ax_def
  by (simp)

end (* M_basic *)

definition
  wellfounded_trancl :: "[i=>o,i,i,i] => o" where
  "wellfounded_trancl(M,Z,r,p) \<equiv>
      \<exists>w[M]. \<exists>wx[M]. \<exists>rp[M].
               w \<in> Z & pair(M,w,p,wx) & tran_closure(M,r,rp) & wx \<in> rp"

lemma empty_intf :
  "infinity_ax(M) \<Longrightarrow>
  (\<exists>z[M]. empty(M,z))"
  by (auto simp add: empty_def infinity_ax_def)

lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

locale M_ZF_trans =
  fixes M
  assumes
    upair_ax:         "upair_ax(##M)"
    and Union_ax:         "Union_ax(##M)"
    and power_ax:         "power_ax(##M)"
    and extensionality:   "extensionality(##M)"
    and foundation_ax:    "foundation_ax(##M)"
    and infinity_ax:      "infinity_ax(##M)"
    and separation_ax:    "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))"
    and replacement_ax:   "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 2 #+ length(env) \<Longrightarrow>
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env))"
    and trans_M:          "Transset(M)"
begin


lemma TranssetI :
  "(\<And>y x. y\<in>x \<Longrightarrow> x\<in>M \<Longrightarrow> y\<in>M) \<Longrightarrow> Transset(M)"
  by (auto simp add: Transset_def)

lemma zero_in_M:  "0 \<in> M"
proof -
  from infinity_ax have
    "(\<exists>z[##M]. empty(##M,z))"
    by (rule empty_intf)
  then obtain z where
    zm: "empty(##M,z)"  "z\<in>M"
    by auto
  with trans_M have "z=0"
    by (simp  add: empty_def, blast intro: Transset_intf )
  with zm show ?thesis
    by simp
qed

subsection\<open>Interface with \<^term>\<open>M_trivial\<close>\<close>
lemma mtrans :
  "M_trans(##M)"
  using Transset_intf[OF trans_M] zero_in_M exI[of "\<lambda>x. x\<in>M"]
  by unfold_locales auto


lemma mtriv :
  "M_trivial(##M)"
  using trans_M M_trivial.intro mtrans M_trivial_axioms.intro upair_ax Union_ax
  by simp

end

sublocale M_ZF_trans \<subseteq> M_trivial "##M"
  by (rule mtriv)

context M_ZF_trans
begin

subsection\<open>Interface with \<^term>\<open>M_basic\<close>\<close>

(* Inter_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>x. \<forall> y[M]. y\<in>A \<Longrightarrow> x\<in>y)" *)
schematic_goal inter_fm_auto:
  assumes
    "nth(i,env) = x" "nth(j,env) = B"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "(\<forall>y\<in>A . y\<in>B \<longrightarrow> x\<in>y) \<longleftrightarrow> sats(A,?ifm(i,j),env)"
  by (insert assms ; (rule sep_rules | simp)+)

lemma inter_sep_intf :
  assumes
    "A\<in>M"
  shows
    "separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y)"
proof -
  obtain ifm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow> (\<forall> y\<in>M. y\<in>(nth(1,env)) \<longrightarrow> nth(0,env)\<in>y)
    \<longleftrightarrow> sats(M,ifm(0,1),env)"
    and
    "ifm(0,1) \<in> formula"
    and
    "arity(ifm(0,1)) = 2"
    using \<open>A\<in>M\<close> inter_fm_auto
    by (simp del:FOL_sats_iff add: nat_simp_union)
  then
  have "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M,ifm(0,1) , [x, a]))"
    using separation_ax by simp
  moreover
  have "(\<forall>y\<in>M . y\<in>a \<longrightarrow> x\<in>y) \<longleftrightarrow> sats(M,ifm(0,1),[x,a])"
    if "a\<in>M" "x\<in>M" for a x
    using that fmsats[of "[x,a]"] by simp
  ultimately
  have "\<forall>a\<in>M. separation(##M, \<lambda>x . \<forall>y\<in>M . y\<in>a \<longrightarrow> x\<in>y)"
    unfolding separation_def by simp
  with \<open>A\<in>M\<close> show ?thesis by simp
qed


(* Diff_separation: "M(B) \<Longrightarrow> separation(M, \<lambda>x. x \<notin> B)" *)
schematic_goal diff_fm_auto:
  assumes
    "nth(i,env) = x" "nth(j,env) = B"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "x\<notin>B \<longleftrightarrow> sats(A,?dfm(i,j),env)"
  by (insert assms ; (rule sep_rules | simp)+)

lemma diff_sep_intf :
  assumes
    "B\<in>M"
  shows
    "separation(##M,\<lambda>x . x\<notin>B)"
proof -
  obtain dfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow> nth(0,env)\<notin>nth(1,env)
    \<longleftrightarrow> sats(M,dfm(0,1),env)"
    and
    "dfm(0,1) \<in> formula"
    and
    "arity(dfm(0,1)) = 2"
    using \<open>B\<in>M\<close> diff_fm_auto
    by (simp del:FOL_sats_iff add: nat_simp_union)
  then
  have "\<forall>b\<in>M. separation(##M, \<lambda>x. sats(M,dfm(0,1) , [x, b]))"
    using separation_ax by simp
  moreover
  have "x\<notin>b \<longleftrightarrow> sats(M,dfm(0,1),[x,b])"
    if "b\<in>M" "x\<in>M" for b x
    using that fmsats[of "[x,b]"] by simp
  ultimately
  have "\<forall>b\<in>M. separation(##M, \<lambda>x . x\<notin>b)"
    unfolding separation_def by simp
  with \<open>B\<in>M\<close> show ?thesis by simp
qed

schematic_goal cprod_fm_auto:
  assumes
    "nth(i,env) = z" "nth(j,env) = B" "nth(h,env) = C"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>x\<in>A. x\<in>B \<and> (\<exists>y\<in>A. y\<in>C \<and> pair(##A,x,y,z))) \<longleftrightarrow> sats(A,?cpfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma cartprod_sep_intf :
  assumes
    "A\<in>M"
    and
    "B\<in>M"
  shows
    "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z)))"
proof -
  obtain cpfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>x\<in>M. x\<in>nth(1,env) \<and> (\<exists>y\<in>M. y\<in>nth(2,env) \<and> pair(##M,x,y,nth(0,env))))
    \<longleftrightarrow> sats(M,cpfm(0,1,2),env)"
    and
    "cpfm(0,1,2) \<in> formula"
    and
    "arity(cpfm(0,1,2)) = 3"
    using cprod_fm_auto by (simp del:FOL_sats_iff add: fm_defs nat_simp_union)
  then
  have "\<forall>a\<in>M. \<forall>b\<in>M. separation(##M, \<lambda>z. sats(M,cpfm(0,1,2) , [z, a, b]))"
    using separation_ax by simp
  moreover
  have "(\<exists>x\<in>M. x\<in>a \<and> (\<exists>y\<in>M. y\<in>b \<and> pair(##M,x,y,z))) \<longleftrightarrow> sats(M,cpfm(0,1,2),[z,a,b])"
    if "a\<in>M" "b\<in>M" "z\<in>M" for a b z
    using that fmsats[of "[z,a,b]"] by simp
  ultimately
  have "\<forall>a\<in>M. \<forall>b\<in>M. separation(##M, \<lambda>z . (\<exists>x\<in>M. x\<in>a \<and> (\<exists>y\<in>M. y\<in>b \<and> pair(##M,x,y,z))))"
    unfolding separation_def by simp
  with \<open>A\<in>M\<close> \<open>B\<in>M\<close> show ?thesis by simp
qed

schematic_goal im_fm_auto:
  assumes
    "nth(i,env) = y" "nth(j,env) = r" "nth(h,env) = B"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>p\<in>A. p\<in>r & (\<exists>x\<in>A. x\<in>B & pair(##A,x,y,p))) \<longleftrightarrow> sats(A,?imfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)

lemma image_sep_intf :
  assumes
    "A\<in>M"
    and
    "r\<in>M"
  shows
    "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p)))"
proof -
  obtain imfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>p\<in>M. p\<in>nth(1,env) & (\<exists>x\<in>M. x\<in>nth(2,env) & pair(##M,x,nth(0,env),p)))
    \<longleftrightarrow> sats(M,imfm(0,1,2),env)"
    and
    "imfm(0,1,2) \<in> formula"
    and
    "arity(imfm(0,1,2)) = 3"
    using im_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>r\<in>M. \<forall>a\<in>M. separation(##M, \<lambda>y. sats(M,imfm(0,1,2) , [y,r,a]))"
    using separation_ax by simp
  moreover
  have "(\<exists>p\<in>M. p\<in>k & (\<exists>x\<in>M. x\<in>a & pair(##M,x,y,p))) \<longleftrightarrow> sats(M,imfm(0,1,2),[y,k,a])"
    if "k\<in>M" "a\<in>M" "y\<in>M" for k a y
    using that fmsats[of "[y,k,a]"] by simp
  ultimately
  have "\<forall>k\<in>M. \<forall>a\<in>M. separation(##M, \<lambda>y . \<exists>p\<in>M. p\<in>k & (\<exists>x\<in>M. x\<in>a & pair(##M,x,y,p)))"
    unfolding separation_def by simp
  with \<open>r\<in>M\<close> \<open>A\<in>M\<close> show ?thesis by simp
qed

schematic_goal con_fm_auto:
  assumes
    "nth(i,env) = z" "nth(j,env) = R"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>p\<in>A. p\<in>R & (\<exists>x\<in>A.\<exists>y\<in>A. pair(##A,x,y,p) & pair(##A,y,x,z)))
  \<longleftrightarrow> sats(A,?cfm(i,j),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma converse_sep_intf :
  assumes
    "R\<in>M"
  shows
    "separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>R & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z)))"
proof -
  obtain cfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>p\<in>M. p\<in>nth(1,env) & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,nth(0,env))))
    \<longleftrightarrow> sats(M,cfm(0,1),env)"
    and
    "cfm(0,1) \<in> formula"
    and
    "arity(cfm(0,1)) = 2"
    using con_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>r\<in>M. separation(##M, \<lambda>z. sats(M,cfm(0,1) , [z,r]))"
    using separation_ax by simp
  moreover
  have "(\<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z))) \<longleftrightarrow>
          sats(M,cfm(0,1),[z,r])"
    if "z\<in>M" "r\<in>M" for z r
    using that fmsats[of "[z,r]"] by simp
  ultimately
  have "\<forall>r\<in>M. separation(##M, \<lambda>z . \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z)))"
    unfolding separation_def by simp
  with \<open>R\<in>M\<close> show ?thesis by simp
qed


schematic_goal rest_fm_auto:
  assumes
    "nth(i,env) = z" "nth(j,env) = C"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>x\<in>A. x\<in>C & (\<exists>y\<in>A. pair(##A,x,y,z)))
  \<longleftrightarrow> sats(A,?rfm(i,j),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma restrict_sep_intf :
  assumes
    "A\<in>M"
  shows
    "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z)))"
proof -
  obtain rfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>x\<in>M. x\<in>nth(1,env) & (\<exists>y\<in>M. pair(##M,x,y,nth(0,env))))
    \<longleftrightarrow> sats(M,rfm(0,1),env)"
    and
    "rfm(0,1) \<in> formula"
    and
    "arity(rfm(0,1)) = 2"
    using rest_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>a\<in>M. separation(##M, \<lambda>z. sats(M,rfm(0,1) , [z,a]))"
    using separation_ax by simp
  moreover
  have "(\<exists>x\<in>M. x\<in>a & (\<exists>y\<in>M. pair(##M,x,y,z))) \<longleftrightarrow>
          sats(M,rfm(0,1),[z,a])"
    if "z\<in>M" "a\<in>M" for z a
    using that fmsats[of "[z,a]"] by simp
  ultimately
  have "\<forall>a\<in>M. separation(##M, \<lambda>z . \<exists>x\<in>M. x\<in>a & (\<exists>y\<in>M. pair(##M,x,y,z)))"
    unfolding separation_def by simp
  with \<open>A\<in>M\<close> show ?thesis by simp
qed

schematic_goal comp_fm_auto:
  assumes
    "nth(i,env) = xz" "nth(j,env) = S" "nth(h,env) = R"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>x\<in>A. \<exists>y\<in>A. \<exists>z\<in>A. \<exists>xy\<in>A. \<exists>yz\<in>A.
              pair(##A,x,z,xz) & pair(##A,x,y,xy) & pair(##A,y,z,yz) & xy\<in>S & yz\<in>R)
  \<longleftrightarrow> sats(A,?cfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma comp_sep_intf :
  assumes
    "R\<in>M"
    and
    "S\<in>M"
  shows
    "separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>S & yz\<in>R)"
proof -
  obtain cfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M. pair(##M,x,z,nth(0,env)) &
            pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>nth(1,env) & yz\<in>nth(2,env))
    \<longleftrightarrow> sats(M,cfm(0,1,2),env)"
    and
    "cfm(0,1,2) \<in> formula"
    and
    "arity(cfm(0,1,2)) = 3"
    using comp_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>r\<in>M. \<forall>s\<in>M. separation(##M, \<lambda>y. sats(M,cfm(0,1,2) , [y,s,r]))"
    using separation_ax by simp
  moreover
  have "(\<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>s & yz\<in>r)
          \<longleftrightarrow> sats(M,cfm(0,1,2) , [xz,s,r])"
    if "xz\<in>M" "s\<in>M" "r\<in>M" for xz s r
    using that fmsats[of "[xz,s,r]"] by simp
  ultimately
  have "\<forall>s\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>xz . \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>s & yz\<in>r)"
    unfolding separation_def by simp
  with \<open>S\<in>M\<close> \<open>R\<in>M\<close> show ?thesis by simp
qed


schematic_goal pred_fm_auto:
  assumes
    "nth(i,env) = y" "nth(j,env) = R" "nth(h,env) = X"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>p\<in>A. p\<in>R & pair(##A,y,X,p)) \<longleftrightarrow> sats(A,?pfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma pred_sep_intf:
  assumes
    "R\<in>M"
    and
    "X\<in>M"
  shows
    "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>R & pair(##M,y,X,p))"
proof -
  obtain pfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>p\<in>M. p\<in>nth(1,env) & pair(##M,nth(0,env),nth(2,env),p)) \<longleftrightarrow> sats(M,pfm(0,1,2),env)"
    and
    "pfm(0,1,2) \<in> formula"
    and
    "arity(pfm(0,1,2)) = 3"
    using pred_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>x\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. sats(M,pfm(0,1,2) , [y,r,x]))"
    using separation_ax by simp
  moreover
  have "(\<exists>p\<in>M. p\<in>r & pair(##M,y,x,p))
          \<longleftrightarrow> sats(M,pfm(0,1,2) , [y,r,x])"
    if "y\<in>M" "r\<in>M" "x\<in>M" for y x r
    using that fmsats[of "[y,r,x]"] by simp
  ultimately
  have "\<forall>x\<in>M. \<forall>r\<in>M. separation(##M, \<lambda> y . \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p))"
    unfolding separation_def by simp
  with \<open>X\<in>M\<close> \<open>R\<in>M\<close> show ?thesis by simp
qed

(* Memrel_separation:
     "separation(M, \<lambda>z. \<exists>x[M]. \<exists>y[M]. pair(M,x,y,z) & x \<in> y)"
*)
schematic_goal mem_fm_auto:
  assumes
    "nth(i,env) = z" "i \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>x\<in>A. \<exists>y\<in>A. pair(##A,x,y,z) & x \<in> y) \<longleftrightarrow> sats(A,?mfm(i),env)"
  by (insert assms ; (rule sep_rules | simp)+)

lemma memrel_sep_intf:
  "separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
proof -
  obtain mfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,nth(0,env)) & x \<in> y) \<longleftrightarrow> sats(M,mfm(0),env)"
    and
    "mfm(0) \<in> formula"
    and
    "arity(mfm(0)) = 1"
    using mem_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "separation(##M, \<lambda>z. sats(M,mfm(0) , [z]))"
    using separation_ax by simp
  moreover
  have "(\<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y) \<longleftrightarrow> sats(M,mfm(0),[z])"
    if "z\<in>M" for z
    using that fmsats[of "[z]"] by simp
  ultimately
  have "separation(##M, \<lambda>z . \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
    unfolding separation_def by simp
  then show ?thesis by simp
qed

schematic_goal recfun_fm_auto:
  assumes
    "nth(i1,env) = x" "nth(i2,env) = r" "nth(i3,env) = f" "nth(i4,env) = g" "nth(i5,env) = a"
    "nth(i6,env) = b" "i1\<in>nat" "i2\<in>nat" "i3\<in>nat" "i4\<in>nat" "i5\<in>nat" "i6\<in>nat" "env \<in> list(A)"
  shows
    "(\<exists>xa\<in>A. \<exists>xb\<in>A. pair(##A,x,a,xa) & xa \<in> r & pair(##A,x,b,xb) & xb \<in> r &
                  (\<exists>fx\<in>A. \<exists>gx\<in>A. fun_apply(##A,f,x,fx) & fun_apply(##A,g,x,gx) & fx \<noteq> gx))
    \<longleftrightarrow> sats(A,?rffm(i1,i2,i3,i4,i5,i6),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma is_recfun_sep_intf :
  assumes
    "r\<in>M" "f\<in>M" "g\<in>M" "a\<in>M" "b\<in>M"
  shows
    "separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx))"
proof -
  obtain rffm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (\<exists>xa\<in>M. \<exists>xb\<in>M. pair(##M,nth(0,env),nth(4,env),xa) & xa \<in> nth(1,env) &
    pair(##M,nth(0,env),nth(5,env),xb) & xb \<in> nth(1,env) & (\<exists>fx\<in>M. \<exists>gx\<in>M.
    fun_apply(##M,nth(2,env),nth(0,env),fx) & fun_apply(##M,nth(3,env),nth(0,env),gx) & fx \<noteq> gx))
    \<longleftrightarrow> sats(M,rffm(0,1,2,3,4,5),env)"
    and
    "rffm(0,1,2,3,4,5) \<in> formula"
    and
    "arity(rffm(0,1,2,3,4,5)) = 6"
    using recfun_fm_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>a1\<in>M. \<forall>a2\<in>M. \<forall>a3\<in>M. \<forall>a4\<in>M. \<forall>a5\<in>M.
        separation(##M, \<lambda>x. sats(M,rffm(0,1,2,3,4,5) , [x,a1,a2,a3,a4,a5]))"
    using separation_ax by simp
  moreover
  have "(\<exists>xa\<in>M. \<exists>xb\<in>M. pair(##M,x,a4,xa) & xa \<in> a1 & pair(##M,x,a5,xb) & xb \<in> a1 &
          (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,a2,x,fx) & fun_apply(##M,a3,x,gx) & fx \<noteq> gx))
          \<longleftrightarrow> sats(M,rffm(0,1,2,3,4,5) , [x,a1,a2,a3,a4,a5])"
    if "x\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "a5\<in>M"  for x a1 a2 a3 a4 a5
    using that fmsats[of "[x,a1,a2,a3,a4,a5]"] by simp
  ultimately
  have "\<forall>a1\<in>M. \<forall>a2\<in>M. \<forall>a3\<in>M. \<forall>a4\<in>M. \<forall>a5\<in>M. separation(##M, \<lambda> x .
          \<exists>xa\<in>M. \<exists>xb\<in>M. pair(##M,x,a4,xa) & xa \<in> a1 & pair(##M,x,a5,xb) & xb \<in> a1 &
          (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,a2,x,fx) & fun_apply(##M,a3,x,gx) & fx \<noteq> gx))"
    unfolding separation_def by simp
  with \<open>r\<in>M\<close> \<open>f\<in>M\<close> \<open>g\<in>M\<close> \<open>a\<in>M\<close> \<open>b\<in>M\<close> show ?thesis by simp
qed


(* Instance of Replacement for M_basic *)

schematic_goal funsp_fm_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = z" "nth(h,env) = n"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>f\<in>A. \<exists>b\<in>A. \<exists>nb\<in>A. \<exists>cnbf\<in>A. pair(##A,f,b,p) & pair(##A,n,b,nb) & is_cons(##A,nb,f,cnbf) &
    upair(##A,cnbf,cnbf,z)) \<longleftrightarrow> sats(A,?fsfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)


lemma funspace_succ_rep_intf :
  assumes
    "n\<in>M"
  shows
    "strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z))"
proof -
  obtain fsfm where
    fmsats:"env\<in>list(M) \<Longrightarrow>
    (\<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M. pair(##M,f,b,nth(0,env)) & pair(##M,nth(2,env),b,nb)
      & is_cons(##M,nb,f,cnbf) & upair(##M,cnbf,cnbf,nth(1,env)))
    \<longleftrightarrow> sats(M,fsfm(0,1,2),env)"
    and "fsfm(0,1,2) \<in> formula" and "arity(fsfm(0,1,2)) = 3" for env
    using funsp_fm_auto[of concl:M] by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>n0\<in>M. strong_replacement(##M, \<lambda>p z. sats(M,fsfm(0,1,2) , [p,z,n0]))"
    using replacement_ax by simp
  moreover
  have "(\<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M. pair(##M,f,b,p) & pair(##M,n0,b,nb) &
          is_cons(##M,nb,f,cnbf) & upair(##M,cnbf,cnbf,z))
          \<longleftrightarrow> sats(M,fsfm(0,1,2) , [p,z,n0])"
    if "p\<in>M" "z\<in>M" "n0\<in>M" for p z n0
    using that fmsats[of "[p,z,n0]"] by simp
  ultimately
  have "\<forall>n0\<in>M. strong_replacement(##M, \<lambda> p z.
          \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M. pair(##M,f,b,p) & pair(##M,n0,b,nb) &
          is_cons(##M,nb,f,cnbf) & upair(##M,cnbf,cnbf,z))"
    unfolding strong_replacement_def univalent_def by simp
  with \<open>n\<in>M\<close> show ?thesis by simp
qed


(* Interface with M_basic *)

lemmas M_basic_sep_instances =
  inter_sep_intf diff_sep_intf cartprod_sep_intf
  image_sep_intf converse_sep_intf restrict_sep_intf
  pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf

lemma mbasic : "M_basic(##M)"
  using trans_M zero_in_M power_ax M_basic_sep_instances funspace_succ_rep_intf mtriv
  by unfold_locales auto

end

sublocale M_ZF_trans \<subseteq> M_basic "##M"
  by (rule mbasic)

subsection\<open>Interface with \<^term>\<open>M_trancl\<close>\<close>

(* rtran_closure_mem *)
schematic_goal rtran_closure_mem_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = r"  "nth(k,env) = B"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" "env \<in> list(A)"
  shows
    "rtran_closure_mem(##A,B,r,p) \<longleftrightarrow> sats(A,?rcfm(i,j,k),env)"
  unfolding rtran_closure_mem_def
  by (insert assms ; (rule sep_rules | simp)+)


lemma (in M_ZF_trans) rtrancl_separation_intf:
  assumes
    "r\<in>M"
    and
    "A\<in>M"
  shows
    "separation (##M, rtran_closure_mem(##M,A,r))"
proof -
  obtain rcfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (rtran_closure_mem(##M,nth(2,env),nth(1,env),nth(0,env))) \<longleftrightarrow> sats(M,rcfm(0,1,2),env)"
    and
    "rcfm(0,1,2) \<in> formula"
    and
    "arity(rcfm(0,1,2)) = 3"
    using rtran_closure_mem_auto by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>x\<in>M. \<forall>a\<in>M. separation(##M, \<lambda>y. sats(M,rcfm(0,1,2) , [y,x,a]))"
    using separation_ax by simp
  moreover
  have "(rtran_closure_mem(##M,a,x,y))
          \<longleftrightarrow> sats(M,rcfm(0,1,2) , [y,x,a])"
    if "y\<in>M" "x\<in>M" "a\<in>M" for y x a
    using that fmsats[of "[y,x,a]"] by simp
  ultimately
  have "\<forall>x\<in>M. \<forall>a\<in>M. separation(##M, rtran_closure_mem(##M,a,x))"
    unfolding separation_def by simp
  with \<open>r\<in>M\<close> \<open>A\<in>M\<close> show ?thesis by simp
qed

schematic_goal rtran_closure_fm_auto:
  assumes
    "nth(i,env) = r" "nth(j,env) = rp"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "rtran_closure(##A,r,rp) \<longleftrightarrow> sats(A,?rtc(i,j),env)"
  unfolding rtran_closure_def
  by (insert assms ; (rule sep_rules rtran_closure_mem_auto | simp)+)

schematic_goal trans_closure_fm_auto:
  assumes
    "nth(i,env) = r" "nth(j,env) = rp"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "tran_closure(##A,r,rp) \<longleftrightarrow> sats(A,?tc(i,j),env)"
  unfolding tran_closure_def
  by (insert assms ; (rule sep_rules rtran_closure_fm_auto | simp))+

synthesize "trans_closure_fm" from_schematic trans_closure_fm_auto

schematic_goal wellfounded_trancl_fm_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = r"  "nth(k,env) = B"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" "env \<in> list(A)"
  shows
    "wellfounded_trancl(##A,B,r,p) \<longleftrightarrow> sats(A,?wtf(i,j,k),env)"
  unfolding  wellfounded_trancl_def
  by (insert assms ; (rule sep_rules trans_closure_fm_iff_sats | simp)+)

lemma (in M_ZF_trans) wftrancl_separation_intf:
  assumes
    "r\<in>M"
    and
    "Z\<in>M"
  shows
    "separation (##M, wellfounded_trancl(##M,Z,r))"
proof -
  obtain rcfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (wellfounded_trancl(##M,nth(2,env),nth(1,env),nth(0,env))) \<longleftrightarrow> sats(M,rcfm(0,1,2),env)"
    and
    "rcfm(0,1,2) \<in> formula"
    and
    "arity(rcfm(0,1,2)) = 3"
    using wellfounded_trancl_fm_auto[of concl:M "nth(2,_)"] unfolding fm_defs trans_closure_fm_def
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  then
  have "\<forall>x\<in>M. \<forall>z\<in>M. separation(##M, \<lambda>y. sats(M,rcfm(0,1,2) , [y,x,z]))"
    using separation_ax by simp
  moreover
  have "(wellfounded_trancl(##M,z,x,y))
          \<longleftrightarrow> sats(M,rcfm(0,1,2) , [y,x,z])"
    if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
    using that fmsats[of "[y,x,z]"] by simp
  ultimately
  have "\<forall>x\<in>M. \<forall>z\<in>M. separation(##M, wellfounded_trancl(##M,z,x))"
    unfolding separation_def by simp
  with \<open>r\<in>M\<close> \<open>Z\<in>M\<close> show ?thesis by simp
qed

(* nat \<in> M *)

lemma (in M_ZF_trans) finite_sep_intf:
  "separation(##M, \<lambda>x. x\<in>nat)"
proof -
  have "arity(finite_ordinal_fm(0)) = 1 "
    unfolding finite_ordinal_fm_def limit_ordinal_fm_def empty_fm_def succ_fm_def cons_fm_def
      union_fm_def upair_fm_def
    by (simp add: nat_union_abs1 Un_commute)
  with separation_ax
  have "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,finite_ordinal_fm(0),[x,v])))"
    by simp
  then have "(\<forall>v\<in>M. separation(##M,finite_ordinal(##M)))"
    unfolding separation_def by simp
  then have "separation(##M,finite_ordinal(##M))"
    using zero_in_M by auto
  then show ?thesis unfolding separation_def by simp
qed


lemma (in M_ZF_trans) nat_subset_I' :
  "\<lbrakk> I\<in>M ; 0\<in>I ; \<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I \<rbrakk> \<Longrightarrow> nat \<subseteq> I"
  by (rule subsetI,induct_tac x,simp+)


lemma (in M_ZF_trans) nat_subset_I :
  "\<exists>I\<in>M. nat \<subseteq> I"
proof -
  have "\<exists>I\<in>M. 0\<in>I \<and> (\<forall>x\<in>M. x\<in>I \<longrightarrow> succ(x)\<in>I)"
    using infinity_ax unfolding infinity_ax_def by auto
  then obtain I where
    "I\<in>M" "0\<in>I" "(\<forall>x\<in>M. x\<in>I \<longrightarrow> succ(x)\<in>I)"
    by auto
  then have "\<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I"
    using Transset_intf[OF trans_M]  by simp
  then have "nat\<subseteq>I"
    using  \<open>I\<in>M\<close> \<open>0\<in>I\<close> nat_subset_I' by simp
  then show ?thesis using \<open>I\<in>M\<close> by auto
qed

lemma (in M_ZF_trans) nat_in_M :
  "nat \<in> M"
proof -
  have 1:"{x\<in>B . x\<in>A}=A" if "A\<subseteq>B" for A B
    using that by auto
  obtain I where
    "I\<in>M" "nat\<subseteq>I"
    using nat_subset_I by auto
  then have "{x\<in>I . x\<in>nat} \<in> M"
    using finite_sep_intf separation_closed[of "\<lambda>x . x\<in>nat"] by simp
  then show ?thesis
    using \<open>nat\<subseteq>I\<close> 1 by simp
qed
  (* end nat \<in> M *)


lemma (in M_ZF_trans) mtrancl : "M_trancl(##M)"
  using  mbasic rtrancl_separation_intf wftrancl_separation_intf nat_in_M
    wellfounded_trancl_def
  by unfold_locales auto

sublocale M_ZF_trans \<subseteq> M_trancl "##M"
  by (rule mtrancl)

subsection\<open>Interface with \<^term>\<open>M_eclose\<close>\<close>

lemma repl_sats:
  assumes
    sat:"\<And>x z. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> sats(M,\<phi>,Cons(x,Cons(z,env))) \<longleftrightarrow> P(x,z)"
  shows
    "strong_replacement(##M,\<lambda>x z. sats(M,\<phi>,Cons(x,Cons(z,env)))) \<longleftrightarrow>
   strong_replacement(##M,P)"
  by (rule strong_replacement_cong,simp add:sat)

lemma (in M_ZF_trans) nat_trans_M :
  "n\<in>M" if "n\<in>nat" for n
  using that nat_in_M Transset_intf[OF trans_M] by simp

lemma (in M_ZF_trans) list_repl1_intf:
  assumes
    "A\<in>M"
  shows
    "iterates_replacement(##M, is_list_functor(##M,A), 0)"
proof -
  {
    fix n
    assume "n\<in>nat"
    have "succ(n)\<in>M"
      using \<open>n\<in>nat\<close> nat_trans_M by simp
    then have 1:"Memrel(succ(n))\<in>M"
      using \<open>n\<in>nat\<close> Memrel_closed by simp
    have "0\<in>M"
      using  nat_0I nat_trans_M by simp
    then have "is_list_functor(##M, A, a, b)
       \<longleftrightarrow> sats(M, list_functor_fm(13,1,0), [b,a,c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),A,0])"
      if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      for a b c d a0 a1 a2 a3 a4 y x z
      using that 1 \<open>A\<in>M\<close> list_functor_iff_sats by simp
    then have "sats(M, iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0), [a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),A,0])
        \<longleftrightarrow> iterates_MH(##M,is_list_functor(##M,A),0,a2, a1, a0)"
      if "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      for a0 a1 a2 a3 a4 y x z
      using that sats_iterates_MH_fm[of M "is_list_functor(##M,A)" _] 1 \<open>0\<in>M\<close> \<open>A\<in>M\<close>  by simp
    then have 2:"sats(M, is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0),
                            [y,x,z,Memrel(succ(n)),A,0])
        \<longleftrightarrow>
        is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) , Memrel(succ(n)), x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using  that sats_is_wfrec_fm 1 \<open>0\<in>M\<close> \<open>A\<in>M\<close> by simp
    let
      ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0)))"
    have satsf:"sats(M, ?f, [x,z,Memrel(succ(n)),A,0])
        \<longleftrightarrow>
        (\<exists>y\<in>M. pair(##M,x,y,z) &
        is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) , Memrel(succ(n)), x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that 2 1 \<open>0\<in>M\<close> \<open>A\<in>M\<close> by (simp del:pair_abs)
    have "arity(?f) = 5"
      unfolding iterates_MH_fm_def is_wfrec_fm_def is_recfun_fm_def is_nat_case_fm_def
        restriction_fm_def list_functor_fm_def number1_fm_def cartprod_fm_def
        sum_fm_def quasinat_fm_def pre_image_fm_def fm_defs
      by (simp add:nat_simp_union)
    then
    have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,Memrel(succ(n)),A,0]))"
      using replacement_ax 1 \<open>A\<in>M\<close> \<open>0\<in>M\<close> by simp
    then
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) ,
                Memrel(succ(n)), x, y))"
      using repl_sats[of M ?f "[Memrel(succ(n)),A,0]"]  satsf by (simp del:pair_abs)
  }
  then
  show ?thesis unfolding iterates_replacement_def wfrec_replacement_def by simp
qed



(* Iterates_replacement para predicados sin parámetros *)
lemma (in M_ZF_trans) iterates_repl_intf :
  assumes
    "v\<in>M" and
    isfm:"is_F_fm \<in> formula" and
    arty:"arity(is_F_fm)=2" and
    satsf: "\<And>a b env'. \<lbrakk> a\<in>M ; b\<in>M ; env'\<in>list(M) \<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow> sats(M, is_F_fm, [b,a]@env')"
  shows
    "iterates_replacement(##M,is_F,v)"
proof -
  {
    fix n
    assume "n\<in>nat"
    have "succ(n)\<in>M"
      using \<open>n\<in>nat\<close> nat_trans_M by simp
    then have 1:"Memrel(succ(n))\<in>M"
      using \<open>n\<in>nat\<close> Memrel_closed by simp
    {
      fix a0 a1 a2 a3 a4 y x z
      assume as:"a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      have "sats(M, is_F_fm, Cons(b,Cons(a,Cons(c,Cons(d,[a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v])))))
          \<longleftrightarrow> is_F(a,b)"
        if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" for a b c d
        using as that 1 satsf[of a b "[c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v]"] \<open>v\<in>M\<close> by simp
      then
      have "sats(M, iterates_MH_fm(is_F_fm,9,2,1,0), [a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v])
          \<longleftrightarrow> iterates_MH(##M,is_F,v,a2, a1, a0)"
        using as
          sats_iterates_MH_fm[of M "is_F" "is_F_fm"] 1 \<open>v\<in>M\<close> by simp
    }
    then have 2:"sats(M, is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0),
                            [y,x,z,Memrel(succ(n)),v])
        \<longleftrightarrow>
        is_wfrec(##M, iterates_MH(##M,is_F,v),Memrel(succ(n)), x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using  that sats_is_wfrec_fm 1 \<open>v\<in>M\<close> by simp
    let
      ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0)))"
    have satsf:"sats(M, ?f, [x,z,Memrel(succ(n)),v])
        \<longleftrightarrow>
        (\<exists>y\<in>M. pair(##M,x,y,z) &
        is_wfrec(##M, iterates_MH(##M,is_F,v) , Memrel(succ(n)), x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that 2 1 \<open>v\<in>M\<close> by (simp del:pair_abs)
    have "arity(?f) = 4"
      unfolding iterates_MH_fm_def is_wfrec_fm_def is_recfun_fm_def is_nat_case_fm_def
        restriction_fm_def pre_image_fm_def quasinat_fm_def fm_defs
      using arty by (simp add:nat_simp_union)
    then
    have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,Memrel(succ(n)),v]))"
      using replacement_ax 1 \<open>v\<in>M\<close> \<open>is_F_fm\<in>formula\<close> by simp
    then
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, iterates_MH(##M,is_F,v) ,
                Memrel(succ(n)), x, y))"
      using repl_sats[of M ?f "[Memrel(succ(n)),v]"]  satsf by (simp del:pair_abs)
  }
  then
  show ?thesis unfolding iterates_replacement_def wfrec_replacement_def by simp
qed

lemma (in M_ZF_trans) formula_repl1_intf :
  "iterates_replacement(##M, is_formula_functor(##M), 0)"
proof -
  have "0\<in>M"
    using  nat_0I nat_trans_M by simp
  have 1:"arity(formula_functor_fm(1,0)) = 2"
    unfolding formula_functor_fm_def fm_defs sum_fm_def cartprod_fm_def number1_fm_def
    by (simp add:nat_simp_union)
  have 2:"formula_functor_fm(1,0)\<in>formula" by simp
  have "is_formula_functor(##M,a,b) \<longleftrightarrow>
        sats(M, formula_functor_fm(1,0), [b,a])"
    if "a\<in>M" "b\<in>M"  for a b
    using that by simp
  then show ?thesis using \<open>0\<in>M\<close> 1 2 iterates_repl_intf by simp
qed

lemma (in M_ZF_trans) nth_repl_intf:
  assumes
    "l \<in> M"
  shows
    "iterates_replacement(##M,\<lambda>l' t. is_tl(##M,l',t),l)"
proof -
  have 1:"arity(tl_fm(1,0)) = 2"
    unfolding tl_fm_def fm_defs quasilist_fm_def Cons_fm_def Nil_fm_def Inr_fm_def number1_fm_def
      Inl_fm_def by (simp add:nat_simp_union)
  have 2:"tl_fm(1,0)\<in>formula" by simp
  have "is_tl(##M,a,b) \<longleftrightarrow> sats(M, tl_fm(1,0), [b,a])"
    if "a\<in>M" "b\<in>M" for a b
    using that by simp
  then show ?thesis using \<open>l\<in>M\<close> 1 2 iterates_repl_intf by simp
qed


lemma (in M_ZF_trans) eclose_repl1_intf:
  assumes
    "A\<in>M"
  shows
    "iterates_replacement(##M, big_union(##M), A)"
proof -
  have 1:"arity(big_union_fm(1,0)) = 2"
    unfolding big_union_fm_def fm_defs by (simp add:nat_simp_union)
  have 2:"big_union_fm(1,0)\<in>formula" by simp
  have "big_union(##M,a,b) \<longleftrightarrow> sats(M, big_union_fm(1,0), [b,a])"
    if "a\<in>M" "b\<in>M" for a b
    using that by simp
  then show ?thesis using \<open>A\<in>M\<close> 1 2 iterates_repl_intf by simp
qed

(*
    and list_replacement2:
   "M(A) \<Longrightarrow> strong_replacement(M,
         \<lambda>n y. n\<in>nat & is_iterates(M, is_list_functor(M,A), 0, n, y))"

*)
lemma (in M_ZF_trans) list_repl2_intf:
  assumes
    "A\<in>M"
  shows
    "strong_replacement(##M,\<lambda>n y. n\<in>nat & is_iterates(##M, is_list_functor(##M,A), 0, n, y))"
proof -
  have "0\<in>M"
    using  nat_0I nat_trans_M by simp
  have "is_list_functor(##M,A,a,b) \<longleftrightarrow>
        sats(M,list_functor_fm(13,1,0),[b,a,c,d,e,f,g,h,i,j,k,n,y,A,0,nat])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that \<open>0\<in>M\<close> nat_in_M \<open>A\<in>M\<close> by simp
  then
  have 1:"sats(M, is_iterates_fm(list_functor_fm(13,1,0),3,0,1),[n,y,A,0,nat] ) \<longleftrightarrow>
           is_iterates(##M, is_list_functor(##M,A), 0, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> \<open>A\<in>M\<close> nat_in_M
      sats_is_iterates_fm[of M "is_list_functor(##M,A)"] by simp
  let ?f = "And(Member(0,4),is_iterates_fm(list_functor_fm(13,1,0),3,0,1))"
  have satsf:"sats(M, ?f,[n,y,A,0,nat] ) \<longleftrightarrow>
        n\<in>nat & is_iterates(##M, is_list_functor(##M,A), 0, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> \<open>A\<in>M\<close> nat_in_M 1 by simp
  have "arity(?f) = 5"
    unfolding is_iterates_fm_def restriction_fm_def list_functor_fm_def number1_fm_def Memrel_fm_def
      cartprod_fm_def sum_fm_def quasinat_fm_def pre_image_fm_def fm_defs is_wfrec_fm_def
      is_recfun_fm_def iterates_MH_fm_def is_nat_case_fm_def
    by (simp add:nat_simp_union)
  then
  have "strong_replacement(##M,\<lambda>n y. sats(M,?f,[n,y,A,0,nat]))"
    using replacement_ax 1 nat_in_M \<open>A\<in>M\<close> \<open>0\<in>M\<close> by simp
  then
  show ?thesis using repl_sats[of M ?f "[A,0,nat]"]  satsf  by simp
qed

lemma (in M_ZF_trans) formula_repl2_intf:
  "strong_replacement(##M,\<lambda>n y. n\<in>nat & is_iterates(##M, is_formula_functor(##M), 0, n, y))"
proof -
  have "0\<in>M"
    using  nat_0I nat_trans_M by simp
  have "is_formula_functor(##M,a,b) \<longleftrightarrow>
        sats(M,formula_functor_fm(1,0),[b,a,c,d,e,f,g,h,i,j,k,n,y,0,nat])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that \<open>0\<in>M\<close> nat_in_M by simp
  then
  have 1:"sats(M, is_iterates_fm(formula_functor_fm(1,0),2,0,1),[n,y,0,nat] ) \<longleftrightarrow>
           is_iterates(##M, is_formula_functor(##M), 0, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> nat_in_M
      sats_is_iterates_fm[of M "is_formula_functor(##M)"] by simp
  let ?f = "And(Member(0,3),is_iterates_fm(formula_functor_fm(1,0),2,0,1))"
  have satsf:"sats(M, ?f,[n,y,0,nat] ) \<longleftrightarrow>
        n\<in>nat & is_iterates(##M, is_formula_functor(##M), 0, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> nat_in_M 1 by simp
  have artyf:"arity(?f) = 4"
    unfolding is_iterates_fm_def formula_functor_fm_def fm_defs sum_fm_def quasinat_fm_def
      cartprod_fm_def number1_fm_def Memrel_fm_def ordinal_fm_def transset_fm_def
      is_wfrec_fm_def is_recfun_fm_def iterates_MH_fm_def is_nat_case_fm_def subset_fm_def
      pre_image_fm_def restriction_fm_def
    by (simp add:nat_simp_union)
  then
  have "strong_replacement(##M,\<lambda>n y. sats(M,?f,[n,y,0,nat]))"
    using replacement_ax 1 artyf \<open>0\<in>M\<close> nat_in_M by simp
  then
  show ?thesis using repl_sats[of M ?f "[0,nat]"]  satsf  by simp
qed


(*
   "M(A) \<Longrightarrow> strong_replacement(M,
         \<lambda>n y. n\<in>nat & is_iterates(M, big_union(M), A, n, y))"
*)

lemma (in M_ZF_trans) eclose_repl2_intf:
  assumes
    "A\<in>M"
  shows
    "strong_replacement(##M,\<lambda>n y. n\<in>nat & is_iterates(##M, big_union(##M), A, n, y))"
proof -
  have "big_union(##M,a,b) \<longleftrightarrow>
        sats(M,big_union_fm(1,0),[b,a,c,d,e,f,g,h,i,j,k,n,y,A,nat])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that \<open>A\<in>M\<close> nat_in_M by simp
  then
  have 1:"sats(M, is_iterates_fm(big_union_fm(1,0),2,0,1),[n,y,A,nat] ) \<longleftrightarrow>
           is_iterates(##M, big_union(##M), A, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>A\<in>M\<close> nat_in_M
      sats_is_iterates_fm[of M "big_union(##M)"] by simp
  let ?f = "And(Member(0,3),is_iterates_fm(big_union_fm(1,0),2,0,1))"
  have satsf:"sats(M, ?f,[n,y,A,nat] ) \<longleftrightarrow>
        n\<in>nat & is_iterates(##M, big_union(##M), A, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>A\<in>M\<close> nat_in_M 1 by simp
  have artyf:"arity(?f) = 4"
    unfolding is_iterates_fm_def formula_functor_fm_def fm_defs sum_fm_def quasinat_fm_def
      cartprod_fm_def number1_fm_def Memrel_fm_def ordinal_fm_def transset_fm_def
      is_wfrec_fm_def is_recfun_fm_def iterates_MH_fm_def is_nat_case_fm_def subset_fm_def
      pre_image_fm_def restriction_fm_def
    by (simp add:nat_simp_union)
  then
  have "strong_replacement(##M,\<lambda>n y. sats(M,?f,[n,y,A,nat]))"
    using replacement_ax 1 artyf \<open>A\<in>M\<close> nat_in_M by simp
  then
  show ?thesis using repl_sats[of M ?f "[A,nat]"]  satsf  by simp
qed

lemma (in M_ZF_trans) mdatatypes : "M_datatypes(##M)"
  using  mtrancl list_repl1_intf list_repl2_intf formula_repl1_intf
    formula_repl2_intf nth_repl_intf
  by unfold_locales auto

sublocale M_ZF_trans \<subseteq> M_datatypes "##M"
  by (rule mdatatypes)

lemma (in M_ZF_trans) meclose : "M_eclose(##M)"
  using mdatatypes eclose_repl1_intf eclose_repl2_intf
  by unfold_locales auto

sublocale M_ZF_trans \<subseteq> M_eclose "##M"
  by (rule meclose)

(* Interface with locale M_eclose_pow *)

(* "powerset(M,A,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> subset(M,x,A)" *)
definition
  powerset_fm :: "[i,i] \<Rightarrow> i" where
  "powerset_fm(A,z) \<equiv> Forall(Iff(Member(0,succ(z)),subset_fm(0,succ(A))))"

lemma powerset_type [TC]:
  "\<lbrakk> x \<in> nat; y \<in> nat \<rbrakk> \<Longrightarrow> powerset_fm(x,y) \<in> formula"
  by (simp add:powerset_fm_def)

definition
  is_powapply_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_powapply_fm(f,y,z) \<equiv>
      Exists(And(fun_apply_fm(succ(f), succ(y), 0),
            Forall(Iff(Member(0, succ(succ(z))),
            Forall(Implies(Member(0, 1), Member(0, 2)))))))"

lemma is_powapply_type [TC] :
  "\<lbrakk>f\<in>nat ; y\<in>nat; z\<in>nat\<rbrakk> \<Longrightarrow> is_powapply_fm(f,y,z)\<in>formula"
  unfolding is_powapply_fm_def by simp

lemma sats_is_powapply_fm :
  assumes
    "f\<in>nat" "y\<in>nat" "z\<in>nat" "env\<in>list(A)" "0\<in>A"
  shows
    "is_powapply(##A,nth(f, env),nth(y, env),nth(z, env))
    \<longleftrightarrow> sats(A,is_powapply_fm(f,y,z),env)"
  unfolding is_powapply_def is_powapply_fm_def is_Collect_def powerset_def subset_def
  using nth_closed assms by simp


lemma (in M_ZF_trans) powapply_repl :
  assumes
    "f\<in>M"
  shows
    "strong_replacement(##M,is_powapply(##M,f))"
proof -
  have "arity(is_powapply_fm(2,0,1)) = 3"
    unfolding is_powapply_fm_def
    by (simp add: fm_defs nat_simp_union)
  then
  have "\<forall>f0\<in>M. strong_replacement(##M, \<lambda>p z. sats(M,is_powapply_fm(2,0,1) , [p,z,f0]))"
    using replacement_ax by simp
  moreover
  have "is_powapply(##M,f0,p,z) \<longleftrightarrow> sats(M,is_powapply_fm(2,0,1) , [p,z,f0])"
    if "p\<in>M" "z\<in>M" "f0\<in>M" for p z f0
    using that zero_in_M sats_is_powapply_fm[of 2 0 1 "[p,z,f0]" M] by simp
  ultimately
  have "\<forall>f0\<in>M. strong_replacement(##M, is_powapply(##M,f0))"
    unfolding strong_replacement_def univalent_def by simp
  with \<open>f\<in>M\<close> show ?thesis by simp
qed


(*"PHrank(M,f,y,z) \<equiv> M(z) \<and> (\<exists>fy[M]. fun_apply(M,f,y,fy) \<and> successor(M,fy,z))"*)
definition
  PHrank_fm :: "[i,i,i] \<Rightarrow> i" where
  "PHrank_fm(f,y,z) \<equiv> Exists(And(fun_apply_fm(succ(f),succ(y),0)
                                 ,succ_fm(0,succ(z))))"

lemma PHrank_type [TC]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat \<rbrakk> \<Longrightarrow> PHrank_fm(x,y,z) \<in> formula"
  by (simp add:PHrank_fm_def)


lemma (in M_ZF_trans) sats_PHrank_fm [simp]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat;  env \<in> list(M) \<rbrakk> 
    \<Longrightarrow> sats(M,PHrank_fm(x,y,z),env) \<longleftrightarrow>
        PHrank(##M,nth(x,env),nth(y,env),nth(z,env))"
  using zero_in_M Internalizations.nth_closed by (simp add: PHrank_def PHrank_fm_def)


lemma (in M_ZF_trans) phrank_repl :
  assumes
    "f\<in>M"
  shows
    "strong_replacement(##M,PHrank(##M,f))"
proof -
  have "arity(PHrank_fm(2,0,1)) = 3"
    unfolding PHrank_fm_def
    by (simp add: fm_defs nat_simp_union)
  then
  have "\<forall>f0\<in>M. strong_replacement(##M, \<lambda>p z. sats(M,PHrank_fm(2,0,1) , [p,z,f0]))"
    using replacement_ax by simp
  then
  have "\<forall>f0\<in>M. strong_replacement(##M, PHrank(##M,f0))"
    unfolding strong_replacement_def univalent_def by simp
  with \<open>f\<in>M\<close> show ?thesis by simp
qed


(*"is_Hrank(M,x,f,hc) \<equiv> (\<exists>R[M]. big_union(M,R,hc) \<and>is_Replace(M,x,PHrank(M,f),R)) "*)
definition
  is_Hrank_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_Hrank_fm(x,f,hc) \<equiv> Exists(And(big_union_fm(0,succ(hc)),
                                Replace_fm(succ(x),PHrank_fm(succ(succ(succ(f))),0,1),0)))"

lemma is_Hrank_type [TC]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat \<rbrakk> \<Longrightarrow> is_Hrank_fm(x,y,z) \<in> formula"
  by (simp add:is_Hrank_fm_def)

lemma (in M_ZF_trans) sats_is_Hrank_fm [simp]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(M)\<rbrakk>
    \<Longrightarrow> sats(M,is_Hrank_fm(x,y,z),env) \<longleftrightarrow>
        is_Hrank(##M,nth(x,env),nth(y,env),nth(z,env))"
  using zero_in_M is_Hrank_def is_Hrank_fm_def sats_Replace_fm
  by simp

(* M(x) \<Longrightarrow> wfrec_replacement(M,is_Hrank(M),rrank(x)) *)
lemma (in M_ZF_trans) wfrec_rank :
  assumes
    "X\<in>M"
  shows
    "wfrec_replacement(##M,is_Hrank(##M),rrank(X))"
proof -
  have
    "is_Hrank(##M,a2, a1, a0) \<longleftrightarrow>
             sats(M, is_Hrank_fm(2,1,0), [a0,a1,a2,a3,a4,y,x,z,rrank(X)])"
    if "a4\<in>M" "a3\<in>M" "a2\<in>M" "a1\<in>M" "a0\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" for a4 a3 a2 a1 a0 y x z
    using that rrank_in_M \<open>X\<in>M\<close> by simp
  then
  have
    1:"sats(M, is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0),[y,x,z,rrank(X)])
  \<longleftrightarrow> is_wfrec(##M, is_Hrank(##M) ,rrank(X), x, y)"
    if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
    using that \<open>X\<in>M\<close> rrank_in_M sats_is_wfrec_fm by simp
  let
    ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0)))"
  have satsf:"sats(M, ?f, [x,z,rrank(X)])
              \<longleftrightarrow> (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hrank(##M) , rrank(X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> rrank_in_M by (simp del:pair_abs)
  have "arity(?f) = 3"
    unfolding is_wfrec_fm_def is_recfun_fm_def is_nat_case_fm_def is_Hrank_fm_def PHrank_fm_def
      restriction_fm_def list_functor_fm_def number1_fm_def cartprod_fm_def
      sum_fm_def quasinat_fm_def pre_image_fm_def fm_defs
    by (simp add:nat_simp_union)
  then
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,rrank(X)]))"
    using replacement_ax 1 \<open>X\<in>M\<close> rrank_in_M by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hrank(##M) , rrank(X), x, y))"
    using repl_sats[of M ?f "[rrank(X)]"]  satsf by (simp del:pair_abs)
  then
  show ?thesis unfolding wfrec_replacement_def  by simp
qed

(*"is_HVfrom(M,A,x,f,h) \<equiv> \<exists>U[M]. \<exists>R[M].  union(M,A,U,h)
        \<and> big_union(M,R,U) \<and> is_Replace(M,x,is_powapply(M,f),R)"*)
definition
  is_HVfrom_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "is_HVfrom_fm(A,x,f,h) \<equiv> Exists(Exists(And(union_fm(A #+ 2,1,h #+ 2),
                            And(big_union_fm(0,1),
                            Replace_fm(x #+ 2,is_powapply_fm(f #+ 4,0,1),0)))))"

lemma is_HVfrom_type [TC]:
  "\<lbrakk> A\<in>nat; x \<in> nat; f \<in> nat; h \<in> nat \<rbrakk> \<Longrightarrow> is_HVfrom_fm(A,x,f,h) \<in> formula"
  by (simp add:is_HVfrom_fm_def)

lemma sats_is_HVfrom_fm :
  "\<lbrakk> a\<in>nat; x \<in> nat; f \<in> nat; h \<in> nat; env \<in> list(A); 0\<in>A\<rbrakk>
    \<Longrightarrow> sats(A,is_HVfrom_fm(a,x,f,h),env) \<longleftrightarrow>
        is_HVfrom(##A,nth(a,env),nth(x,env),nth(f,env),nth(h,env))"
  using is_HVfrom_def is_HVfrom_fm_def sats_Replace_fm[OF sats_is_powapply_fm]
  by simp

lemma is_HVfrom_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(x,env) = xx" "nth(f,env) = ff" "nth(h,env) = hh"
    "a\<in>nat" "x\<in>nat" "f\<in>nat" "h\<in>nat" "env\<in>list(A)" "0\<in>A"
  shows
    "is_HVfrom(##A,aa,xx,ff,hh) \<longleftrightarrow> sats(A, is_HVfrom_fm(a,x,f,h), env)"
  using assms sats_is_HVfrom_fm by simp

(* FIX US *)
schematic_goal sats_is_Vset_fm_auto:
  assumes
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,nth(i, env),nth(v, env))
    \<longleftrightarrow> sats(A,?ivs_fm(i,v),env)"
  unfolding is_Vset_def is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp)+)

schematic_goal is_Vset_iff_sats:
  assumes
    "nth(i,env) = ii" "nth(v,env) = vv"
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,ii,vv) \<longleftrightarrow> sats(A, ?ivs_fm(i,v), env)"
  unfolding \<open>nth(i,env) = ii\<close>[symmetric] \<open>nth(v,env) = vv\<close>[symmetric]
  by (rule sats_is_Vset_fm_auto(1); simp add:assms)


lemma (in M_ZF_trans) memrel_eclose_sing :
  "a\<in>M \<Longrightarrow> \<exists>sa\<in>M. \<exists>esa\<in>M. \<exists>mesa\<in>M.
       upair(##M,a,a,sa) & is_eclose(##M,sa,esa) & membership(##M,esa,mesa)"
  using upair_ax eclose_closed Memrel_closed unfolding upair_ax_def
  by (simp del:upair_abs)


lemma (in M_ZF_trans) trans_repl_HVFrom :
  assumes
    "A\<in>M" "i\<in>M"
  shows
    "transrec_replacement(##M,is_HVfrom(##M,A),i)"
proof -
  { fix mesa
    assume "mesa\<in>M"
    have
      0:"is_HVfrom(##M,A,a2, a1, a0) \<longleftrightarrow>
      sats(M, is_HVfrom_fm(8,2,1,0), [a0,a1,a2,a3,a4,y,x,z,A,mesa])"
      if "a4\<in>M" "a3\<in>M" "a2\<in>M" "a1\<in>M" "a0\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" for a4 a3 a2 a1 a0 y x z
      using that zero_in_M sats_is_HVfrom_fm \<open>mesa\<in>M\<close> \<open>A\<in>M\<close> by simp
    have
      1:"sats(M, is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0),[y,x,z,A,mesa])
        \<longleftrightarrow> is_wfrec(##M, is_HVfrom(##M,A),mesa, x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using that \<open>A\<in>M\<close> \<open>mesa\<in>M\<close> sats_is_wfrec_fm[OF 0] by simp
    let
      ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0)))"
    have satsf:"sats(M, ?f, [x,z,A,mesa])
              \<longleftrightarrow> (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_HVfrom(##M,A) , mesa, x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that 1 \<open>A\<in>M\<close> \<open>mesa\<in>M\<close> by (simp del:pair_abs)
    have "arity(?f) = 4"
      unfolding is_HVfrom_fm_def is_wfrec_fm_def is_recfun_fm_def is_nat_case_fm_def
        restriction_fm_def list_functor_fm_def number1_fm_def cartprod_fm_def
        is_powapply_fm_def sum_fm_def quasinat_fm_def pre_image_fm_def fm_defs
      by (simp add:nat_simp_union)
    then
    have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,A,mesa]))"
      using replacement_ax 1 \<open>A\<in>M\<close> \<open>mesa\<in>M\<close> by simp
    then
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_HVfrom(##M,A) , mesa, x, y))"
      using repl_sats[of M ?f "[A,mesa]"]  satsf by (simp del:pair_abs)
    then
    have "wfrec_replacement(##M,is_HVfrom(##M,A),mesa)"
      unfolding wfrec_replacement_def  by simp
  }
  then show ?thesis unfolding transrec_replacement_def
    using \<open>i\<in>M\<close> memrel_eclose_sing by simp
qed


lemma (in M_ZF_trans) meclose_pow : "M_eclose_pow(##M)"
  using meclose power_ax powapply_repl phrank_repl trans_repl_HVFrom wfrec_rank
  by unfold_locales auto

sublocale M_ZF_trans \<subseteq> M_eclose_pow "##M"
  by (rule meclose_pow)

lemma (in M_ZF_trans) repl_gen :
  assumes
    f_abs: "\<And>x y. \<lbrakk> x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_F(##M,x,y) \<longleftrightarrow> y = f(x)"
    and
    f_sats: "\<And>x y. \<lbrakk>x\<in>M ; y\<in>M \<rbrakk> \<Longrightarrow>
             sats(M,f_fm,Cons(x,Cons(y,env))) \<longleftrightarrow> is_F(##M,x,y)"
    and
    f_form: "f_fm \<in> formula"
    and
    f_arty: "arity(f_fm) = 2"
    and
    "env\<in>list(M)"
  shows
    "strong_replacement(##M, \<lambda>x y. y = f(x))"
proof -
  have "sats(M,f_fm,[x,y]@env) \<longleftrightarrow> is_F(##M,x,y)" if "x\<in>M" "y\<in>M" for x y
    using that f_sats[of x y] by simp
  moreover
  from f_form f_arty
  have "strong_replacement(##M, \<lambda>x y. sats(M,f_fm,[x,y]@env))"
    using \<open>env\<in>list(M)\<close> replacement_ax by simp
  ultimately
  have "strong_replacement(##M, is_F(##M))"
    using strong_replacement_cong[of "##M" "\<lambda>x y. sats(M,f_fm,[x,y]@env)" "is_F(##M)"] by simp
  with f_abs show ?thesis
    using strong_replacement_cong[of "##M" "is_F(##M)" "\<lambda>x y. y = f(x)"] by simp
qed

(* Proof Scheme for instances of separation *)
lemma (in M_ZF_trans) sep_in_M :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 #+ length(env)" "A\<in>M" and
    satsQ: "\<And>x. x\<in>M \<Longrightarrow> sats(M,\<phi>,[x]@env) \<longleftrightarrow> Q(x)"
  shows
    "{y\<in>A . Q(y)}\<in>M"
proof -
  have "separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))"
    using assms separation_ax by simp
  then show ?thesis using
      \<open>A\<in>M\<close> satsQ trans_M
      separation_cong[of "##M" "\<lambda>y. sats(M,\<phi>,[y]@env)" "Q"]
      separation_closed  by simp
qed

end