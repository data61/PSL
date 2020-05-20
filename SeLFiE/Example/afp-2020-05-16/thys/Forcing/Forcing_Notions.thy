section\<open>Forcing notions\<close>
text\<open>This theory defines a locale for forcing notions, that is,
 preorders with a distinguished maximum element.\<close>

theory Forcing_Notions
  imports "ZF-Constructible.Relative"
begin

subsection\<open>Basic concepts\<close>
text\<open>We say that two elements $p,q$ are
  \<^emph>\<open>compatible\<close> if they have a lower bound in $P$\<close>
definition compat_in :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "compat_in(A,r,p,q) \<equiv> \<exists>d\<in>A . \<langle>d,p\<rangle>\<in>r \<and> \<langle>d,q\<rangle>\<in>r"

definition
  is_compat_in :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_compat_in(M,A,r,p,q) \<equiv> \<exists>d[M]. d\<in>A \<and> (\<exists>dp[M]. pair(M,d,p,dp) \<and> dp\<in>r \<and> 
                                   (\<exists>dq[M]. pair(M,d,q,dq) \<and> dq\<in>r))"

lemma compat_inI : 
  "\<lbrakk> d\<in>A ; \<langle>d,p\<rangle>\<in>r ; \<langle>d,g\<rangle>\<in>r \<rbrakk> \<Longrightarrow> compat_in(A,r,p,g)"
  by (auto simp add: compat_in_def)

lemma refl_compat:
  "\<lbrakk> refl(A,r) ; \<langle>p,q\<rangle> \<in> r | p=q | \<langle>q,p\<rangle> \<in> r ; p\<in>A ; q\<in>A\<rbrakk> \<Longrightarrow> compat_in(A,r,p,q)"
  by (auto simp add: refl_def compat_inI)

lemma  chain_compat:
  "refl(A,r) \<Longrightarrow> linear(A,r) \<Longrightarrow>  (\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,r,p,q))"
  by (simp add: refl_compat linear_def)

lemma subset_fun_image: "f:N\<rightarrow>P \<Longrightarrow> f``N\<subseteq>P"
  by (auto simp add: image_fun apply_funtype)

lemma refl_monot_domain: "refl(B,r) \<Longrightarrow> A\<subseteq>B \<Longrightarrow> refl(A,r)"  
  unfolding refl_def by blast

definition
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not> compat_in(P,leq,p,q)))"

definition 
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) \<equiv> \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"

locale forcing_notion =
  fixes P leq one
  assumes one_in_P:         "one \<in> P"
    and leq_preord:       "preorder_on(P,leq)"
    and one_max:          "\<forall>p\<in>P. \<langle>p,one\<rangle>\<in>leq"
begin

abbreviation Leq :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>" 50)
  where "x \<preceq> y \<equiv> \<langle>x,y\<rangle>\<in>leq"

lemma refl_leq:
  "r\<in>P \<Longrightarrow> r\<preceq>r"
  using leq_preord unfolding preorder_on_def refl_def by simp

text\<open>A set $D$ is \<^emph>\<open>dense\<close> if every element $p\in P$ has a lower 
bound in $D$.\<close>
definition 
  dense :: "i\<Rightarrow>o" where
  "dense(D) \<equiv> \<forall>p\<in>P. \<exists>d\<in>D . d\<preceq>p"

text\<open>There is also a weaker definition which asks for 
a lower bound in $D$ only for the elements below some fixed 
element $q$.\<close>
definition 
  dense_below :: "i\<Rightarrow>i\<Rightarrow>o" where
  "dense_below(D,q) \<equiv> \<forall>p\<in>P. p\<preceq>q \<longrightarrow> (\<exists>d\<in>D. d\<in>P \<and> d\<preceq>p)"

lemma P_dense: "dense(P)"
  by (insert leq_preord, auto simp add: preorder_on_def refl_def dense_def)

definition 
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) \<equiv> \<forall>x\<in>F. \<forall> p \<in> P . x\<preceq>p \<longrightarrow> p\<in>F"

definition 
  compat :: "i\<Rightarrow>i\<Rightarrow>o" where
  "compat(p,q) \<equiv> compat_in(P,leq,p,q)"

lemma leq_transD:  "a\<preceq>b \<Longrightarrow> b\<preceq>c \<Longrightarrow> a \<in> P\<Longrightarrow> b \<in> P\<Longrightarrow> c \<in> P\<Longrightarrow> a\<preceq>c"
  using leq_preord trans_onD unfolding preorder_on_def by blast

lemma leq_transD':  "A\<subseteq>P \<Longrightarrow> a\<preceq>b \<Longrightarrow> b\<preceq>c \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> P\<Longrightarrow> c \<in> P\<Longrightarrow> a\<preceq>c"
  using leq_preord trans_onD subsetD unfolding preorder_on_def by blast


lemma leq_reflI: "p\<in>P \<Longrightarrow> p\<preceq>p"
  using leq_preord unfolding preorder_on_def refl_def by blast

lemma compatD[dest!]: "compat(p,q) \<Longrightarrow> \<exists>d\<in>P. d\<preceq>p \<and> d\<preceq>q"
  unfolding compat_def compat_in_def .

abbreviation Incompatible :: "[i, i] \<Rightarrow> o"  (infixl "\<bottom>" 50)
  where "p \<bottom> q \<equiv> \<not> compat(p,q)"

lemma compatI[intro!]: "d\<in>P \<Longrightarrow> d\<preceq>p \<Longrightarrow> d\<preceq>q \<Longrightarrow> compat(p,q)"
  unfolding compat_def compat_in_def by blast

lemma denseD [dest]: "dense(D) \<Longrightarrow> p\<in>P \<Longrightarrow>  \<exists>d\<in>D. d\<preceq> p"
  unfolding dense_def by blast

lemma denseI [intro!]: "\<lbrakk> \<And>p. p\<in>P \<Longrightarrow> \<exists>d\<in>D. d\<preceq> p \<rbrakk> \<Longrightarrow> dense(D)"
  unfolding dense_def by blast

lemma dense_belowD [dest]:
  assumes "dense_below(D,p)" "q\<in>P" "q\<preceq>p"
  shows "\<exists>d\<in>D. d\<in>P \<and> d\<preceq>q"
  using assms unfolding dense_below_def by simp
    (*obtains d where "d\<in>D" "d\<in>P" "d\<preceq>q"
  using assms unfolding dense_below_def by blast *)

lemma dense_belowI [intro!]: 
  assumes "\<And>q. q\<in>P \<Longrightarrow> q\<preceq>p \<Longrightarrow> \<exists>d\<in>D. d\<in>P \<and> d\<preceq>q" 
  shows "dense_below(D,p)"
  using assms unfolding dense_below_def by simp

lemma dense_below_cong: "p\<in>P \<Longrightarrow> D = D' \<Longrightarrow> dense_below(D,p) \<longleftrightarrow> dense_below(D',p)"
  by blast

lemma dense_below_cong': "p\<in>P \<Longrightarrow> \<lbrakk>\<And>x. x\<in>P \<Longrightarrow> Q(x) \<longleftrightarrow> Q'(x)\<rbrakk> \<Longrightarrow> 
           dense_below({q\<in>P. Q(q)},p) \<longleftrightarrow> dense_below({q\<in>P. Q'(q)},p)"
  by blast

lemma dense_below_mono: "p\<in>P \<Longrightarrow> D \<subseteq> D' \<Longrightarrow> dense_below(D,p) \<Longrightarrow> dense_below(D',p)"
  by blast

lemma dense_below_under:
  assumes "dense_below(D,p)" "p\<in>P" "q\<in>P" "q\<preceq>p"
  shows "dense_below(D,q)"
  using assms leq_transD by blast

lemma ideal_dense_below:
  assumes "\<And>q. q\<in>P \<Longrightarrow> q\<preceq>p \<Longrightarrow> q\<in>D"
  shows "dense_below(D,p)"
  using assms leq_reflI by blast

lemma dense_below_dense_below: 
  assumes "dense_below({q\<in>P. dense_below(D,q)},p)" "p\<in>P" 
  shows "dense_below(D,p)"  
  using assms leq_transD leq_reflI  by blast
    (* Long proof *)
    (*  unfolding dense_below_def
proof (intro ballI impI)
  fix r
  assume "r\<in>P" \<open>r\<preceq>p\<close>
  with assms
  obtain q where "q\<in>P" "q\<preceq>r" "dense_below(D,q)"
    using assms by auto
  moreover from this
  obtain d where "d\<in>P" "d\<preceq>q" "d\<in>D"
    using assms leq_preord unfolding preorder_on_def refl_def by blast
  moreover
  note \<open>r\<in>P\<close>
  ultimately
  show "\<exists>d\<in>D. d \<in> P \<and> d\<preceq> r"
    using leq_preord trans_onD unfolding preorder_on_def by blast
qed *)

definition
  antichain :: "i\<Rightarrow>o" where
  "antichain(A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not>compat(p,q)))"

text\<open>A filter is an increasing set $G$ with all its elements 
being compatible in $G$.\<close>
definition 
  filter :: "i\<Rightarrow>o" where
  "filter(G) \<equiv> G\<subseteq>P \<and> increasing(G) \<and> (\<forall>p\<in>G. \<forall>q\<in>G. compat_in(G,leq,p,q))"

lemma filterD : "filter(G) \<Longrightarrow> x \<in> G \<Longrightarrow> x \<in> P"
  by (auto simp add : subsetD filter_def)

lemma filter_leqD : "filter(G) \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> P \<Longrightarrow> x\<preceq>y \<Longrightarrow> y \<in> G"
  by (simp add: filter_def increasing_def)

lemma filter_imp_compat: "filter(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>G \<Longrightarrow> compat(p,q)"
  unfolding filter_def compat_in_def compat_def by blast

lemma low_bound_filter: \<comment> \<open>says the compatibility is attained inside G\<close>
  assumes "filter(G)" and "p\<in>G" and "q\<in>G"
  shows "\<exists>r\<in>G. r\<preceq>p \<and> r\<preceq>q" 
  using assms 
  unfolding compat_in_def filter_def by blast

text\<open>We finally introduce the upward closure of a set
and prove that the closure of $A$ is a filter if its elements are
compatible in $A$.\<close>
definition  
  upclosure :: "i\<Rightarrow>i" where
  "upclosure(A) \<equiv> {p\<in>P.\<exists>a\<in>A. a\<preceq>p}"

lemma  upclosureI [intro] : "p\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> a\<preceq>p \<Longrightarrow> p\<in>upclosure(A)"
  by (simp add:upclosure_def, auto)

lemma  upclosureE [elim] :
  "p\<in>upclosure(A) \<Longrightarrow> (\<And>x a. x\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> a\<preceq>x \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add:upclosure_def)

lemma  upclosureD [dest] :
  "p\<in>upclosure(A) \<Longrightarrow> \<exists>a\<in>A.(a\<preceq>p) \<and> p\<in>P"
  by (simp add:upclosure_def)

lemma upclosure_increasing :
  assumes "A\<subseteq>P"
  shows "increasing(upclosure(A))"
  unfolding increasing_def upclosure_def
  using leq_transD'[OF \<open>A\<subseteq>P\<close>] by auto

lemma  upclosure_in_P: "A \<subseteq> P \<Longrightarrow> upclosure(A) \<subseteq> P"
  using subsetI upclosure_def by simp

lemma  A_sub_upclosure: "A \<subseteq> P \<Longrightarrow> A\<subseteq>upclosure(A)"
  using subsetI leq_preord 
  unfolding upclosure_def preorder_on_def refl_def by auto

lemma  elem_upclosure: "A\<subseteq>P \<Longrightarrow> x\<in>A  \<Longrightarrow> x\<in>upclosure(A)"
  by (blast dest:A_sub_upclosure)

lemma  closure_compat_filter:
  assumes "A\<subseteq>P" "(\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,leq,p,q))"
  shows "filter(upclosure(A))"
  unfolding filter_def
proof(auto)
  show "increasing(upclosure(A))"
    using assms upclosure_increasing by simp
next
  let ?UA="upclosure(A)"
  show "compat_in(upclosure(A), leq, p, q)" if "p\<in>?UA" "q\<in>?UA" for p q
  proof -
    from that
    obtain a b where 1:"a\<in>A" "b\<in>A" "a\<preceq>p" "b\<preceq>q" "p\<in>P" "q\<in>P"
      using upclosureD[OF \<open>p\<in>?UA\<close>] upclosureD[OF \<open>q\<in>?UA\<close>] by auto
    with assms(2)
    obtain d where "d\<in>A" "d\<preceq>a" "d\<preceq>b"
      unfolding compat_in_def by auto
    with 1
    have 2:"d\<preceq>p" "d\<preceq>q" "d\<in>?UA"
      using A_sub_upclosure[THEN subsetD] \<open>A\<subseteq>P\<close>
        leq_transD'[of A d a] leq_transD'[of A d b] by auto
    then
    show ?thesis unfolding compat_in_def by auto
  qed
qed

lemma  aux_RS1:  "f \<in> N \<rightarrow> P \<Longrightarrow> n\<in>N \<Longrightarrow> f`n \<in> upclosure(f ``N)"
  using elem_upclosure[OF subset_fun_image] image_fun
  by (simp, blast)

lemma decr_succ_decr: 
  assumes "f \<in> nat \<rightarrow> P" "preorder_on(P,leq)"
    "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    "m\<in>nat"
  shows "n\<in>nat \<Longrightarrow> n\<le>m \<Longrightarrow> \<langle>f ` m, f ` n\<rangle> \<in> leq"
  using \<open>m\<in>_\<close>
proof(induct m)
  case 0
  then show ?case using assms leq_reflI by simp
next
  case (succ x)
  then
  have 1:"f`succ(x) \<preceq> f`x" "f`n\<in>P" "f`x\<in>P" "f`succ(x)\<in>P"
    using assms by simp_all
  consider (lt) "n<succ(x)" | (eq) "n=succ(x)"
    using succ le_succ_iff by auto
  then 
  show ?case 
  proof(cases)
    case lt
    with 1 show ?thesis using leI succ leq_transD by auto
  next
    case eq
    with 1 show ?thesis using leq_reflI by simp
  qed
qed

lemma decr_seq_linear: 
  assumes "refl(P,leq)" "f \<in> nat \<rightarrow> P"
    "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    "trans[P](leq)"
  shows "linear(f `` nat, leq)"
proof -
  have "preorder_on(P,leq)" 
    unfolding preorder_on_def using assms by simp
  {
    fix n m
    assume "n\<in>nat" "m\<in>nat"
    then
    have "f`m \<preceq> f`n \<or> f`n \<preceq> f`m"
    proof(cases "m\<le>n")
      case True
      with \<open>n\<in>_\<close> \<open>m\<in>_\<close>
      show ?thesis 
        using decr_succ_decr[of f n m] assms leI \<open>preorder_on(P,leq)\<close> by simp
    next
      case False
      with \<open>n\<in>_\<close> \<open>m\<in>_\<close>
      show ?thesis 
        using decr_succ_decr[of f m n] assms leI not_le_iff_lt \<open>preorder_on(P,leq)\<close> by simp
    qed
  }
  then
  show ?thesis
    unfolding linear_def using ball_image_simp assms by auto
qed

end (* forcing_notion *)

subsection\<open>Towards Rasiowa-Sikorski Lemma (RSL)\<close>
locale countable_generic = forcing_notion +
  fixes \<D>
  assumes countable_subs_of_P:  "\<D> \<in> nat\<rightarrow>Pow(P)"
    and     seq_of_denses:        "\<forall>n \<in> nat. dense(\<D>`n)"

begin

definition
  D_generic :: "i\<Rightarrow>o" where
  "D_generic(G) \<equiv> filter(G) \<and> (\<forall>n\<in>nat.(\<D>`n)\<inter>G\<noteq>0)"

text\<open>The next lemma identifies a sufficient condition for obtaining
RSL.\<close>
lemma RS_sequence_imp_rasiowa_sikorski:
  assumes 
    "p\<in>P" "f : nat\<rightarrow>P" "f ` 0 = p"
    "\<And>n. n\<in>nat \<Longrightarrow> f ` succ(n)\<preceq> f ` n \<and> f ` succ(n) \<in> \<D> ` n" 
  shows
    "\<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  note assms
  moreover from this 
  have "f``nat  \<subseteq> P"
    by (simp add:subset_fun_image)
  moreover from calculation
  have "refl(f``nat, leq) \<and> trans[P](leq)"
    using leq_preord unfolding preorder_on_def by (blast intro:refl_monot_domain)
  moreover from calculation 
  have "\<forall>n\<in>nat.  f ` succ(n)\<preceq> f ` n" by (simp)
  moreover from calculation
  have "linear(f``nat, leq)"
    using leq_preord and decr_seq_linear unfolding preorder_on_def by (blast)
  moreover from calculation
  have "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"             
    using chain_compat by (auto)
  ultimately  
  have "filter(upclosure(f``nat))" (is "filter(?G)")
    using closure_compat_filter by simp
  moreover
  have "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume "n\<in>nat"
    with assms 
    have "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then 
    show "\<D> ` n \<inter> ?G \<noteq> 0"  by blast
  qed
  moreover from assms 
  have "p \<in> ?G"
    using aux_RS1 by auto
  ultimately 
  show ?thesis unfolding D_generic_def by auto
qed

end (* countable_generic *)

text\<open>Now, the following recursive definition will fulfill the 
requirements of lemma \<^term>\<open>RS_sequence_imp_rasiowa_sikorski\<close> \<close>

consts RS_seq :: "[i,i,i,i,i,i] \<Rightarrow> i"
primrec
  "RS_seq(0,P,leq,p,enum,\<D>) = p"
  "RS_seq(succ(n),P,leq,p,enum,\<D>) = 
    enum`(\<mu> m. \<langle>enum`m, RS_seq(n,P,leq,p,enum,\<D>)\<rangle> \<in> leq \<and> enum`m \<in> \<D> ` n)"

context countable_generic
begin

lemma preimage_rangeD:
  assumes "f\<in>Pi(A,B)" "b \<in> range(f)" 
  shows "\<exists>a\<in>A. f`a = b"
  using assms apply_equality[OF _ assms(1), of _ b] domain_type[OF _ assms(1)] by auto

lemma countable_RS_sequence_aux:
  fixes p enum
  defines "f(n) \<equiv> RS_seq(n,P,leq,p,enum,\<D>)"
    and   "Q(q,k,m) \<equiv> enum`m\<preceq> q \<and> enum`m \<in> \<D> ` k"
  assumes "n\<in>nat" "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
    "\<And>x k. x\<in>P \<Longrightarrow> k\<in>nat \<Longrightarrow>  \<exists>q\<in>P. q\<preceq> x \<and> q \<in> \<D> ` k" 
  shows 
    "f(succ(n)) \<in> P \<and> f(succ(n))\<preceq> f(n) \<and> f(succ(n)) \<in> \<D> ` n"
  using \<open>n\<in>nat\<close>
proof (induct)
  case 0
  from assms 
  obtain q where "q\<in>P" "q\<preceq> p" "q \<in> \<D> ` 0" by blast
  moreover from this and \<open>P \<subseteq> range(enum)\<close>
  obtain m where "m\<in>nat" "enum`m = q" 
    using preimage_rangeD[OF \<open>enum:nat\<rightarrow>M\<close>] by blast
  moreover 
  have "\<D>`0 \<subseteq> P"
    using apply_funtype[OF countable_subs_of_P] by simp
  moreover note \<open>p\<in>P\<close>
  ultimately
  show ?case 
    using LeastI[of "Q(p,0)" m] unfolding Q_def f_def by auto
next
  case (succ n)
  with assms 
  obtain q where "q\<in>P" "q\<preceq> f(succ(n))" "q \<in> \<D> ` succ(n)" by blast
  moreover from this and \<open>P \<subseteq> range(enum)\<close>
  obtain m where "m\<in>nat" "enum`m\<preceq> f(succ(n))" "enum`m \<in> \<D> ` succ(n)"
    using preimage_rangeD[OF \<open>enum:nat\<rightarrow>M\<close>] by blast
  moreover note succ
  moreover from calculation
  have "\<D>`succ(n) \<subseteq> P" 
    using apply_funtype[OF countable_subs_of_P] by auto
  ultimately
  show ?case
    using LeastI[of "Q(f(succ(n)),succ(n))" m] unfolding Q_def f_def by auto
qed

lemma countable_RS_sequence:
  fixes p enum
  defines "f \<equiv> \<lambda>n\<in>nat. RS_seq(n,P,leq,p,enum,\<D>)"
    and   "Q(q,k,m) \<equiv> enum`m\<preceq> q \<and> enum`m \<in> \<D> ` k"
  assumes "n\<in>nat" "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows 
    "f`0 = p" "f`succ(n)\<preceq> f`n \<and> f`succ(n) \<in> \<D> ` n" "f`succ(n) \<in> P"
proof -
  from assms
  show "f`0 = p" by simp
  {
    fix x k
    assume "x\<in>P" "k\<in>nat"
    then
    have "\<exists>q\<in>P. q\<preceq> x \<and> q \<in> \<D> ` k"
      using seq_of_denses apply_funtype[OF countable_subs_of_P] 
      unfolding dense_def by blast
  }
  with assms
  show "f`succ(n)\<preceq> f`n \<and> f`succ(n) \<in> \<D> ` n" "f`succ(n)\<in>P"
    unfolding f_def using countable_RS_sequence_aux by simp_all
qed

lemma RS_seq_type: 
  assumes "n \<in> nat" "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows "RS_seq(n,P,leq,p,enum,\<D>) \<in> P"
  using assms countable_RS_sequence(1,3)  
  by (induct;simp) 

lemma RS_seq_funtype:
  assumes "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows "(\<lambda>n\<in>nat. RS_seq(n,P,leq,p,enum,\<D>)): nat \<rightarrow> P"
  using assms lam_type RS_seq_type by auto

lemmas countable_rasiowa_sikorski = 
  RS_sequence_imp_rasiowa_sikorski[OF _ RS_seq_funtype countable_RS_sequence(1,2)]
end (* countable_generic *)

end
