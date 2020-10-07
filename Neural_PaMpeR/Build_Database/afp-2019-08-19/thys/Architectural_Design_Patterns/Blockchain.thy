(*
  Title:      Blockchain.thy
  Author:     Diego Marmsoler
*)
section "Blockchain Architectures"

theory Blockchain imports Auxiliary DynamicArchitectures.Dynamic_Architecture_Calculus RF_LTL
begin

subsection "Blockchains"
text \<open>
  A blockchain itself is modeled as a simple list.
\<close>

type_synonym 'a BC = "'a list"

abbreviation max_cond:: "('a BC) set \<Rightarrow> 'a BC \<Rightarrow> bool"
  where "max_cond B b \<equiv> b \<in> B \<and> (\<forall>b'\<in>B. length b' \<le> length b)"

no_syntax 
  "_MAX1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3MAX _./ _)" [0, 10] 10)
  "_MAX"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3MAX _:_./ _)" [0, 0, 10] 10)
  "_MAX1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3MAX _./ _)" [0, 10] 10)
  "_MAX"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3MAX _\<in>_./ _)" [0, 0, 10] 10)

definition MAX:: "('a BC) set \<Rightarrow> 'a BC"
  where "MAX B = (SOME b. max_cond B b)"

lemma max_ex:
  fixes XS::"('a BC) set"
  assumes "XS \<noteq> {}"
    and "finite XS"
  shows "\<exists>xs\<in>XS. (\<forall>ys\<in>XS. length ys \<le> length xs)"
proof (rule Finite_Set.finite_ne_induct)
  show "finite XS" using assms by simp
next
  from assms show "XS \<noteq> {}" by simp
next
  fix x::"'a BC"
  show "\<exists>xs\<in>{x}. \<forall>ys\<in>{x}. length ys \<le> length xs" by simp
next
  fix zs::"'a BC" and F::"('a BC) set"
  assume "finite F" and "F \<noteq> {}" and "zs \<notin> F" and "\<exists>xs\<in>F. \<forall>ys\<in>F. length ys \<le> length xs"
  then obtain xs where "xs\<in>F" and "\<forall>ys\<in>F. length ys \<le> length xs" by auto
  show "\<exists>xs\<in>insert zs F. \<forall>ys\<in>insert zs F. length ys \<le> length xs"
  proof (cases)
    assume "length zs \<ge> length xs"
    with \<open>\<forall>ys\<in>F. length ys \<le> length xs\<close> show ?thesis by auto
  next
    assume "\<not> length zs \<ge> length xs"
    hence "length zs \<le> length xs" by simp
    with \<open>xs \<in> F\<close> show ?thesis using \<open>\<forall>ys\<in>F. length ys \<le> length xs\<close> by auto
  qed
qed

lemma max_prop:
  fixes XS::"('a BC) set"
  assumes "XS \<noteq> {}"
    and "finite XS"
  shows "MAX XS \<in> XS"
    and "\<forall>b'\<in>XS. length b' \<le> length (MAX XS)"
proof -
  from assms have "\<exists>xs\<in>XS. \<forall>ys\<in>XS. length ys \<le> length xs" using max_ex[of XS] by auto
  with MAX_def[of XS] show "MAX XS \<in> XS" and "\<forall>b'\<in>XS. length b' \<le> length (MAX XS)"
    using someI_ex[of "\<lambda>b. b \<in> XS \<and> (\<forall>b'\<in>XS. length b' \<le> length b)"] by auto
qed

lemma max_less:
  fixes b::"'a BC" and b'::"'a BC" and B::"('a BC) set"
  assumes "b\<in>B"
    and "finite B"
    and "length b > length b'"
  shows "length (MAX B) > length b'"
proof -
  from assms have "\<exists>xs\<in>B. \<forall>ys\<in>B. length ys \<le> length xs" using max_ex[of B] by auto
  with MAX_def[of B] have "\<forall>b'\<in>B. length b' \<le> length (MAX B)"
    using someI_ex[of "\<lambda>b. b \<in> B \<and> (\<forall>b'\<in>B. length b' \<le> length b)"] by auto
  with \<open>b\<in>B\<close> have "length b \<le> length (MAX B)" by simp
  with \<open>length b > length b'\<close> show ?thesis by simp
qed

subsection "Blockchain Architectures"
text \<open>
  In the following we describe the locale for blockchain architectures.
\<close>

locale Blockchain = dynamic_component cmp active
  for active :: "'nid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and cmp :: "'nid \<Rightarrow> cnf \<Rightarrow> 'ND" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60) +
  fixes pin :: "'ND \<Rightarrow> ('nid BC) set"
    and pout :: "'ND \<Rightarrow> 'nid BC"
    and bc :: "'ND \<Rightarrow> 'nid BC"
    and mining :: "'ND \<Rightarrow> bool"
    and honest :: "'nid \<Rightarrow> bool"
    and actHn :: "cnf \<Rightarrow> 'nid set"
    and actDn :: "cnf \<Rightarrow> 'nid set"
    and PoW:: "trace \<Rightarrow> nat \<Rightarrow> nat"
    and hmining:: "trace \<Rightarrow> nat \<Rightarrow> bool"
    and dmining:: "trace \<Rightarrow> nat \<Rightarrow> bool"
    and cb:: nat
  defines "actHn k \<equiv> {nid. \<parallel>nid\<parallel>\<^bsub>k\<^esub> \<and> honest nid}"
    and "actDn k \<equiv> {nid. \<parallel>nid\<parallel>\<^bsub>k\<^esub> \<and> \<not> honest nid}"
    and "PoW t n \<equiv> (LEAST x. \<forall>nid\<in>actHn (t n). length (bc (\<sigma>\<^bsub>nid\<^esub>(t n))) \<le> x)"
    and "hmining t \<equiv> (\<lambda>n. \<exists>nid\<in>actHn (t n). mining (\<sigma>\<^bsub>nid\<^esub>(t n)))"
    and "dmining t \<equiv> (\<lambda>n. \<exists>nid\<in>actDn (t n). mining (\<sigma>\<^bsub>nid\<^esub>(t n)))"
  assumes consensus: "\<And>nid t t' bc'::('nid BC). \<lbrakk>honest nid\<rbrakk> \<Longrightarrow> eval nid t t' 0
    (\<box>\<^sub>b ([\<lambda>nd. bc' = (if (\<exists>b\<in>pin nd. length b > length (bc nd)) then (MAX (pin nd)) else (bc nd))]\<^sub>b
      \<longrightarrow>\<^sup>b \<circle>\<^sub>b [\<lambda>nd.(\<not> mining nd \<and> bc nd = bc' \<or> mining nd \<and> (\<exists>b. bc nd = bc' @ [b]))]\<^sub>b))"
    and attacker: "\<And>nid t t' bc'. \<lbrakk>\<not> honest nid\<rbrakk> \<Longrightarrow> eval nid t t' 0
    (\<box>\<^sub>b ([\<lambda>nd. bc' = (SOME b. b \<in> (pin nd \<union> {bc nd}))]\<^sub>b \<longrightarrow>\<^sup>b
      \<circle>\<^sub>b [\<lambda>nd.(\<not> mining nd \<and> prefix (bc nd) bc' \<or> mining nd \<and> (\<exists>b. bc nd = bc' @ [b]))]\<^sub>b))"
    and forward: "\<And>nid t t'. eval nid t t' 0 (\<box>\<^sub>b [\<lambda>nd. pout nd = bc nd]\<^sub>b)"
    \<comment> \<open>At each time point a node will forward its blockchain to the network\<close>
    and init: "\<And>nid t t'. eval nid t t' 0 [\<lambda>nd. bc nd=[]]\<^sub>b"
    and conn: "\<And>k nid. \<lbrakk>\<parallel>nid\<parallel>\<^bsub>k\<^esub>; honest nid\<rbrakk>
      \<Longrightarrow> pin (cmp nid k) = (\<Union>nid'\<in>actHn k. {pout (cmp nid' k)})"
    and act: "\<And>t n::nat. finite {nid::'nid. \<parallel>nid\<parallel>\<^bsub>t n\<^esub>}"
    and actHn: "\<And>t n::nat. \<exists>nid. honest nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<and> \<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>"
    and fair: "\<And>n n'. ccard n n' (dmining t) > cb \<Longrightarrow> ccard n n' (hmining t) > cb"
    and closed: "\<And>t nid b n::nat. \<lbrakk>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>; b \<in> pin (\<sigma>\<^bsub>nid\<^esub>(t n))\<rbrakk> \<Longrightarrow> \<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t n\<^esub> \<and> bc (\<sigma>\<^bsub>nid'\<^esub>(t n)) = b"
    and mine: "\<And>t nid n::nat. \<lbrakk>honest nid; \<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>; mining (\<sigma>\<^bsub>nid\<^esub>(t (Suc n)))\<rbrakk> \<Longrightarrow> \<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
begin

lemma init_model:
  assumes "\<not> (\<exists>n'. latestAct_cond nid t n n')"
    and "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
  shows "bc (\<sigma>\<^bsub>nid\<^esub>t n) = []"
proof -
  from assms(2) have "\<exists>i\<ge>0. \<parallel>nid\<parallel>\<^bsub>t i\<^esub>" by auto
  with init have "bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>0\<^esub>) = []" using baEA[of 0 nid t] by blast
  moreover from assms have "n=\<langle>nid \<rightarrow> t\<rangle>\<^bsub>0\<^esub>" using nxtAct_eq by simp
  ultimately show ?thesis by simp
qed

lemma fwd_bc:
  fixes nid and t::"nat \<Rightarrow> cnf" and t'::"nat \<Rightarrow> 'ND"
  assumes "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
  shows "pout (\<sigma>\<^bsub>nid\<^esub>t n) = bc (\<sigma>\<^bsub>nid\<^esub>t n)"
  using assms forward globEANow[THEN baEANow[of nid t t' n]] by blast

lemma finite_input:
  fixes t n nid
  assumes "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
  defines "dep nid' \<equiv> pout (\<sigma>\<^bsub>nid'\<^esub>(t n))"
  shows "finite (pin (cmp nid (t n)))"
proof -
  have "finite {nid'. \<parallel>nid'\<parallel>\<^bsub>t n\<^esub>}" using act by auto
  moreover have "pin (cmp nid (t n)) \<subseteq> dep ` {nid'. \<parallel>nid'\<parallel>\<^bsub>t n\<^esub>}"
  proof
    fix x assume "x \<in> pin (cmp nid (t n))"
    show "x \<in> dep ` {nid'. \<parallel>nid'\<parallel>\<^bsub>t n\<^esub>}"
    proof -
      from assms obtain nid' where "\<parallel>nid'\<parallel>\<^bsub>t n\<^esub>" and "bc (\<sigma>\<^bsub>nid'\<^esub>(t n)) = x"
        using closed \<open>x \<in> pin (cmp nid (t n))\<close> by blast
      hence "pout (\<sigma>\<^bsub>nid'\<^esub>(t n)) = x" using fwd_bc by auto
      hence "x=dep nid'" using dep_def by simp
      moreover from \<open>\<parallel>nid'\<parallel>\<^bsub>t n\<^esub>\<close> have "nid' \<in> {nid'. \<parallel>nid'\<parallel>\<^bsub>t n\<^esub>}" by simp
      ultimately show ?thesis using image_eqI by simp
    qed
  qed
  ultimately show ?thesis using finite_surj by metis
qed

lemma nempty_input:
  fixes t n nid
  assumes "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
    and "honest nid"
  shows "pin (cmp nid (t n))\<noteq>{}" using conn[of nid "t n"] act assms actHn_def by auto

lemma onlyone:
  assumes "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<exists>!i. \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
proof
  show "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
    by (metis assms dynamic_component.nxtActI latestAct_prop(1) latestAct_prop(2) less_le_trans order_refl)
next
  fix i
  show "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub> \<Longrightarrow> i = \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    by (metis latestActless(1) leI le_less_Suc_eq le_less_trans nxtActI order_refl)
qed

subsubsection "Component Behavior"

lemma bhv_hn_ex:
  fixes t and t'::"nat \<Rightarrow> 'ND" and tid
  assumes "honest tid"
    and "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
  shows "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) =
    Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and>
    (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])"
proof -
  let ?cond = "\<lambda>nd. MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) =
    (if (\<exists>b\<in>pin nd. length b > length (bc nd)) then (MAX (pin nd)) else (bc nd))"
  let ?check = "\<lambda>nd. \<not> mining nd \<and> bc nd = MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining nd \<and>
    (\<exists>b. bc nd = MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])"
  from \<open>honest tid\<close> have "eval tid t t' 0 (\<box>\<^sub>b([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b))"
    using consensus[of tid _ _ "MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"] by simp
  moreover from assms have "\<exists>i\<ge>0. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover have "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately have "eval tid t t' \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> ([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b)"
    using globEA[of 0 tid t t' "([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b)" "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by fastforce
  moreover have "eval tid t t' \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> [?cond]\<^sub>b"
  proof (rule baIA)
    from \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> show "\<exists>i\<ge>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" using latestAct_prop(1) by blast
    from assms(3) assms(4) show "?cond (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>)" using latestActNxt by simp
  qed
  ultimately have "eval tid t t' \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> (\<circle>\<^sub>b [?check]\<^sub>b)"
    using impE[of tid t t' _ "[?cond]\<^sub>b" "\<circle>\<^sub>b [?check]\<^sub>b"] by simp
  moreover have "\<exists>i>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
  proof -
    from assms have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" using latestActNxtAct by simp
    with assms(3) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using latestActNxt by simp
    moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"  using nxtActI by simp
    ultimately show ?thesis by auto
  qed
  moreover from assms have "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    using latestActNxtAct by (simp add: order.strict_implies_order)
  moreover from assms have "\<exists>!i. \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
    using onlyone by simp
  ultimately have "eval tid t t' \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> [?check]\<^sub>b"
    using nxtEA1[of tid t "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" t' "[?check]\<^sub>b" "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
  ultimately show ?thesis using baEANow[of tid t t' "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" ?check] by simp
qed

lemma bhv_hn_in:
  fixes t and t'::"nat \<Rightarrow> 'ND" and tid
  assumes "honest tid"
    and "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
  shows "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or>
    mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b])"
proof -
  let ?cond = "\<lambda>nd. bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) = (if (\<exists>b\<in>pin nd. length b > length (bc nd)) then (MAX (pin nd)) else (bc nd))"
  let ?check = "\<lambda>nd. \<not> mining nd \<and> bc nd = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> mining nd \<and> (\<exists>b. bc nd = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b])"
  from \<open>honest tid\<close> have "eval tid t t' 0 ((\<box>\<^sub>b([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b)))"
    using consensus[of tid _ _ "bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)"] by simp
  moreover from assms have "\<exists>i\<ge>0. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover have "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately have "eval tid t t' \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> ([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b)"
    using globEA[of 0 tid t t' "[?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b" "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by fastforce
  moreover have "eval tid t t' \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> [?cond]\<^sub>b"
  proof (rule baIA)
    from \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> show "\<exists>i\<ge>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" using latestAct_prop(1) by blast
    from assms(3) assms(4) show "?cond (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>)" using latestActNxt by simp
  qed
  ultimately have "eval tid t t' \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> (\<circle>\<^sub>b [?check]\<^sub>b)"
    using impE[of tid t t' _ "[?cond]\<^sub>b" "\<circle>\<^sub>b [?check]\<^sub>b"] by simp
  moreover have "\<exists>i>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
  proof -
    from assms have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" using latestActNxtAct by simp
    with assms(3) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using latestActNxt by simp
    moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"  using nxtActI by simp
    ultimately show ?thesis by auto
  qed
  moreover from assms have "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    using latestActNxtAct by (simp add: order.strict_implies_order)
  moreover from assms have "\<exists>!i. \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
    using onlyone by simp
  ultimately have "eval tid t t' \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> [?check]\<^sub>b"
    using nxtEA1[of tid t "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" t' "[?check]\<^sub>b" "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
  ultimately show ?thesis using baEANow[of tid t t' "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" ?check] by simp
qed

lemma bhv_hn_context:
  assumes "honest tid"
      and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
      and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    shows "\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>tid\<^esub>t n) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t n) = bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b]) \<or>
      \<not> mining (\<sigma>\<^bsub>tid\<^esub>t n) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t n) = bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
proof cases
  assume casmp: "\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
  moreover from assms(2) have "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  moreover from assms(3) have "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  ultimately have "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or>
    mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])"
    using assms(1) bhv_hn_ex by auto
  moreover from assms(2) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t n) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or>
    mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t n) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])" by simp
  moreover from assms(2) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t n) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t n) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or>
    mining (\<sigma>\<^bsub>tid\<^esub>t n) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t n) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])" by simp
  moreover have "Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<in> pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
  proof -
    from \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using latestAct_prop(1) by simp
    hence "finite (pin (\<sigma>\<^bsub>tid\<^esub>(t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" using finite_input[of tid t "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
    moreover from casmp obtain b where "b \<in> pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)" and "length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
    ultimately show ?thesis using max_prop(1) by auto
  qed
  with \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close>  obtain nid where "\<parallel>nid\<parallel>\<^bsub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
    and "bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using
    closed[of tid t "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" "MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"] latestAct_prop(1) by auto
  ultimately show ?thesis by auto
next
  assume "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
  moreover from assms(2) have "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  moreover from assms(3) have "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  ultimately have "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or>
    mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b])"
    using assms(1) bhv_hn_in[of tid n t] by auto
  moreover from assms(2) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t n) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t n) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or>
    mining (\<sigma>\<^bsub>tid\<^esub>t n) \<and> (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t n) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b])" by simp
  moreover from \<open>\<exists>n'. latestAct_cond tid t n n'\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
    using latestAct_prop(1) by simp
  ultimately show ?thesis by auto
qed

lemma bhv_dn:
  fixes t and t'::"nat \<Rightarrow> 'ND" and uid
  assumes "\<not> honest uid"
    and "\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)) (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)})
         \<or> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}) @ [b])"
proof -
  let ?cond = "\<lambda>nd. (SOME b. b \<in> (pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)})) = (SOME b. b \<in> pin nd \<union> {bc nd})"
  let ?check = "\<lambda>nd. \<not> mining nd \<and> prefix (bc nd) (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)})
    \<or> mining nd \<and> (\<exists>b. bc nd = (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}) @ [b])"
  from \<open>\<not> honest uid\<close> have "eval uid t t' 0 ((\<box>\<^sub>b([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b [?check]\<^sub>b)))"
    using attacker[of uid _ _ "(SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)})"]
    by simp
  moreover from assms have "\<exists>i\<ge>0. \<parallel>uid\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover have "\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately have "eval uid t t' \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> ([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b[?check]\<^sub>b)"
    using globEA[of 0 uid t t' "([?cond]\<^sub>b \<longrightarrow>\<^sup>b \<circle>\<^sub>b[?check]\<^sub>b)" "\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by fastforce
  moreover have "eval uid t t' \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> [?cond]\<^sub>b"
  proof (rule baIA)
    from \<open>\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> show "\<exists>i\<ge>\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>uid\<parallel>\<^bsub>t i\<^esub>" using latestAct_prop(1) by blast
    with assms(3) show "?cond (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>)" using latestActNxt by simp
  qed
  ultimately have "eval uid t t' \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> (\<circle>\<^sub>b [?check]\<^sub>b)"
    using impE[of uid t t' _ "[?cond]\<^sub>b" "\<circle>\<^sub>b [?check]\<^sub>b"] by simp
  moreover have "\<exists>i>\<langle>uid \<rightarrow> t\<rangle>\<^bsub>\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>. \<parallel>uid\<parallel>\<^bsub>t i\<^esub>"
  proof -
    from assms have "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" using latestActNxtAct by simp
    with assms(3) have "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>uid \<rightarrow> t\<rangle>\<^bsub>\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using latestActNxt by simp
    moreover from \<open>\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>uid\<parallel>\<^bsub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"  using nxtActI by simp
    ultimately show ?thesis by auto
  qed
  moreover from assms have "\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    using latestActNxtAct by (simp add: order.strict_implies_order)
  moreover from assms have "\<exists>!i. \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>uid\<parallel>\<^bsub>t i\<^esub>"
    using onlyone by simp
  ultimately have "eval uid t t' \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> [?check]\<^sub>b"
    using nxtEA1[of uid t "\<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" t' "[?check]\<^sub>b" "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  moreover from \<open>\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>uid\<parallel>\<^bsub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
  ultimately show ?thesis using baEANow[of uid t t' "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" ?check] by simp
qed

lemma bhv_dn_context:
  assumes "\<not> honest uid"
      and "\<parallel>uid\<parallel>\<^bsub>t n\<^esub>"
      and "\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> (\<exists>b. prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b]))
  \<or> \<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
proof -
  let ?bc="SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}"
  have bc_ex: "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> ?bc \<in> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}"
  proof -
    have "\<exists>b. b\<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}" by auto
    hence "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}" using someI_ex by simp
    thus ?thesis by auto
  qed

  from assms(2) have "\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>" by auto
  moreover from assms(3) have "\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>" by auto
  ultimately have "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)) ?bc \<or>
    mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = ?bc @ [b])"
    using bhv_dn[of uid n t] assms(1) by simp
  moreover from assms(2) have "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have casmp: "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) ?bc \<or>
    mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> (\<exists>b. bc (\<sigma>\<^bsub>uid\<^esub>t n) = ?bc @ [b])" by simp

  from bc_ex have "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> ?bc \<in> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}" .
  thus ?thesis
  proof
    assume "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
    moreover from \<open>\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>uid\<parallel>\<^bsub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using latestAct_prop(1) by simp
    ultimately obtain nid where "\<parallel>nid\<parallel>\<^bsub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) = ?bc"
      using closed by blast
    with casmp have "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or>
      mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> (\<exists>b. bc (\<sigma>\<^bsub>uid\<^esub>t n) = (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])" by simp
    with \<open>\<parallel>nid\<parallel>\<^bsub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> show ?thesis by auto
  next
    assume "?bc \<in> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)}"
    hence "?bc = bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)" by simp
    moreover from \<open>\<exists>n'. latestAct_cond uid t n n'\<close> have "\<parallel>uid\<parallel>\<^bsub>t \<langle>uid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
      using latestAct_prop(1) by simp
    ultimately show ?thesis using casmp by auto
  qed
qed

subsubsection "Maximal Honest Blockchains"

abbreviation mbc_cond:: "trace \<Rightarrow> nat \<Rightarrow> 'nid \<Rightarrow> bool"
  where "mbc_cond t n nid \<equiv> nid\<in>actHn (t n) \<and> (\<forall>nid'\<in>actHn (t n). length (bc (\<sigma>\<^bsub>nid'\<^esub>(t n))) \<le> length (bc (\<sigma>\<^bsub>nid\<^esub>(t n))))"

lemma mbc_ex:
  fixes t n
  shows "\<exists>x. mbc_cond t n x"
proof -
  let ?ALL="{b. \<exists>nid\<in>actHn (t n). b = bc (\<sigma>\<^bsub>nid\<^esub>(t n))}"
  have "MAX ?ALL \<in> ?ALL"
  proof (rule max_prop)
    from actHn have "actHn (t n) \<noteq> {}" using actHn_def by blast
    thus "?ALL\<noteq>{}" by auto
    from act have "finite (actHn (t n))" using actHn_def by simp
    thus "finite ?ALL" by simp
  qed
  then obtain nid where "nid \<in> actHn (t n) \<and> bc (\<sigma>\<^bsub>nid\<^esub>(t n)) = MAX ?ALL" by auto
  moreover have "\<forall>nid'\<in>actHn (t n). length (bc (\<sigma>\<^bsub>nid'\<^esub>(t n))) \<le> length (MAX ?ALL)"
  proof
    fix nid
    assume "nid \<in> actHn (t n)"
    hence "bc (\<sigma>\<^bsub>nid\<^esub>(t n)) \<in> ?ALL" by auto
    moreover have "\<forall>b'\<in>?ALL. length b' \<le> length (MAX ?ALL)"
    proof (rule max_prop)
      from \<open>bc (\<sigma>\<^bsub>nid\<^esub>(t n)) \<in> ?ALL\<close> show "?ALL\<noteq>{}" by auto
      from act have "finite (actHn (t n))" using actHn_def by simp
      thus "finite ?ALL" by simp
    qed
    ultimately show "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> length (Blockchain.MAX {b. \<exists>nid\<in>actHn (t n). b = bc (\<sigma>\<^bsub>nid\<^esub>t n)})" by simp
  qed
  ultimately show ?thesis by auto
qed

definition MBC:: "trace \<Rightarrow> nat \<Rightarrow> 'nid"
  where "MBC t n = (SOME b. mbc_cond t n b)"

lemma mbc_prop[simp]:
  shows "mbc_cond t n (MBC t n)"
  using someI_ex[OF mbc_ex] MBC_def by simp

subsubsection "Honest Proof of Work"
text \<open>
  An important construction is the maximal proof of work available in the honest community.
  The construction was already introduces in the locale itself since it was used to express some of the locale assumptions.
\<close>

abbreviation pow_cond:: "trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "pow_cond t n n' \<equiv> \<forall>nid\<in>actHn (t n). length (bc (\<sigma>\<^bsub>nid\<^esub>(t n))) \<le> n'"

lemma pow_ex:
  fixes t n
  shows "pow_cond t n (length (bc (\<sigma>\<^bsub>MBC t n\<^esub>(t n))))"
    and "\<forall>x'. pow_cond t n x' \<longrightarrow> x'\<ge>length (bc (\<sigma>\<^bsub>MBC t n\<^esub>(t n)))"
  using mbc_prop by auto

lemma pow_prop:
  "pow_cond t n (PoW t n)"
proof -
  from pow_ex have "pow_cond t n (LEAST x. pow_cond t n x)" using LeastI_ex[of "pow_cond t n"] by blast
  thus ?thesis using PoW_def by simp
qed 

lemma pow_eq:
  fixes n
  assumes "\<exists>tid\<in>actHn (t n). length (bc (\<sigma>\<^bsub>tid\<^esub>(t n))) = x"
    and "\<forall>tid\<in>actHn (t n). length (bc (\<sigma>\<^bsub>tid\<^esub>(t n))) \<le> x"
  shows "PoW t n = x"
proof -
  have "(LEAST x. pow_cond t n x) = x"
  proof (rule Least_equality)
    from assms(2) show "\<forall>nid\<in>actHn (t n). length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> x" by simp
  next
    fix y
    assume "\<forall>nid\<in>actHn (t n). length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> y"
    thus "x \<le> y" using assms(1) by auto
  qed
  with PoW_def show ?thesis by simp
qed

lemma pow_mbc:
  shows "length (bc (\<sigma>\<^bsub>MBC t n\<^esub>t n)) = PoW t n"
  by (metis mbc_prop pow_eq)

lemma pow_less:
  fixes t n nid
  assumes "pow_cond t n x"
  shows "PoW t n \<le> x"
proof -
  from pow_ex assms have "(LEAST x. pow_cond t n x) \<le> x" using Least_le[of "pow_cond t n"] by blast
  thus ?thesis using PoW_def by simp
qed

lemma pow_le_max:
  assumes "honest tid"
    and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
  shows "PoW t n \<le> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)))"
proof -
  from mbc_prop have "honest (MBC t n)" and "\<parallel>MBC t n\<parallel>\<^bsub>t n\<^esub>" using actHn_def by auto
  hence "pout (\<sigma>\<^bsub>MBC t n\<^esub>t n) = bc (\<sigma>\<^bsub>MBC t n\<^esub>t n)"
    using forward globEANow[THEN baEANow[of "MBC t n" t t' n "\<lambda>nd. pout nd = bc nd"]] by auto
  with assms \<open>\<parallel>MBC t n\<parallel>\<^bsub>t n\<^esub>\<close> \<open>honest (MBC t n)\<close> have "bc (\<sigma>\<^bsub>MBC t n\<^esub>t n) \<in> pin (\<sigma>\<^bsub>tid\<^esub>t n)"
    using conn actHn_def by auto
  moreover from assms (2) have "finite (pin (\<sigma>\<^bsub>tid\<^esub>t n))" using finite_input[of tid t n] by simp
  ultimately have "length (bc (\<sigma>\<^bsub>MBC t n\<^esub>t n)) \<le> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)))"
    using max_prop(2) by auto
  with pow_mbc show ?thesis by simp
qed

lemma pow_ge_lgth:
  assumes "honest tid"
    and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
  shows "length (bc (\<sigma>\<^bsub>tid\<^esub>t n)) \<le> PoW t n"
proof -
  from assms have "tid \<in> actHn (t n)" using actHn_def by simp
  thus ?thesis using pow_prop by simp
qed

lemma pow_le_lgth:
  assumes "honest tid"
    and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
    and "\<not>(\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t n)))"
  shows "length (bc (\<sigma>\<^bsub>tid\<^esub>t n)) \<ge> PoW t n"
proof -
  from assms (3) have "\<forall>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n). length b \<le> length (bc (\<sigma>\<^bsub>tid\<^esub>t n))" by auto
  moreover from assms nempty_input[of tid t n] finite_input[of tid t n]
  have "MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)) \<in> pin (\<sigma>\<^bsub>tid\<^esub>t n)" using max_prop(1)[of "pin (\<sigma>\<^bsub>tid\<^esub>t n)"] by simp
  ultimately have "length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n))) \<le> length (bc (\<sigma>\<^bsub>tid\<^esub>t n))" by simp
  moreover from assms have "PoW t n \<le> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)))" using pow_le_max by simp
  ultimately show ?thesis by simp
qed

lemma pow_mono:
  shows "n'\<ge>n \<Longrightarrow> PoW t n' \<ge> PoW t n"
proof (induction n' rule: dec_induct)
  case base
  then show ?case by simp
next
  case (step n')
  hence "PoW t n \<le> PoW t n'" by simp
  moreover have "PoW t (Suc n') \<ge> PoW t n'"
  proof -
    from actHn obtain tid where "honest tid" and "\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" and "\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>" by auto
    show ?thesis
    proof cases
      assume "\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n'). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t n'))"
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = Suc n'"
        using nxtAct_active by simp
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = n'"
        using latestAct_prop(2) latestActless le_less_Suc_eq by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<exists>n''<Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<exists>n''\<ge>Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by auto
      ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n')) \<or>
        (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n')) @ b)"
        using \<open>honest tid\<close> bhv_hn_ex[of tid "Suc n'" t] by auto
      hence "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<ge> length (Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n')))" by auto
      moreover from \<open>honest tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close>
        have "length (Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n'))) \<ge> PoW t n'" using pow_le_max by simp
      ultimately have "PoW t n' \<le> length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')))" by simp
      moreover from \<open>honest tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close>
        have "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<le> PoW t (Suc n')" using pow_ge_lgth by simp
      ultimately show ?thesis by simp
    next
      assume asmp: "\<not>(\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n'). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t n')))"
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = Suc n'"
        using nxtAct_active by simp
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = n'"
        using latestAct_prop(2) latestActless le_less_Suc_eq by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<exists>n''<Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<exists>n''\<ge>Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by auto
      ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = bc (\<sigma>\<^bsub>tid\<^esub>t n') \<or>
        (\<exists>b. bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = bc (\<sigma>\<^bsub>tid\<^esub>t n') @ b)"
        using \<open>honest tid\<close> bhv_hn_in[of tid "Suc n'" t] by auto
      hence "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<ge> length (bc (\<sigma>\<^bsub>tid\<^esub>t n'))" by auto
      moreover from \<open>honest tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> asmp have "length (bc (\<sigma>\<^bsub>tid\<^esub>t n')) \<ge> PoW t n'"
        using pow_le_lgth by simp
      moreover from \<open>honest tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close>
      have "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<le> PoW t (Suc n')" using pow_ge_lgth by simp
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show ?case by auto
qed

lemma pow_equals:
  assumes "PoW t n = PoW t n'"
  and "n'\<ge>n"
  and "n''\<ge>n"
  and "n''\<le>n'"
shows "PoW t n = PoW t n''" by (metis pow_mono assms(1) assms(3) assms(4) eq_iff)

lemma pow_mining_suc:
    assumes "hmining t (Suc n)"
    shows "PoW t n < PoW t (Suc n)"
proof -
  from assms obtain nid where "nid\<in>actHn (t (Suc n))" and "mining (\<sigma>\<^bsub>nid\<^esub>(t (Suc n)))"
    using hmining_def by auto
  show ?thesis
  proof cases
    assume asmp: "(\<exists>b\<in>pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>). length b > length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>)))"
    moreover from \<open>nid\<in>actHn (t (Suc n))\<close> have "honest nid" and "\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>"
      using actHn_def by auto
    moreover from \<open>honest nid\<close> \<open>mining (\<sigma>\<^bsub>nid\<^esub>(t (Suc n)))\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>\<close> have "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
      using mine by simp
    hence "\<exists>n'. latestAct_cond nid t (Suc n) n'" by auto
    ultimately have "\<not> mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) \<and> bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>)) \<or>
    mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>)) @ [b])" using bhv_hn_ex[of nid "Suc n"] by auto
    moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>\<close> have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub> = Suc n" using nxtAct_active by simp
    moreover have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub> = n"
    proof (rule latestActEq)
      from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>" by simp
      show "\<not> (\<exists>n''>n. n'' < Suc n \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub>)" by simp
      show "n < Suc n" by simp
    qed
    hence "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub> = n" using latestAct_def by simp
    ultimately have "\<not> mining (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) \<and> bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t n)) \<or>
    mining (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t n)) @ [b])" by simp
    with \<open>mining (\<sigma>\<^bsub>nid\<^esub>(t (Suc n)))\<close>
      have "\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t n)) @ [b]" by auto
    moreover from \<open>honest nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>\<close> have "length (bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n))) \<le> PoW t (Suc n)"
      using pow_ge_lgth[of nid t "Suc n"] by simp
    ultimately have "length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t (Suc n)" by auto
    moreover from \<open>honest nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t n))) \<ge> PoW t n"
      using pow_le_max by simp
    ultimately show ?thesis by simp
  next
    assume asmp: "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>). length b > length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>)))"
    moreover from \<open>nid\<in>actHn (t (Suc n))\<close> have "honest nid" and "\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>"
      using actHn_def by auto
    moreover from \<open>honest nid\<close> \<open>mining (\<sigma>\<^bsub>nid\<^esub>(t (Suc n)))\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>\<close> have "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
      using mine by simp
    hence "\<exists>n'. latestAct_cond nid t (Suc n) n'" by auto
    ultimately have "\<not> mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) \<and> bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) = bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>) \<or>
    mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub>) = bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub>) @ [b])"
      using bhv_hn_in[of nid "Suc n"] by auto
    moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>\<close> have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>Suc n\<^esub> = Suc n" using nxtAct_active by simp
    moreover have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub> = n"
    proof (rule latestActEq)
      from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>" by simp
      show "\<not> (\<exists>n''>n. n'' < Suc n \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub>)" by simp
      show "n < Suc n" by simp
    qed
    hence "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub> = n" using latestAct_def by simp
    ultimately have "\<not> mining (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) \<and> bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) = bc (\<sigma>\<^bsub>nid\<^esub>t n) \<or>
    mining (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) = bc (\<sigma>\<^bsub>nid\<^esub>t n) @ [b])" by simp
    with \<open>mining (\<sigma>\<^bsub>nid\<^esub>(t (Suc n)))\<close> have "\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n)) = bc (\<sigma>\<^bsub>nid\<^esub>t n) @ [b]" by simp
    moreover from \<open>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>Suc n\<^esub> = n\<close>
      have "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>nid\<^esub>t n). length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) < length b)"
      using asmp by simp
    with \<open>honest nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<ge> PoW t n"
      using pow_le_lgth[of nid t n] by simp
    moreover from \<open>honest nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>\<close> have "length (bc (\<sigma>\<^bsub>nid\<^esub>t (Suc n))) \<le> PoW t (Suc n)"
      using pow_ge_lgth[of nid t "Suc n"] by simp
    ultimately show ?thesis by auto
  qed
qed

subsubsection "History"
text \<open>
  In the following we introduce an operator which extracts the development of a blockchain up to a time point @{term n}.
\<close>

abbreviation "his_prop t n nid n' nid' x \<equiv>
  (\<exists>n. latestAct_cond nid' t n' n) \<and> \<parallel>snd x\<parallel>\<^bsub>t (fst x)\<^esub> \<and> fst x = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<and>
  (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) \<or>
    (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n'))))"

inductive_set 
his:: "trace \<Rightarrow> nat \<Rightarrow> 'nid \<Rightarrow> (nat \<times> 'nid) set"
  for t::trace and n::nat and nid::'nid 
  where "\<lbrakk>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<rbrakk> \<Longrightarrow> (n,nid) \<in> his t n nid"
  | "\<lbrakk>(n',nid') \<in> his t n nid; \<exists>x. his_prop t n nid n' nid' x\<rbrakk> \<Longrightarrow> (SOME x. his_prop t n nid n' nid' x) \<in> his t n nid"

lemma his_act:
  assumes "(n',nid') \<in> his t n nid"
  shows "\<parallel>nid'\<parallel>\<^bsub>t n'\<^esub>"
  using assms
proof (rule his.cases)
  assume "(n', nid') = (n, nid)" and "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
  thus "\<parallel>nid'\<parallel>\<^bsub>t n'\<^esub>" by simp
next
  fix n'' nid'' assume asmp: "(n', nid') = (SOME x. his_prop t n nid n'' nid'' x)"
  and "(n'', nid'') \<in> his t n nid" and "\<exists>x. his_prop t n nid n'' nid'' x"
  hence "his_prop t n nid n'' nid'' (SOME x. his_prop t n nid n'' nid'' x)"
    using someI_ex[of "\<lambda>x. his_prop t n nid n'' nid'' x"] by auto
  hence "\<parallel>snd (SOME x. his_prop t n nid n'' nid'' x)\<parallel>\<^bsub>t (fst (SOME x. his_prop t n nid n'' nid'' x))\<^esub>"
    by blast
  moreover from asmp have "fst (SOME x. his_prop t n nid n'' nid'' x) = fst (n', nid')" by simp
  moreover from asmp have "snd (SOME x. his_prop t n nid n'' nid'' x) = snd (n', nid')" by simp
  ultimately show ?thesis by simp
qed

text \<open>
  In addition we also introduce an operator to obtain the predecessor of a blockchains development.
\<close>

definition "hisPred"
  where "hisPred t n nid n' \<equiv> (GREATEST n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n')"

lemma hisPrev_prop:
  assumes "\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid"
  shows "hisPred t n nid n' < n'" and "\<exists>nid'. (hisPred t n nid n',nid')\<in> his t n nid"
proof -
  from assms obtain n'' where "\<exists>nid'. (n'',nid')\<in> his t n nid \<and> n''<n'" by auto
  moreover from \<open>\<exists>nid'. (n'',nid')\<in> his t n nid \<and> n''<n'\<close>
    have "\<exists>i'\<le>n'. (\<exists>nid'. (i', nid') \<in> his t n nid \<and> i' < n') \<and> (\<forall>n'a. (\<exists>nid'. (n'a, nid') \<in> his t n nid \<and> n'a < n') \<longrightarrow> n'a \<le> i')"
    using boundedGreatest[of "\<lambda>n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n'" n'' n'] by simp
  then obtain i' where "\<forall>n'a. (\<exists>nid'. (n'a, nid') \<in> his t n nid \<and> n'a < n') \<longrightarrow> n'a \<le> i'" by auto
  ultimately show "hisPred t n nid n' < n'" and "\<exists>nid'. (hisPred t n nid n',nid')\<in> his t n nid"
    using GreatestI_nat[of "\<lambda>n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n'" n'' i'] hisPred_def by auto
qed

lemma hisPrev_nex_less:
  assumes "\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid"
  shows "\<not>(\<exists>x\<in>his t n nid. fst x < n' \<and> fst x>hisPred t n nid n')"
proof (rule ccontr)
  assume "\<not>\<not>(\<exists>x\<in>his t n nid. fst x < n' \<and> fst x>hisPred t n nid n')"
  then obtain n'' nid'' where "(n'',nid'')\<in>his t n nid" and "n''< n'" and "n''>hisPred t n nid n'" by auto
  moreover have "n''\<le>hisPred t n nid n'"
  proof -
    from \<open>(n'',nid'')\<in>his t n nid\<close> \<open>n''< n'\<close> have "\<exists>nid'. (n'',nid')\<in> his t n nid \<and> n''<n'" by auto
    moreover from \<open>\<exists>nid'. (n'',nid')\<in> his t n nid \<and> n''<n'\<close> have "\<exists>i'\<le>n'. (\<exists>nid'. (i', nid') \<in> his t n nid \<and> i' < n') \<and> (\<forall>n'a. (\<exists>nid'. (n'a, nid') \<in> his t n nid \<and> n'a < n') \<longrightarrow> n'a \<le> i')"
      using boundedGreatest[of "\<lambda>n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n'" n'' n'] by simp
    then obtain i' where "\<forall>n'a. (\<exists>nid'. (n'a, nid') \<in> his t n nid \<and> n'a < n') \<longrightarrow> n'a \<le> i'" by auto
    ultimately show ?thesis using Greatest_le_nat[of "\<lambda>n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n'" n'' i'] hisPred_def by simp
  qed
  ultimately show False by simp
qed

lemma his_le:
  assumes "x \<in> his t n nid"
  shows "fst x\<le>n"
using assms
proof (induction rule: his.induct)
  case 1
  then show ?case by simp
next
  case (2 n' nid')
  moreover have "fst (SOME x. his_prop t n nid n' nid' x) \<le> n'"
  proof -
    from "2.hyps" have "\<exists>x. his_prop t n nid n' nid' x" by simp
    hence "his_prop t n nid n' nid' (SOME x. his_prop t n nid n' nid' x)"
      using someI_ex[of "\<lambda>x. his_prop t n nid n' nid' x"] by auto
    hence "fst (SOME x. his_prop t n nid n' nid' x) = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>" by force
    moreover from \<open>his_prop t n nid n' nid' (SOME x. his_prop t n nid n' nid' x)\<close>
    have "\<exists>n. latestAct_cond nid' t n' n" by simp
    ultimately show ?thesis using latestAct_prop(2)[of n' nid' t] by simp
  qed
  ultimately show ?case by simp
qed

lemma his_determ_base:
  shows "(n, nid') \<in> his t n nid \<Longrightarrow> nid'=nid"
proof (rule his.cases)
  assume "(n, nid') = (n, nid)"
  thus ?thesis by simp
next
  fix n' nid'a
  assume "(n, nid') \<in> his t n nid" and "(n, nid') = (SOME x. his_prop t n nid n' nid'a x)"
    and "(n', nid'a) \<in> his t n nid" and "\<exists>x. his_prop t n nid n' nid'a x"
  hence "his_prop t n nid n' nid'a (SOME x. his_prop t n nid n' nid'a x)"
    using someI_ex[of "\<lambda>x. his_prop t n nid n' nid'a x"] by auto
  hence "fst (SOME x. his_prop t n nid n' nid'a x) = \<langle>nid'a \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>" by force
  moreover from \<open>his_prop t n nid n' nid'a (SOME x. his_prop t n nid n' nid'a x)\<close>
    have "\<exists>n. latestAct_cond nid'a t n' n" by simp
  ultimately have "fst (SOME x. his_prop t n nid n' nid'a x) < n'"
    using latestAct_prop(2)[of n' nid'a t] by simp
  with \<open>(n, nid') = (SOME x. his_prop t n nid n' nid'a x)\<close> have "fst (n, nid')<n'" by simp
  hence "n<n'" by simp
  moreover from \<open>(n', nid'a) \<in> his t n nid\<close> have "n'\<le>n" using his_le by auto
  ultimately show "nid' = nid" by simp
qed

lemma hisPrev_same:
  assumes "\<exists>n'<n''. \<exists>nid'. (n',nid')\<in> his t n nid"
  and "\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid"
  and "(n',nid')\<in> his t n nid"
  and "(n'',nid'')\<in> his t n nid"
  and "hisPred t n nid n'=hisPred t n nid n''"
  shows "n'=n''"
proof (rule ccontr)
  assume "\<not> n'=n''"
  hence "n'>n'' \<or> n'<n''" by auto
  thus False
  proof
    assume "n'<n''"
    hence "fst (n',nid')<n''" by simp
    moreover from assms(2) have "hisPred t n nid n'<n'" using hisPrev_prop(1) by simp
    with assms have "hisPred t n nid n''<n'" by simp
    hence "hisPred t n nid n''<fst (n',nid')" by simp
    ultimately show False using hisPrev_nex_less[of n'' t n nid] assms by auto
  next (*Symmetric*)
    assume "n'>n''"
    hence "fst (n'',nid')<n'" by simp
    moreover from assms(1) have "hisPred t n nid n''<n''" using hisPrev_prop(1) by simp
    with assms have "hisPred t n nid n'<n''" by simp
    hence "hisPred t n nid n'<fst (n'',nid')" by simp
    ultimately show False using hisPrev_nex_less[of n' t n nid] assms by auto
  qed
qed

lemma his_determ_ext:
  shows "n'\<le>n \<Longrightarrow> (\<exists>nid'. (n',nid')\<in>his t n nid) \<Longrightarrow> (\<exists>!nid'. (n',nid')\<in>his t n nid) \<and>
    ((\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid) \<longrightarrow> (\<exists>x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x) \<and>
    (hisPred t n nid n', (SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x))"
proof (induction n' rule: my_induct)
  case base
  then obtain nid' where "(n, nid') \<in> his t n nid" by auto
  hence "\<exists>!nid'. (n, nid') \<in> his t n nid"
  proof
    fix nid'' assume "(n, nid'') \<in> his t n nid"
    with his_determ_base have "nid''=nid" by simp
    moreover from \<open>(n, nid') \<in> his t n nid\<close> have "nid'=nid" using his_determ_base by simp
    ultimately show "nid'' = nid'" by simp
  qed
  moreover have "(\<exists>n''<n. \<exists>nid'. (n'',nid')\<in> his t n nid) \<longrightarrow> (\<exists>x. his_prop t n nid n (THE nid'. (n,nid')\<in>his t n nid) x) \<and> (hisPred t n nid n, (SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n (THE nid'. (n,nid')\<in>his t n nid) x)"
  proof
    assume "\<exists>n''<n. \<exists>nid'. (n'',nid')\<in> his t n nid"
    hence "\<exists>nid'. (hisPred t n nid n, nid')\<in> his t n nid" using hisPrev_prop(2) by simp
    hence "(hisPred t n nid n, (SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid)) \<in> his t n nid"
      using someI_ex[of "\<lambda>nid'. (hisPred t n nid n, nid') \<in> his t n nid"] by simp
    thus "(\<exists>x. his_prop t n nid n (THE nid'. (n,nid')\<in>his t n nid) x) \<and>
      (hisPred t n nid n, (SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n (THE nid'. (n,nid')\<in>his t n nid) x)"
    proof (rule his.cases)
      assume "(hisPred t n nid n, SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid) = (n, nid)"
      hence "hisPred t n nid n=n" by simp
      with \<open>\<exists>n''<n. \<exists>nid'. (n'',nid')\<in> his t n nid\<close> show ?thesis using hisPrev_prop(1)[of n t n nid] by force
    next
      fix n'' nid'' assume asmp: "(hisPred t n nid n, SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid) = (SOME x. his_prop t n nid n'' nid'' x)"
      and "(n'', nid'') \<in> his t n nid" and "\<exists>x. his_prop t n nid n'' nid'' x"
      moreover have "n''=n"
      proof (rule antisym)
        show "n''\<ge>n"
        proof (rule ccontr)
          assume "(\<not>n''\<ge>n)"
          hence "n''<n" by simp
          moreover have "n''>hisPred t n nid n"
          proof -
            let ?x="\<lambda>x. his_prop t n nid n'' nid'' x"
            from \<open>\<exists>x. his_prop t n nid n'' nid'' x\<close> have "his_prop t n nid n'' nid'' (SOME x. ?x x)"
              using someI_ex[of ?x] by auto
            hence "n''>fst (SOME x. ?x x)" using latestAct_prop(2)[of n'' nid'' t] by force
            moreover from asmp have "fst (hisPred t n nid n, SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid) = fst (SOME x. ?x x)" by simp
            ultimately show ?thesis by simp
          qed
          moreover from \<open>\<exists>n''<n. \<exists>nid'. (n'',nid')\<in> his t n nid\<close>
            have "\<not>(\<exists>x\<in>his t n nid. fst x < n \<and> fst x > hisPred t n nid n)"
            using hisPrev_nex_less by simp
          ultimately show False using \<open>(n'', nid'') \<in> his t n nid\<close> by auto
        qed
      next
        from \<open>(n'', nid'') \<in> his t n nid\<close> show "n'' \<le> n" using his_le by auto
      qed
      ultimately have "(hisPred t n nid n, SOME nid'. (hisPred t n nid n, nid') \<in> his t n nid) = (SOME x. his_prop t n nid n nid'' x)" by simp
      moreover from \<open>n''=n\<close> \<open>(n'', nid'') \<in> his t n nid\<close> have "(n, nid'') \<in> his t n nid" by simp
      with \<open>\<exists>!nid'. (n,nid') \<in> his t n nid\<close> have "nid''=(THE nid'. (n,nid')\<in>his t n nid)"
        using the1_equality[of "\<lambda>nid'. (n, nid') \<in> his t n nid"] by simp
      moreover from \<open>\<exists>x. his_prop t n nid n'' nid'' x\<close> \<open>n''=n\<close> \<open>nid''=(THE nid'. (n,nid')\<in>his t n nid)\<close>
        have "\<exists>x. his_prop t n nid n (THE nid'. (n,nid')\<in>his t n nid) x" by simp
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show ?case by simp
next
  case (step n')
  then obtain nid' where "(n', nid') \<in> his t n nid" by auto
  hence "\<exists>!nid'. (n', nid') \<in> his t n nid"
  proof (rule his.cases)
    assume "(n', nid') = (n, nid)"
    hence "n'=n" by simp
    with step.hyps show ?thesis by simp
  next
    fix n'''' nid''''
    assume "(n'''', nid'''') \<in> his t n nid"
      and n'nid': "(n', nid') = (SOME x. his_prop t n nid n'''' nid'''' x)"
      and "(n'''', nid'''') \<in> his t n nid" and "\<exists>x. his_prop t n nid n'''' nid'''' x"
    from \<open>(n', nid') \<in> his t n nid\<close> show ?thesis
    proof
      fix nid'' assume "(n', nid'') \<in> his t n nid"
      thus "nid'' = nid'"
      proof (rule his.cases)
        assume "(n', nid'') = (n, nid)"
        hence "n'=n" by simp
        with step.hyps show ?thesis by simp
      next
        fix n''' nid'''
        assume "(n''', nid''') \<in> his t n nid"
          and n'nid'': "(n', nid'') = (SOME x. his_prop t n nid n''' nid''' x)"
          and "(n''', nid''') \<in> his t n nid" and "\<exists>x. his_prop t n nid n''' nid''' x"
        moreover have "n'''=n''''"
        proof -
          have "hisPred t n nid n''' = n'"
          proof -
            from n'nid'' \<open>\<exists>x. his_prop t n nid n''' nid''' x\<close>
              have "his_prop t n nid n''' nid''' (n',nid'')"
              using someI_ex[of "\<lambda>x. his_prop t n nid n''' nid''' x"] by auto
            hence "n'''>n'" using latestAct_prop(2) by simp
            moreover from \<open>(n''', nid''') \<in> his t n nid\<close> have "n'''\<le> n" using his_le by auto
            moreover from \<open>(n''', nid''') \<in> his t n nid\<close>
              have "\<exists>nid'. (n''', nid') \<in> his t n nid" by auto
            ultimately have "(\<exists>n'<n'''. \<exists>nid'. (n',nid')\<in> his t n nid) \<longrightarrow> (\<exists>!nid'. (n''',nid') \<in> his t n nid) \<and> (hisPred t n nid n''', (SOME nid'. (hisPred t n nid n''', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n''' (THE nid'. (n''',nid')\<in>his t n nid) x)" using step.IH by auto
            with \<open>n'''>n'\<close> \<open>(n', nid') \<in> his t n nid\<close> have "\<exists>!nid'. (n''',nid') \<in> his t n nid" and "(hisPred t n nid n''', (SOME nid'. (hisPred t n nid n''', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n''' (THE nid'. (n''',nid')\<in>his t n nid) x)" by auto
            moreover from \<open>\<exists>!nid'. (n''',nid') \<in> his t n nid\<close> \<open>(n''', nid''') \<in> his t n nid\<close> have "nid'''=(THE nid'. (n''',nid')\<in>his t n nid)" using the1_equality[of "\<lambda>nid'. (n''', nid') \<in> his t n nid"] by simp
            ultimately have "(hisPred t n nid n''', (SOME nid'. (hisPred t n nid n''', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n''' nid''' x)" by simp
            with n'nid'' have "(n', nid'') = (hisPred t n nid n''', (SOME nid'. (hisPred t n nid n''', nid') \<in> his t n nid))" by simp
            thus ?thesis by simp
          qed
          moreover have "hisPred t n nid n'''' = n'" (*Symmetric*)
          proof -
            from n'nid' \<open>\<exists>x. his_prop t n nid n'''' nid'''' x\<close> have "his_prop t n nid n'''' nid'''' (n',nid')"
              using someI_ex[of "\<lambda>x. his_prop t n nid n'''' nid'''' x"] by auto
            hence "n''''>n'" using latestAct_prop(2) by simp
            moreover from \<open>(n'''', nid'''') \<in> his t n nid\<close> have "n''''\<le> n" using his_le by auto
            moreover from \<open>(n'''', nid'''') \<in> his t n nid\<close>
              have "\<exists>nid'. (n'''', nid') \<in> his t n nid" by auto
            ultimately have "(\<exists>n'<n''''. \<exists>nid'. (n',nid')\<in> his t n nid) \<longrightarrow> (\<exists>!nid'. (n'''',nid') \<in> his t n nid) \<and> (hisPred t n nid n'''', (SOME nid'. (hisPred t n nid n'''', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n'''' (THE nid'. (n'''',nid')\<in>his t n nid) x)" using step.IH by auto
            with \<open>n''''>n'\<close> \<open>(n', nid') \<in> his t n nid\<close> have "\<exists>!nid'. (n'''',nid') \<in> his t n nid" and "(hisPred t n nid n'''', (SOME nid'. (hisPred t n nid n'''', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n'''' (THE nid'. (n'''',nid')\<in>his t n nid) x)" by auto
            moreover from \<open>\<exists>!nid'. (n'''',nid') \<in> his t n nid\<close> \<open>(n'''', nid'''') \<in> his t n nid\<close> have "nid''''=(THE nid'. (n'''',nid')\<in>his t n nid)" using the1_equality[of "\<lambda>nid'. (n'''', nid') \<in> his t n nid"] by simp
            ultimately have "(hisPred t n nid n'''', (SOME nid'. (hisPred t n nid n'''', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n'''' nid'''' x)" by simp
            with n'nid' have "(n', nid') = (hisPred t n nid n'''', (SOME nid'. (hisPred t n nid n'''', nid') \<in> his t n nid))" by simp
            thus ?thesis by simp
          qed
          ultimately have "hisPred t n nid n'''=hisPred t n nid n''''" ..
          moreover have "\<exists>n'<n'''. \<exists>nid'. (n',nid')\<in> his t n nid"
          proof -
            from n'nid'' \<open>\<exists>x. his_prop t n nid n''' nid''' x\<close> have "his_prop t n nid n''' nid''' (n',nid'')"
              using someI_ex[of "\<lambda>x. his_prop t n nid n''' nid''' x"] by auto
            hence "n'''>n'" using latestAct_prop(2) by simp
            with \<open>(n', nid') \<in> his t n nid\<close> show ?thesis by auto
          qed
          moreover have "\<exists>n'<n''''. \<exists>nid'. (n',nid')\<in> his t n nid"
          proof -
            from n'nid' \<open>\<exists>x. his_prop t n nid n'''' nid'''' x\<close> have "his_prop t n nid n'''' nid'''' (n',nid')"
              using someI_ex[of "\<lambda>x. his_prop t n nid n'''' nid'''' x"] by auto
            hence "n''''>n'" using latestAct_prop(2) by simp
            with \<open>(n', nid') \<in> his t n nid\<close> show ?thesis by auto
          qed
          ultimately show ?thesis
            using hisPrev_same \<open>(n''', nid''') \<in> his t n nid\<close> \<open>(n'''', nid'''') \<in> his t n nid\<close>
            by blast
        qed
        moreover have "nid'''=nid''''"
        proof -
          from n'nid'' \<open>\<exists>x. his_prop t n nid n''' nid''' x\<close>
            have "his_prop t n nid n''' nid''' (n',nid'')"
            using someI_ex[of "\<lambda>x. his_prop t n nid n''' nid''' x"] by auto
          hence "n'''>n'" using latestAct_prop(2) by simp
          moreover from \<open>(n''', nid''') \<in> his t n nid\<close> have "n'''\<le> n" using his_le by auto
          moreover from \<open>(n''', nid''') \<in> his t n nid\<close>
            have "\<exists>nid'. (n''', nid') \<in> his t n nid" by auto
          ultimately have "\<exists>!nid'. (n''', nid') \<in> his t n nid" using step.IH by auto
          with \<open>(n''', nid''') \<in> his t n nid\<close> \<open>(n'''', nid'''') \<in> his t n nid\<close> \<open>n'''=n''''\<close>
            show ?thesis by auto
        qed
        ultimately have "(n', nid') = (n', nid'')" using n'nid' by simp
        thus "nid'' = nid'" by simp
      qed
    qed
  qed
  moreover have "(\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid) \<longrightarrow> (\<exists>x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x) \<and> (hisPred t n nid n', (SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x)"
  proof
    assume "\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid"
    hence "\<exists>nid'. (hisPred t n nid n', nid')\<in> his t n nid" using hisPrev_prop(2) by simp
    hence "(hisPred t n nid n', (SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid)) \<in> his t n nid"
      using someI_ex[of "\<lambda>nid'. (hisPred t n nid n', nid') \<in> his t n nid"] by simp
    thus "(\<exists>x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x) \<and> (hisPred t n nid n', (SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x)"
    proof (rule his.cases)
      assume "(hisPred t n nid n', SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid) = (n, nid)"
      hence "hisPred t n nid n'=n" by simp
      moreover from \<open>\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close> have "hisPred t n nid n'<n'"
        using hisPrev_prop(1)[of n'] by force
      ultimately show ?thesis using step.hyps by simp
    next
      fix n'' nid'' assume asmp: "(hisPred t n nid n', SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid) = (SOME x. his_prop t n nid n'' nid'' x)"
      and "(n'', nid'') \<in> his t n nid" and "\<exists>x. his_prop t n nid n'' nid'' x"
      moreover have "n''=n'"
      proof (rule antisym)
        show "n''\<ge>n'"
        proof (rule ccontr)
          assume "(\<not>n''\<ge>n')"
          hence "n''<n'" by simp
          moreover have "n''>hisPred t n nid n'"
          proof -
            let ?x="\<lambda>x. his_prop t n nid n'' nid'' x"
            from \<open>\<exists>x. his_prop t n nid n'' nid'' x\<close> have "his_prop t n nid n'' nid'' (SOME x. ?x x)"
              using someI_ex[of ?x] by auto
            hence "n''>fst (SOME x. ?x x)" using latestAct_prop(2)[of n'' nid'' t] by force
            moreover from asmp have "fst (hisPred t n nid n', SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid) = fst (SOME x. ?x x)" by simp
            ultimately show ?thesis by simp
          qed
          moreover from \<open>\<exists>n''<n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close>
            have "\<not>(\<exists>x\<in>his t n nid. fst x < n' \<and> fst x > hisPred t n nid n')"
            using hisPrev_nex_less by simp
          ultimately show False using \<open>(n'', nid'') \<in> his t n nid\<close> by auto
        qed
      next
        show "n'\<ge>n''"
        proof (rule ccontr)
          assume "(\<not>n'\<ge>n'')"
          hence "n'<n''" by simp
          moreover from \<open>(n'', nid'') \<in> his t n nid\<close> have "n''\<le> n" using his_le by auto
          moreover from \<open>(n'', nid'') \<in> his t n nid\<close> have "\<exists>nid'. (n'', nid') \<in> his t n nid" by auto
          ultimately have "(\<exists>n'<n''. \<exists>nid'. (n',nid')\<in> his t n nid) \<longrightarrow> (\<exists>!nid'. (n'',nid') \<in> his t n nid) \<and> (hisPred t n nid n'', (SOME nid'. (hisPred t n nid n'', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n'' (THE nid'. (n'',nid')\<in>his t n nid) x)" using step.IH by auto
          with \<open>n'<n''\<close> \<open>(n', nid') \<in> his t n nid\<close> have "\<exists>!nid'. (n'',nid') \<in> his t n nid" and "(hisPred t n nid n'', (SOME nid'. (hisPred t n nid n'', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n'' (THE nid'. (n'',nid')\<in>his t n nid) x)" by auto
          moreover from \<open>\<exists>!nid'. (n'',nid') \<in> his t n nid\<close> \<open>(n'', nid'') \<in> his t n nid\<close>
            have "nid'' = (THE nid'. (n'',nid')\<in>his t n nid)"
            using the1_equality[of "\<lambda>nid'. (n'', nid') \<in> his t n nid"] by simp
          ultimately have "(hisPred t n nid n'', (SOME nid'. (hisPred t n nid n'', nid') \<in> his t n nid)) = (SOME x. his_prop t n nid n'' nid'' x)" by simp
          with asmp have "(hisPred t n nid n', SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid)=(hisPred t n nid n'', SOME nid'. (hisPred t n nid n'', nid') \<in> his t n nid)" by simp
          hence "hisPred t n nid n' = hisPred t n nid n''" by simp
          with \<open>\<exists>n''<n'. \<exists>nid'. (n'', nid') \<in> his t n nid\<close> \<open>n'<n''\<close> \<open>(n', nid') \<in> his t n nid\<close> \<open>(n'', nid'') \<in> his t n nid\<close> \<open>(n', nid') \<in> his t n nid\<close> have "n'=n''" using hisPrev_same by blast
          with \<open>n'<n''\<close> show False by simp
        qed
      qed
      ultimately have "(hisPred t n nid n', SOME nid'. (hisPred t n nid n', nid') \<in> his t n nid) = (SOME x. his_prop t n nid n' nid'' x)" by simp
      moreover from \<open>(n'', nid'') \<in> his t n nid\<close> \<open>n''=n'\<close> have "(n', nid'') \<in> his t n nid" by simp
      with \<open>\<exists>!nid'. (n',nid') \<in> his t n nid\<close> have "nid''=(THE nid'. (n',nid')\<in>his t n nid)"
        using the1_equality[of "\<lambda>nid'. (n', nid') \<in> his t n nid"] by simp
      moreover from \<open>\<exists>x. his_prop t n nid n'' nid'' x\<close> \<open>n''=n'\<close> \<open>nid''=(THE nid'. (n',nid')\<in>his t n nid)\<close>
        have "\<exists>x. his_prop t n nid n' (THE nid'. (n',nid')\<in>his t n nid) x" by simp
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show ?case by simp
qed

corollary his_determ_ex:
  assumes "(n',nid')\<in>his t n nid"
  shows "\<exists>!nid'. (n',nid')\<in>his t n nid"
  using assms his_le his_determ_ext[of n' n t nid] by force

corollary his_determ:
  assumes "(n',nid')\<in>his t n nid"
    and "(n',nid'')\<in>his t n nid"
  shows "nid'=nid''" using assms his_le his_determ_ext[of n' n t nid] by force

corollary his_determ_the:
  assumes "(n',nid')\<in>his t n nid"
  shows "(THE nid'. (n', nid')\<in>his t n nid) = nid'"
  using assms his_determ theI'[of "\<lambda>nid'. (n', nid')\<in>his t n nid"] his_determ_ex by simp

subsubsection "Blockchain Development"

definition devBC::"trace \<Rightarrow> nat \<Rightarrow> 'nid \<Rightarrow> nat \<Rightarrow> 'nid option"
  where "devBC t n nid n' \<equiv>
    (if (\<exists>nid'. (n', nid')\<in> his t n nid) then (Some (THE nid'. (n', nid')\<in>his t n nid))
    else Option.None)"

lemma devBC_some[simp]: assumes "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>" shows "devBC t n nid n = Some nid"
proof -
  from assms have "(n, nid)\<in> his t n nid" using his.intros(1) by simp
  hence "devBC t n nid n = (Some (THE nid'. (n, nid')\<in>his t n nid))" using devBC_def by auto
  moreover have "(THE nid'. (n, nid')\<in>his t n nid) = nid"
  proof
    from \<open>(n, nid)\<in> his t n nid\<close> show "(n, nid)\<in> his t n nid" .
  next
    fix nid' assume "(n, nid') \<in> his t n nid"
    thus "nid' = nid" using his_determ_base by simp
  qed
  ultimately show ?thesis by simp
qed

lemma devBC_act: assumes "\<not> Option.is_none (devBC t n nid n')" shows "\<parallel>the (devBC t n nid n')\<parallel>\<^bsub>t n'\<^esub>"
proof -
  from assms have "\<not> devBC t n nid n'=Option.None" by (metis is_none_simps(1))
  then obtain nid' where "(n', nid')\<in> his t n nid" and "devBC t n nid n' = (Some (THE nid'. (n', nid')\<in>his t n nid))"
    using devBC_def[of t n nid] by metis
  hence "nid'= (THE nid'. (n', nid')\<in>his t n nid)" using his_determ_the by simp
  with \<open>devBC t n nid n' = (Some (THE nid'. (n', nid')\<in>his t n nid))\<close> have "the (devBC t n nid n') = nid'" by simp
  with \<open>(n', nid')\<in> his t n nid\<close> show ?thesis using his_act by simp
qed

lemma his_ex:
  assumes "\<not>Option.is_none (devBC t n nid n')"
  shows "\<exists>nid'. (n',nid')\<in>his t n nid"
proof (rule ccontr)
  assume "\<not>(\<exists>nid'. (n',nid')\<in>his t n nid)"
  with devBC_def have "Option.is_none (devBC t n nid n')" by simp
  with assms show False by simp
qed

lemma devExt_nopt_leq:
  assumes "\<not>Option.is_none (devBC t n nid n')"
  shows "n'\<le>n"
proof -
  from assms have "\<exists>nid'. (n',nid')\<in>his t n nid" using his_ex by simp
  then obtain nid' where "(n',nid')\<in>his t n nid" by auto
  with his_le[of "(n',nid')"] show ?thesis by simp
qed

text \<open>
  An extended version of the development in which deactivations are filled with the last value.
\<close>

function devExt::"trace \<Rightarrow> nat \<Rightarrow> 'nid \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'nid BC"
  where "\<lbrakk>\<exists>n'<n\<^sub>s. \<not>Option.is_none (devBC t n nid n'); Option.is_none (devBC t n nid n\<^sub>s)\<rbrakk> \<Longrightarrow> devExt t n nid n\<^sub>s 0 = bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'. n'<n\<^sub>s \<and> \<not>Option.is_none (devBC t n nid n')))\<^esub>(t (GREATEST n'. n'<n\<^sub>s \<and> \<not>Option.is_none (devBC t n nid n'))))"
  | "\<lbrakk>\<not> (\<exists>n'<n\<^sub>s. \<not>Option.is_none (devBC t n nid n')); Option.is_none (devBC t n nid n\<^sub>s)\<rbrakk> \<Longrightarrow> devExt t n nid n\<^sub>s 0 = []"
  | "\<not> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> devExt t n nid n\<^sub>s 0 = bc (\<sigma>\<^bsub>the (devBC t n nid n\<^sub>s)\<^esub>(t n\<^sub>s))"
  | "\<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow> devExt t n nid n\<^sub>s (Suc n') = bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n')))"
  | "Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow> devExt t n nid n\<^sub>s (Suc n') = devExt t n nid n\<^sub>s n'"
proof -
  show "\<And>n\<^sub>s t n nid n\<^sub>s' ta na nida.
       \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<exists>n'<n\<^sub>s'. \<not> Option.is_none (devBC ta na nida n') \<Longrightarrow>
       Option.is_none (devBC ta na nida n\<^sub>s') \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', 0) \<Longrightarrow>
       bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n')))\<^esub>t (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n'))) =
       bc (\<sigma>\<^bsub>the (devBC ta na nida
                    (GREATEST n'. n' < n\<^sub>s' \<and> \<not> Option.is_none (devBC ta na nida n')))\<^esub>ta (GREATEST n'. n' < n\<^sub>s' \<and> \<not> Option.is_none (devBC ta na nida n')))" by auto
  show "\<And>n\<^sub>s t n nid n\<^sub>s' ta na nida.
       \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> (\<exists>n'<n\<^sub>s'. \<not> Option.is_none (devBC ta na nida n')) \<Longrightarrow>
       Option.is_none (devBC ta na nida n\<^sub>s') \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', 0) \<Longrightarrow>
       bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n')))\<^esub>t (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n'))) = []" by auto
  show "\<And>n\<^sub>s t n nid ta na nida n\<^sub>s'.
       \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> Option.is_none (devBC ta na nida n\<^sub>s') \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', 0) \<Longrightarrow>
       bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n')))\<^esub>t (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n'))) =
       bc (\<sigma>\<^bsub>the (devBC ta na nida n\<^sub>s')\<^esub>ta n\<^sub>s')" by auto
  show "\<And>n\<^sub>s t n nid ta na nida n\<^sub>s' n'.
       \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n')) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', Suc n') \<Longrightarrow>
       bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n')))\<^esub>t (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n'))) =
       bc (\<sigma>\<^bsub>the (devBC ta na nida (n\<^sub>s' + Suc n'))\<^esub>ta (n\<^sub>s' + Suc n'))" by auto
  show "\<And>n\<^sub>s t n nid ta na nida n\<^sub>s' n'.
       \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n')) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', Suc n') \<Longrightarrow>
       bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n')))\<^esub>t (GREATEST n'. n' < n\<^sub>s \<and> \<not> Option.is_none (devBC t n nid n'))) =
       devExt_sumC (ta, na, nida, n\<^sub>s', n')" by auto
  show"\<And>n\<^sub>s t n nid n\<^sub>s' ta na nida.
       \<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')) \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> (\<exists>n'<n\<^sub>s'. \<not> Option.is_none (devBC ta na nida n')) \<Longrightarrow>
       Option.is_none (devBC ta na nida n\<^sub>s') \<Longrightarrow> (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', 0) \<Longrightarrow> [] = []" by auto
  show "\<And>n\<^sub>s t n nid ta na nida n\<^sub>s'.
       \<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')) \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> Option.is_none (devBC ta na nida n\<^sub>s') \<Longrightarrow> (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', 0) \<Longrightarrow> [] = bc (\<sigma>\<^bsub>the (devBC ta na nida n\<^sub>s')\<^esub>ta n\<^sub>s')" by auto
  show "\<And>n\<^sub>s t n nid ta na nida n\<^sub>s' n'.
       \<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')) \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n')) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', Suc n') \<Longrightarrow> [] = bc (\<sigma>\<^bsub>the (devBC ta na nida (n\<^sub>s' + Suc n'))\<^esub>ta (n\<^sub>s' + Suc n'))" by auto
  show "\<And>n\<^sub>s t n nid ta na nida n\<^sub>s' n'.
       \<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')) \<Longrightarrow>
       Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n')) \<Longrightarrow> (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', Suc n') \<Longrightarrow> [] = devExt_sumC (ta, na, nida, n\<^sub>s', n')" by auto
  show "\<And>t n nid n\<^sub>s ta na nida n\<^sub>s'.
       \<not> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       \<not> Option.is_none (devBC ta na nida n\<^sub>s') \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', 0) \<Longrightarrow> bc (\<sigma>\<^bsub>the (devBC t n nid n\<^sub>s)\<^esub>t n\<^sub>s) = bc (\<sigma>\<^bsub>the (devBC ta na nida n\<^sub>s')\<^esub>ta n\<^sub>s')" by auto
  show "\<And>t n nid n\<^sub>s ta na nida n\<^sub>s' n'.
        \<not> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
        \<not> Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n')) \<Longrightarrow>
        (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', Suc n') \<Longrightarrow> bc (\<sigma>\<^bsub>the (devBC t n nid n\<^sub>s)\<^esub>t n\<^sub>s) = bc (\<sigma>\<^bsub>the (devBC ta na nida (n\<^sub>s' + Suc n'))\<^esub>ta (n\<^sub>s' + Suc n'))" by auto
  show "\<And>t n nid n\<^sub>s ta na nida n\<^sub>s' n'.
       \<not> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow>
       Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n')) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, 0) = (ta, na, nida, n\<^sub>s', Suc n') \<Longrightarrow> bc (\<sigma>\<^bsub>the (devBC t n nid n\<^sub>s)\<^esub>t n\<^sub>s) = devExt_sumC (ta, na, nida, n\<^sub>s', n')" by auto
  show "\<And>t n nid n\<^sub>s n' ta na nida n\<^sub>s' n'a.
       \<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow>
       \<not> Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n'a)) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, Suc n') = (ta, na, nida, n\<^sub>s', Suc n'a) \<Longrightarrow>
       bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>t (n\<^sub>s + Suc n')) = bc (\<sigma>\<^bsub>the (devBC ta na nida (n\<^sub>s' + Suc n'a))\<^esub>ta (n\<^sub>s' + Suc n'a))" by auto
  show "\<And>t n nid n\<^sub>s n' ta na nida n\<^sub>s' n'a.
       \<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow>
       Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n'a)) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, Suc n') = (ta, na, nida, n\<^sub>s', Suc n'a) \<Longrightarrow> bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>t (n\<^sub>s + Suc n')) = devExt_sumC (ta, na, nida, n\<^sub>s', n'a)" by auto
  show "\<And>t n nid n\<^sub>s n' ta na nida n\<^sub>s' n'a.
       Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow>
       Option.is_none (devBC ta na nida (n\<^sub>s' + Suc n'a)) \<Longrightarrow>
       (t, n, nid, n\<^sub>s, Suc n') = (ta, na, nida, n\<^sub>s', Suc n'a) \<Longrightarrow> devExt_sumC (t, n, nid, n\<^sub>s, n') = devExt_sumC (ta, na, nida, n\<^sub>s', n'a)" by auto
  show "\<And>P x. (\<And>n\<^sub>s t n nid. \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, 0) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>n\<^sub>s t n nid. \<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')) \<Longrightarrow> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, 0) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>t n nid n\<^sub>s. \<not> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, 0) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>t n nid n\<^sub>s n'. \<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, Suc n') \<Longrightarrow> P) \<Longrightarrow>
           (\<And>t n nid n\<^sub>s n'. Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, Suc n') \<Longrightarrow> P) \<Longrightarrow> P"
  proof -
    fix P::bool and x::"trace \<times>nat\<times>'nid\<times>nat\<times>nat"
    assume a1:"(\<And>n\<^sub>s t n nid. \<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n') \<Longrightarrow> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, 0) \<Longrightarrow> P)" and
           a2:"(\<And>n\<^sub>s t n nid. \<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')) \<Longrightarrow> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, 0) \<Longrightarrow> P)" and
           a3:"(\<And>t n nid n\<^sub>s. \<not> Option.is_none (devBC t n nid n\<^sub>s) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, 0) \<Longrightarrow> P)" and
           a4:"(\<And>t n nid n\<^sub>s n'. \<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, Suc n') \<Longrightarrow> P)" and
           a5:"(\<And>t n nid n\<^sub>s n'. Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<Longrightarrow> x = (t, n, nid, n\<^sub>s, Suc n') \<Longrightarrow> P)"
    show P
    proof (cases x)
      case (fields t n nid n\<^sub>s n')
      then show ?thesis
      proof (cases n')
        case 0
        then show ?thesis
        proof cases
          assume "Option.is_none (devBC t n nid n\<^sub>s)"
          thus ?thesis
          proof cases
            assume "\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n')"
            with \<open>x = (t, n , nid, n\<^sub>s, n')\<close> \<open>Option.is_none (devBC t n nid n\<^sub>s)\<close> \<open>n'=0\<close> show ?thesis using a1 by simp
          next
            assume "\<not> (\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t n nid n'))"
            with \<open>x = (t, n , nid, n\<^sub>s, n')\<close> \<open>Option.is_none (devBC t n nid n\<^sub>s)\<close> \<open>n'=0\<close> show ?thesis using a2 by simp
          qed
        next
          assume "\<not> Option.is_none (devBC t n nid n\<^sub>s)"
          with \<open>x = (t, n , nid, n\<^sub>s, n')\<close> \<open>n'=0\<close> show ?thesis using a3 by simp
        qed
      next
        case (Suc n'')
        then show ?thesis
        proof cases
          assume "Option.is_none (devBC t n nid (n\<^sub>s + Suc n''))"
          with \<open>x = (t, n , nid, n\<^sub>s, n')\<close> \<open>n'=Suc n''\<close> show ?thesis using a5[of t n nid n\<^sub>s n''] by simp
        next
          assume "\<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n''))"
          with \<open>x = (t, n , nid, n\<^sub>s, n')\<close> \<open>n'=Suc n''\<close> show ?thesis using a4[of t n nid n\<^sub>s n''] by simp
        qed
      qed
    qed
  qed
qed
termination by lexicographic_order

lemma devExt_same:
  assumes "\<forall>n'''>n'. n'''\<le>n'' \<longrightarrow> Option.is_none (devBC t n nid n''')"
    and "n'\<ge>n\<^sub>s"
    and "n'''\<le>n''"
  shows "n'''\<ge>n'\<Longrightarrow>devExt t n nid n\<^sub>s (n'''-n\<^sub>s) = devExt t n nid n\<^sub>s (n'-n\<^sub>s)"
proof (induction n''' rule: dec_induct)
  case base
  then show ?case by simp
next
  case (step n'''')
  hence "Suc n''''>n'" by simp
  moreover from step.hyps assms(3) have "Suc n''''\<le>n''" by simp
  ultimately have "Option.is_none (devBC t n nid (Suc n''''))" using assms(1) by simp
  moreover from assms(2) step.hyps have "n''''\<ge>n\<^sub>s" by simp
  hence "Suc n'''' = n\<^sub>s + Suc (n''''-n\<^sub>s)" by simp
  ultimately have "Option.is_none (devBC t n nid (n\<^sub>s + Suc (n''''-n\<^sub>s)))" by metis
  hence "devExt t n nid n\<^sub>s (Suc (n''''-n\<^sub>s)) = devExt t n nid n\<^sub>s (n''''-n\<^sub>s)" by simp
  moreover from \<open>n''''\<ge>n\<^sub>s\<close> have "Suc (n''''-n\<^sub>s) = Suc n''''-n\<^sub>s" by simp
  ultimately have "devExt t n nid n\<^sub>s (Suc n''''-n\<^sub>s) = devExt t n nid n\<^sub>s (n''''-n\<^sub>s)" by simp
  with step.IH show ?case by simp
qed

lemma devExt_bc[simp]:
  assumes "\<not> Option.is_none (devBC t n nid (n'+n''))"
  shows "devExt t n nid n' n'' = bc (\<sigma>\<^bsub>the (devBC t n nid (n'+n''))\<^esub>(t (n'+n'')))"
proof (cases n'')
  case 0
  with assms show ?thesis by simp
next
  case (Suc nat)
  with assms show ?thesis by simp
qed

lemma devExt_greatest:
  assumes "\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n''')"
    and "Option.is_none (devBC t n nid (n'+n''))" and "\<not> n''=0"
  shows "devExt t n nid n' n'' = bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n''')))\<^esub>(t (GREATEST n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n'''))))"
proof -
  let ?P="\<lambda>n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n''')"
  let ?G="GREATEST n'''. ?P n'''"
  have "\<forall>n'''>n'+n''. \<not> ?P n'''" by simp
  with \<open>\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n''')\<close> have "\<exists>n'''. ?P n''' \<and> (\<forall>n''''. ?P n'''' \<longrightarrow> n''''\<le>n''')" using boundedGreatest[of ?P] by blast
  hence "?P ?G" using GreatestI_ex_nat[of ?P] by auto
  hence "\<not>Option.is_none (devBC t n nid ?G)" by simp
  show ?thesis
  proof cases
    assume "?G>n'"
    hence "?G-n'+n' = ?G" by simp
    with \<open>\<not>Option.is_none (devBC t n nid ?G)\<close> have "\<not>Option.is_none (devBC t n nid (?G-n'+n'))" by simp
    moreover from \<open>?G>n'\<close> have "?G-n'\<noteq>0" by auto
    hence "\<exists>nat. Suc nat = ?G - n'" by presburger
    then obtain nat where "Suc nat = ?G-n'" by auto
    ultimately have "\<not>Option.is_none (devBC t n nid (n'+Suc nat))" by simp
    hence "devExt t n nid n' (Suc nat) = bc (\<sigma>\<^bsub>the (devBC t n nid (n' + Suc nat))\<^esub>t (n' + Suc nat))" by simp
    with \<open>Suc nat = ?G - n'\<close> have "devExt t n nid n' (?G - n') = bc (\<sigma>\<^bsub>the (devBC t n nid (?G-n'+n'))\<^esub>(t (?G-n'+n')))" by simp
    with \<open>?G-n'+n' = ?G\<close> have "devExt t n nid n' (?G - n') = bc (\<sigma>\<^bsub>the (devBC t n nid ?G)\<^esub>(t ?G))" by simp
    moreover have "devExt t n nid n' (n' + n'' - n') = devExt t n nid n' (?G - n')"
    proof -
      from \<open>\<exists>n'''. ?P n''' \<and> (\<forall>n''''. ?P n'''' \<longrightarrow> n''''\<le>n''')\<close> have "\<forall>n'''. ?P n''' \<longrightarrow> n'''\<le>?G"
        using Greatest_le_nat[of ?P] by blast
      hence "\<forall>n'''>?G. n'''<n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
      with \<open>Option.is_none (devBC t n nid (n'+n''))\<close>
        have "\<forall>n'''>?G. n'''\<le>n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
      moreover from \<open>?P ?G\<close> have "?G\<le>n'+n''" by simp
      moreover from \<open>?G>n'\<close> have "?G\<ge>n'" by simp
      ultimately show ?thesis using \<open>?G>n'\<close> devExt_same[of ?G "n'+n''" t n nid n' "n'+n''"] by blast
    qed
    ultimately show ?thesis by simp
  next
    assume "\<not>?G>n'"
    thus ?thesis
    proof cases
      assume "?G=n'"
      with \<open>\<not>Option.is_none (devBC t n nid ?G)\<close> have "\<not> Option.is_none (devBC t n nid n')" by simp
      with \<open>\<not>Option.is_none (devBC t n nid ?G)\<close> have "devExt t n nid n' 0 = bc (\<sigma>\<^bsub>the (devBC t n nid n')\<^esub>(t n'))" by simp
      moreover have "devExt t n nid n' n'' = devExt t n nid n' 0"
      proof -
        from \<open>\<exists>n'''. ?P n''' \<and> (\<forall>n''''. ?P n'''' \<longrightarrow> n''''\<le>n''')\<close> have "\<forall>n'''>?G. ?P n''' \<longrightarrow> n'''\<le>?G"
          using Greatest_le_nat[of ?P] by blast
        with \<open>?G=n'\<close> have "\<forall>n'''>n'. n''' < n' + n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by simp
        with \<open>Option.is_none (devBC t n nid (n'+n''))\<close>
          have "\<forall>n'''>n'. n'''\<le>n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
        moreover from \<open>\<not> n''=0\<close> have "n'<n'+n''" by simp
        ultimately show ?thesis using devExt_same[of n' "n'+n''" t n nid n' "n'+n''"] by simp
      qed
      ultimately show ?thesis using \<open>?G=n'\<close> by simp
    next
      assume "\<not>?G=n'"
      with \<open>\<not>?G>n'\<close> have "?G<n'" by simp
      hence "devExt t n nid n' n'' = devExt t n nid n' 0"
      proof -
        from \<open>\<exists>n'''. ?P n''' \<and> (\<forall>n''''. ?P n'''' \<longrightarrow> n''''\<le>n''')\<close> have "\<forall>n'''>?G. ?P n''' \<longrightarrow> n'''\<le>?G"
          using Greatest_le_nat[of ?P] by blast
        with \<open>\<not>?G>n'\<close> have "\<forall>n'''>n'. n'''<n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
        with \<open>Option.is_none (devBC t n nid (n'+n''))\<close>
          have "\<forall>n'''>n'. n'''\<le>n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
        moreover from \<open>?P ?G\<close> have "?G<n'+n''" by simp
        moreover from \<open>\<not> n''=0\<close> have "n'<n'+n''" by simp
        ultimately show ?thesis using devExt_same[of n' "n'+n''" t n nid n' "n'+n''"] by simp
      qed
      moreover have "devExt t n nid n' 0 = bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'''. n'''<n' \<and> \<not>Option.is_none (devBC t n nid n''')))\<^esub>(t (GREATEST n'''. n'''<n' \<and> \<not>Option.is_none (devBC t n nid n'''))))"
      proof -
        from \<open>\<not> n''=0\<close> have "n'<n'+n''" by simp
        moreover from \<open>\<exists>n'''. ?P n''' \<and> (\<forall>n''''. ?P n'''' \<longrightarrow> n''''\<le>n''')\<close> have "\<forall>n'''>?G. ?P n''' \<longrightarrow> n'''\<le>?G" using Greatest_le_nat[of ?P] by blast
        ultimately have "Option.is_none (devBC t n nid n')" using \<open>?G<n'\<close> by simp
        moreover from \<open>\<forall>n'''>?G. ?P n''' \<longrightarrow> n'''\<le>?G\<close> \<open>?G<n'\<close> \<open>n'<n'+n''\<close> have "\<forall>n'''\<ge>n'. n'''<n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
        have "\<exists>n'''<n'. \<not> Option.is_none (devBC t n nid n''')"
        proof -
          from \<open>\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n''')\<close> obtain n'''
            where "n'''<n'+n''" and "\<not> Option.is_none (devBC t n nid n''')" by auto
          moreover have "n'''<n'"
          proof (rule ccontr)
            assume "\<not>n'''<n'"
            hence "n'''\<ge>n'" by simp
            with \<open>\<forall>n'''\<ge>n'. n'''<n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')\<close> \<open>n'''<n'+n''\<close>
              \<open>\<not> Option.is_none (devBC t n nid n''')\<close> show False by simp
          qed
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis by simp
      qed
      moreover have "(GREATEST n'''. n'''<n' \<and> \<not>Option.is_none (devBC t n nid n''')) = ?G"
      proof(rule Greatest_equality)
        from \<open>?P ?G\<close> have "?G < n'+n''" and "\<not>Option.is_none (devBC t n nid ?G)" by auto
        with \<open>?G<n'\<close> show "?G < n' \<and> \<not> Option.is_none (devBC t n nid ?G)" by simp
      next
        fix y assume "y < n' \<and> \<not> Option.is_none (devBC t n nid y)"
        moreover from \<open>\<exists>n'''. ?P n''' \<and> (\<forall>n''''. ?P n'''' \<longrightarrow> n''''\<le>n''')\<close>
          have "\<forall>n'''. ?P n''' \<longrightarrow> n'''\<le>?G" using Greatest_le_nat[of ?P] by blast
        ultimately show "y \<le> ?G" by simp
      qed
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma devExt_shift: "devExt t n nid (n'+n'') 0 = devExt t n nid n' n''"
proof (cases)
  assume "n''=0"
  thus ?thesis by simp
next
  assume "\<not> (n''=0)"
  thus ?thesis
  proof (cases)
    assume "Option.is_none (devBC t n nid (n'+n''))"
    thus ?thesis
    proof cases
      assume "\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n''')"
      with \<open>Option.is_none (devBC t n nid (n'+n''))\<close> have "devExt t n nid (n'+n'') 0 = bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n''')))\<^esub>(t (GREATEST n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n'''))))" by simp
      moreover from \<open>\<not> (n''=0)\<close> \<open>Option.is_none (devBC t n nid (n'+n''))\<close> \<open>\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n''')\<close> have "devExt t n nid n' n'' = bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n''')))\<^esub>(t (GREATEST n'''. n'''<(n'+n'') \<and> \<not>Option.is_none (devBC t n nid n'''))))" using devExt_greatest by simp
      ultimately show ?thesis by simp
    next
      assume "\<not> (\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n'''))"
      with \<open>Option.is_none (devBC t n nid (n'+n''))\<close> have "devExt t n nid (n'+n'') 0=[]" by simp
      moreover have "devExt t n nid n' n''=[]"
      proof -
        from \<open>\<not> (\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n'''))\<close> \<open>n''\<noteq>0\<close>
          have "Option.is_none (devBC t n nid n')" by simp
        moreover from \<open>\<not> (\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n'''))\<close>
          have "\<not> (\<exists>n'''<n'. \<not> Option.is_none (devBC t n nid n'''))" by simp
        ultimately have "devExt t n nid n' 0=[]" by simp
        moreover have "devExt t n nid n' n''=devExt t n nid n' 0"
        proof -
          from \<open>\<not> (\<exists>n'''<n'+n''. \<not> Option.is_none (devBC t n nid n'''))\<close>
            have "\<forall>n'''>n'. n''' < n' + n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by simp
          with \<open>Option.is_none (devBC t n nid (n'+n''))\<close> 
            have "\<forall>n'''>n'. n'''\<le>n'+n'' \<longrightarrow> Option.is_none (devBC t n nid n''')" by auto
          moreover from \<open>\<not> n''=0\<close> have "n'<n'+n''" by simp
          ultimately show ?thesis using devExt_same[of n' "n'+n''" t n nid n' "n'+n''"] by simp
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
  next
    assume "\<not> Option.is_none (devBC t n nid (n'+n''))"
    hence "devExt t n nid (n'+n'') 0 = bc (\<sigma>\<^bsub>the (devBC t n nid (n'+n''))\<^esub>(t (n'+n'')))" by simp
    moreover from \<open>\<not> Option.is_none (devBC t n nid (n'+n''))\<close>
      have "devExt t n nid n' n'' = bc (\<sigma>\<^bsub>the (devBC t n nid (n'+n''))\<^esub>(t (n'+n'')))" by simp
    ultimately show ?thesis by simp
  qed
qed

lemma devExt_bc_geq:
  assumes "\<not> Option.is_none (devBC t n nid n')" and "n'\<ge>n\<^sub>s"
  shows "devExt t n nid n\<^sub>s (n'-n\<^sub>s) = bc (\<sigma>\<^bsub>the (devBC t n nid n')\<^esub>(t n'))" (is "?LHS = ?RHS")
proof -
  have "devExt t n nid n\<^sub>s (n'-n\<^sub>s) = devExt t n nid (n\<^sub>s+(n'-n\<^sub>s)) 0" using devExt_shift by auto
  moreover from assms(2) have "n\<^sub>s+(n'-n\<^sub>s) = n'" by simp
  ultimately have "devExt t n nid n\<^sub>s (n'-n\<^sub>s) = devExt t n nid n' 0" by simp
  with assms(1) show ?thesis by simp
qed

lemma his_bc_empty:
  assumes "(n',nid')\<in> his t n nid" and "\<not>(\<exists>n''<n'. \<exists>nid''. (n'',nid'')\<in> his t n nid)"
  shows "bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = []"
proof -
  have "\<not> (\<exists>x. his_prop t n nid n' nid' x)"
  proof (rule ccontr)
    assume "\<not> \<not> (\<exists>x. his_prop t n nid n' nid' x)"
    hence "\<exists>x. his_prop t n nid n' nid' x" by simp
    with \<open>(n',nid')\<in> his t n nid\<close> have "(SOME x. his_prop t n nid n' nid' x) \<in> his t n nid"
      using his.intros by simp
    moreover from \<open>\<exists>x. his_prop t n nid n' nid' x\<close> have "his_prop t n nid n' nid' (SOME x. his_prop t n nid n' nid' x)"
      using someI_ex[of "\<lambda>x. his_prop t n nid n' nid' x"] by auto
    hence "(\<exists>n. latestAct_cond nid' t n' n) \<and> fst (SOME x. his_prop t n nid n' nid' x) = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>"
      by force
    hence "fst (SOME x. his_prop t n nid n' nid' x) < n'" using latestAct_prop(2)[of n' nid' t] by force
    ultimately have "fst (SOME x. his_prop t n nid n' nid' x)<n' \<and>
      (fst (SOME x. his_prop t n nid n' nid' x),snd (SOME x. his_prop t n nid n' nid' x))\<in> his t n nid" by simp
    thus False using assms(2) by blast
  qed
  hence "\<forall>x. \<not> (\<exists>n. latestAct_cond nid' t n' n) \<or> \<not> \<parallel>snd x\<parallel>\<^bsub>t (fst x)\<^esub> \<or> \<not> fst x = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<or> \<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n'))))" by auto
  hence "\<not> (\<exists>n. latestAct_cond nid' t n' n) \<or> (\<exists>n. latestAct_cond nid' t n' n) \<and> (\<forall>x. \<not> \<parallel>snd x\<parallel>\<^bsub>t (fst x)\<^esub> \<or> \<not> fst x = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<or> \<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n')))))" by auto
  thus ?thesis
  proof
    assume "\<not> (\<exists>n. latestAct_cond nid' t n' n)"
    moreover from assms(1) have "\<parallel>nid'\<parallel>\<^bsub>t n'\<^esub>" using his_act by simp
    ultimately show ?thesis using init_model by simp
  next
    assume "(\<exists>n. latestAct_cond nid' t n' n) \<and> (\<forall>x. \<not> \<parallel>snd x\<parallel>\<^bsub>t (fst x)\<^esub> \<or> \<not> fst x = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<or> \<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n')))))"
    hence "\<exists>n. latestAct_cond nid' t n' n" and "\<forall>x. \<not> \<parallel>snd x\<parallel>\<^bsub>t (fst x)\<^esub> \<or> \<not> fst x = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<or> \<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n'))))" by auto
    hence asmp: "\<forall>x. \<parallel>snd x\<parallel>\<^bsub>t (fst x)\<^esub> \<longrightarrow> fst x = \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> \<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>snd x\<^esub>(t (fst x)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n'))))" by auto
    show ?thesis
    proof cases
      assume "honest nid'"
      moreover from assms(1) have "\<parallel>nid'\<parallel>\<^bsub>t n'\<^esub>" using his_act by simp
      ultimately obtain nid'' where "\<parallel>nid''\<parallel>\<^bsub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<^esub>" and "mining (\<sigma>\<^bsub>nid'\<^esub>t n') \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>t n') = bc (\<sigma>\<^bsub>nid''\<^esub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>) @ [b]) \<or> \<not> mining (\<sigma>\<^bsub>nid'\<^esub>t n') \<and> bc (\<sigma>\<^bsub>nid'\<^esub>t n') = bc (\<sigma>\<^bsub>nid''\<^esub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>)" using \<open>\<exists>n. latestAct_cond nid' t n' n\<close> bhv_hn_context[of nid' t n'] by auto
      moreover from \<open>\<parallel>nid''\<parallel>\<^bsub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<^esub>\<close> have "\<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>nid''\<^esub>(t (\<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>nid''\<^esub>(t (\<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n'))))" using asmp by auto
      ultimately have False by auto
      thus ?thesis ..
    next
      assume "\<not> honest nid'"
      moreover from assms(1) have "\<parallel>nid'\<parallel>\<^bsub>t n'\<^esub>" using his_act by simp
      ultimately obtain nid'' where "\<parallel>nid''\<parallel>\<^bsub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<^esub>" and "(mining (\<sigma>\<^bsub>nid'\<^esub>t n') \<and> (\<exists>b. prefix (bc (\<sigma>\<^bsub>nid'\<^esub>t n')) (bc (\<sigma>\<^bsub>nid''\<^esub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>) @ [b])) \<or> \<not> mining (\<sigma>\<^bsub>nid'\<^esub>t n') \<and> prefix (bc (\<sigma>\<^bsub>nid'\<^esub>t n')) (bc (\<sigma>\<^bsub>nid''\<^esub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>)))" using \<open>\<exists>n. latestAct_cond nid' t n' n\<close> bhv_dn_context[of nid' t n'] by auto
      moreover from \<open>\<parallel>nid''\<parallel>\<^bsub>t \<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<^esub>\<close> have "\<not> (prefix (bc (\<sigma>\<^bsub>nid'\<^esub>(t n'))) (bc (\<sigma>\<^bsub>nid''\<^esub>(t (\<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>nid'\<^esub>(t n')) = (bc (\<sigma>\<^bsub>nid''\<^esub>(t (\<langle>nid' \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>)))) @ [b] \<and> mining (\<sigma>\<^bsub>nid'\<^esub>(t n'))))" using asmp by auto
      ultimately have False by auto
      thus ?thesis ..
    qed
  qed
qed

lemma devExt_devop:
  "prefix (devExt t n nid n\<^sub>s (Suc n')) (devExt t n nid n\<^sub>s n') \<or> (\<exists>b. devExt t n nid n\<^sub>s (Suc n') = devExt t n nid n\<^sub>s n' @ [b]) \<and> \<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<and> \<parallel>the (devBC t n nid (n\<^sub>s + Suc n'))\<parallel>\<^bsub>t (n\<^sub>s + Suc n')\<^esub> \<and> n\<^sub>s + Suc n' \<le> n \<and> mining (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n')))"
proof cases
  assume "n\<^sub>s + Suc n' > n"
  hence "\<not>(\<exists>nid'. (n\<^sub>s + Suc n', nid') \<in> his t n nid)" using his_le by fastforce
  hence "Option.is_none (devBC t n nid (n\<^sub>s + Suc n'))" using devBC_def by simp
  hence "devExt t n nid n\<^sub>s (Suc n') = devExt t n nid n\<^sub>s n'" by simp
  thus ?thesis by simp
next
  assume "\<not>n\<^sub>s + Suc n' > n"
  hence "n\<^sub>s + Suc n' \<le> n" by simp
  show ?thesis
  proof cases
    assume "Option.is_none (devBC t n nid (n\<^sub>s + Suc n'))"
    hence "devExt t n nid n\<^sub>s (Suc n') = devExt t n nid n\<^sub>s n'" by simp
    thus ?thesis by simp
  next
    assume "\<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n'))"
    hence "devExt t n nid n\<^sub>s (Suc n') = bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n')))" by simp
    moreover have "prefix (bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n')))) (devExt t n nid n\<^sub>s n') \<or> (\<exists>b. bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n'))) = devExt t n nid n\<^sub>s n' @ [b] \<and> \<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n')) \<and> \<parallel>the (devBC t n nid (n\<^sub>s + Suc n'))\<parallel>\<^bsub>t (n\<^sub>s + Suc n')\<^esub> \<and> n\<^sub>s + Suc n' \<le> n \<and> mining (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n'))))"
    proof cases
      assume "\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid"
      let ?nid="(THE nid'. (n\<^sub>s + Suc n',nid')\<in>his t n nid)"
      let ?x="SOME x. his_prop t n nid (n\<^sub>s + Suc n') ?nid x"
      from \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n'))\<close>
        have "n\<^sub>s + Suc n'\<le>n" using devExt_nopt_leq by simp
      moreover from \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n'))\<close>
        have "\<exists>nid'. (n\<^sub>s + Suc n',nid')\<in>his t n nid" using his_ex by simp
      ultimately have "\<exists>x. his_prop t n nid (n\<^sub>s + Suc n') (THE nid'. ((n\<^sub>s + Suc n'),nid')\<in>his t n nid) x"
        and "(hisPred t n nid (n\<^sub>s + Suc n'), (SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)) = ?x"
        using \<open>\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close>
        his_determ_ext[of "n\<^sub>s + Suc n'" n t nid] by auto
      moreover have "bc (\<sigma>\<^bsub>(SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)\<^esub>(t (hisPred t n nid (n\<^sub>s + Suc n')))) = devExt t n nid n\<^sub>s n'"
      proof cases
        assume "Option.is_none (devBC t n nid (n\<^sub>s+n'))"
        have "devExt t n nid n\<^sub>s n' = bc (\<sigma>\<^bsub>the (devBC t n nid (GREATEST n''. n''<n\<^sub>s+n' \<and> \<not>Option.is_none (devBC t n nid n'')))\<^esub>(t (GREATEST n''. n''<n\<^sub>s+n' \<and> \<not>Option.is_none (devBC t n nid n''))))"
        proof cases
          assume "n'=0"
          moreover have "\<exists>n''<n\<^sub>s+n'. \<not>Option.is_none (devBC t n nid n'')"
          proof -
            from \<open>\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close> obtain n''
              where "n''<Suc n\<^sub>s + n'" and "\<exists>nid'. (n'',nid')\<in> his t n nid" by auto
            hence "\<not> Option.is_none (devBC t n nid n'')" using devBC_def by simp
            moreover from \<open>\<not> Option.is_none (devBC t n nid n'')\<close>
              \<open>Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close> have "\<not> n''=n\<^sub>s+n'" by auto
            with \<open>n''<Suc n\<^sub>s+n'\<close> have "n''<n\<^sub>s+n'" by simp
            ultimately show ?thesis by auto
          qed
          ultimately show ?thesis using \<open>Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close> by simp
        next
          assume "\<not> n'=0"
          moreover have "\<exists>n''<n\<^sub>s + n'. \<not> Option.is_none (devBC t n nid n'')"
          proof -
            from \<open>\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close> obtain n''
              where "n''<Suc n\<^sub>s + n'" and "\<exists>nid'. (n'',nid')\<in> his t n nid" by auto
            hence "\<not> Option.is_none (devBC t n nid n'')" using devBC_def by simp
            moreover from \<open>\<not> Option.is_none (devBC t n nid n'')\<close> \<open>Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close>
              have "\<not> n''=n\<^sub>s+n'" by auto
            with \<open>n''<Suc n\<^sub>s+n'\<close> have "n''<n\<^sub>s+n'" by simp
            ultimately show ?thesis by auto
          qed
          with \<open>\<not> (n'=0)\<close> \<open>Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close> show ?thesis
            using devExt_greatest[of n\<^sub>s n' t n nid] by simp
        qed
        moreover have "(GREATEST n''. n''<n\<^sub>s+n' \<and> \<not>Option.is_none (devBC t n nid n''))=hisPred t n nid (n\<^sub>s + Suc n')"
        proof -
          have "(\<lambda>n''. n''<n\<^sub>s+n' \<and> \<not>Option.is_none (devBC t n nid n'')) = (\<lambda>n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n\<^sub>s + Suc n')"
          proof
            fix n''
            show "(n'' < n\<^sub>s + n' \<and> \<not> Option.is_none (devBC t n nid n'')) = (\<exists>nid'. (n'', nid') \<in> his t n nid \<and> n'' < n\<^sub>s + Suc n')"
            proof
              assume "n'' < n\<^sub>s + n' \<and> \<not> Option.is_none (devBC t n nid n'')"
              thus "(\<exists>nid'. (n'', nid') \<in> his t n nid \<and> n'' < n\<^sub>s + Suc n')" using his_ex by simp
            next
              assume "(\<exists>nid'. (n'', nid') \<in> his t n nid \<and> n'' < n\<^sub>s + Suc n')"
              hence "\<exists>nid'. (n'', nid') \<in> his t n nid" and "n'' < n\<^sub>s + Suc n'" by auto
              hence "\<not> Option.is_none (devBC t n nid n'')" using devBC_def by simp
              moreover from \<open>\<not> Option.is_none (devBC t n nid n'')\<close> \<open>Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close>
              have "n''\<noteq>n\<^sub>s+n'" by auto
              with \<open>n'' < n\<^sub>s + Suc n'\<close> have "n'' < n\<^sub>s + n'" by simp
              ultimately show "n'' < n\<^sub>s + n' \<and> \<not> Option.is_none (devBC t n nid n'')" by simp
            qed
          qed
          hence "(GREATEST n''. n''<n\<^sub>s+n' \<and> \<not>Option.is_none (devBC t n nid n''))= (GREATEST n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n\<^sub>s + Suc n')" using arg_cong[of "\<lambda>n''. n''<n\<^sub>s+n' \<and> \<not>Option.is_none (devBC t n nid n'')" "(\<lambda>n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < n\<^sub>s + Suc n')"] by simp
          with hisPred_def show ?thesis by simp
        qed
        moreover have "the (devBC t n nid (hisPred t n nid (n\<^sub>s + Suc n')))=(SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)"
        proof -
          from \<open>\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close>
            have "\<exists>nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in> his t n nid"
            using hisPrev_prop(2) by simp
          hence "the (devBC t n nid (hisPred t n nid (n\<^sub>s + Suc n'))) = (THE nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in>his t n nid)"
            using devBC_def by simp
          moreover from \<open>\<exists>nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in> his t n nid\<close>
            have "(hisPred t n nid (n\<^sub>s + Suc n'), SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid) \<in> his t n nid"
            using someI_ex[of "\<lambda>nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in>his t n nid"] by simp
          hence "(THE nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in>his t n nid) = (SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)"
            using his_determ_the by simp
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      next
        assume "\<not> Option.is_none (devBC t n nid (n\<^sub>s+n'))"
        hence "devExt t n nid n\<^sub>s n' = bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s+n'))\<^esub>(t (n\<^sub>s+n')))"
        proof cases
          assume "n'=0"
          with \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close> show ?thesis by simp
        next
          assume "\<not> n'=0"
          hence "\<exists>nat. n' = Suc nat" by presburger
          then obtain nat where "n' = Suc nat" by auto
          with \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close> have "devExt t n nid n\<^sub>s (Suc nat) = bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc nat))\<^esub>(t (n\<^sub>s + Suc nat)))" by simp
          with \<open>n' = Suc nat\<close>  show ?thesis by simp
        qed
        moreover have "hisPred t n nid (n\<^sub>s + Suc n') = n\<^sub>s+n'"
        proof -
          have "(GREATEST n''. \<exists>nid'. (n'',nid')\<in> his t n nid \<and> n'' < (n\<^sub>s + Suc n')) = n\<^sub>s+n'"
          proof (rule Greatest_equality)
            from \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s+n'))\<close> have "\<exists>nid'. (n\<^sub>s + n', nid') \<in> his t n nid" using his_ex by simp
            thus "\<exists>nid'. (n\<^sub>s + n', nid') \<in> his t n nid \<and> n\<^sub>s + n' < n\<^sub>s + Suc n'" by simp
          next
            fix y assume "\<exists>nid'. (y, nid') \<in> his t n nid \<and> y < n\<^sub>s + Suc n'"
            thus "y \<le> n\<^sub>s + n'" by simp
          qed
          thus ?thesis using hisPred_def by simp
        qed
        moreover have "the (devBC t n nid (hisPred t n nid (n\<^sub>s + Suc n')))=(SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)"
        proof -
          from \<open>\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid\<close>
            have "\<exists>nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in> his t n nid"
            using hisPrev_prop(2) by simp
          hence "the (devBC t n nid (hisPred t n nid (n\<^sub>s + Suc n'))) = (THE nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in>his t n nid)"
            using devBC_def by simp
          moreover from \<open>\<exists>nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in> his t n nid\<close>
            have "(hisPred t n nid (n\<^sub>s + Suc n'), SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid) \<in> his t n nid"
            using someI_ex[of "\<lambda>nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in>his t n nid"] by simp
          hence "(THE nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid')\<in>his t n nid) = (SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)"
            using his_determ_the by simp
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      ultimately have "bc (\<sigma>\<^bsub>snd ?x\<^esub>(t (fst ?x))) = devExt t n nid n\<^sub>s n'"
        using fst_conv[of "hisPred t n nid (n\<^sub>s + Suc n')"
        "(SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)"]
        snd_conv[of "hisPred t n nid (n\<^sub>s + Suc n')"
        "(SOME nid'. (hisPred t n nid (n\<^sub>s + Suc n'), nid') \<in> his t n nid)"] by simp
      moreover from \<open>\<exists>x. his_prop t n nid (n\<^sub>s + Suc n') ?nid x\<close>
        have "his_prop t n nid (n\<^sub>s + Suc n') ?nid ?x"
        using someI_ex[of "\<lambda>x. his_prop t n nid (n\<^sub>s + Suc n') ?nid x"] by blast
      hence "prefix (bc (\<sigma>\<^bsub>?nid\<^esub>(t (n\<^sub>s + Suc n')))) (bc (\<sigma>\<^bsub>snd ?x\<^esub>(t (fst ?x)))) \<or> (\<exists>b. bc (\<sigma>\<^bsub>?nid\<^esub>(t (n\<^sub>s + Suc n'))) = (bc (\<sigma>\<^bsub>snd ?x\<^esub>(t (fst ?x)))) @ [b] \<and> mining (\<sigma>\<^bsub>?nid\<^esub>(t (n\<^sub>s + Suc n'))))" by blast
      ultimately have "prefix (bc (\<sigma>\<^bsub>?nid\<^esub>(t (n\<^sub>s + Suc n')))) (devExt t n nid n\<^sub>s n') \<or> (\<exists>b. bc (\<sigma>\<^bsub>?nid\<^esub>(t (n\<^sub>s + Suc n'))) = (devExt t n nid n\<^sub>s n') @ [b] \<and> mining (\<sigma>\<^bsub>?nid\<^esub>(t (n\<^sub>s + Suc n'))))" by simp
      moreover from \<open>\<exists>nid'. (n\<^sub>s + Suc n',nid')\<in> his t n nid\<close>
        have "?nid=the (devBC t n nid (n\<^sub>s + Suc n'))" using devBC_def by simp
      moreover have "\<parallel>the (devBC t n nid (n\<^sub>s + Suc n'))\<parallel>\<^bsub>t (n\<^sub>s + Suc n')\<^esub>"
      proof -
        from \<open>\<exists>nid'. (n\<^sub>s + Suc n',nid')\<in>his t n nid\<close> obtain nid'
          where "(n\<^sub>s + Suc n',nid')\<in>his t n nid" by auto
        with his_determ_the have "nid' = (THE nid'. (n\<^sub>s + Suc n', nid') \<in> his t n nid)" by simp
        with \<open>?nid=the (devBC t n nid (n\<^sub>s + Suc n'))\<close>
          have "the (devBC t n nid (n\<^sub>s + Suc n')) = nid'" by simp
        with \<open>(n\<^sub>s + Suc n',nid')\<in>his t n nid\<close> show ?thesis using his_act by simp
      qed
      ultimately show ?thesis
        using \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s+Suc n'))\<close> \<open>n\<^sub>s + Suc n' \<le> n\<close> by simp
    next
      assume "\<not> (\<exists>n''<n\<^sub>s + Suc n'. \<exists>nid'. (n'',nid')\<in> his t n nid)"
      moreover have "(n\<^sub>s + Suc n', the (devBC t n nid (n\<^sub>s + Suc n'))) \<in> his t n nid"
      proof -
        from \<open>\<not> Option.is_none (devBC t n nid (n\<^sub>s + Suc n'))\<close>
          have "\<exists>nid'. (n\<^sub>s + Suc n',nid')\<in>his t n nid" using his_ex by simp
        hence "the (devBC t n nid (n\<^sub>s + Suc n')) = (THE nid'. (n\<^sub>s + Suc n', nid') \<in> his t n nid)"
          using devBC_def by simp
        moreover from \<open>\<exists>nid'. (n\<^sub>s + Suc n',nid')\<in>his t n nid\<close> obtain nid'
          where "(n\<^sub>s + Suc n',nid')\<in>his t n nid" by auto
        with his_determ_the have "nid' = (THE nid'. (n\<^sub>s + Suc n', nid') \<in> his t n nid)" by simp
        ultimately have "the (devBC t n nid (n\<^sub>s + Suc n')) = nid'" by simp
        with \<open>(n\<^sub>s + Suc n',nid')\<in>his t n nid\<close> show ?thesis by simp
      qed
      ultimately have "bc (\<sigma>\<^bsub>the (devBC t n nid (n\<^sub>s + Suc n'))\<^esub>(t (n\<^sub>s + Suc n'))) = []"
        using his_bc_empty by simp
      thus ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

abbreviation devLgthBC where "devLgthBC t n nid n\<^sub>s \<equiv> (\<lambda>n'. length (devExt t n nid n\<^sub>s n'))"

theorem blockchain_save:
  fixes t::"nat\<Rightarrow>cnf" and n\<^sub>s and sbc and n
  assumes "\<forall>nid. honest nid \<longrightarrow> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t (\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>))))"
    and "\<forall>nid\<in>actDn (t n\<^sub>s). length (bc (\<sigma>\<^bsub>nid\<^esub>(t n\<^sub>s))) < length sbc"
    and "PoW t n\<^sub>s\<ge>length sbc + cb"
    and "\<forall>n'<n\<^sub>s. \<forall>nid. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<longrightarrow> length (bc (\<sigma>\<^bsub>nid\<^esub>t n')) < length sbc \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n')))"
    and "n\<ge>n\<^sub>s"
  shows "\<forall>nid \<in> actHn (t n). prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))"
proof (cases)
  assume "sbc=[]"
  thus ?thesis by simp
next
  assume "\<not> sbc=[]"
  have "n\<ge>n\<^sub>s \<Longrightarrow> \<forall>nid \<in> actHn (t n). prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))"
  proof (induction n rule: ge_induct)
    case (step n)
    show ?case
    proof
      fix nid assume "nid \<in> actHn (t n)"
      hence "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>" and "honest nid" using actHn_def by auto
      show "prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
      proof cases
        assume lAct: "\<exists>n' < n. n' \<ge> n\<^sub>s \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"    
        show ?thesis
        proof cases
          assume "\<exists>b\<in>pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
          moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "\<exists>n'\<ge>n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>" by auto
          moreover from lAct have "\<exists>n'. latestAct_cond nid t n n'" by auto
          ultimately have "\<not> mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or>
            mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [b])"
            using \<open>honest nid\<close> bhv_hn_ex[of nid n t] by simp
          moreover have "prefix sbc (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
          proof -
            from \<open>\<exists>n'. latestAct_cond nid t n n'\<close> have "\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
              using latestAct_prop(1) by simp
            hence "pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<noteq> {}" and "finite (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
              using nempty_input[of nid t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] finite_input[of nid t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] \<open>honest nid\<close> by auto
            hence "MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<in> pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)" using max_prop(1) by auto
            with \<open>\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> obtain nid' where "\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
              and "bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
              using closed[where b="MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"] by blast
            moreover have "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
            proof cases
              assume "honest nid'"
              with \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "nid' \<in> actHn (t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
                using actHn_def by simp
              moreover from \<open>\<exists>n'. latestAct_cond nid t n n'\<close> have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> < n"
                using latestAct_prop(2) by simp
              moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>s" using latestActless by blast
              ultimately show ?thesis using \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> step.IH by simp
            next
              assume "\<not> honest nid'"
              show ?thesis
              proof (rule ccontr)
                assume "\<not> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
                moreover have "\<exists>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'\<ge>n\<^sub>s \<and> length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' 0) < length sbc \<and> (\<forall>n''>n'. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'')))"
                proof cases
                  assume "\<exists>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'\<ge>n\<^sub>s \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<and> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))"
                  hence "\<exists>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'\<ge>n\<^sub>s \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<and> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')) \<and> (\<forall>n''>n'. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'')))"
                  proof -
                    let ?P="\<lambda>n'. n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> n'\<ge>n\<^sub>s  \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<and> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))"
                    from \<open>\<exists>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'\<ge>n\<^sub>s  \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<and> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))\<close> have "\<exists>n'. ?P n'" by simp
                    moreover have "\<forall>n'>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<not> ?P n'" by simp
                    ultimately obtain n' where "?P n'" and "\<forall>n''. ?P n'' \<longrightarrow> n''\<le>n'" using boundedGreatest[of ?P _ "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by auto
                    hence "\<forall>n''>n'. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by auto
                    thus ?thesis using \<open>?P n'\<close> by auto
                  qed
                  then obtain n' where "n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" and "\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')"
                    and "n'\<ge>n\<^sub>s" and "honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))"
                    and "\<forall>n''>n'. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by auto
                  hence "n'\<ge>n\<^sub>s" and dishonest: "\<forall>n''>n'. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by auto
                  moreover have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub><n" using \<open>\<exists>n'. latestAct_cond nid t n n'\<close> latestAct_prop(2) by blast
                  with \<open>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> have "n'<n" by simp
                  moreover from \<open>\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')\<close>
                    have "\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')\<parallel>\<^bsub>t n'\<^esub>" using devBC_act by simp
                  with \<open>honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))\<close>
                    have "the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<in>actHn (t n')" using actHn_def by simp
                  ultimately have "prefix sbc (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')\<^esub>t n'))"
                    using step.IH by simp
  
                  interpret ut: dishonest "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'" "\<lambda>n. dmining t (n' + n)"
                  proof
                    fix n''
                    from devExt_devop[of t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid' n'] have "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'') \<or> (\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]) \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n'')) \<and> \<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub> \<and> n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<^esub>t (n' + Suc n''))" .
                    thus "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'') \<or> (\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]) \<and> dmining t (n' + Suc n'')"
                    proof
                      assume "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'')"
                      thus ?thesis by simp
                    next
                      assume "(\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]) \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n'')) \<and> \<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub> \<and> n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<^esub>t (n' + Suc n''))"
                      hence "\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]" and "\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))" and "\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub>" and "n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" and "mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<^esub>t (n' + Suc n''))" by auto
                      moreover from \<open>n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> \<open>\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<close> have "\<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n'')))" using dishonest by simp
                      with \<open>\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub>\<close> have "the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<in>actDn (t (n' + Suc n''))" using actDn_def by simp
                      ultimately show ?thesis using dmining_def by auto
                    qed
                  qed
                  from \<open>\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')\<close> have "bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')\<^esub>t n') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' 0"
                    using devExt_bc_geq[of t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid' n'] by simp
                  moreover from \<open>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n')"
                    using devExt_bc_geq by simp
                  with \<open>\<not> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))\<close> have "\<not> prefix sbc (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n'))" by simp
                  ultimately have "\<exists>n'''. n''' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n' \<and> length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n''') < length sbc"
                    using \<open>prefix sbc (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')\<^esub>(t n')))\<close>
                    ut.prefix_length[of sbc 0 "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n'"] by auto
                  then obtain n\<^sub>p where "n\<^sub>p \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n'"
                    and "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n\<^sub>p) < length sbc" by auto
                  hence "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + n\<^sub>p) 0) < length sbc" using devExt_shift[of t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid' n' n\<^sub>p] by simp
                  moreover from \<open>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n'\<close> \<open>n\<^sub>p \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n'\<close> have "(n' + n\<^sub>p) \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
                  ultimately show ?thesis using \<open>n'\<ge>n\<^sub>s\<close> dishonest by auto
                next
                  assume "\<not>(\<exists>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'\<ge>n\<^sub>s \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<and> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')))"
                  hence cas: "\<forall>n'\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'\<ge>n\<^sub>s \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))" by auto
                  show ?thesis
                  proof cases
                    assume "Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)"
                    thus ?thesis
                    proof cases
                      assume "\<forall>n'<n\<^sub>s. Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')"
                      with \<open>Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<close> have "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0 = []" by simp
                      with \<open>\<not> sbc=[]\<close> have "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0) < length sbc" by simp
                      moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>s" using latestActless by blast
                      moreover from cas have "\<forall>n''>n\<^sub>s. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by simp
                      ultimately show ?thesis by auto
                    next
                      let ?P="\<lambda>n'. n'<n\<^sub>s \<and> \<not>Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')"
                      let ?n'="GREATEST n'. ?P n'"
                      assume "\<not> (\<forall>n'<n\<^sub>s. Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'))"
                      moreover have "\<forall>n'>n\<^sub>s. \<not> ?P n'" by simp
                      ultimately have exists: "\<exists>n'. ?P n' \<and> (\<forall>n''. ?P n''\<longrightarrow> n''\<le>n')"
                        using boundedGreatest[of ?P] by blast
                      hence "?P ?n'" using GreatestI_ex_nat[of ?P] by auto
                      moreover from \<open>?P ?n'\<close> have "\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<parallel>\<^bsub>t ?n'\<^esub>" using devBC_act by simp
                      ultimately have "length (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<^esub>t ?n')) < length sbc \<or> prefix sbc (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<^esub>(t ?n')))" using assms(4) by simp
                      thus ?thesis
                      proof
                        assume "length (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<^esub>t ?n')) < length sbc"
                        moreover from exists have "\<not>(\<exists>n'>?n'. ?P n')" using Greatest_ex_le_nat[of ?P] by simp
                        moreover from \<open>?P ?n'\<close> have "\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')" by blast
                        with \<open>Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<close>
                          have "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0 = bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<^esub>(t ?n'))" by simp
                        ultimately have "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0) < length sbc" by simp
                        moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>s" using latestActless by blast
                        moreover from cas have "\<forall>n''>n\<^sub>s. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by simp
                        ultimately show ?thesis by auto
                      next
                        interpret ut: dishonest "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s" "\<lambda>n. dmining t (n\<^sub>s + n)"
                        proof
                          fix n''
                          from devExt_devop[of t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid' n\<^sub>s] have "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'') \<or> (\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'' @ [b]) \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n'')) \<and> \<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<parallel>\<^bsub>t (n\<^sub>s + Suc n'')\<^esub> \<and> n\<^sub>s + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<^esub>t (n\<^sub>s + Suc n''))" .
                          thus "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'') \<or> (\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'' @ [b]) \<and> dmining t (n\<^sub>s + Suc n'')"
                          proof
                            assume "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'')" thus ?thesis by simp
                          next
                            assume "(\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'' @ [b]) \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n'')) \<and> \<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<parallel>\<^bsub>t (n\<^sub>s + Suc n'')\<^esub> \<and> n\<^sub>s + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<^esub>t (n\<^sub>s + Suc n''))"
                            hence "\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n'' @ [b]"
                              and "\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))"
                              and "\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<parallel>\<^bsub>t (n\<^sub>s + Suc n'')\<^esub>"
                              and "n\<^sub>s + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                              and "mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<^esub>t (n\<^sub>s + Suc n''))"
                              by auto
                            moreover from \<open>n\<^sub>s + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> \<open>\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<close>
                              have "\<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n'')))"
                              using cas by simp
                            with \<open>\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<parallel>\<^bsub>t (n\<^sub>s + Suc n'')\<^esub>\<close>
                              have "the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + Suc n''))\<in>actDn (t (n\<^sub>s + Suc n''))" using actDn_def by simp
                            ultimately show ?thesis using dmining_def by auto
                          qed
                        qed
  
                        assume "prefix sbc (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<^esub>(t ?n')))"
                        moreover from exists have "\<not>(\<exists>n'>?n'. ?P n')" using Greatest_ex_le_nat[of ?P] by simp
                        moreover from \<open>?P ?n'\<close> have "\<exists>n'<n\<^sub>s. \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n')" by blast
                        with \<open>Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<close> have "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0 = bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' ?n')\<^esub>(t ?n'))" by simp
                        ultimately have "prefix sbc (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0)" by simp
                        moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>s" using latestActless by blast
                        with \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s)" using devExt_bc_geq by simp
                        with \<open>\<not> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "\<not> prefix sbc (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s (\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s))" by simp
                        ultimately have "\<exists>n'''>0. n''' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s \<and> length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n''') < length sbc" using ut.prefix_length[of sbc 0 "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s"] by simp
                        then obtain n\<^sub>p where "n\<^sub>p>0" and "n\<^sub>p \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s" and "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s n\<^sub>p) < length sbc" by auto
                        hence "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n\<^sub>s + n\<^sub>p) 0) < length sbc" using devExt_shift by simp
                        moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>s" using latestActless by blast
                        with \<open>n\<^sub>p \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s\<close> have "(n\<^sub>s + n\<^sub>p) \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
                        moreover from \<open>n\<^sub>p \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n\<^sub>s\<close> have "n\<^sub>p \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
                        moreover have "\<forall>n''>n\<^sub>s + n\<^sub>p. n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" using cas by simp
                        ultimately show ?thesis by auto
                      qed
                    qed
                  next
                    assume asmp: "\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)"
                    moreover from lAct have "n\<^sub>s\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" using latestActless by blast
                    ultimately have "\<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s))" using cas by simp
                    moreover from asmp have "\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<parallel>\<^bsub>t n\<^sub>s\<^esub>"
                      using devBC_act by simp
                    ultimately have "the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<in>actDn (t n\<^sub>s)"
                      using actDn_def by simp
                    hence "length (bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<^esub>(t n\<^sub>s))) < length sbc"
                      using assms(2) by simp
                    moreover from asmp have
                      "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0 = bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s)\<^esub>(t n\<^sub>s))"
                      by simp
                    ultimately have "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n\<^sub>s 0) < length sbc" by simp
                    moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>s" using latestActless by blast
                    moreover from cas have "\<forall>n''>n\<^sub>s. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by simp
                    ultimately show ?thesis by auto
                  qed
                qed
                then obtain n' where "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n'" and "n'\<ge>n\<^sub>s"
                  and "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' 0) < length sbc"
                  and dishonest: "\<forall>n''>n'. n''\<le>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'') \<longrightarrow> \<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n''))" by auto
                interpret ut: dishonest "devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'" "\<lambda>n. dmining t (n' + n)"
                proof
                  fix n''
                  from devExt_devop[of t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid' n']
                  have "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'') \<or>
                    (\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]) \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n'')) \<and> \<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub> \<and> n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<^esub>t (n' + Suc n''))" .
                  thus "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'')
                    \<or> (\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]) \<and> dmining t (n' + Suc n'')"
                  proof
                    assume "prefix (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'')) (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'')"
                    thus ?thesis by simp
                  next
                    assume "(\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]) \<and> \<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n'')) \<and> \<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub> \<and> n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<^esub>t (n' + Suc n''))"
                    hence "\<exists>b. devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (Suc n'') = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' n'' @ [b]"
                      and "\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))"
                      and "\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub>"
                      and "n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                      and "mining (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<^esub>t (n' + Suc n''))"
                      by auto
                    moreover from \<open>n' + Suc n'' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> \<open>\<not> Option.is_none (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<close>
                      have "\<not> honest (the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n'')))" using dishonest by simp
                    with \<open>\<parallel>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<parallel>\<^bsub>t (n' + Suc n'')\<^esub>\<close>
                      have "the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' (n' + Suc n''))\<in>actDn (t (n' + Suc n''))"
                      using actDn_def by simp
                    ultimately show ?thesis using dmining_def by auto
                  qed
                qed
                interpret dishonest_growth "devLgthBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'" "\<lambda>n. dmining t (n' + n)"
                  by unfold_locales
                interpret honest_growth "\<lambda>n. PoW t (n' + n)" "\<lambda>n. hmining t (n' + n)"
                proof
                  show "\<And>n. PoW t (n' + n) \<le> PoW t (n' + Suc n)" using pow_mono by simp
                  show "\<And>n. hmining t (n' + Suc n) \<Longrightarrow> PoW t (n' + n) < PoW t (n' + Suc n)"
                    using pow_mining_suc by simp
                qed
                interpret bg: bounded_growth "length sbc" "\<lambda>n. PoW t (n' + n)" "devLgthBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n'" "\<lambda>n. hmining t (n' + n)" "\<lambda>n. dmining t (n' + n)" "length sbc" cb
                proof
                  from assms(3) \<open>n'\<ge>n\<^sub>s\<close> show "length sbc + cb \<le> PoW t (n' + 0)" using pow_mono[of n\<^sub>s n' t] by simp
                next
                  from \<open>length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' 0) < length sbc\<close> show "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' 0) < length sbc" .
                next
                  fix n'' n'''
                  assume "cb < card {i. n'' < i \<and> i \<le> n''' \<and> dmining t (n' + i)}"
                  hence "cb < card {i. n'' + n' < i \<and> i \<le> n''' + n' \<and> dmining t i}"
                    using cardshift[of n'' n''' "dmining t" n'] by simp
                  with fair[of "n'' + n'" "n''' + n'" t]
                  have "cb < card {i. n'' + n' < i \<and> i \<le> n''' + n' \<and> hmining t i}" by simp
                  thus "cb < card {i. n'' < i \<and> i \<le> n''' \<and> hmining t (n' + i)}"
                    using cardshift[of n'' n''' "hmining t" n'] by simp
                qed
                from \<open>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n'\<close> have "length (devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n')) < PoW t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                  using bg.hn_upper_bound[of "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n'"] by simp
                moreover from \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> \<open>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n'\<close>
                  have "bc (\<sigma>\<^bsub>the (devBC t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) = devExt t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> nid' n' (\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>-n')"
                  using devExt_bc_geq[of t "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid' "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>" n'] by simp
                ultimately have "length (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                  using \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> by simp
                moreover have "PoW t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> length (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" (is "?lhs \<le> ?rhs")
                proof -
                  from \<open>honest nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close>
                    have "?lhs \<le> length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" using pow_le_max by simp
                  also from \<open>bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)) = MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))\<close>
                    have "\<dots> = length (bc (\<sigma>\<^bsub>nid'\<^esub>(t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" by simp
                  finally show ?thesis .
                qed
                ultimately show False by simp
              qed
            qed
            moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>=n" using nxtAct_active by simp
            ultimately show ?thesis by auto
          qed
          moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>=n" using nxtAct_active by simp
          ultimately show ?thesis by auto
        next
          assume "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
          moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "\<exists>n'\<ge>n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>" by auto
          moreover from lAct have "\<exists>n'. latestAct_cond nid t n n'" by auto
          ultimately have "\<not> mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or>
            mining (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> (\<exists>b. bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [b])"
            using \<open>honest nid\<close> bhv_hn_in[of nid n t] by simp
          moreover have "prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
          proof -
            from \<open>\<exists>n'. latestAct_cond nid t n n'\<close> have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> < n" using latestAct_prop(2) by simp
            moreover from lAct have "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>s" using latestActless by blast
            moreover from \<open>\<exists>n'. latestAct_cond nid t n n'\<close> have "\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
              using latestAct_prop(1) by simp
            with \<open>honest nid\<close> have "nid \<in> actHn (t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>)" using actHn_def by simp
            ultimately show ?thesis using step.IH by auto
          qed
          moreover from \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>=n" using nxtAct_active by simp
          ultimately show ?thesis by auto
        qed
      next
        assume nAct: "\<not> (\<exists>n' < n. n' \<ge> n\<^sub>s \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>)"
        moreover from step.hyps have "n\<^sub>s \<le> n" by simp
        ultimately have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub> = n" using \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> nxtAct_eq[of n\<^sub>s n nid t] by simp
        with \<open>honest nid\<close> show ?thesis using assms(1) by auto
      qed
    qed
  qed
  with assms(5) show ?thesis by simp
qed

end

end