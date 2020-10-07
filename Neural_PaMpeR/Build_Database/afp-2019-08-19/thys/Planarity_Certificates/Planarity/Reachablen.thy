section \<open>$n$-step reachability\<close>

theory Reachablen
imports
  Graph_Theory.Graph_Theory
begin

inductive
  ntrancl_onp :: "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for F :: "'a set" and r :: "'a rel"
where
    ntrancl_on_0: "a = b \<Longrightarrow> a \<in> F \<Longrightarrow> ntrancl_onp F r 0 a b"
  | ntrancl_on_Suc: "(a,b) \<in> r \<Longrightarrow> ntrancl_onp F r n b c \<Longrightarrow> a \<in> F \<Longrightarrow> ntrancl_onp F r (Suc n) a c"

lemma ntrancl_onpD_rtrancl_on:
  assumes "ntrancl_onp F r n a b" shows "(a,b) \<in> rtrancl_on F r"
  using assms by induct (auto intro: converse_rtrancl_on_into_rtrancl_on)

lemma rtrancl_onE_ntrancl_onp:
  assumes "(a,b) \<in> rtrancl_on F r" obtains n where "ntrancl_onp F r n a b"
proof atomize_elim
  from assms show "\<exists>n. ntrancl_onp F r n a b"
  proof induct
    case base
    then have "ntrancl_onp F r 0 b b" by (auto intro: ntrancl_onp.intros)
    then show ?case ..
  next
    case (step a c)
    from \<open>\<exists>n. _\<close> obtain n where "ntrancl_onp F r n c b" ..
    with \<open>(a,c) \<in> r\<close> have "ntrancl_onp F r (Suc n) a b" using  \<open>a \<in> F\<close> by (rule ntrancl_onp.intros)
    then show ?case ..
  qed
qed

lemma rtrancl_on_conv_ntrancl_onp: "(a,b) \<in> rtrancl_on F r \<longleftrightarrow> (\<exists>n. ntrancl_onp F r n a b)"
  by (metis ntrancl_onpD_rtrancl_on rtrancl_onE_ntrancl_onp)


definition nreachable :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^bsup>_\<^esup>\<index> _" [100,100] 40) where
  "nreachable G u n v \<equiv> ntrancl_onp (verts G) (arcs_ends G) n u v"

context wf_digraph begin

lemma reachableE_nreachable:
  assumes "u \<rightarrow>\<^sup>* v" obtains n where "u \<rightarrow>\<^bsup>n\<^esup> v"
  using assms by (auto simp: reachable_def nreachable_def elim: rtrancl_onE_ntrancl_onp)

lemma converse_nreachable_cases[cases pred: nreachable]:
  assumes "u \<rightarrow>\<^bsup>n\<^esup> v"
  obtains (ntrancl_on_0) "u = v" "n = 0" "u \<in> verts G"
    | (ntrancl_on_Suc) w m where "u \<rightarrow> w" "n = Suc m" "w \<rightarrow>\<^bsup>m\<^esup> v"
  using assms unfolding nreachable_def by cases auto

lemma converse_nreachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^bsup>n\<^esup>\<^bsub>G\<^esub> v"
    and cases: "v \<in> verts G \<Longrightarrow> P 0 v"
       "\<And>n x y. \<lbrakk>x \<rightarrow>\<^bsub>G\<^esub> y; y \<rightarrow>\<^bsup>n\<^esup>\<^bsub>G\<^esub> v; P n y\<rbrakk> \<Longrightarrow> P (Suc n) x"
  shows "P n u"
  using assms unfolding nreachable_def by induct auto

lemma converse_nreachable_induct_less[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^bsup>n\<^esup>\<^bsub>G\<^esub> v"
    and cases: "v \<in> verts G \<Longrightarrow> P 0 v"
       "\<And>n x y. \<lbrakk>x \<rightarrow>\<^bsub>G\<^esub> y; y \<rightarrow>\<^bsup>n\<^esup>\<^bsub>G\<^esub> v; \<And>z m. m \<le> n \<Longrightarrow> (z \<rightarrow>\<^bsup>m\<^esup>\<^bsub>G\<^esub> v) \<Longrightarrow> P m z\<rbrakk> \<Longrightarrow> P (Suc n) x"
  shows "P n u"
proof -
  have "\<And>q u. q \<le> n \<Longrightarrow> (u \<rightarrow>\<^bsup>q\<^esup>\<^bsub>G\<^esub> v) \<Longrightarrow> P q u"
  proof (induction n arbitrary: u rule: less_induct)
    case (less n)
    show ?case
    proof (cases q)
      case 0 with less show ?thesis by (auto intro: cases elim: converse_nreachable_cases)
    next
      case (Suc q')
      with \<open>u \<rightarrow>\<^bsup>q\<^esup> v\<close> obtain w where "u \<rightarrow> w" "w \<rightarrow>\<^bsup>q'\<^esup> v" by (auto elim: converse_nreachable_cases)
      then show ?thesis
        unfolding \<open>q = _\<close> using Suc less by (auto intro!: less.IH cases)
    qed
  qed
  with major show ?thesis by auto
qed

end

end
