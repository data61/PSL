(*
  Title:      Blackboard.thy
  Author:     Diego Marmsoler
*)
section "A Theory of Blackboard Architectures"
text\<open>
  In the following, we formalize the specification of the blackboard pattern as described in~\cite{Marmsoler2018c}.
\<close>

theory Blackboard
imports Publisher_Subscriber
begin

subsection "Problems and Solutions"
text \<open>
  Blackboards work with problems and solutions for them.
\<close>
typedecl PROB
consts sb :: "(PROB \<times> PROB) set"
axiomatization where sbWF: "wf sb"
typedecl SOL
consts solve:: "PROB \<Rightarrow> SOL"

subsection "Blackboard Architectures"
text \<open>
  In the following, we describe the locale for the blackboard pattern.
\<close>
locale blackboard = publisher_subscriber bbactive bbcmp ksactive kscmp bbrp bbcs kscs ksrp
  for bbactive :: "'bid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and bbcmp :: "'bid \<Rightarrow> cnf \<Rightarrow> 'BB" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60)
    and ksactive :: "'kid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and kscmp :: "'kid \<Rightarrow> cnf \<Rightarrow> 'KS" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60)
    and bbrp :: "'BB \<Rightarrow> (PROB set) subscription set"
    and bbcs :: "'BB \<Rightarrow> (PROB \<times> SOL)"
    and kscs :: "'KS \<Rightarrow> (PROB \<times> SOL) set"
    and ksrp :: "'KS \<Rightarrow> (PROB set) subscription" +
  fixes bbns :: "'BB \<Rightarrow> (PROB \<times> SOL) set"
    and ksns :: "'KS \<Rightarrow> (PROB \<times> SOL)"
    and bbop :: "'BB \<Rightarrow> PROB"
    and ksop :: "'KS \<Rightarrow> PROB set"
    and prob :: "'kid \<Rightarrow> PROB"
  assumes
    ks1: "\<forall>p. \<exists>ks. p=prob ks" \<comment> \<open>Component Parameter\<close>
    \<comment> \<open>Assertions about component behavior.\<close>
    and bhvbb1: "\<And>t t' bId p s. \<lbrakk>t \<in> arch\<rbrakk> \<Longrightarrow> pb.eval bId t t' 0
      (\<box>\<^sub>b ([\<lambda>bb. (p,s)\<in>bbns bb]\<^sub>b
      \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b [\<lambda>bb. (p,s) = bbcs bb]\<^sub>b)))"
    and bhvbb2: "\<And>t t' bId P q. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> pb.eval bId t t' 0
      (\<box>\<^sub>b ([\<lambda>bb. sub P \<in> bbrp bb \<and> q \<in> P]\<^sub>b \<longrightarrow>\<^sup>b
      (\<diamond>\<^sub>b [\<lambda>bb. q = bbop bb]\<^sub>b)))"
    and bhvbb3: "\<And>t t' bId p . \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> pb.eval bId t t' 0
      (\<box>\<^sub>b ([\<lambda>bb. p = bbop(bb)]\<^sub>b \<longrightarrow>\<^sup>b
      ([\<lambda>bb. p=bbop(bb)]\<^sub>b \<WW>\<^sub>b [\<lambda>bb. (p,solve(p)) = bbcs(bb)]\<^sub>b)))"
    and bhvks1: "\<And>t t' kId p P. \<lbrakk>t\<in>arch; p = prob kId\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (\<box>\<^sub>b ([\<lambda>ks. sub P = ksrp ks]\<^sub>b \<and>\<^sup>b
      (\<forall>\<^sub>b q. ((sb.pred (q\<in>P)) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b ([\<lambda>ks. (q,solve(q)) \<in> kscs ks]\<^sub>b))))
      \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b [\<lambda>ks. (p, solve p) = ksns ks]\<^sub>b)))"
    and bhvks2: "\<And>t t' kId p P q. \<lbrakk>t \<in> arch;p = prob kId\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (\<box>\<^sub>b [\<lambda>ks. sub P = ksrp ks \<and> q \<in> P \<longrightarrow> (q,p) \<in> sb]\<^sub>b)"
    and bhvks3: "\<And>t t' kId p. \<lbrakk>t\<in>arch;p = prob kId\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (\<box>\<^sub>b ([\<lambda>ks. p\<in>ksop ks]\<^sub>b \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b [\<lambda>ks. (\<exists>P. sub P = ksrp ks)]\<^sub>b)))"
    and bhvks4: "\<And>t t' kId p P. \<lbrakk>t\<in>arch; p\<in>P\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (\<box>\<^sub>b ([\<lambda>ks. sub P = ksrp ks]\<^sub>b \<longrightarrow>\<^sup>b
      ((\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p\<in>P') \<and>\<^sup>b [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b))) \<WW>\<^sub>b
      [\<lambda>ks. (p,solve p) \<in> kscs ks]\<^sub>b)))"

    \<comment> \<open>Assertions about component activation.\<close>
    and actks:
      "\<And>t n kid p. \<lbrakk>t \<in> arch; \<parallel>kid\<parallel>\<^bsub>t n\<^esub>; p=prob kid; p\<in>ksop (\<sigma>\<^bsub>kid\<^esub>(t n))\<rbrakk>
      \<Longrightarrow> (\<exists>n'\<ge>n. \<parallel>kid\<parallel>\<^bsub>t n'\<^esub> \<and> (p, solve p) = ksns (\<sigma>\<^bsub>kid\<^esub>(t n')) \<and>
      (\<forall>n''\<ge>n. n''<n' \<longrightarrow> \<parallel>kid\<parallel>\<^bsub>t n''\<^esub>))
      \<or> (\<forall>n'\<ge>n. (\<parallel>kid\<parallel>\<^bsub>t n'\<^esub> \<and> (\<not>(p, solve p) = ksns (\<sigma>\<^bsub>kid\<^esub>(t n')))))"

    \<comment> \<open>Assertions about connections.\<close>
    and conn1: "\<And>k bid. \<parallel>bid\<parallel>\<^bsub>k\<^esub>
      \<Longrightarrow> bbns (\<sigma>\<^bsub>bid\<^esub>(k)) = (\<Union>kid\<in>{kid. \<parallel>kid\<parallel>\<^bsub>k\<^esub>}. {ksns (\<sigma>\<^bsub>kid\<^esub>(k))})"
    and conn2: "\<And>k kid. \<parallel>kid\<parallel>\<^bsub>k\<^esub>
      \<Longrightarrow> ksop (\<sigma>\<^bsub>kid\<^esub>(k)) = (\<Union>bid\<in>{bid. \<parallel>bid\<parallel>\<^bsub>k\<^esub>}. {bbop (\<sigma>\<^bsub>bid\<^esub>(k))})"
begin
  notation sb.lNAct ("\<langle>_ \<Leftarrow> _\<rangle>\<^bsub>_\<^esub>")
  notation sb.nxtAct ("\<langle>_ \<rightarrow> _\<rangle>\<^bsub>_\<^esub>")
  notation pb.lNAct ("\<langle>_ \<Leftarrow> _\<rangle>\<^bsub>_\<^esub>")
  notation pb.nxtAct ("\<langle>_ \<rightarrow> _\<rangle>\<^bsub>_\<^esub>")

  subsubsection "Calculus Interpretation"
  text \<open>
  \noindent
  @{thm[source] pb.baIA}: @{thm pb.baIA [no_vars]}
\<close>
  text \<open>
  \noindent
  @{thm[source] sb.baIA}: @{thm sb.baIA [no_vars]}
\<close>

  subsubsection "Results from Singleton"
  abbreviation "the_bb \<equiv> the_pb"
  text \<open>
  \noindent
  @{thm[source] pb.ts_prop(1)}: @{thm pb.ts_prop(1) [no_vars]}
\<close>
  text \<open>
  \noindent
  @{thm[source] pb.ts_prop(2)}: @{thm pb.ts_prop(2) [no_vars]}
\<close>
  subsubsection "Results from Publisher Subscriber"
  text \<open>
	\noindent
	@{thm[source] msgDelivery}: @{thm msgDelivery [no_vars]}
\<close>
  lemma conn2_bb:
    fixes k and kid::'kid
    assumes "\<parallel>kid\<parallel>\<^bsub>k\<^esub>"
    shows "bbop (\<sigma>\<^bsub>the_bb\<^esub>(k))\<in>ksop (\<sigma>\<^bsub>kid\<^esub>(k))"
  proof -
    from assms have "ksop (\<sigma>\<^bsub>kid\<^esub>(k)) = (\<Union>bid\<in>{bid. \<parallel>bid\<parallel>\<^bsub>k\<^esub>}. {bbop (\<sigma>\<^bsub>bid\<^esub>(k))})" using conn2 by simp
    moreover have "(\<Union>bid.{bid. \<parallel>bid\<parallel>\<^bsub>k\<^esub>})={the_bb}" using pb.ts_prop(1) by auto
    hence "(\<Union>bid\<in>{bid. \<parallel>bid\<parallel>\<^bsub>k\<^esub>}. {bbop (\<sigma>\<^bsub>bid\<^esub>(k))}) = {bbop (\<sigma>\<^bsub>the_bb\<^esub>(k))}" by auto
    ultimately show ?thesis by simp
  qed

  subsubsection "Knowledge Sources"
  text \<open>
    In the following we introduce an abbreviation for knowledge sources which are able to solve a specific problem.
\<close>
  definition sKs:: "PROB \<Rightarrow> 'kid" where
    "sKs p \<equiv> (SOME kid. p = prob kid)"

  lemma sks_prob:
    "p = prob (sKs p)"
  using sKs_def someI_ex[of "\<lambda>kid. p = prob kid"] ks1 by auto

  subsubsection "Architectural Guarantees"
  text\<open>
    The following theorem verifies that a problem is eventually solved by the pattern even if no knowledge source exist which can solve the problem on its own.
    It assumes, however, that for every open sub problem, a corresponding knowledge source able to solve the problem will be eventually activated.
\<close>
  lemma pSolved_Ind:
    fixes t and t'::"nat \<Rightarrow>'BB" and p and t''::"nat \<Rightarrow>'KS"
    assumes "t\<in>arch" and
      "\<forall>n. (\<exists>n'\<ge>n. \<parallel>sKs (bbop(\<sigma>\<^bsub>the_bb\<^esub>(t n)))\<parallel>\<^bsub>t n'\<^esub>)"
    shows
      "\<forall>n. (\<exists>P. sub P \<in> bbrp(\<sigma>\<^bsub>the_bb\<^esub>(t n)) \<and> p \<in> P) \<longrightarrow>
        (\<exists>m\<ge>n. (p,solve(p)) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t m)))" (*\eqref{eq:bb:g}*)
  \<comment> \<open>The proof is by well-founded induction over the subproblem relation @{term sb}\<close>
  proof (rule wf_induct[where r=sb])
    \<comment> \<open>We first show that the subproblem relation is indeed well-founded ...\<close>
    show "wf sb" by (simp add: sbWF)
  next
    \<comment> \<open>... then we show that a problem @{term p} is indeed solved\<close>
    \<comment> \<open>if all its sub-problems @{term p'} are eventually solved\<close>
    fix p assume indH: "\<forall>p'. (p', p) \<in> sb \<longrightarrow> (\<forall>n. (\<exists>P. sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n)) \<and> p'\<in>P)
      \<longrightarrow> (\<exists>m\<ge>n. (p',solve(p')) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t m))))"
    show "\<forall>n. (\<exists>P. sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n)) \<and> p \<in> P)
      \<longrightarrow> (\<exists>m\<ge>n. (p,solve(p)) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t m)))"
    proof
      fix n\<^sub>0 show "(\<exists>P. sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>0)) \<and> p \<in> P) \<longrightarrow>
      (\<exists>m\<ge>n\<^sub>0. (p,solve(p)) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t m)))"
      proof
        assume "\<exists>P. sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>0)) \<and> p \<in> P"
        moreover have "(\<exists>P. sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>0)) \<and> p \<in> P) \<longrightarrow> (\<exists>n'\<ge>n\<^sub>0. p=bbop(\<sigma>\<^bsub>the_bb\<^esub>(t n')))"
        proof
          assume "\<exists>P. sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>0)) \<and> p \<in> P"
          then obtain P where "sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>0))" and "p \<in> P" by auto
          hence "pb.eval the_bb t t' n\<^sub>0 [\<lambda>bb. sub P \<in> bbrp bb \<and> p \<in> P]\<^sub>b" using pb.baI by simp
          moreover from pb.globE[OF bhvbb2] have
            "pb.eval the_bb t t' n\<^sub>0 ([\<lambda>bb. sub P \<in> bbrp bb \<and> p \<in> P]\<^sub>b \<longrightarrow>\<^sup>b \<diamond>\<^sub>b [\<lambda>bb. p = bbop bb]\<^sub>b)"
            using \<open>t\<in>arch\<close> by simp
          ultimately have "pb.eval the_bb t t' n\<^sub>0 (\<diamond>\<^sub>b [\<lambda>bb. p = bbop bb]\<^sub>b)" using pb.impE by blast
          then obtain n' where "n'\<ge>n\<^sub>0" and "pb.eval the_bb t t' n' [\<lambda>bb. p = bbop bb]\<^sub>b"
            using pb.evtE by blast
          hence "p=bbop(\<sigma>\<^bsub>the_bb\<^esub>(t n'))" using pb.baE by auto
          with \<open>n'\<ge>n\<^sub>0\<close> show "\<exists>n'\<ge>n\<^sub>0. p=bbop(\<sigma>\<^bsub>the_bb\<^esub>(t n'))" by auto
        qed
        ultimately obtain n where "n\<ge>n\<^sub>0" and "p=bbop(\<sigma>\<^bsub>the_bb\<^esub>(t n))" by auto

        \<comment> \<open>Problem p is provided at the output of the blackboard until it is solved\<close>
        \<comment> \<open>or forever...\<close>
        from pb.globE[OF bhvbb3] have
          "pb.eval the_bb t t' n ([\<lambda> bb. p = bbop(bb)]\<^sub>b \<longrightarrow>\<^sup>b
          ([\<lambda> bb. p=bbop(bb)]\<^sub>b \<WW>\<^sub>b [\<lambda>bb. (p,solve(p)) = bbcs(bb)]\<^sub>b))"
          using \<open>t\<in>arch\<close> by auto
        moreover from \<open>p = bbop (\<sigma>\<^bsub>the_bb\<^esub>(t n))\<close> have
          "pb.eval the_bb t t' n [\<lambda> bb. p=bbop bb]\<^sub>b"
          using \<open>t\<in>arch\<close> pb.baI by simp
        ultimately have "pb.eval the_bb t t' n
          ([\<lambda> bb. p=bbop(bb)]\<^sub>b \<WW>\<^sub>b [\<lambda> bb. (p,solve(p)) = bbcs(bb)]\<^sub>b)"
          using pb.impE by blast
        hence "pb.eval the_bb t t' n (([\<lambda> bb. p=bbop bb]\<^sub>b \<UU>\<^sub>b
          [\<lambda> bb. (p,solve(p)) = bbcs bb]\<^sub>b) \<or>\<^sup>b (\<box>\<^sub>b [\<lambda> bb. p=bbop bb]\<^sub>b))"
          using pb.wuntil_def by simp
        hence "pb.eval the_bb t t' n
          ([\<lambda>bb. p=bbop bb]\<^sub>b \<UU>\<^sub>b [\<lambda>bb. (p,solve(p)) = bbcs bb]\<^sub>b) \<or>
          (pb.eval the_bb t t' n (\<box>\<^sub>b [\<lambda> bb. p=bbop bb]\<^sub>b))"
          using pb.disjE by simp
        thus "\<exists>m\<ge>n\<^sub>0. (p,solve p) = bbcs(\<sigma>\<^bsub>the_bb\<^esub>(t m))"
        \<comment> \<open>We need to consider both cases, the case in which the problem is eventually\<close>
        \<comment> \<open>solved and the case in which the problem is always provided as an output\<close>
        proof
          \<comment> \<open>First we consider the case in which the problem is eventually solved:\<close>
          assume "pb.eval the_bb t t' n
            ([\<lambda>bb. p=bbop bb]\<^sub>b \<UU>\<^sub>b [\<lambda>bb. (p,solve(p)) = bbcs bb]\<^sub>b)"
          hence "\<exists>i\<ge>n. (pb.eval the_bb t t' i
            [\<lambda>bb. (p,solve(p)) = bbcs bb]\<^sub>b \<and>
            (\<forall>k\<ge>n. k<i \<longrightarrow> pb.eval the_bb t t' k [\<lambda>bb. p = bbop bb]\<^sub>b))"
            using \<open>t\<in>arch\<close> pb.untilE by simp
          then obtain i where "i\<ge>n" and
            "pb.eval the_bb t t' i [\<lambda>bb. (p,solve(p)) = bbcs bb]\<^sub>b" by auto
          hence "(p,solve(p)) = bbcs(\<sigma>\<^bsub>the_bb\<^esub>(t i))"
            using \<open>t\<in>arch\<close> pb.baEA by auto
          moreover from \<open>i\<ge>n\<close> \<open>n\<ge>n\<^sub>0\<close> have "i\<ge>n\<^sub>0" by simp
          ultimately show ?thesis by auto
        next
          \<comment> \<open>Now we consider the case in which p is always provided at the output\<close>
          \<comment> \<open>of the blackboard:\<close>
          assume "pb.eval the_bb t t' n
            (\<box>\<^sub>b [\<lambda>bb. p=bbop bb]\<^sub>b)"
          hence "\<forall>n'\<ge>n. (pb.eval the_bb t t' n' [\<lambda>bb. p = bbop bb]\<^sub>b)"
            using \<open>t\<in>arch\<close> pb.globE by auto
          hence outp: "\<forall>n'\<ge>n. (p = bbop (\<sigma>\<^bsub>the_bb\<^esub>(t n')))"
            using \<open>t\<in>arch\<close> pb.baE by blast

          \<comment> \<open>thus, by assumption there exists a KS which is able to solve p and which\<close>
          \<comment> \<open>is active at @{text n'}...\<close>
          with assms(2) have "\<exists>n'\<ge>n. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub>" by auto
          then obtain n\<^sub>k where "n\<^sub>k\<ge>n" and "\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>" by auto
          \<comment> \<open>... and get the problem as its input.\<close>
          moreover from \<open>n\<^sub>k\<ge>n\<close> have "p = bbop (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>k))"
            using outp by simp
          ultimately have "p\<in>ksop(\<sigma>\<^bsub>sKs p\<^esub>(t n\<^sub>k))" using conn2_bb[of "sKs p" "t n\<^sub>k"] by simp

          \<comment> \<open>thus the ks will either solve the problem or not solve it and\<close>
          \<comment> \<open>be activated forever\<close>
          hence "(\<exists>n'\<ge>n\<^sub>k. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub> \<and>
            (p, solve p) = ksns (\<sigma>\<^bsub>sKs p\<^esub>(t n')) \<and>
            (\<forall>n''\<ge>n\<^sub>k. n''<n' \<longrightarrow> \<parallel>sKs p\<parallel>\<^bsub>t n''\<^esub>)) \<or>
            (\<forall>n'\<ge>n\<^sub>k. (\<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub> \<and>
            (\<not>(p, solve p) = ksns (\<sigma>\<^bsub>sKs p\<^esub>(t n')))))"
            using \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> actks[of t "sKs p"] \<open>t\<in>arch\<close> sks_prob by simp
          thus ?thesis
          proof
            \<comment> \<open>if the ks solves it\<close>
            assume "\<exists>n'\<ge>n\<^sub>k. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub> \<and> (p, solve p) = ksns (\<sigma>\<^bsub>sKs p\<^esub>t n')
              \<and> (\<forall>n''\<ge>n\<^sub>k. n'' < n' \<longrightarrow> \<parallel>sKs p\<parallel>\<^bsub>t n''\<^esub>)"
            \<comment> \<open>it is forwarded to the blackboard\<close>
            then obtain n\<^sub>s where "n\<^sub>s\<ge>n\<^sub>k" and "\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>s\<^esub>"
              and "(p, solve p) = ksns (\<sigma>\<^bsub>sKs p\<^esub>t n\<^sub>s)" by auto
            moreover have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub> = n\<^sub>s"
              by (simp add: \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>s\<^esub>\<close> sb.nxtAct_active)
            ultimately have
              "(p,solve(p)) \<in> bbns (\<sigma>\<^bsub>the_bb\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>)))"
              using conn1[OF pb.ts_prop(2)] \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>s\<^esub>\<close> by auto

            \<comment> \<open>finally, the blackboard will forward the solution which finishes the proof.\<close>
            with bhvbb1 have "pb.eval the_bb t t' (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>)
              (\<diamond>\<^sub>b [\<lambda>bb. (p, solve p) = bbcs bb]\<^sub>b)"
              using \<open>t\<in>arch\<close> pb.globE pb.impE[of the_bb t t'] by blast
            then obtain n\<^sub>f where "n\<^sub>f\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>" and
              "pb.eval the_bb t t' n\<^sub>f [\<lambda>bb. (p, solve p) = bbcs bb]\<^sub>b"
              using \<open>t\<in>arch\<close> pb.evtE[of t t' "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>"] by auto
            hence "(p, solve p) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>f))"
              using \<open>t \<in> arch\<close> pb.baEA by auto
            moreover have "n\<^sub>f\<ge>n\<^sub>0"
            proof -
              from \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>\<ge>n\<^sub>k"
                using sb.nxtActI by blast
              with \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub> = n\<^sub>s\<close> show ?thesis
                using \<open>n\<^sub>f\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>\<close> \<open>n\<^sub>s\<ge>n\<^sub>k\<close> \<open>n\<^sub>k\<ge>n\<close> \<open>n\<ge>n\<^sub>0\<close> by arith
            qed
            ultimately show ?thesis by auto
          next
            \<comment> \<open>otherwise, we derive a contradiction\<close>
            assume case_ass: "\<forall>n'\<ge>n\<^sub>k. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub> \<and> \<not>(p, solve p) = ksns (\<sigma>\<^bsub>sKs p\<^esub>t n')"

            \<comment> \<open>first, the KS will eventually register for the subproblems P it requires to solve p...\<close>
            from \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> have "\<exists>i\<ge>0. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>" by auto
            moreover have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> n\<^sub>k" by simp
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>k
              ([\<lambda>ks. p\<in>ksop ks]\<^sub>b \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b [\<lambda>ks. \<exists>P. sub P = ksrp ks]\<^sub>b))"
              using sb.globEA[OF _ bhvks3[of t p "sKs p" t'']] \<open>t\<in>arch\<close> sks_prob by simp
            moreover have "sb.eval (sKs p) t t'' n\<^sub>k [\<lambda>ks. p \<in> ksop ks]\<^sub>b"
            proof -
              from \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> have "\<exists>n'\<ge>n\<^sub>k. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub>" by auto
              moreover have "p \<in> ksop (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>)))"
              proof -
                from \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>=n\<^sub>k"
                  using sb.nxtAct_active by blast
                with \<open>p\<in>ksop(\<sigma>\<^bsub>sKs p\<^esub>(t n\<^sub>k))\<close> show ?thesis by simp
              qed
              ultimately show ?thesis using sb.baIA[of n\<^sub>k "sKs p" t] by blast
            qed
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>k (\<diamond>\<^sub>b [\<lambda>ks. \<exists>P. sub P = ksrp ks]\<^sub>b)"
              using sb.impE by blast
            then obtain n\<^sub>r where "n\<^sub>r\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>" and
              "\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub> \<and>
              (\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>. n'' \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>
              \<longrightarrow> sb.eval (sKs p) t t'' n'' [\<lambda>ks. \<exists>P. sub P = ksrp ks]\<^sub>b) \<or>
              \<not> (\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>) \<and>
              sb.eval (sKs p) t t'' n\<^sub>r [\<lambda>ks. \<exists>P. sub P = ksrp ks]\<^sub>b"
              using \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> sb.evtEA[of n\<^sub>k "sKs p" t] by blast
            moreover from case_ass have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>\<ge>n\<^sub>k" using sb.nxtActI by blast
            with \<open>n\<^sub>r\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>\<close> have "n\<^sub>r\<ge>n\<^sub>k" by arith
            hence "\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>" using case_ass by auto
            hence "n\<^sub>r \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" using sb.nxtActLe by simp
            moreover have "n\<^sub>r \<ge> \<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" by simp
            ultimately have
              "sb.eval (sKs p) t t'' n\<^sub>r [\<lambda>ks. \<exists>P. sub P = ksrp ks]\<^sub>b" by blast
            with \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> obtain P where
              "sub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)))"
              using sb.baEA by blast
            hence "sb.eval (sKs p) t t'' n\<^sub>r [\<lambda>ks. sub P = ksrp ks]\<^sub>b"
              using \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> sb.baIA sks_prob by blast

            \<comment> \<open>the knowledgesource will eventually get a solution for each required subproblem:\<close>
            moreover have "sb.eval (sKs p) t t'' n\<^sub>r (\<forall>\<^sub>b p'. (sb.pred (p'\<in>P) \<longrightarrow>\<^sup>b
              (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b)))"
            proof -
              have "\<forall>p'. sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P) \<longrightarrow>\<^sup>b
                (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b))"
              proof
                \<comment> \<open>by induction hypothesis, the blackboard will eventually provide solutions for subproblems\<close>
                fix p'
                have "sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P)) \<longrightarrow>
                  (sb.eval (sKs p) t t'' n\<^sub>r
                  (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b))"
                proof
                  assume "sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P))"
                  hence "p' \<in> P" using sb.predE by blast
                  thus "(sb.eval (sKs p) t t'' n\<^sub>r (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b))"
                  proof -
                    have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> n\<^sub>r" by simp
                    moreover from \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> have "\<exists>i\<ge>0. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>" by auto
                    ultimately have "sb.eval (sKs p) t t'' n\<^sub>r ([\<lambda>ks. sub P = ksrp ks]\<^sub>b
                      \<longrightarrow>\<^sup>b ((\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P') \<and>\<^sup>b [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b))) \<WW>\<^sub>b
                      [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b))"
                      using sb.globEA[OF _ bhvks4[of t p' P "sKs p" t'']]
                      \<open>t\<in>arch\<close> \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> \<open>p'\<in>P\<close> by simp
                    with \<open>sb.eval (sKs p) t t'' n\<^sub>r [\<lambda>ks. sub P = ksrp ks]\<^sub>b\<close> have
                      "sb.eval (sKs p) t t'' n\<^sub>r ((\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P') \<and>\<^sup>b
                      [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b))) \<WW>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b)"
                      using sb.impE[of "(sKs p)" t t'' n\<^sub>r "[\<lambda>ks. sub P = ksrp ks]\<^sub>b"] by blast
                    hence "sb.eval (sKs p) t t'' n\<^sub>r ((\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P') \<and>\<^sup>b
                      [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b))) \<UU>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b) \<or>
                      sb.eval (sKs p) t t'' n\<^sub>r (\<box>\<^sub>b (\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P') \<and>\<^sup>b
                      [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b))))" using sb.wuntil_def by auto
                    thus "(sb.eval (sKs p) t t'' n\<^sub>r (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b))"
                    proof
                      let ?\<gamma>'="\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P') \<and>\<^sup>b ([\<lambda>ks. unsub P' = ksrp ks]\<^sub>b)))"
                      let ?\<gamma>="[\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b"
                      assume "sb.eval (sKs p) t t'' n\<^sub>r (?\<gamma>' \<UU>\<^sub>b ?\<gamma>)"
                      with \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> obtain n' where "n'\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" and
                        lass: "(\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>) \<and> (\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>
                        \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>) \<and>
                        (\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>. n'' < \<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>
                        \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>') \<or>
                        \<not> (\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>) \<and> sb.eval (sKs p) t t'' n' ?\<gamma> \<and>
                        (\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>. n'' < n' \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>')"
                        using sb.untilEA[of n\<^sub>r "sKs p" t t''] \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> by blast
                      thus "?thesis"
                      proof cases
                        assume "\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>"
                        with lass have "\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>
                          \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>" by auto
                        moreover have "n'\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>" by simp
                        moreover have "n' \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>"
                          using \<open>\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> sb.nxtActLe by simp
                        ultimately have "sb.eval (sKs p) t t'' n' ?\<gamma>" by simp
                        moreover have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n'" using \<open>n\<^sub>r \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<close>
                        \<open>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n\<^sub>r\<close> \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n'\<close> by linarith
                        ultimately show ?thesis using \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close>
                          \<open>n'\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<close> \<open>n' \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>\<close>
                          sb.evtIA[of n\<^sub>r "sKs p" t n' t'' ?\<gamma>] by blast
                      next
                        assume "\<not> (\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>)"
                        with lass have "sb.eval (sKs p) t t'' n' ?\<gamma> \<and>
                          (\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>. n'' < n' \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>')" by auto
                        moreover have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n'"
                          using \<open>n\<^sub>r \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<close> \<open>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n\<^sub>r\<close>
                          \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n'\<close> by linarith
                        ultimately show ?thesis using \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>)\<close>
                            sb.evtIA[of n\<^sub>r "sKs p" t n' t'' ?\<gamma>] by blast
                      qed
                    next
                      assume cass: "sb.eval (sKs p) t t'' n\<^sub>r
                        (\<box>\<^sub>b (\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P') \<and>\<^sup>b [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b))))"

                      have "sub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>))) \<and>
                        p' \<in> P \<longrightarrow> (p', p) \<in> sb"
                      proof -
                        have "\<exists>i\<ge>0. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>" using \<open>\<exists>i\<ge>0. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> by auto
                        moreover have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)" by simp
                        ultimately have "sb.eval (sKs p) t t'' (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)
                          [\<lambda>ks. sub P = ksrp ks \<and> p' \<in> P \<longrightarrow> (p', p) \<in> sb]\<^sub>b"
                          using sb.globEA[OF _ bhvks2[of t p "sKs p" t'' P]] \<open>t \<in> arch\<close> sks_prob by blast
                        moreover from \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have
                          "\<parallel>sKs p\<parallel>\<^bsub>t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)\<^esub>" using sb.nxtActI by blast
                        ultimately show ?thesis
                          using sb.baEANow[of "sKs p" t t'' "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>"] by simp
                      qed
                      with \<open>p' \<in> P\<close> have "(p', p) \<in> sb"
                        using \<open>sub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)))\<close>
                        sks_prob by simp
                      moreover from \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have "\<parallel>sKs p\<parallel>\<^bsub>t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)\<^esub>"
                        using sb.nxtActI by blast
                        with \<open>sub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)))\<close>
                          have "sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)))"
                          using conn1A by auto
                      with \<open> p' \<in> P\<close> have "sub P \<in> bbrp (\<sigma>\<^bsub>the_bb\<^esub>t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)) \<and> p' \<in> P" by auto
                      ultimately obtain m where "m\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" and "(p', solve p') = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t m))"
                        using indH by auto

                      \<comment> \<open>and due to the publisher subscriber property,\<close>
                      \<comment> \<open>the knowledge source will receive them\<close>
                      moreover have
                        "\<nexists>n P. \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n \<and> n \<le> m \<and> \<parallel>sKs p\<parallel>\<^bsub>t n\<^esub> \<and>
                        unsub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t n)) \<and> p' \<in> P"
                      proof
                        assume "\<exists>n P'. \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n \<and> n \<le> m \<and> \<parallel>sKs p\<parallel>\<^bsub>t n\<^esub> \<and>
                          unsub P' = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t n)) \<and> p' \<in> P'"
                        then obtain n P' where
                          "\<parallel>sKs p\<parallel>\<^bsub>t n\<^esub>" and "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n" and "n \<le> m" and
                          "unsub P' = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t n))" and "p' \<in> P'" by auto
                        hence "sb.eval (sKs p) t t'' n (\<exists>\<^sub>b P'. sb.pred (p'\<in>P') \<and>\<^sup>b
                          [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b)" by blast
                        moreover have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n"
                          using \<open>n\<^sub>r \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<close> \<open>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n\<^sub>r\<close>
                          \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> n\<close> by linarith
                        with cass have "sb.eval (sKs p) t t'' n (\<not>\<^sup>b (\<exists>\<^sub>b P'. (sb.pred (p'\<in>P')
                          \<and>\<^sup>b [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b)))"
                          using sb.globEA[of n\<^sub>r "sKs p" t t''
                          "\<not>\<^sup>b (\<exists>\<^sub>bP'. sb.pred (p' \<in> P') \<and>\<^sup>b [\<lambda>ks. unsub P' = ksrp ks]\<^sub>b)" n]
                          \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> by auto
                        ultimately show False using sb.negE by auto
                      qed
                      moreover from \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have
                        "\<parallel>sKs p\<parallel>\<^bsub>t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)\<^esub>" using sb.nxtActI by blast
                      moreover have "sub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)))"
                        using \<open>sub P = ksrp (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>)))\<close> .
                      moreover from \<open>m\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<close> have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> m" by simp
                      moreover from \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close>
                        have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<ge>n\<^sub>r" using sb.nxtActI by blast
                      hence "m\<ge>n\<^sub>k" using \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> m\<close> \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub> \<le> n\<^sub>r\<close>
                        \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub> \<ge> n\<^sub>k\<close> by simp
                      with case_ass have "\<parallel>sKs p\<parallel>\<^bsub>t m\<^esub>" by simp
                      ultimately have "(p', solve p') \<in> kscs (\<sigma>\<^bsub>sKs p\<^esub>(t m))"
                        and "\<parallel>sKs p\<parallel>\<^bsub>t m\<^esub>"
                        using \<open>t \<in> arch\<close> msgDelivery[of t "sKs p" "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" P m p' "solve p'"]
                        \<open>p' \<in> P\<close> by auto
                      hence "sb.eval (sKs p) t t'' m [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b"
                        using sb.baIANow by simp
                      moreover have "m \<ge> \<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>m\<^esub>" by simp
                      moreover from \<open>\<parallel>sKs p\<parallel>\<^bsub>t m\<^esub>\<close> have "m \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>m\<^esub>"
                        using sb.nxtActLe by auto
                      moreover from \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have
                        "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" by simp
                      with \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> m\<close> have "\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<le> m" by arith
                      ultimately show "sb.eval (sKs p) t t'' n\<^sub>r
                        (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b)"
                        using \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> sb.evtIA by blast
                    qed
                  qed
                qed
                thus "sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P) \<longrightarrow>\<^sup>b
                  (\<diamond>\<^sub>b [\<lambda>ks. (p',solve p') \<in> kscs ks]\<^sub>b))"
                  using sb.impI by auto
              qed
              thus ?thesis using sb.allI by blast
            qed

            \<comment> \<open>Thus, the knowlege source will eventually solve the problem at hand...\<close>
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>r
              ([\<lambda>ks. sub P = ksrp ks]\<^sub>b \<and>\<^sup>b
              (\<forall>\<^sub>b q. (sb.pred (q \<in> P) \<longrightarrow>\<^sup>b \<diamond>\<^sub>b [\<lambda>ks. (q, solve q) \<in> kscs ks]\<^sub>b)))"
              using sb.conjI by simp
            moreover from \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have "\<exists>i\<ge>0. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>" by blast
            hence "sb.eval (sKs p) t t'' n\<^sub>r
              (([\<lambda>ks. sub P = ksrp ks]\<^sub>b \<and>\<^sup>b
              (\<forall>\<^sub>b q. (sb.pred (q \<in> P) \<longrightarrow>\<^sup>b
              \<diamond>\<^sub>b [\<lambda>ks. (q, solve q) \<in> kscs ks]\<^sub>b))) \<longrightarrow>\<^sup>b
              (\<diamond>\<^sub>b [\<lambda>ks. (p, solve p) = ksns ks]\<^sub>b))" using \<open>t \<in> arch\<close>
              sb.globEA[OF _ bhvks1[of t p "sKs p" t'' P]] sks_prob by simp
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>r
              (\<diamond>\<^sub>b [\<lambda>ks. (p,solve(p))=ksns(ks)]\<^sub>b)"
              using sb.impE[of "sKs p" t t'' n\<^sub>r] by blast

            \<comment> \<open>and forward it to the blackboard\<close>
            then obtain n\<^sub>s where "n\<^sub>s\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>" and
              "(\<exists>i\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub> \<and>
              (\<forall>n''\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>. n'' \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub> \<longrightarrow>
              sb.eval (sKs p) t t'' n'' [\<lambda>ks. (p,solve(p))=ksns(ks)]\<^sub>b)) \<or>
              \<not> (\<exists>i\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>) \<and>
              sb.eval (sKs p) t t'' n\<^sub>s [\<lambda>ks. (p,solve(p))=ksns(ks)]\<^sub>b"
              using sb.evtEA[of n\<^sub>r "sKs p" t] \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> by blast
            moreover from \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub> \<ge> n\<^sub>r\<close> \<open>n\<^sub>r\<ge>n\<^sub>k\<close> \<open>n\<^sub>s\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<close>
              have "n\<^sub>s\<ge>n\<^sub>k" by arith
            with case_ass have "\<exists>i\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>" by auto
            moreover have "n\<^sub>s\<ge>\<langle>sKs p \<Leftarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>" by simp
            moreover from \<open>\<exists>i\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have "n\<^sub>s \<le> \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>"
              using sb.nxtActLe by simp
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>s [\<lambda>ks. (p,solve(p))=ksns(ks)]\<^sub>b"
              using sb.evtEA[of n\<^sub>r "sKs p" t] \<open>\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> by blast
            with \<open>\<exists>i\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> have
              "(p,solve(p)) = ksns (\<sigma>\<^bsub>sKs p\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>)))"
              using sb.baEA[of n\<^sub>s "sKs p" t t'' "\<lambda>ks. (p, solve p) = ksns ks"] by auto
            moreover from \<open>\<exists>i\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close>
              have "\<parallel>sKs p\<parallel>\<^bsub>t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>)\<^esub>" using sb.nxtActI by simp
            ultimately have "(p,solve(p)) \<in> bbns (\<sigma>\<^bsub>the_bb\<^esub>(t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>)))"
              using conn1[OF pb.ts_prop(2)[of "t (\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>)"]] by auto
            hence "pb.eval the_bb t t' \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub> [\<lambda>bb. (p,solve(p)) \<in> bbns bb]\<^sub>b"
              using \<open>t\<in>arch\<close> pb.baI by simp

            \<comment> \<open>finally, the blackboard will forward the solution which finishes the proof.\<close>
            with bhvbb1 have "pb.eval the_bb t t' \<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>
              (\<diamond>\<^sub>b [\<lambda>bb. (p, solve p) = bbcs bb]\<^sub>b)"
              using \<open>t\<in>arch\<close> pb.globE pb.impE[of the_bb t t'] by blast
            then obtain n\<^sub>f where "n\<^sub>f\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>" and
              "pb.eval the_bb t t' n\<^sub>f [\<lambda>bb. (p, solve p) = bbcs bb]\<^sub>b"
              using \<open>t\<in>arch\<close> pb.evtE[of t t' "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>"] by auto
            hence "(p, solve p) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t n\<^sub>f))"
              using \<open>t \<in> arch\<close> pb.baEA by auto
            moreover have "n\<^sub>f\<ge>n\<^sub>0"
            proof -
              from \<open>\<exists>n'''\<ge>n\<^sub>s. \<parallel>sKs p\<parallel>\<^bsub>t n'''\<^esub>\<close> have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>\<ge>n\<^sub>s"
                using sb.nxtActLe by simp
              moreover from \<open>n\<^sub>k\<ge>n\<close> and \<open>\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>k\<^esub>\<close> have "\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>\<ge>n\<^sub>k"
                using sb.nxtActI by blast
              ultimately show ?thesis
                using \<open>n\<^sub>f\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>s\<^esub>\<close> \<open>n\<^sub>s\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<close>
                \<open>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>r\<^esub>\<ge>n\<^sub>r\<close> \<open>n\<^sub>r\<ge>\<langle>sKs p \<rightarrow> t\<rangle>\<^bsub>n\<^sub>k\<^esub>\<close> \<open>n\<^sub>k\<ge>n\<close> \<open>n\<ge>n\<^sub>0\<close> by arith
            qed
            ultimately show ?thesis by auto
          qed
        qed
      qed
    qed
  qed

  theorem pSolved:
    fixes t and t'::"nat \<Rightarrow>'BB" and t''::"nat \<Rightarrow>'KS"
    assumes "t\<in>arch" and
      "\<forall>n. (\<exists>n'\<ge>n. \<parallel>sKs (bbop(\<sigma>\<^bsub>the_bb\<^esub>(t n)))\<parallel>\<^bsub>t n'\<^esub>)"
    shows
      "\<forall>n. (\<forall>P. (sub P \<in> bbrp(\<sigma>\<^bsub>the_bb\<^esub>(t n))
        \<longrightarrow> (\<forall>p \<in> P. (\<exists>m\<ge>n. (p,solve(p)) = bbcs (\<sigma>\<^bsub>the_bb\<^esub>(t m))))))"
    using assms pSolved_Ind by blast
end

end