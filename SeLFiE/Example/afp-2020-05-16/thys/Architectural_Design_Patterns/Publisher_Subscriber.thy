(*
  Title:      Publisher_Subscriber.thy
  Author:     Diego Marmsoler
*)
section "A Theory of Publisher-Subscriber Architectures"
text\<open>
  In the following, we formalize the specification of the publisher subscriber pattern as described in~\cite{Marmsoler2018c}.
\<close>
  
theory Publisher_Subscriber
imports Singleton
begin

subsection "Subscriptions"

datatype 'evt subscription = sub 'evt | unsub 'evt

subsection "Publisher-Subscriber Architectures"

locale publisher_subscriber =
  pb: singleton pbactive pbcmp +
  sb: dynamic_component sbcmp sbactive
    for pbactive :: "'pid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and pbcmp :: "'pid \<Rightarrow> cnf \<Rightarrow> 'PB" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60)
    and sbactive :: "'sid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and sbcmp :: "'sid \<Rightarrow> cnf \<Rightarrow> 'SB" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60) +
  fixes pbsb :: "'PB \<Rightarrow> ('evt set) subscription set"
    and pbnt :: "'PB \<Rightarrow> ('evt \<times> 'msg)"             
    and sbnt :: "'SB \<Rightarrow> ('evt \<times> 'msg) set"
    and sbsb :: "'SB \<Rightarrow> ('evt set) subscription"
  assumes conn1: "\<And>k pid. \<parallel>pid\<parallel>\<^bsub>k\<^esub>
      \<Longrightarrow> pbsb (\<sigma>\<^bsub>pid\<^esub>(k)) = (\<Union>sid\<in>{sid. \<parallel>sid\<parallel>\<^bsub>k\<^esub>}. {sbsb (\<sigma>\<^bsub>sid\<^esub>(k))})"
    and conn2: "\<And>t n n'' sid pid E e m.
      \<lbrakk>t \<in> arch; \<parallel>pid\<parallel>\<^bsub>t n\<^esub>; \<parallel>sid\<parallel>\<^bsub>t n\<^esub>; sub E = sbsb (\<sigma>\<^bsub>sid\<^esub>(t n)); n''\<ge> n; e \<in> E;
      \<nexists>n' E'. n' \<ge> n \<and> n' \<le> n'' \<and> \<parallel>sid\<parallel>\<^bsub>t n'\<^esub> \<and>
        unsub E' = sbsb (\<sigma>\<^bsub>sid\<^esub>(t n')) \<and> e \<in> E';
      (e, m) = pbnt (\<sigma>\<^bsub>pid\<^esub>(t n'')); \<parallel>sid\<parallel>\<^bsub>t n''\<^esub>\<rbrakk>
      \<Longrightarrow> pbnt (\<sigma>\<^bsub>pid\<^esub>(t n'')) \<in> sbnt (\<sigma>\<^bsub>sid\<^esub>(t n''))"
begin

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
abbreviation the_pb :: "'pid" where
"the_pb \<equiv> pb.the_singleton"

text \<open>
\noindent
@{thm[source] pb.ts_prop(1)}: @{thm pb.ts_prop(1) [no_vars]}
\<close>
text \<open>
\noindent
@{thm[source] pb.ts_prop(2)}: @{thm pb.ts_prop(2) [no_vars]}
\<close>

subsubsection "Architectural Guarantees"
text \<open>
  The following theorem ensures that a subscriber indeed receives all messages associated with an event for which he is subscribed.
\<close>
theorem msgDelivery:
  fixes t n n'' and sid::'sid and E e m
  assumes "t \<in> arch"
    and "\<parallel>sid\<parallel>\<^bsub>t n\<^esub>"
    and "sub E = sbsb (\<sigma>\<^bsub>sid\<^esub>(t n))"
    and "n'' \<ge> n"
    and "\<nexists>n' E'. n' \<ge> n \<and> n' \<le> n'' \<and> \<parallel>sid\<parallel>\<^bsub>t n'\<^esub> \<and> unsub E' = sbsb(\<sigma>\<^bsub>sid\<^esub>(t n'))
          \<and> e \<in> E'"
    and "e \<in> E"
    and "(e,m) = pbnt (\<sigma>\<^bsub>the_pb\<^esub>(t n''))"
    and "\<parallel>sid\<parallel>\<^bsub>t n''\<^esub>"
  shows "(e,m) \<in> sbnt (\<sigma>\<^bsub>sid\<^esub>(t n''))"
  using assms conn2 pb.ts_prop(2) by simp

text \<open>
  Since a publisher is actually a singleton, we can provide an alternative version of constraint @{thm[source] conn1}.
\<close>
lemma conn1A:
  fixes k
  shows "pbsb (\<sigma>\<^bsub>the_pb\<^esub>(k)) = (\<Union>sid\<in>{sid. \<parallel>sid\<parallel>\<^bsub>k\<^esub>}. {sbsb (\<sigma>\<^bsub>sid\<^esub>(k))})"
  using conn1[OF pb.ts_prop(2)] .
end
  
end