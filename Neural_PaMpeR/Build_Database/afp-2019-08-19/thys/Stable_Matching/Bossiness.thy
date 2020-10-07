(*<*)
theory Bossiness
imports
  COP
begin

(*>*)
section\<open> \citet{Kojima:2010}: The non-existence of a stable and non-bossy mechanism \label{sec:bossiness} \<close>

text (in Contracts) \<open>

\citet{Kojima:2010} says that ``a mechanism is @{emph \<open>nonbossy\<close>} if an
agent cannot change [the] allocation of other agents unless doing so
also changes her own allocation.'' He shows that no mechanism can be
both @{const "stable_on"} and @{emph \<open>nonbossy\<close>} in a one-to-one marriage
market. We establish this result in our matching-with-contracts
setting here.

There are two complications. Firstly, as not all agent preferences
yield stable matches (unlike the marriage market), we constrain
hospital choice functions to satisfy @{const
"ContractsWithBilateralSubstitutesAndIRC"}, which is the weakest
condition formalized here that ensures that @{const "fp_cop_F"} yields
stable matches. (We note that it is not the weakest condition
guaranteeing the existence of stable matches.)

Secondly, non-bossiness needs to separately treat the preferences of
the doctors and the choice functions of the hospitals.

We work in the @{const "Contracts"} locale for its types and the
constants @{term "Xd"} and @{term "Xh"}. To account for the
quantification over preferences, we directly use some raw constants
from the @{const "Contracts"} locale.

\<close>

context Contracts
begin

abbreviation (input) mechanism_domain :: "('d \<Rightarrow> 'x rel) \<Rightarrow> ('h \<Rightarrow> 'x cfun) \<Rightarrow> bool" where
  "mechanism_domain \<equiv> ContractsWithBilateralSubstitutesAndIRC Xd Xh"

definition nonbossy :: "'d set \<Rightarrow> ('d, 'h, 'x) mechanism \<Rightarrow> bool" where
  "nonbossy ds \<phi> \<longleftrightarrow>
    (\<forall>Pd Pd' Ch. \<forall>d\<in>ds. mechanism_domain Pd Ch \<and> mechanism_domain (Pd(d:=Pd')) Ch \<longrightarrow>
      dX (\<phi> Pd Ch ds) d = dX (\<phi> (Pd(d:=Pd')) Ch ds) d \<longrightarrow> \<phi> Pd Ch ds = \<phi> (Pd(d:=Pd')) Ch ds)
  \<and> (\<forall>Pd Ch Ch' h. mechanism_domain Pd Ch \<and> mechanism_domain Pd (Ch(h:=Ch')) \<longrightarrow>
      hX (\<phi> Pd Ch ds) h = hX (\<phi> Pd (Ch(h:=Ch')) ds) h \<longrightarrow> \<phi> Pd Ch ds = \<phi> Pd (Ch(h:=Ch')) ds)"

definition mechanism_stable :: "'d set \<Rightarrow> ('d, 'h, 'x) mechanism \<Rightarrow> bool" where
  "mechanism_stable ds \<phi>
     \<longleftrightarrow> (\<forall>Pd Ch. mechanism_domain Pd Ch \<longrightarrow> Contracts.stable_on Pd Ch ds (\<phi> Pd Ch ds))"

(*<*)

lemma nonbossy_Pd:
  assumes "nonbossy ds \<phi>"
  assumes "mechanism_domain Pd' Ch'"
  assumes "mechanism_domain (Pd'(d:=Pd'')) Ch'"
  assumes "dX (\<phi> Pd' Ch' ds) d = dX (\<phi> (Pd'(d:=Pd'')) Ch' ds) d"
  assumes "d \<in> ds"
  shows "\<phi> Pd' Ch' ds = \<phi> (Pd'(d:=Pd'')) Ch' ds"
using assms unfolding nonbossy_def by blast

lemma nonbossy_Ch:
  assumes "nonbossy ds \<phi>"
  assumes "mechanism_domain Pd' Ch'"
  assumes "mechanism_domain Pd' (Ch'(h:=Ch''))"
  assumes "hX (\<phi> Pd' Ch' ds) h = hX (\<phi> Pd' (Ch'(h:=Ch'')) ds) h"
  shows "\<phi> Pd' Ch' ds = \<phi> Pd' (Ch'(h:=Ch'')) ds"
using assms unfolding nonbossy_def by blast

(*>*)

end

text (in Contracts) \<open>

The proof is somewhat similar to those for Roth's impossibility
results (see, for instance, \citet[Theorem~4.4]{RothSotomayor:1990}).
It relies on the existence of at least three doctors, three hospitals,
and a complete set of contracts between these. The following locale
captures a suitable set of constraints.

\<close>

locale BossyConstants =
  fixes Xd :: "'x \<Rightarrow> 'd"
  fixes Xh :: "'x \<Rightarrow> 'h"
  fixes d1h1 d1h2 d1h3 :: 'x
  fixes d2h1 d2h2 d2h3 :: 'x
  fixes d3h1 d3h2 d3h3 :: 'x
  fixes ds :: "'d set"
  assumes ds: "distinct [Xd d1h1, Xd d2h1, Xd d3h1]"
  assumes hs: "distinct [Xh d1h1, Xh d1h2, Xh d1h3]"
  assumes Xd_xs:
    "Xd ` {d1h2, d1h3} = {Xd d1h1}"
    "Xd ` {d2h2, d2h3} = {Xd d2h1}"
    "Xd ` {d3h2, d3h3} = {Xd d3h1}"
  assumes Xh_xs:
    "Xh ` {d2h1, d3h1} = {Xh d1h1}"
    "Xh ` {d2h2, d3h2} = {Xh d1h2}"
    "Xh ` {d2h3, d3h3} = {Xh d1h3}"
  assumes dset: "{Xd d1h1, Xd d2h1, Xd d3h1} \<subseteq> ds"

locale ContractsWithBossyConstants =
  Contracts + BossyConstants
begin

abbreviation (input) "d1 \<equiv> Xd d1h1"
abbreviation (input) "d2 \<equiv> Xd d2h1"
abbreviation (input) "d3 \<equiv> Xd d3h1"

abbreviation (input) "h1 \<equiv> Xh d1h1"
abbreviation (input) "h2 \<equiv> Xh d1h2"
abbreviation (input) "h3 \<equiv> Xh d1h3"

(*<*)

lemma xs:
  shows "distinct [d1h1, d1h2, d1h3, d2h1, d2h2, d2h3, d3h1, d3h2, d3h3]"
using Xd_xs Xh_xs ds hs by auto

(*>*)

text\<open>

We proceed to show that variations on the following preferences for
doctors and hospitals force a stable mechanism to be bossy. Recall
that @{const "linord_of_list"} constructs a linear order from a list of
elements greatest to least. The hospital choice functions take at most
one contract from those on offer, and are again ordered from most
preferable to least.

\<close>

definition BPd :: "'b \<Rightarrow> 'a rel" where
  "BPd \<equiv> map_of_default {} [ (d1, linord_of_list [d1h3, d1h2, d1h1])
                           , (d2, linord_of_list [d2h3, d2h2, d2h1])
                           , (d3, linord_of_list [d3h1, d3h2, d3h3]) ]"

abbreviation mkhord :: "'d list \<Rightarrow> 'd cfun" where
  "mkhord xs X \<equiv> set_option (List.find (\<lambda>x. x\<in>X) xs)"

definition BCh :: "'c \<Rightarrow> 'a cfun" where
  "BCh \<equiv> map_of_default (\<lambda>_. {}) [ (h1, mkhord [d1h1, d2h1, d3h1])
                                 , (h2, mkhord [])
                                 , (h3, mkhord [d3h3, d2h3, d1h3]) ]"

text\<open>

Interpreting the @{const "Contracts"} locale gives us access to some
useful constants.

\<close>

interpretation Bossy: Contracts Xd Xh BPd BCh
using %invisible Xd_xs Xh_xs xs unfolding BPd_def BCh_def
by unfold_locales (auto simp: linord_of_list_Linear_order)

lemma BPd_BCh_mechanism_domain:
  shows "mechanism_domain BPd BCh"
by %invisible unfold_locales (auto simp: BCh_def bilateral_substitutes_on_def irc_on_def)

(*<*)

lemma BPd_simps:
  "BPd d1 = linord_of_list [d1h3, d1h2, d1h1]"
  "BPd d2 = linord_of_list [d2h3, d2h2, d2h1]"
  "BPd d3 = linord_of_list [d3h1, d3h2, d3h3]"
  "d \<notin> {d1, d2, d3} \<longleftrightarrow> BPd d = {}"
unfolding BPd_def using Xd_xs ds by auto

lemma BCh_simps:
  "BCh h1 = mkhord [d1h1, d2h1, d3h1]"
  "BCh h3 = mkhord [d3h3, d2h3, d1h3]"
  "h \<notin> {h1, h3} \<Longrightarrow> BCh h X = {}"
unfolding BCh_def using Xh_xs hs by auto

lemma Bossy_CD_on_Cd:
  shows "Bossy.CD_on ds X = Bossy.Cd d1 X \<union> Bossy.Cd d2 X \<union> Bossy.Cd d3 X" (is "?lhs = ?rhs")
proof(rule equalityI)
  show "?lhs \<subseteq> ?rhs"
    unfolding Bossy.CD_on_def by clarsimp (metis BPd_simps(4) Bossy.Cd_range' Field_empty Int_iff empty_iff insertE)
  from dset show "?rhs \<subseteq> ?lhs"
    unfolding Bossy.CD_on_def by blast
qed

lemma Bossy_CH_BCh:
  shows "Bossy.CH X = BCh h1 X \<union> BCh h3 X" (is "?lhs = ?rhs")
proof(rule equalityI)
  show "?lhs \<subseteq> ?rhs"
    unfolding Bossy.CH_def by clarsimp (simp add: BCh_def split: if_splits)
  show "?rhs \<subseteq> ?lhs"
    unfolding Bossy.CH_def by blast
qed

lemma Bossy_CH_range:
  assumes "X \<subseteq> Bossy.CH X'"
  shows "X \<subseteq> set [d1h1, d1h3, d2h1, d2h3, d3h1, d3h3]"
using assms by (auto simp: Bossy_CH_BCh BCh_simps split: if_splits)

(*>*)

lemma Bossy_stable:
  shows "Bossy.stable_on ds X \<longleftrightarrow> X = {d1h1, d3h3}"
(*<*) (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs with Xd_xs ds xs show ?rhs
    apply -
    apply (frule Bossy.stable_on_allocation)
    apply (frule Bossy.stable_on_CH)
    apply (frule Bossy.stable_on_CD_on)

    (* Enumerate all possible contracts *)
    apply (frule Bossy_CH_range[OF Set.equalityD2])
    apply (drule subset_subseqs)

    apply clarsimp
    apply (elim disjE)
    apply (simp_all add: Bossy_CH_BCh BCh_simps insert_eq_iff insert_commute)
    using Bossy.stable_on_blocking_onD[where h="h3" and X''="{d3h3}" and X="X" and ds=ds]
          Bossy.stable_on_blocking_onD[where h="h1" and X''="{d2h1}" and X="X" and ds=ds]
          Bossy.stable_on_blocking_onD[where h="h1" and X''="{d1h1}" and X="X" and ds=ds]
    apply (simp_all add: Bossy_CH_BCh BCh_simps Bossy_CD_on_Cd BPd_simps)
    done
next
  assume ?rhs show ?lhs
  proof(rule Bossy.stable_onI)
    show "Bossy.individually_rational_on ds X"
    proof(rule Bossy.individually_rational_onI)
      from xs \<open>?rhs\<close> show "Bossy.CD_on ds X = X" by clarsimp (force simp: Bossy_CD_on_Cd BPd_simps)
      from \<open>?rhs\<close> show "Bossy.CH X = X" by (simp add: Bossy_CH_BCh BCh_simps insert_commute)
    qed
    show "Bossy.stable_no_blocking_on ds X"
    proof(rule Bossy.stable_no_blocking_onI)
      fix h X'' assume XXX: "X'' = BCh h (X \<union> X'')" "X'' \<noteq> BCh h X" "X'' \<subseteq> Bossy.CD_on ds (X \<union> X'')"
      from \<open>?rhs\<close> XXX(1,2) have h: "h \<in> {h1, h3}" using BCh_simps by auto
      from XXX(1) have X'': "X'' \<subseteq> set [d1h1, d1h3, d2h1, d2h3, d3h1, d3h3]"
        using Bossy_CH_range[unfolded Bossy.CH_def] by blast
      from \<open>?rhs\<close> XXX h X'' Xh_xs hs xs show False
        apply -
        apply (drule subset_subseqs)
        apply clarsimp
        apply (elim disjE)
        apply (simp_all add: BCh_simps)
        done
    qed
  qed
qed

(*>*)
text\<open>

The second preference order has doctor @{const "d2"} reject all
contracts and is otherwise the same as the first.

\<close>

definition BPd' :: "'b \<Rightarrow> 'a rel" where
  "BPd' = BPd(d2 := {})"

interpretation Bossy': Contracts Xd Xh BPd' BCh
using %invisible Xd_xs Xh_xs xs unfolding BPd_def BPd'_def BCh_def
by unfold_locales (auto simp: linord_of_list_Linear_order)

lemma BPd'_BCh_mechanism_domain:
  shows "mechanism_domain BPd' BCh"
by %invisible unfold_locales (auto simp: BCh_def bilateral_substitutes_on_def irc_on_def)

(*<*)

lemma BPd'_simps:
  "BPd' d1 = linord_of_list [d1h3, d1h2, d1h1]"
  "BPd' d3 = linord_of_list [d3h1, d3h2, d3h3]"
  "d \<notin> {d1, d3} \<longleftrightarrow> BPd' d = {}"
unfolding BPd_def BPd'_def using Xd_xs ds by auto

lemma Bossy'_CD_on_Cd:
  "Bossy'.CD_on ds X = Bossy'.Cd d1 X \<union> Bossy'.Cd d3 X" (is "?lhs = ?rhs")
proof(rule equalityI)
  show "?lhs \<subseteq> ?rhs"
    unfolding Bossy'.CD_on_def by clarsimp (metis BPd'_simps(3) Bossy'.Cd_range' Field_empty Int_iff empty_iff insertE)
  from dset show "?rhs \<subseteq> ?lhs"
    unfolding Bossy'.CD_on_def by blast
qed

(*>*)

lemma Bossy'_stable:
  shows "Bossy'.stable_on ds X \<longleftrightarrow> X = {d1h3, d3h1} \<or> X = {d1h1, d3h3}"
(*<*) (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs
  with dset \<open>?lhs\<close> Xd_xs ds xs show ?rhs
    apply -
    apply (frule Bossy'.stable_on_allocation)
    apply (frule Bossy'.stable_on_CH)
    apply (frule Bossy'.stable_on_CD_on)

    (* Enumerate all possible contracts *)
    apply (frule Bossy_CH_range[OF Set.equalityD2])
    apply (drule subset_subseqs)

    apply clarsimp
    apply (elim disjE)
    apply (simp_all add: Bossy_CH_BCh BCh_simps insert_eq_iff insert_commute)
    using Bossy'.stable_on_blocking_onD[where h="h3" and X''="{d3h3}" and X="X" and ds=ds]
          Bossy'.stable_on_blocking_onD[where h="h1" and X''="{d1h1}" and X="X" and ds=ds]
    apply (simp_all add: Bossy_CH_BCh BCh_simps Bossy'_CD_on_Cd BPd'_simps)
    done
next
  assume ?rhs show ?lhs
  proof(rule Bossy'.stable_onI)
    show "Bossy'.individually_rational_on ds X"
    proof(rule Bossy'.individually_rational_onI)
      from ds xs \<open>?rhs\<close> show "Bossy'.CD_on ds X = X" by (force simp: Bossy'_CD_on_Cd BPd'_simps)
      from xs \<open>?rhs\<close> show "Bossy.CH X = X" by (force simp: Bossy_CH_BCh BCh_simps)
    qed
    show "Bossy'.stable_no_blocking_on ds X"
    proof(rule Bossy'.stable_no_blocking_onI)
      fix h X'' assume XXX: "X'' = BCh h (X \<union> X'')" "X'' \<noteq> BCh h X" "X'' \<subseteq> Bossy'.CD_on ds (X \<union> X'')"
      from \<open>?rhs\<close> XXX(1,2) have h: "h \<in> {h1, h2, h3}" using BCh_simps by auto
      from XXX(1) have X'': "X'' \<subseteq> set [d1h1, d1h3, d2h1, d2h3, d3h1, d3h3]"
        using Bossy_CH_range[unfolded Bossy.CH_def] by blast
      from \<open>?rhs\<close> XXX h X'' Xh_xs ds hs xs show False
        apply -
        apply (drule subset_subseqs)
        apply clarsimp
        apply (elim disjE)
        apply (simp_all add: BCh_simps)
        apply (simp_all add: Bossy'_CD_on_Cd Bossy'.maxR_def linord_of_list_linord_of_listP BPd'_simps)
        done
    qed
  qed
qed

(*>*)
text\<open>

The third preference order adjusts the choice function of hospital
@{const "h2"} and is otherwise the same as the second.

\<close>

definition BCh' :: "'c \<Rightarrow> 'a cfun" where
  "BCh' \<equiv> BCh(h2 := mkhord [d1h2, d2h2, d3h2])"

interpretation Bossy'': Contracts Xd Xh BPd' BCh'
using %invisible Xd_xs Xh_xs xs unfolding BPd_def BPd'_def BCh_def BCh'_def
by unfold_locales (auto simp: linord_of_list_Linear_order)

lemma BPd'_BCh'_mechanism_domain:
  shows "mechanism_domain BPd' BCh'"
by %invisible unfold_locales (auto simp: BCh_def BCh'_def bilateral_substitutes_on_def irc_on_def)

(*<*)

lemma BCh'_simps:
  "BCh' h1 = mkhord [d1h1, d2h1, d3h1]"
  "BCh' h2 = mkhord [d1h2, d2h2, d3h2]"
  "BCh' h3 = mkhord [d3h3, d2h3, d1h3]"
  "h \<notin> {h1, h2, h3} \<Longrightarrow> BCh' h X = {}"
unfolding BCh_def BCh'_def using Xh_xs hs by auto

lemma Bossy''_CH_BCh':
  "Bossy''.CH X = BCh' h1 X \<union> BCh' h2 X \<union> BCh' h3 X" (is "?lhs = ?rhs")
proof(rule equalityI)
  show "?lhs \<subseteq> ?rhs"
    unfolding Bossy''.CH_def by clarsimp (simp add: BCh_def BCh'_def split: if_splits)
  show "?rhs \<subseteq> ?lhs"
    unfolding Bossy''.CH_def by blast
qed

lemma Bossy''_CD_on_range:
  assumes "X \<subseteq> Bossy''.CD_on ds X'"
  shows "X \<subseteq> set [d1h1, d1h2, d1h3, d3h1, d3h2, d3h3]"
using assms by (auto simp: Bossy'_CD_on_Cd BPd'_simps dest!: Bossy''.Cd_range')

(*>*)

lemma Bossy''_stable:
  shows "Bossy''.stable_on ds X \<longleftrightarrow> X = {d3h1, d1h3}"
(*<*) (is "?lhs = ?rhs")
proof(rule iffI)
  assume ?lhs with Xd_xs ds xs show ?rhs
    apply -
    apply (frule Bossy''.stable_on_allocation)
    apply (frule Bossy''.stable_on_CH)
    apply (frule Bossy''.stable_on_CD_on)

    (* Enumerate all possible contracts *)
    apply (frule Bossy''_CD_on_range[OF Set.equalityD2])
    apply (drule subset_subseqs)

    apply clarsimp
    apply (elim disjE)
    apply (simp_all add: Bossy''_CH_BCh' BCh'_simps insert_eq_iff insert_commute)
    using Bossy''.stable_on_blocking_onD[where h="h1" and X''="{d3h1}" and X="X" and ds=ds]
          Bossy''.stable_on_blocking_onD[where h="h2" and X''="{d1h2}" and X="X" and ds=ds]
          Bossy''.stable_on_blocking_onD[where h="h3" and X''="{d1h3}" and X="X" and ds=ds]
    apply (simp_all add: BCh'_simps Bossy'_CD_on_Cd BPd'_simps)
    apply (simp_all add: Bossy''.maxR_def linord_of_list_linord_of_listP BPd'_simps)
    done
next
  assume ?rhs show ?lhs
  proof(rule Bossy''.stable_onI)
    show "Bossy''.individually_rational_on ds X"
    proof(rule Bossy''.individually_rational_onI)
      from ds xs \<open>?rhs\<close> show "Bossy''.CD_on ds X = X" by (force simp: Bossy'_CD_on_Cd BPd'_simps)
      from xs \<open>?rhs\<close> show "Bossy''.CH X = X" by (force simp: Bossy''_CH_BCh' BCh'_simps)
    qed
    show "Bossy''.stable_no_blocking_on ds X"
    proof(rule Bossy''.stable_no_blocking_onI)
      fix h X'' assume XXX: "X'' = BCh' h (X \<union> X'')" "X'' \<noteq> BCh' h X" "X'' \<subseteq> Bossy''.CD_on ds (X \<union> X'')"
      from \<open>?rhs\<close> XXX(1,2) have h: "h \<in> {h1, h2, h3}" using BCh'_simps by auto
      from XXX(3) have X'': "X'' \<subseteq> set [d1h1, d1h2, d1h3, d3h1, d3h2, d3h3]"
        using Bossy''_CD_on_range by blast
      from \<open>?rhs\<close> XXX h X'' Xh_xs ds hs xs show False
        apply -
        apply (drule subset_subseqs)
        apply clarsimp
        apply (elim disjE)
        apply (simp_all add: BCh'_simps)
        apply (simp_all add: Bossy'_CD_on_Cd BPd'_simps Bossy'.maxR_def linord_of_list_linord_of_listP)
        done
    qed
  qed
qed

(*>*)
text\<open>\<close>

theorem Theorem_1:
  shows "\<not>(mechanism_stable ds \<phi> \<and> nonbossy ds \<phi>)"
proof(rule notI, erule conjE)
  assume S: "Bossy.mechanism_stable ds \<phi>"
  assume NB: "Bossy.nonbossy ds \<phi>"
  from S Bossy'_stable BPd'_BCh_mechanism_domain
  consider (A) "\<phi> BPd' BCh ds = {d1h3, d3h1}" | (B) "\<phi> BPd' BCh ds = {d1h1, d3h3}"
    unfolding mechanism_stable_def by blast
  then show False
  proof cases
    case A
    from S BPd_BCh_mechanism_domain Bossy_stable have "\<phi> BPd BCh ds = {d1h1, d3h3}"
      unfolding mechanism_stable_def by blast
    with Xd_xs ds xs dset A show False
      using nonbossy_Pd[OF NB BPd_BCh_mechanism_domain BPd'_BCh_mechanism_domain[unfolded BPd'_def]]
      unfolding BPd'_def[symmetric] dX_def by fastforce
  next
    case B
    from S BPd'_BCh'_mechanism_domain Bossy''_stable have "\<phi> BPd' BCh' ds = {d3h1, d1h3}"
      unfolding mechanism_stable_def by blast
    with Xh_xs hs xs dset B show False
      using nonbossy_Ch[OF NB BPd'_BCh_mechanism_domain BPd'_BCh'_mechanism_domain[unfolded BCh'_def]]
      unfolding BCh'_def[symmetric] hX_def by fastforce
  qed
qed

text\<open>

In particular, the COP (see \S\ref{sec:cop}) is bossy as it always
yields stable matches under @{const "mechanism_stable"}.

\<close>

theorem Theorem_1_COP:
  "\<not>nonbossy ds Contracts.cop"
using ContractsWithBilateralSubstitutesAndIRC.Theorem_1 Theorem_1 mechanism_stable_def by blast

end

text\<open>

Therefore doctors can interfere with other doctors' allocations under
the COP without necessarily disadvantaging themselves, which has
implications for the notion of @{emph \<open>group strategy-proof\<close>}
\citep{HatfieldKojima:2009}; see \S\ref{sec:strategic-gsp}.

\<close>
(*<*)

end
(*>*)
