(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory FixedPointTheorems
imports
  HOLCF
begin

setup \<open>
  Thy_Output.antiquotation_raw \<^binding>\<open>haskell\<close> (Scan.lift Args.name)
    (fn _ => fn s => Latex.string ("\\" ^ "<" ^ s ^ "\\>"))
\<close>

(* LaTeXsugar fights with HOLCF syntax: at least cdot *)

(* THEOREMS *)
notation (Rule output)
  Pure.imp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>\\mbox{}\\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms"
  ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\\\\\<close>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

(*>*)
section\<open>Fixed-point theorems for program transformation\<close>

text\<open>

We begin by recounting some standard theorems from the early days of
denotational semantics. The origins of these results are lost to
history; the interested reader can find some of it in
\citet{Bekic:1969, Manna:1974, Greibach:1975, Stoy:1977,
DBLP:books/daglib/0002432, Harel:1980, Plotkin:1983, Winskel:1993,
DBLP:journals/toplas/Sangiorgi09}.

\<close>

subsection\<open>The rolling rule\<close>

text\<open>

The \emph{rolling rule} captures what intuitively happens when we
re-order a recursive computation consisting of two parts. This theorem
dates from the 1970s at the latest -- see \citet[p210]{Stoy:1977} and
\citet{Plotkin:1983}. The following proofs were provided by
\citet{GillHutton:2009}.

\<close>

lemma rolling_rule_ltr: "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
proof -
  have "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by (rule below_refl) \<comment> \<open>reflexivity\<close>
  hence "g\<cdot>((f oo g)\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_eq[where F="f oo g"] by simp \<comment> \<open>computation\<close>
  hence "(g oo f)\<cdot>(g\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by simp \<comment> \<open>re-associate @{term "(oo)"}\<close>
  thus "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_least_below by blast \<comment> \<open>induction\<close>
qed

lemma rolling_rule_rtl: "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
proof -
  have "fix\<cdot>(f oo g) \<sqsubseteq> f\<cdot>(fix\<cdot>(g oo f))" by (rule rolling_rule_ltr)
  hence "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(f\<cdot>(fix\<cdot>(g oo f)))"
    by (rule monofun_cfun_arg) \<comment> \<open>g is monotonic\<close>
  thus "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
    using fix_eq[where F="g oo f"] by simp \<comment> \<open>computation\<close>
qed

lemma rolling_rule: "fix\<cdot>(g oo f) = g\<cdot>(fix\<cdot>(f oo g))"
  by (rule below_antisym[OF rolling_rule_ltr rolling_rule_rtl])
(*

This property of a fixed-point operator is termed \emph{dinaturality}
by \citet{DBLP:conf/lics/SimpsonP00}.

*)

subsection\<open>Least-fixed-point fusion\<close>

text\<open>

\label{sec:lfp-fusion}

\emph{Least-fixed-point fusion} provides a kind of induction that has
proven to be very useful in calculational settings. Intuitively it
lifts the step-by-step correspondence between @{term "f"} and @{term
"h"} witnessed by the strict function @{term "g"} to the fixed points
of @{term "f"} and @{term "g"}:
\[
  \begin{diagram}
    \node{\bullet} \arrow{e,t}{h} \node{\bullet}\\
    \node{\bullet} \arrow{n,l}{g} \arrow{e,b}{f} \node{\bullet} \arrow{n,r}{g}
  \end{diagram}
  \qquad \Longrightarrow \qquad
  \begin{diagram}
    \node{\mathsf{fix}\ h}\\
    \node{\mathsf{fix}\ f} \arrow{n,r}{g}
  \end{diagram}
\]
\citet*{FokkingaMeijer:1991}, and also their later
\citet*{barbed-wire:1991}, made extensive use of this rule, as did
\citet{Tullsen:PhDThesis} in his program transformation tool PATH.
This diagram is strongly reminiscent of the simulations used to
establish refinement relations between imperative programs and their
specifications \citep*{EdR:cup98}.

The following proof is close to the third variant of
\citet[p215]{Stoy:1977}. We relate the two fixpoints using the rule
\texttt{parallel\_fix\_ind}:
\begin{center}
  @{thm[mode=Rule] parallel_fix_ind}
\end{center}
in a very straightforward way:

\<close>

lemma lfp_fusion:
  assumes "g\<cdot>\<bottom> = \<bottom>"
  assumes "g oo f = h oo g"
  shows "g\<cdot>(fix\<cdot>f) = fix\<cdot>h"
proof(induct rule: parallel_fix_ind)
  case 2 show "g\<cdot>\<bottom> = \<bottom>" by fact
  case (3 x y)
  from \<open>g\<cdot>x = y\<close> \<open>g oo f = h oo g\<close> show "g\<cdot>(f\<cdot>x) = h\<cdot>y"
    by (simp add: cfun_eq_iff)
qed simp

text\<open>

This lemma also goes by the name of \emph{Plotkin's axiom}
\citep{PittsAM:relpod} or \emph{uniformity}
\citep{DBLP:conf/lics/SimpsonP00}.

\<close>
(*<*)

(* The rest of this theory is only of historical interest. *)

text \<open>Some may find the pointed version easier to read.\<close>

lemma lfp_fusion_pointed:
  assumes Cfg: "\<And>f. C\<cdot>(F\<cdot>f) = G\<cdot>(C\<cdot>f)"
      and strictC: "C\<cdot>\<bottom> = \<bottom>"
  shows "C\<cdot>(fix\<cdot>F) = fix\<cdot>G"
  using lfp_fusion[where f=F and g=C and h=G] assms
  by (simp add: cfcomp1)

subsubsection\<open>More about \<open>lfp-fusion\<close>\<close>

text\<open>

Alternative proofs. This is the ``intuitive'' one
\citet[p125]{Gunter:1992} and \citet[p46]{Tullsen:PhDThesis}, where we
can shuffle @{term "g"} to the end of the the iteration of @{term "f"}
using @{term "fgh"}.

\<close>

lemma lfp_fusion2_aux:
  assumes fgh: "g oo f = h oo g"
  shows "g\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>) = iterate i\<cdot>h\<cdot>(g\<cdot>\<bottom>)"
proof(induct i)
  case (Suc i)
  have "g\<cdot>(iterate (Suc i)\<cdot>f\<cdot>\<bottom>) = (g oo f)\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>)" by simp
  also have "... = h\<cdot>(g\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>))" using fgh by (simp add: cfcomp1)
  also have "... = h\<cdot>(iterate i\<cdot>h\<cdot>(g\<cdot>\<bottom>))" using Suc by simp
  also have "... = iterate (Suc i)\<cdot>h\<cdot>(g\<cdot>\<bottom>)" by simp
  finally show ?case .
qed simp

lemma lfp_fusion2:
  assumes fgh: "g oo f = h oo g"
      and strictg: "g\<cdot>\<bottom> = \<bottom>"
  shows "g\<cdot>(fix\<cdot>f) = fix\<cdot>h"
proof -
  have "g\<cdot>(fix\<cdot>f) = g\<cdot>(\<Squnion>i. iterate i\<cdot>f\<cdot>\<bottom>)" by (simp only: fix_def2)
  also have "... = (\<Squnion>i. g\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>))" by (simp add: contlub_cfun_arg)
  also have "... = (\<Squnion>i. (iterate i\<cdot>h\<cdot>(g\<cdot>\<bottom>)))" by (simp only: lfp_fusion2_aux[OF fgh])
  also have "... = fix\<cdot>h" using strictg by (simp only: fix_def2)
  finally show ?thesis .
qed

text\<open>This is the first one by \citet[p213]{Stoy:1977}, almost
identical to the above.\<close>

lemma lfp_fusion3_aux:
  assumes fgh: "g oo f = h oo g"
      and strictg: "g\<cdot>\<bottom> = \<bottom>"
  shows "g\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>) = iterate i\<cdot>h\<cdot>\<bottom>"
proof(induct i)
  case 0 from strictg show ?case by simp
next
  case (Suc i)
  have "g\<cdot>(iterate (Suc i)\<cdot>f\<cdot>\<bottom>) = (g oo f)\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>)" by simp
  also have "... = h\<cdot>(g\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>))" using fgh by (simp add: cfcomp1)
  also have "... = h\<cdot>(iterate i\<cdot>h\<cdot>\<bottom>)" using Suc by simp
  also have "... = iterate (Suc i)\<cdot>h\<cdot>\<bottom>" by simp
  finally show ?case .
qed

lemma lfp_fusion3:
  assumes fgh: "g oo f = h oo g"
      and strictg: "g\<cdot>\<bottom> = \<bottom>"
  shows "g\<cdot>(fix\<cdot>f) = fix\<cdot>h"
proof -
  have "g\<cdot>(fix\<cdot>f) = g\<cdot>(\<Squnion>i. iterate i\<cdot>f\<cdot>\<bottom>)" by (simp only: fix_def2)
  also have "... = (\<Squnion>i. g\<cdot>(iterate i\<cdot>f\<cdot>\<bottom>))" by (simp add: contlub_cfun_arg)
  also have "... = (\<Squnion>i. (iterate i\<cdot>h\<cdot>\<bottom>))" by (simp only: lfp_fusion3_aux[OF fgh strictg])
  also have "... = fix\<cdot>h" by (simp only: fix_def2)
  finally show ?thesis .
qed

text\<open>Stoy's second proof \citep[p214]{Stoy:1977} is similar to the
original proof using fixed-point induction.\<close>

lemma lfp_fusion4:
  assumes fgh: "g oo f = h oo g"
      and strictg: "g\<cdot>\<bottom> = \<bottom>"
  shows "g\<cdot>(fix\<cdot>f) = fix\<cdot>h"
proof(rule below_antisym)
  show "fix\<cdot>h \<sqsubseteq> g\<cdot>(fix\<cdot>f)"
  proof -
    have "h\<cdot>(g\<cdot>(fix\<cdot>f)) = (g oo f)\<cdot>(fix\<cdot>f)" using fgh by simp
    also have "... = g\<cdot>(fix\<cdot>f)" by (subst fix_eq, simp)
    finally show ?thesis by (rule fix_least)
  qed
  let ?P = "\<lambda>x. g\<cdot>x \<sqsubseteq> fix\<cdot>h"
  show "?P (fix\<cdot>f)"
  proof(induct rule: fix_ind[where P="?P"])
    case 2 with strictg show ?case by simp
  next
    case (3 x) hence indhyp: "g\<cdot>x \<sqsubseteq> fix\<cdot>h" .
    have "g\<cdot>(f\<cdot>x) = (h oo g)\<cdot>x" using fgh[symmetric] by simp
    with indhyp show "g\<cdot>(f\<cdot>x) \<sqsubseteq> fix\<cdot>h"
      by (subst fix_eq, simp add: monofun_cfun)
  qed simp
qed

text\<open>A wrinkly variant from \citet[p11]{barbed-wire:1991}.\<close>

lemma lfp_fusion_barbed_variant:
  assumes ff': "f\<cdot>\<bottom> = f'\<cdot>\<bottom>"
      and fgh: "f oo g = h oo f"
      and f'g'h: "f' oo g' = h oo f'"
  shows "f\<cdot>(fix\<cdot>g) = f'\<cdot>(fix\<cdot>g')"
proof(induct rule: parallel_fix_ind)
  case 2 show "f\<cdot>\<bottom> = f'\<cdot>\<bottom>" by (rule ff')
  case (3 x y)
  from \<open>f\<cdot>x = f'\<cdot>y\<close> have "h\<cdot>(f\<cdot>x) = h\<cdot>(f'\<cdot>y)" by simp
  with fgh f'g'h have "f\<cdot>(g\<cdot>x) = f'\<cdot>(g'\<cdot>y)"
    using cfcomp2[where f="f" and g="g", symmetric]
          cfcomp2[where f="f'" and g="g'", symmetric]
    by simp
  thus ?case by simp
qed simp
(*>*)

(*<*)
end
(*>*)
