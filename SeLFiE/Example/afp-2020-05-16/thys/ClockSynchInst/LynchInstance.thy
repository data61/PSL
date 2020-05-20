(*  Title:       Instances of Schneider's generalized protocol of clock synchronization
    Author:      Damián Barsotti <damian at hal.famaf.unc.edu.ar>, 2006
    Maintainer:  Damián Barsotti <damian at hal.famaf.unc.edu.ar>
*)

section \<open>Fault-tolerant Midpoint algorithm\<close>

theory LynchInstance imports Complex_Main begin

text \<open>This algorithm is presented in \cite{lynch_cs}.\<close>

subsection \<open>Model of the system\<close>

text \<open>The main ideas for the formalization of the system were
obtained from \cite{shankar92mechanical}.\<close>

subsubsection \<open>Types in the formalization\<close>

text \<open>The election of the basics types was based on
\cite{shankar92mechanical}. There, the process are natural numbers and
the real time and the clock readings are reals.\<close>

type_synonym process = nat  
type_synonym time = real      \<comment> \<open>real time\<close>
type_synonym Clocktime = real \<comment> \<open>time of the clock readings (clock time)\<close>

subsubsection \<open>Some constants\<close>

text\<open>Here we define some parameters of the algorithm that we use:
the number of process and the number of lowest and highest readed
values that the algorithm discards. The defined constants must satisfy
this axiom. If not, the algorithm cannot obtain the maximum and
minimum value, because it will have discarded all the values.\<close>

axiomatization
  np  :: nat  \<comment> \<open>Number of processes\<close> and
  khl :: nat  \<comment> \<open>Number of lowest and highest values\<close> where
  constants_ax: "2 * khl < np"

text \<open>We define also the set of process that the algorithm
manage. This definition exist only for readability matters.\<close>

definition
PR :: "process set" where
[simp]: "PR = {..<np}"


subsubsection \<open>Convergence function\<close>

text \<open>This functions is called ``Fault-tolerant Midpoint''
(\cite{schneider87understanding})\<close>

text \<open>In this algorithm each process has an array where it store the
clocks readings from the others processes (including itself). We
formalise that as a function from processes to clock time as
\cite{shankar92mechanical}.\<close>

text \<open>First we define two functions. They take a function of clock
readings and a set of processes and they return a set of @{term khl}
processes which has the greater (smaller) clock readings. They were
defined with the Hilbert's $\varepsilon$-operator (the indefinite
description operator \<open>SOME\<close> in Isabelle) because in this way the
formalization is not fixed to a particular eleccion of the processes's
readings to discards and then the modelization is more general.\<close>

definition
kmax :: "(process \<Rightarrow> Clocktime) \<Rightarrow> process set \<Rightarrow> process set" where
"kmax f P = (SOME S. S \<subseteq> P \<and> card S = khl \<and> 
                (\<forall> i\<in>S. \<forall> j\<in>(P-S). f j <= f i))"

definition
kmin :: "(process \<Rightarrow> Clocktime) \<Rightarrow> process set \<Rightarrow> process set" where
"kmin f P = (SOME S. S \<subseteq> P \<and> card S = khl \<and> 
                (\<forall> i\<in>S. \<forall> j\<in>(P-S). f i <= f j))"

text \<open>With the previus functions we define a new one @{term
reduce}\footnote{The name of this function was taken from
\cite{lynch_cs}.}. This take a function of clock readings and a set of
processes and return de set of readings of the not dicarded
processes. In order to define this function we use the image operator
(@{term "(`)"}) of Isabelle.\<close>

definition
reduce :: "(process \<Rightarrow> Clocktime) \<Rightarrow> process set \<Rightarrow> Clocktime set" where
"reduce f P = f ` (P - (kmax f P \<union> kmin f P))"

text \<open>And finally the convergence function. This is defined with the
builtin @{term Max} and @{term Min} functions of Isabelle.
\<close>

definition
cfnl :: "process  \<Rightarrow> (process \<Rightarrow> Clocktime) \<Rightarrow> Clocktime" where
"cfnl p f = (Max (reduce f PR) + Min (reduce f PR)) / 2"


subsection \<open>Translation Invariance property.\<close>

subsubsection \<open>Auxiliary lemmas\<close>

text \<open>These lemmas proves the existence of the maximum and minimum
of the image of a set, if the set is finite and not empty.\<close>

(* The proofs are almost the same one that those of the lemmas @{thm *)
(* [source] ex_Max} and @{thm [source] ex_Min} in the Isabelle's standard *)
(* theories. *)

lemma ex_Maxf:
fixes S and f :: "'a \<Rightarrow> ('b::linorder)"
  assumes fin: "finite S" 
  shows "S \<noteq> {} ==> \<exists>m\<in>S. \<forall>s \<in> S. f s \<le> f m"
using fin
proof (induct)
  case empty thus ?case by simp
next
  case (insert x S)
  show ?case
  proof (cases)
    assume "S = {}" thus ?thesis by simp
  next
    assume nonempty: "S \<noteq> {}"
    then obtain m where m: "m\<in>S" "\<forall>s\<in>S. f s \<le> f m" 
      using insert by blast
    show ?thesis
    proof (cases)
      assume "f x \<le> f m" thus ?thesis using m by blast
    next
      assume "~ f x \<le> f m" thus ?thesis using m
        by(simp add:linorder_not_le order_less_le)
          (blast intro: order_trans)
    qed
  qed
qed

lemma ex_Minf:
fixes S and f :: "'a \<Rightarrow> ('b::linorder)"
  assumes fin: "finite S" 
  shows "S \<noteq> {} ==> \<exists>m\<in>S. \<forall>s \<in> S. f m \<le> f s"
using fin
proof (induct)
  case empty thus ?case by simp
next
  case (insert x S)
  show ?case
  proof (cases)
    assume "S = {}" thus ?thesis by simp
  next
    assume nonempty: "S \<noteq> {}"
    then obtain m where m: "m\<in>S" "\<forall>s\<in>S. f m \<le> f s" 
      using insert by blast
    show ?thesis
    proof (cases)
      assume "f m \<le> f x" thus ?thesis using m by blast
    next
      assume "~ f m \<le> f x" thus ?thesis using m
        by(simp add:linorder_not_le order_less_le)
          (blast intro: order_trans)
    qed
  qed
qed

text \<open>This trivial lemma is needed by the next two.\<close>

lemma khl_bound: "khl < np"
  using constants_ax by arith

text \<open>The next two lemmas prove that de functions kmin and kmax
return some values that satisfy their definition. This is not trivial
because we need to prove the existence of these values, according to
the rule of the Hilbert's operator. We will need this lemma many
times because is the only thing that we know about these functions.\<close>

lemma kmax_prop:
fixes f :: "nat \<Rightarrow> Clocktime"
  shows
"(kmax f PR) \<subseteq> PR \<and> card (kmax f PR) = khl \<and> 
                (\<forall>i\<in>(kmax f PR). \<forall>j\<in>PR - (kmax f PR). f j \<le> f i)"
proof-
  have "khl <= np \<longrightarrow> 
    (\<exists> S. S \<subseteq> PR \<and> card S = khl \<and> (\<forall>i\<in>S. \<forall>j\<in>PR - S. f j \<le> f i))"
    ( is "khl <= np \<longrightarrow> ?P khl" )
  proof(induct (khl))
    have "?P 0" by force
    thus "0 <= np \<longrightarrow> ?P 0" ..
  next
    fix n 
    assume asm: "n <= np \<longrightarrow> ?P n" 
    show "Suc n <= np \<longrightarrow> ?P (Suc n)"
    proof
      assume asm2: "Suc n <= np"
      with asm have "?P n" by simp
      then obtain S where
        SinPR : "S\<subseteq>PR" and 
        cardS: "card S = n" and 
        HI: "(\<forall>i\<in>S. \<forall>j\<in>PR - S. f j \<le> f i)" 
        by blast
      let ?e = "SOME i. i\<in>PR-S \<and> 
        (\<forall>j\<in>PR-S. f j \<le> f i)"
      let ?S = "insert  ?e S"
      have "\<exists>i. i\<in>PR-S \<and> (\<forall>j\<in>PR-S. f j \<le> f i)"
      proof-
        from SinPR and finite_subset 
        have "finite (PR-S)" 
          by auto
        moreover
        from cardS and asm2 SinPR
        have "S\<subset>PR" by auto
        hence "PR-S \<noteq> {}" by auto
        ultimately
        show ?thesis using ex_Maxf by blast
      qed
      hence 
        ePRS: "?e \<in> PR-S" and maxH: "(\<forall>j \<in> PR-S. f j \<le> f ?e)"
        by (auto dest!: someI_ex)
      from maxH and HI
      have "(\<forall>i\<in>?S. \<forall>j\<in>PR - ?S. f j \<le> f i)"
        by blast
      moreover
      from SinPR and finite_subset 
      cardS and ePRS 
      have "card ?S = Suc n"  
        by (auto dest: card_insert_disjoint)
      moreover
      have "?S \<subseteq> PR" using SinPR and ePRS by auto
      ultimately
      show "?P (Suc n)" by blast
    qed
  qed
  hence "?P khl" using khl_bound by auto
  then obtain S where 
    "S\<le>PR \<and> card S = khl \<and> (\<forall>i\<in>S. \<forall>j\<in>PR - S. f j \<le> f i)" ..
    thus ?thesis by (unfold kmax_def)
      (rule someI [where P="\<lambda>S. S \<subseteq> PR \<and> card S = khl \<and> (\<forall>i\<in>S. \<forall>j\<in>PR - S. f j \<le> f i)"])
qed

lemma kmin_prop:
fixes f :: "nat \<Rightarrow> Clocktime"
  shows
"(kmin f PR) \<subseteq> PR \<and> card (kmin f PR) = khl \<and> 
                (\<forall>i\<in>(kmin f PR). \<forall>j\<in>PR - (kmin f PR). f i \<le> f j)"
proof-
  have "khl <= np \<longrightarrow> 
    (\<exists> S. S \<subseteq> PR \<and> card S = khl \<and> (\<forall>i\<in>S. \<forall>j\<in>PR - S. f i \<le> f j))"
    ( is "khl <= np \<longrightarrow> ?P khl" )
  proof(induct (khl))
    have "?P 0" by force
    thus "0 <= np \<longrightarrow> ?P 0" ..
  next
    fix n 
    assume asm: "n <= np \<longrightarrow> ?P n" 
    show "Suc n <= np \<longrightarrow> ?P (Suc n)"
    proof
      assume asm2: "Suc n <= np"
      with asm have "?P n" by simp
      then obtain S where
        SinPR : "S\<subseteq>PR" and 
        cardS: "card S = n" and 
        HI: "(\<forall>i\<in>S. \<forall>j\<in>PR - S. f i \<le> f j)" 
        by blast
      let ?e = "SOME i. i\<in>PR-S \<and> 
        (\<forall>j\<in>PR-S. f i \<le> f j)"
      let ?S = "insert  ?e S"
      have "\<exists>i. i\<in>PR-S \<and> (\<forall>j\<in>PR-S. f i \<le> f j)"
      proof-
        from SinPR and finite_subset 
        have "finite (PR-S)" 
          by auto
        moreover
        from cardS and asm2 SinPR
        have "S\<subset>PR" by auto
        hence "PR-S \<noteq> {}" by auto
        ultimately
        show ?thesis using ex_Minf by blast
      qed
      hence 
        ePRS: "?e \<in> PR-S" and minH: "(\<forall>j \<in> PR-S. f ?e \<le> f j)"
        by (auto dest!: someI_ex)
      from minH and  HI 
      have "(\<forall>i\<in>?S. \<forall>j\<in>PR - ?S. f i \<le> f j)"
        by blast
      moreover
      from SinPR and finite_subset and
        cardS and ePRS
      have "card ?S = Suc n" 
        by (auto dest: card_insert_disjoint)
      moreover
      have "?S \<subseteq> PR" using SinPR and ePRS by auto
      ultimately
      show "?P (Suc n)" by blast
    qed
  qed
  hence "?P khl" using khl_bound by auto
  then obtain S where 
    "S\<le>PR \<and> card S = khl \<and> (\<forall>i\<in>S. \<forall>j\<in>PR - S. f i \<le> f j)" ..
    thus ?thesis by (unfold kmin_def)
      (rule someI [where P="\<lambda>S. S \<subseteq> PR \<and> card S = khl \<and> (\<forall>i\<in>S. \<forall>j\<in>PR - S. f i \<le> f j)"])
qed

text \<open>The next two lemmas are trivial from the previous ones\<close>

lemma finite_kmax:
"finite (kmax f PR)"
proof-
  have "finite PR" by auto
  with  kmax_prop and finite_subset show ?thesis
    by blast
qed

lemma finite_kmin:
"finite (kmin f PR)"
proof-
  have "finite PR" by auto
  with  kmin_prop and finite_subset show ?thesis
    by blast
qed

text \<open>This lemma is necesary because the definition of the
convergence function use the builtin Max and Min.\<close>

lemma reduce_not_empty:
"reduce f PR \<noteq> {}"
proof-
  from constants_ax have 
    "0 < (np - 2 * khl)" by arith
  also
  {
    from kmax_prop kmin_prop 
    have "card (kmax f PR) = khl \<and> card (kmin f PR) = khl" 
      by blast
    hence "card (kmax f PR \<union> kmin f PR) <= 2 * khl"
    using card_Un_le[of "kmax f PR" "kmin f PR"] by simp
  }
  hence 
    "... <= card PR - card (kmax f PR \<union> kmin f PR)"
    by simp
  also
  {
    from kmax_prop and kmin_prop have
    "(kmax f PR \<union> kmin f PR) \<subseteq> PR" by blast
  }
  hence
    "... = card (PR-(kmax f PR \<union> kmin f PR))"
    apply (intro card_Diff_subset[THEN sym])
    apply (rule finite_subset)
    by auto
    (* by (intro card_Diff_subset,auto) *)
  finally
  have "0 < card (PR-(kmax f PR \<union> kmin f PR))" .
  hence "(PR-(kmax f PR \<union> kmin f PR)) \<noteq> {}"
    by (intro notI, simp only: card_0_eq, simp)
  thus ?thesis
    by (auto simp add: reduce_def)
qed

text \<open>The next three are the main lemmas necessary for prove the
Translation Invariance property.\<close>

lemma reduce_shift:
fixes f :: "nat \<Rightarrow> Clocktime"
  shows
  "f ` (PR - (kmax f PR \<union> kmin f PR)) = 
            f ` (PR - (kmax (\<lambda> p. f p + c) PR \<union> kmin (\<lambda> p. f p + c) PR))"
apply (unfold kmin_def kmax_def)
by simp

lemma max_shift:
fixes f :: "nat \<Rightarrow> Clocktime" and S
assumes notEmpFin: "S \<noteq> {}" "finite S"
shows
"Max (f`S) + x = Max ( (\<lambda> p. f p + x) ` S) "
proof-  
  from notEmpFin have "f`S \<noteq> {}" and "(\<lambda> p. f p + x) ` S \<noteq> {}"
    by auto
  with notEmpFin have
    "Max (f`S) \<in> f ` S " "Max ((\<lambda> p. f p + x)`S) \<in> (\<lambda> p. f p + x) ` S "
    "(\<forall>fs \<in> (f`S). fs \<le> Max (f`S))" 
    "(\<forall>fs \<in> ((\<lambda> p. f p + x)`S). fs \<le> Max ((\<lambda> p. f p + x)`S))"
    by auto
  thus ?thesis by force
qed
  
lemma min_shift:
fixes f :: "nat \<Rightarrow> Clocktime" and S
assumes notEmpFin: "S \<noteq> {}" "finite S"
shows
"Min (f`S) + x = Min ( (\<lambda> p. f p + x) ` S) "
proof-
  from notEmpFin have "f`S \<noteq> {}" and "(\<lambda> p. f p + x) ` S \<noteq> {}"
    by auto
  with notEmpFin have
    "Min (f`S) \<in> f ` S " "Min ((\<lambda> p. f p + x)`S) \<in> (\<lambda> p. f p + x) ` S "
    "(\<forall>fs \<in> (f`S). Min (f`S) <= fs)" 
    "(\<forall>fs \<in> ((\<lambda> p. f p + x)`S). Min ((\<lambda> p. f p + x)`S) <= fs)"
    by auto
  thus ?thesis by force
qed

subsubsection \<open>Main theorem\<close>
  
theorem trans_inv: 
fixes f :: "nat \<Rightarrow> Clocktime"
  shows
"cfnl p f + x = cfnl p (\<lambda> p. f p + x)"
proof-
  have "cfnl p (\<lambda> p. f p + x) = 
      (Max (reduce (\<lambda> p. f p + x) PR) + Min (reduce (\<lambda> p. f p + x) PR)) / 2" 
    by (unfold cfnl_def, simp)
  also
  have "... = 
    (Max ((\<lambda> p. f p + x) ` 
             (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR))) + 
     Min ((\<lambda> p. f p + x) ` 
             (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR)))) / 2"
    by (unfold reduce_def, simp)
  also
  have
    "... = 
    (Max (f ` 
             (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR))) + x + 
     Min (f ` 
             (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR))) + x ) / 2"
  proof-
    have "finite (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR))"
      by auto
    moreover
    from reduce_not_empty have 
      "PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR) \<noteq> {}"
      by (auto simp add: reduce_def)
    ultimately
    have 
      "Max ((\<lambda> p. f p + x) ` 
       (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR)))
      = 
       Max (f ` 
             (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR))) + x"
       and 
      "Min ((\<lambda> p. f p + x) ` 
       (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR)))
      = 
       Min (f ` 
             (PR - (kmax (\<lambda> p. f p + x) PR \<union> kmin (\<lambda> p. f p + x) PR))) + x"
      using max_shift and min_shift
      by auto
    thus ?thesis by auto
  qed
  also
  from reduce_shift
  have
    "... = 
    (Max (f ` 
             (PR - (kmax f  PR \<union> kmin f PR))) + x + 
     Min (f ` 
             (PR - (kmax f PR \<union> kmin f PR))) + x ) / 2"
    by auto
  also
  have "... = ((Max (reduce f PR)+ x) + (Min (reduce f PR) + x)) / 2"
    by (auto simp add: reduce_def)
  also
  have "... = (Max (reduce f PR) + Min (reduce f PR)) / 2 + x" 
    by auto
  finally
  show ?thesis by (auto simp add: cfnl_def) 
qed


subsection \<open>Precision Enhancement property\<close>

text \<open>An informal proof of this theorem can be found in \cite{miner93}\<close>

subsubsection \<open>Auxiliary lemmas\<close>

text \<open>This first lemma is most important for prove the
property. This is a consecuence of the @{thm [source] card_Un_Int}
lemma\<close>

lemma pigeonhole:
assumes
  finitA: "finite A" and 
  Bss: "B \<subseteq> A" and Css: "C \<subseteq> A" and 
  cardH: "card A + k <= card B + card C"
shows "k <= card (B \<inter> C)"
proof-
  from Bss Css have "B \<union> C \<subseteq> A" by blast
  with finitA have "card (B \<union> C) <= card A"
    by (simp add: card_mono)
  with cardH have
      h: "k <= card B + card C - card (B \<union> C)" 
    by arith
  from finitA Bss Css and finite_subset 
  have "finite B \<and> finite C" by auto
  thus ?thesis
    using card_Un_Int and h by force
qed

text \<open>This lemma is a trivial consecuence of the previous one. With
only this lemma we can prove the Precision Enhancement property with
the bound $\pi(x,y) = x + y$. But this bound not satisfy the property
\[ \pi(2\Lambda + 2 \beta\rho, \delta_S + 2\rho(r_{max}+\beta) +
2\Lambda) \leq \delta_S 
\] that is used in \cite{shankar92mechanical} for prove the
Schneider's schema.\<close>

lemma subsets_int:
assumes
  finitA: "finite A" and 
  Bss: "B \<subseteq> A" and Css: "C \<subseteq> A" and 
  cardH: "card A < card B + card C"
shows
  "B \<inter> C \<noteq> {}"
proof-
  from finitA Bss Css cardH
  have "1 <= card (B \<inter> C)"
    by (auto intro!:  pigeonhole)
  thus ?thesis by auto
qed

text \<open>This lemma is true because @{term "reduce f PR"} is the image
of @{term "PR-(kmax f PR \<union> kmin f PR)"} by the function @{term f}.\<close>

lemma exist_reduce:
"\<forall> c \<in> reduce f PR. \<exists> i\<in> PR-(kmax f PR \<union> kmin f PR). f i = c"
proof
fix c assume asm: "c \<in> reduce f PR"
thus "\<exists> i\<in> PR-(kmax f PR \<union> kmin f PR). f i = c"
  by (auto simp add: reduce_def kmax_def kmin_def)
qed

text \<open>The next three lemmas are consequence of the definition of
@{term reduce}, @{term kmax} and @{term kmin}\<close>
 
lemma finite_reduce:
"finite (reduce f PR)"
proof(unfold reduce_def)
  show "finite (f ` (PR - (kmax f PR \<union> kmin f PR)))"
    by auto
qed

lemma kmax_ge:
  "\<forall> i\<in> (kmax f PR). \<forall> r \<in> (reduce f PR). r <= f i "
proof
  fix i assume asm: "i \<in> kmax f PR"
  show "\<forall>r\<in>reduce f PR. r \<le> f i"
  proof
    fix r assume asm2: "r \<in> reduce f PR"
    show "r \<le> f i"
    proof-
      from asm2 and exist_reduce have
        "\<exists> j \<in> PR-(kmax f PR \<union> kmin f PR). f j = r" by blast
      then obtain j 
      where fjr:"j \<in> PR-(kmax f PR \<union> kmin f PR) \<and> f j = r" 
        by blast
      hence "j \<in> (PR - kmax f PR)"
        by blast
      from this fjr asm  
      show ?thesis using kmax_prop
        by auto
    qed
  qed
qed

lemma kmin_le:
  "\<forall> i\<in> (kmin f PR). \<forall> r \<in> (reduce f PR). f i <= r "
proof
  fix i assume asm: "i \<in> kmin f PR"
  show "\<forall>r\<in>reduce f PR. f i \<le> r"
  proof
    fix r assume asm2: "r \<in> reduce f PR"
    show "f i <= r"
    proof-
      from asm2 and exist_reduce have
        "\<exists> j\<in> PR-(kmax f PR \<union> kmin f PR). f j = r" by blast
      then obtain j 
      where fjr:"j \<in> PR-(kmax f PR \<union> kmin f PR) \<and> f j = r" 
        by blast
      hence "j \<in> (PR - kmin f PR)"
        by blast
      from this fjr asm  
      show ?thesis using kmin_prop
        by auto
    qed
  qed
qed

text \<open>The next lemma is used for prove the Precision Enhancement
property. This has been proved in ICS. The proof is in the appendix
\ref{sec:abs_distrib_mult}.  This cannot be prove by a simple \<open>arith\<close> or \<open>auto\<close> tactic.\<close>

text\<open>This lemma is true also with \<open>0 <= c\<close> !!\<close>


lemma abs_distrib_div:
  "0 < (c::real)  \<Longrightarrow> \<bar>a / c - b / c\<bar> = \<bar>a - b\<bar> / c"
proof-
  assume ch: "0<c"
  {
    fix d :: real
    assume dh: "0<=d"
    have "a * d - b * d = (a - b) * d "
      by (simp add: algebra_simps)
    hence "\<bar>a * d - b * d\<bar> = \<bar>(a - b) * d\<bar>"
      by simp
    also with dh have
      "... = \<bar>a - b\<bar> * d"
      by (simp add: abs_mult)
    finally
      have "\<bar>a * d - b * d\<bar> = \<bar>a - b\<bar> * d"
        .
    (* This sublemma is solved by ICS, file: abs_distrib_mult.ics *)
    (* It is not solved nor 
       by (auto simp add: distrib_right diff_minus)(arith) 
        in Isabelle  *)
  }
  with ch and divide_inverse show ?thesis
    by (auto simp add: divide_inverse)
qed

text \<open>The next three lemmas are about the existence of bounds of the
values @{term "Max (reduce f PR)"} and @{term "Min (reduce f PR)"}. These
are used in the proof of the main property.\<close>

lemma uboundmax:
assumes 
  hC: "C \<subseteq> PR" and
  hCk: "np <= card C + khl"
shows
  "\<exists> i\<in>C. Max (reduce f PR) <= f i"
proof-
  from reduce_not_empty and finite_reduce 
  have maxrinr: "Max (reduce f PR) \<in> reduce f PR" 
    by simp
  with exist_reduce
  have "\<exists> i\<in> PR-(kmax f PR \<union> kmin f PR). f i = Max (reduce f PR)"
    by simp
  then obtain pmax where 
    pmax_in_reduc: "pmax \<in> PR-(kmax f PR \<union> kmin f PR)" and 
    fpmax_ismax: "f pmax = Max (reduce f PR)" ..
  hence "C \<inter> insert pmax (kmax f PR)  \<noteq> {}"
  proof-
    from kmax_prop and pmax_in_reduc 
      and finite_kmax and hCk  have 
      "card PR < card C + card (insert pmax (kmax f PR))"
      by simp
    moreover
    from pmax_in_reduc and kmax_prop
    have "insert pmax (kmax f PR) \<subseteq> PR" by blast
    moreover
    note hC
    ultimately
    show ?thesis 
      using subsets_int[of PR C "insert pmax (kmax f PR)"]
      by simp
  qed
  hence res: "\<exists> i\<in>C. i=pmax \<or> i \<in> kmax f PR" by blast
  then obtain i where
    iinC: "i\<in>C" and altern: "i=pmax \<or> i \<in> kmax f PR" ..
  thus ?thesis
  proof(cases "i=pmax")
    case True
    with iinC fpmax_ismax show ?thesis by force
  next
    case False
    with altern maxrinr fpmax_ismax kmax_ge
    have "f pmax <= f i" by simp
    with iinC fpmax_ismax show ?thesis by auto 
  qed
qed
  
lemma lboundmin:
assumes 
  hC: "C \<subseteq> PR" and
  hCk: "np <= card C + khl"
shows
  "\<exists> i\<in>C. f i <= Min (reduce f PR)"
proof-
  from reduce_not_empty and finite_reduce 
  have minrinr: "Min (reduce f PR) \<in> reduce f PR" 
    by simp
  with exist_reduce
  have "\<exists> i\<in> PR-(kmax f PR \<union> kmin f PR). f i = Min (reduce f PR)"
    by simp
  then obtain pmin where 
    pmin_in_reduc: "pmin \<in> PR-(kmax f PR \<union> kmin f PR)" and 
    fpmin_ismin: "f pmin = Min (reduce f PR)" ..
  hence "C \<inter> insert pmin (kmin f PR)  \<noteq> {}"
  proof-
    from kmin_prop and pmin_in_reduc 
      and finite_kmin and hCk  have 
      "card PR < card C + card (insert pmin (kmin f PR))"
      by simp
    moreover
    from pmin_in_reduc and kmin_prop
    have "insert pmin (kmin f PR) \<subseteq> PR" by blast
    moreover
    note hC
    ultimately
    show ?thesis 
      using subsets_int[of PR C "insert pmin (kmin f PR)"]
      by simp
  qed
  hence res: "\<exists> i\<in>C. i=pmin \<or> i \<in> kmin f PR" by blast
  then obtain i where
    iinC: "i\<in>C" and altern: "i=pmin \<or> i \<in> kmin f PR" ..
  thus ?thesis
  proof(cases "i=pmin")
    case True
    with iinC fpmin_ismin show ?thesis by force
  next
    case False
    with altern minrinr fpmin_ismin kmin_le
    have "f i <= f pmin" by simp
    with iinC fpmin_ismin show ?thesis by auto 
  qed
qed
  
lemma same_bound:
assumes 
  hC: "C \<subseteq> PR" and
  hCk: "np <= card C + khl" and
  hnk: "3 * khl < np" 
shows
  "\<exists> i\<in>C. Min (reduce f PR) <= f i \<and> g i <= Max (reduce g PR) "
proof-
  have b1: "khl + 1 <= card (C \<inter> (PR - kmin f PR))"
  proof(rule pigeonhole)
    show "finite PR" by simp
  next
    show "C \<subseteq> PR" by fact
  next
    show "PR - kmin f PR \<subseteq> PR" by blast
  next
    show "card PR + (khl + 1) \<le> card C + card (PR - kmin f PR)" 
    proof-
      from hnk and hCk have 
        "np + khl < np + card C - khl" by arith 
      also
      from kmin_prop
      have "... = np + card C - card (kmin f PR)"
        by auto
      also
      have "... = card C + (card PR - card (kmin f PR))"
      proof-
        from kmin_prop have
          "card (kmin f PR) <= card PR"
          by (intro card_mono, auto)
        thus ?thesis by (simp)
      qed
      also
      from kmin_prop 
      have "... = card C +  card (PR - kmin f PR)" 
      proof-
        from kmin_prop and finite_kmin have 
          "card PR - card (kmin f PR) =  card (PR - kmin f PR)"
          by (intro card_Diff_subset[THEN sym])(auto)
        thus ?thesis by auto
      qed
      finally
      show ?thesis 
        by (simp)
    qed
  qed
        
  have "C \<inter> (PR - kmin f PR) \<inter> (PR - kmax g PR) \<noteq> {}"
  proof(intro subsets_int)
    show "finite PR" by simp
  next
    show "C \<inter> (PR - kmin f PR) \<subseteq> PR"
      by blast
  next
    show "PR - kmax g PR \<subseteq> PR" 
      by blast
  next
    show "card PR < 
      card (C \<inter> (PR - kmin f PR)) + card (PR - kmax g PR)"
    proof-
      from kmax_prop and finite_kmax
      have "card (PR - kmax g PR)= card PR - card (kmax g PR) " 
        by  (intro card_Diff_subset, auto)
      with kmax_prop have 
        "card (PR - kmax g PR) = card PR - khl" by simp
      with b1
      show ?thesis by arith
    qed
  qed

  hence 
    "\<exists> i. i \<in> C \<and> i \<in> (PR - kmin f PR) \<and> i \<in> (PR - kmax g PR)"
    by blast
  then obtain i where 
    in_C: "i \<in> C" and 
    not_in_kmin: "i \<in> (PR - kmin f PR)" and 
    not_in_kmax: "i \<in> (PR - kmax g PR)" by blast
  have "Min (reduce f PR) <= f i" 
  proof(cases "i \<in> kmax f PR")
    case True
    from reduce_not_empty and finite_reduce have
      " Min (reduce f PR) \<in> reduce f PR" by auto
    with True show ?thesis
      using kmax_ge by blast
  next
    case False
    with not_in_kmin  
    have "i \<in> PR - (kmax f PR \<union> kmin f PR)" 
      by blast
    with reduce_def have "f i \<in> reduce f PR"
      by auto
    with reduce_not_empty and finite_reduce
    show ?thesis by auto
  qed
  moreover
  have "g i <= Max (reduce g PR)" 
  proof(cases "i \<in> kmin g PR")
    case True
    from reduce_not_empty and finite_reduce have
      " Max (reduce g PR) \<in> reduce g PR" by auto
    with True show ?thesis
      using kmin_le by blast
  next
    case False
    with not_in_kmax  
    have "i \<in> PR - (kmax g PR \<union> kmin g PR)" 
      by blast
    with reduce_def have "g i \<in> reduce g PR"
      by auto
    with reduce_not_empty and finite_reduce
    show ?thesis by auto
  qed
  moreover
  note in_C
  ultimately
  show ?thesis by blast
qed


subsubsection \<open>Main theorem\<close>

text \<open>The most part of this theorem can be proved with CVC-lite
using the three previous lemmas (appendix \ref{sec:bound_prec_enh}).\<close>

theorem prec_enh:
assumes 
  hC: "C \<subseteq> PR" and
  hCF: "np - nF <= card C" and
  hFn: "3 * nF < np" and
  hFk: "nF = khl" and
  hbx: "\<forall> l\<in>C. \<bar>f l - g l\<bar> <= x" and
  hby1: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hby2: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>g l - g m\<bar> <= y" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" 
shows "\<bar> cfnl p f - cfnl q g \<bar> <= y / 2 + x"
proof-
  from hCF and hFk 
  have hCk: "np <= card C + khl" by arith
  from hFn and hFk 
  have hnk: "3 * khl < np"  by arith
  let    ?maxf = "Max (reduce f PR)" 
    and  ?minf = "Min (reduce f PR)"
    and  ?maxg = "Max (reduce g PR)" 
    and  ?ming = "Min (reduce g PR)"
  from abs_distrib_div
  have "\<bar>cfnl p f - cfnl q g\<bar> = 
    \<bar>?maxf + ?minf  +  - ?maxg + - ?ming\<bar> / 2"
    by (unfold cfnl_def) simp
  moreover
  have "\<bar>?maxf + ?minf  +  - ?maxg + - ?ming\<bar> <= y + 2 * x"
    \<comment> \<open>The rest of the property can be proved by CVC-lite
           (see appendix \ref{sec:bound_prec_enh})\<close>
  proof ( cases "0 <= ?maxf + ?minf  +  - ?maxg + - ?ming")
    case True
    hence
    "\<bar>?maxf + ?minf  +  - ?maxg + - ?ming\<bar> = 
      ?maxf + ?minf  +  - ?maxg + - ?ming" by arith
    moreover
    from uboundmax hC hCk 
    obtain mxf
      where mxfinC: "mxf\<in>C" and 
            maxf: "?maxf <= f mxf" by blast
    moreover
    from lboundmin hC hCk 
    obtain mng 
      where mnginC: "mng\<in>C" and 
            ming: "g mng <= ?ming" by blast    
    moreover
    from same_bound hC hCk hnk  
    obtain mxn 
      where mxninC: "mxn\<in>C" and 
            mxnf: "?minf  \<le> f mxn" and
            mxng: "g mxn \<le> ?maxg" by blast
    ultimately
    have 
      "\<bar> ?maxf + ?minf  +  - ?maxg + - ?ming\<bar> <= 
      (f mxf + - g mng) + (f mxn  +  - g mxn)" by arith
    also 
    from  mxninC hbx abs_le_D1
    have
      "... <= (f mxf + - g mng) + x"
      by auto
    also
    have 
      "... = (f mxf + - f mng ) + ( f mng + - g mng) + x"
      by arith
    also
    have "... <= y + ( f mng + - g mng) + x"
    proof-
      from  mxfinC mnginC hby1 abs_le_D1
      have "f mxf + - f mng <= y" 
        by auto
      thus ?thesis
        by auto
    qed
    also
    from  mnginC hbx abs_le_D1
    have "... <= y + 2 * x"
      by auto
    finally 
    show ?thesis .
  next
    case False
    hence
    "\<bar>?maxf + ?minf  +  - ?maxg + - ?ming\<bar> = 
      ?maxg + ?ming  +  - ?maxf + - ?minf" by arith
    moreover
    from uboundmax hC hCk 
    obtain mxg 
      where mxginC: "mxg\<in>C" and 
            maxg: "?maxg <= g mxg" by blast
    moreover
    from lboundmin hC hCk 
    obtain mnf 
      where mnfinC: "mnf\<in>C" and 
            minf: "f mnf <= ?minf" by blast    
    moreover
    from same_bound hC hCk hnk  
    obtain mxn 
      where mxninC: "mxn\<in>C" and 
            mxnf: "?ming  \<le> g mxn" and
            mxng: "f mxn \<le> ?maxf" by blast
    ultimately
    have 
      "\<bar> ?maxf + ?minf  +  - ?maxg + - ?ming\<bar> <= 
      (g mxg + - f mnf) + (g mxn  +  - f mxn)" by arith
    also
    from  mxninC hbx 
    have "... <= (g mxg + - f mnf) + x"
        by (auto dest!: abs_le_D2)
    also
    have 
      "... = (g mxg + - g mnf ) + ( g mnf + - f mnf) + x"
      by arith
    also
    have "... <= y + ( g mnf + - f mnf) + x"
    proof-
      from  mxginC mnfinC hby2 abs_le_D1
      have "g mxg + - g mnf <= y" 
        by auto
      thus ?thesis
        by auto
    qed
    also
    from  mnfinC hbx
    have "... <= y + 2 * x"
      by (auto dest!: abs_le_D2)
    finally 
    show ?thesis .
  qed
  ultimately
  show ?thesis
    by simp
qed

subsection \<open>Accuracy Preservation property\<close>

text \<open>No new lemmas are needed for prove this property. The bound
has been found using the lemmas @{thm [source] uboundmax} and @{thm
[source] lboundmin}\<close>

text \<open>This theorem can be proved with ICS and CVC-lite assuming
those lemmas (see appendix \ref{sec:accur_pres}).\<close>

theorem accur_pres:
assumes
  hC: "C \<subseteq> PR" and
  hCF: "np - nF <= card C" and
  hFk: "nF = khl" and
  hby: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hqC: "q\<in>C" 
shows "\<bar> cfnl p f - f q \<bar> <= y"
proof-
  from hCF and hFk 
  have npleCk: "np <= card C + khl" by arith
  show ?thesis
  proof(cases "f q <= cfnl p f")
    case True
    from npleCk hC and  uboundmax 
    have "\<exists> i\<in>C. Max (reduce f PR) <= f i"
      by auto
    then obtain pi where 
      hpiC: "pi \<in> C" and 
      fpiGeMax: "Max (reduce f PR) <= f pi" by blast
    from reduce_not_empty 
    have "Min (reduce f PR) <= Max (reduce f PR)"
      by (auto simp add: reduce_def)
    with fpiGeMax have
      cfnlLefpi: "cfnl p f <= f pi"
      by (auto simp add: cfnl_def)
    with True have 
      "\<bar> cfnl p f - f q \<bar> <= \<bar> f pi - f q \<bar>"
      by arith
    with hpiC and hqC and hby show ?thesis 
      by force
  next
    case False
    from npleCk hC and lboundmin 
    have "\<exists> i\<in>C. f i <= Min (reduce f PR)"
      by auto
    then obtain qi where 
      hqiC: "qi \<in> C" and 
      fqiLeMax: "f qi <= Min (reduce f PR)" by blast
    from reduce_not_empty 
    have "Min (reduce f PR) <= Max (reduce f PR)"
      by (auto simp add: reduce_def)
    with fqiLeMax 
    have "f qi <= cfnl p f"
      by (auto simp add: cfnl_def)
    with False have 
      "\<bar> cfnl p f - f q \<bar> <= \<bar> f qi - f q \<bar>"
      by arith
    with hqiC and hqC and hby show ?thesis 
      by force
  qed
qed

end
