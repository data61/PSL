theory ValueSimilarity
imports Value CValue Pointwise
begin

text \<open>
This theory formalizes Section 3 of \cite{functionspaces}. Their domain $D$ is our type @{typ Value},
their domain $E$ is our type @{typ CValue} and $A$ corresponds to @{typ "(C \<rightarrow> CValue)"}.

In our case, the construction of the domains was taken care of by the HOLCF package
(\cite{holcf}), so where \cite{functionspaces} refers to elements of the domain approximations
$D_n$ resp. $E_n$, these are just elements of @{typ Value} resp. @{typ CValue} here. Therefore the
\emph{n-injection} $\phi_n^E \colon E_n \to E$ is the identity here.

The projections correspond to the take-functions generated by the HOLCF package:
\begin{alignstar}
\psi_n^E &\colon E \to E_n &\text{ corresponds to }&&@{term CValue_take}\<open>::\<close>&@{typeof "CValue_take :: nat \<Rightarrow> CValue \<rightarrow> CValue" } \\
\psi_n^A &\colon A \to A_n &\text{ corresponds to }&&@{term C_to_CValue_take}\<open>::\<close>&@{typeof "C_to_CValue_take :: nat \<Rightarrow> (C \<rightarrow> CValue) \<rightarrow> (C \<rightarrow> CValue)"} \\
\psi_n^D &\colon D \to D_n &\text{ corresponds to }&&@{term Value_take}\<open>::\<close>&@{typeof Value_take}.
\end{alignstar}

The syntactic overloading of $e(a)(c)$ to mean either $\mathrm{ |mathsf{Ap}}_{E_n}^|bot$ or $\mathrm{ |mathsf{AP}}_{E}^|bot$
turns into our non-overloaded \<open>_ \<down>CFn _\<close>\<open>::\<close>@{typeof "(\<down>CFn)"}.
\<close>

text \<open>
To have our presentation closer to \cite{functionspaces}, we introduce some notation:
\<close>

notation Value_take ("\<psi>\<^sup>D\<^bsub>_\<^esub>")
notation C_to_CValue_take ("\<psi>\<^sup>A\<^bsub>_\<^esub>")
notation CValue_take ("\<psi>\<^sup>E\<^bsub>_\<^esub>")

subsubsection \<open>A note about section 2.3\<close>

text \<open>
Section 2.3 of  \cite{functionspaces} contains equations (2) and (3) which do not hold in general.
We demonstrate that fact here using our corresponding definition, but the counter-example carries
over to the original formulation. Lemma (2) is a generalisation of (3) to the resourced semantics,
so the counter-example for (3) is the simpler and more educating:
\<close>

lemma counter_example:
  assumes "Equation (3)": "\<And> n d d'. \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(d \<down>Fn d') = \<psi>\<^sup>D\<^bsub>Suc n\<^esub>\<cdot>d \<down>Fn \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d'"
  shows "False"
proof-
  define n :: nat where "n = 1"
  define d where "d = Fn\<cdot>(\<Lambda> e. (e \<down>Fn \<bottom>))"
  define d' where "d' = Fn\<cdot>(\<Lambda> _. Fn\<cdot>(\<Lambda> _. \<bottom>))"
  have "Fn\<cdot>(\<Lambda> _. \<bottom>) = \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(d \<down>Fn d')"
    by (simp add: d_def d'_def n_def cfun_map_def)
  also
  have "\<dots> = \<psi>\<^sup>D\<^bsub>Suc n\<^esub>\<cdot>d \<down>Fn \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d'"
    using "Equation (3)".
  also have "\<dots> = \<bottom>"
    by (simp add: d_def d'_def n_def)
  finally show False by simp
qed

text \<open>
For completeness, and to avoid making false assertions, the counter-example to equation (2):
\<close>

lemma counter_example2:
  assumes "Equation (2)": "\<And> n e a c. \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>((e \<down>CFn a)\<cdot>c) = (\<psi>\<^sup>E\<^bsub>Suc n\<^esub>\<cdot>e \<down>CFn \<psi>\<^sup>A\<^bsub>n\<^esub>\<cdot>a)\<cdot>c"
  shows "False"
proof-
  define n :: nat where "n = 1"
  define e where "e = CFn\<cdot>(\<Lambda> e r. (e\<cdot>r \<down>CFn \<bottom>)\<cdot>r)"
  define a :: "C \<rightarrow> CValue" where "a = (\<Lambda> _ . CFn\<cdot>(\<Lambda> _ _. CFn\<cdot>(\<Lambda> _ _. \<bottom>)))"
  fix c :: C
  have "CFn\<cdot>(\<Lambda> _ _. \<bottom>) = \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>((e \<down>CFn a)\<cdot>c)"
    by (simp add: e_def a_def n_def cfun_map_def)
  also
  have "\<dots> = (\<psi>\<^sup>E\<^bsub>Suc n\<^esub>\<cdot>e \<down>CFn \<psi>\<^sup>A\<^bsub>n\<^esub>\<cdot>a)\<cdot>c"
    using "Equation (2)".
  also have "\<dots> = \<bottom>"
    by (simp add: e_def a_def n_def)
  finally show False by simp
qed


text \<open>A suitable substitute for the lemma can be found in 4.3.5 (1) in \cite{fullabstraction},
which in our setting becomes the following (note the extra invocation of @{term "Value_take n"} on
the left hand side):
\<close>

lemma "Abramsky 4,3,5 (1)":
  "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(d \<down>Fn \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d') = \<psi>\<^sup>D\<^bsub>Suc n\<^esub>\<cdot>d \<down>Fn \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d'"
  by (cases d) (auto simp add: Value.take_take)

text \<open>
The problematic equations are used in the proof of the only-if direction of proposition 9 in
\cite{functionspaces}. It can be fixed by applying take-induction, which inserts the
extra call to @{term "Value_take n"} in the right spot.
\<close>

subsubsection \<open>Working with @{typ Value} and @{typ CValue}\<close>

text \<open>Combined case distinguishing and induction rules.\<close>

lemma value_CValue_cases:
  obtains
  "x = \<bottom>" "y = \<bottom>" |
  f where "x = Fn\<cdot>f" "y = \<bottom>" |
  g where "x = \<bottom>" "y = CFn\<cdot>g" |
  f g where "x = Fn\<cdot>f" "y = CFn \<cdot> g" |
  b\<^sub>1 where "x = B\<cdot>(Discr b\<^sub>1)" "y = \<bottom>" |
  b\<^sub>1 g where "x = B\<cdot>(Discr b\<^sub>1)" "y = CFn\<cdot>g" |
  b\<^sub>1 b\<^sub>2 where "x = B\<cdot>(Discr b\<^sub>1)" "y = CB\<cdot>(Discr b\<^sub>2)" |
  f b\<^sub>2 where "x = Fn\<cdot>f" "y = CB\<cdot>(Discr b\<^sub>2)" |
  b\<^sub>2 where "x = \<bottom>" "y = CB\<cdot>(Discr b\<^sub>2)"
  by (metis CValue.exhaust Discr_undiscr Value.exhaust)

lemma Value_CValue_take_induct:
  assumes "adm (case_prod P)"
  assumes "\<And> n. P (\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x) (\<psi>\<^sup>A\<^bsub>n\<^esub>\<cdot>y)"
  shows "P x y"
proof-
  have "case_prod P (\<Squnion>n. (\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x, \<psi>\<^sup>A\<^bsub>n\<^esub>\<cdot>y))"
    by (rule admD[OF \<open>adm (case_prod P)\<close> ch2ch_Pair[OF ch2ch_Rep_cfunL[OF Value.chain_take] ch2ch_Rep_cfunL[OF C_to_CValue_chain_take]]])
       (simp add: assms(2))
  hence "case_prod P (x,y)"
    by (simp add: lub_Pair[OF ch2ch_Rep_cfunL[OF Value.chain_take] ch2ch_Rep_cfunL[OF C_to_CValue_chain_take]]
                  Value.reach C_to_CValue_reach)
  thus ?thesis by simp
qed

subsubsection \<open>Restricted similarity is defined recursively\<close>

text \<open>The base case\<close>

inductive similar'_base :: "Value \<Rightarrow> CValue \<Rightarrow> bool" where
  bot_similar'_base[simp,intro]: "similar'_base \<bottom> \<bottom>"

inductive_cases [elim!]:
   "similar'_base x y"

text \<open>The inductive case\<close>

inductive similar'_step :: "(Value \<Rightarrow> CValue \<Rightarrow> bool) \<Rightarrow> Value \<Rightarrow> CValue \<Rightarrow> bool" for s where
  bot_similar'_step[intro!]: "similar'_step s \<bottom> \<bottom>" |
  bool_similar'_step[intro]: "similar'_step s (B\<cdot>b) (CB\<cdot>b)" |
  Fun_similar'_step[intro]: "(\<And> x y . s x (y\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> s (f\<cdot>x) (g\<cdot>y\<cdot>C\<^sup>\<infinity>)) \<Longrightarrow> similar'_step s (Fn\<cdot>f) (CFn\<cdot>g)"

inductive_cases [elim!]:
   "similar'_step s x \<bottom>"
   "similar'_step s \<bottom> y"
   "similar'_step s (B\<cdot>f) (CB\<cdot>g)"
   "similar'_step s (Fn\<cdot>f) (CFn\<cdot>g)"

text \<open>
We now create the restricted similarity relation, by primitive recursion over @{term n}.

This cannot be done using an inductive definition, as it would not be monotone.
\<close>

fun similar' where
 "similar' 0 = similar'_base" |
 "similar' (Suc n) = similar'_step (similar' n)"
declare similar'.simps[simp del]

abbreviation similar'_syn  ("_ \<triangleleft>\<triangleright>\<^bsub>_\<^esub> _" [50,50,50] 50)
  where "similar'_syn x n y \<equiv> similar' n x y"

lemma similar'_botI[intro!,simp]: "\<bottom> \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<bottom>"
  by (cases n) (auto simp add: similar'.simps)

lemma similar'_FnI[intro]:
  assumes "\<And>x y.  x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> g\<cdot>y\<cdot>C\<^sup>\<infinity>"
  shows "Fn\<cdot>f \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> CFn\<cdot>g"
using assms by (auto simp add: similar'.simps)

lemma similar'_FnE[elim!]:
  assumes "Fn\<cdot>f \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> CFn\<cdot>g"
  assumes "(\<And>x y.  x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> g\<cdot>y\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> P"
  shows P
using assms by (auto simp add: similar'.simps)

lemma bot_or_not_bot':
  "x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y \<Longrightarrow> (x = \<bottom> \<longleftrightarrow> y = \<bottom>)"
  by (cases n) (auto simp add: similar'.simps elim: similar'_base.cases similar'_step.cases)

lemma similar'_bot[elim_format, elim!]:
    "\<bottom> \<triangleleft>\<triangleright>\<^bsub>n\<^esub> x \<Longrightarrow> x = \<bottom>"
    "y \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<bottom> \<Longrightarrow> y = \<bottom>"
by (metis bot_or_not_bot')+

lemma similar'_typed[simp]:
  "\<not> B\<cdot>b \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CFn\<cdot>g"
  "\<not> Fn\<cdot>f \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CB\<cdot>b"
  by (cases n, auto simp add: similar'.simps elim: similar'_base.cases similar'_step.cases)+

lemma similar'_bool[simp]:
  "B\<cdot>b\<^sub>1 \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> CB\<cdot>b\<^sub>2 \<longleftrightarrow> b\<^sub>1 = b\<^sub>2"
  by (auto simp add: similar'.simps elim: similar'_base.cases similar'_step.cases)

subsubsection \<open>Moving up and down the similarity relations\<close>

text \<open>
These correspond to Lemma 7 in |cite{functionspaces}.
\<close>

lemma similar'_down: "d \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> e \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>e"
  and similar'_up: "d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> e \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>e"
proof (induction n arbitrary: d e)
  case (Suc n) case 1 with  Suc
  show ?case
    by (cases d e rule:value_CValue_cases) auto
next
  case (Suc n) case 2 with Suc
  show ?case
    by (cases d e rule:value_CValue_cases) auto
qed auto

text \<open>
A generalisation of the above, doing multiple steps at once.
\<close>

lemma similar'_up_le: "n \<le> m \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>e \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>m\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>e"
  by (induction rule: dec_induct )
     (auto dest: similar'_up simp add: Value.take_take CValue.take_take min_absorb2)

lemma similar'_down_le: "n \<le> m \<Longrightarrow> \<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>m\<^esub> \<psi>\<^sup>E\<^bsub>m\<^esub>\<cdot>e \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>e"
  by (induction rule: inc_induct )
     (auto dest: similar'_down simp add: Value.take_take CValue.take_take min_absorb1)

lemma similar'_take: "d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> e \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>e"
  apply (drule similar'_up)
  apply (drule similar'_down)
  apply (simp add: Value.take_take CValue.take_take)
  done

subsubsection \<open>Admissibility\<close>

text \<open>
A technical prerequisite for induction is admissibility of the predicate, i.e.\ that the predicate
holds for the limit of a chain, given that it holds for all elements.
\<close>

lemma similar'_base_adm: "adm (\<lambda> x. similar'_base (fst x) (snd x))"
proof (rule admI, goal_cases)
  case (1 Y)
  then have "Y = (\<lambda> _ . \<bottom>)" by (metis prod.exhaust fst_eqD inst_prod_pcpo similar'_base.simps snd_eqD)
  thus ?case by auto
qed

lemma similar'_step_adm:
  assumes "adm (\<lambda> x. s (fst x) (snd x))"
  shows "adm (\<lambda> x. similar'_step s (fst x) (snd x))"
proof (rule admI, goal_cases)
  case prems: (1 Y)
  from \<open>chain Y\<close>
  have "chain (\<lambda> i. fst (Y i))" by (rule ch2ch_fst)
  thus ?case
  proof(cases rule: Value_chainE)
  case bot
    hence *: "\<And> i. fst (Y i) = \<bottom>" by metis
    with prems(2)[unfolded split_beta]
    have "\<And>i. snd (Y i) = \<bottom>" by auto
    hence "Y = (\<lambda> i. (\<bottom>, \<bottom>))" using * by (metis surjective_pairing)
    thus ?thesis by auto
  next
  case (B n b)
    hence "\<forall>i. fst (Y (i + n)) = B\<cdot>b" by (metis add.commute not_add_less1)
    with prems(2)
    have "\<forall>i. Y (i + n) = (B\<cdot>b, CB\<cdot>b)"
      apply auto
      apply (erule_tac x = "i + n" in allE)
      apply (erule_tac x = "i" in allE)
      apply (erule similar'_step.cases)
      apply auto
      by (metis fst_conv old.prod.exhaust snd_conv)
    hence "similar'_step s (fst (\<Squnion> i. Y (i + n))) (snd (\<Squnion> i. Y (i + n)))" by auto
    thus ?thesis
      by (simp add: lub_range_shift[OF \<open>chain Y\<close>])
  next
    fix n
    fix Y'
    assume "chain Y'" and "(\<lambda>i. fst (Y i)) = (\<lambda> m. (if m < n then \<bottom> else Fn\<cdot>(Y' (m-n))))"
    hence Y': "\<And> i. fst (Y (i+n)) = Fn\<cdot>(Y' i)" by (metis add_diff_cancel_right' not_add_less2)
    with prems(2)[unfolded split_beta]
    have "\<And>i. \<exists> g'. snd (Y (i+n)) = CFn\<cdot>g'"
      by -(erule_tac x = "i + n" in allE, auto elim!: similar'_step.cases)
    then obtain Y'' where Y'': "\<And> i. snd (Y (i+n)) = CFn\<cdot>(Y'' i)" by metis
    from prems(1) have "\<And>i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: po_class.chain_def)
    then have *: "\<And>i. Y (i + n) \<sqsubseteq> Y (Suc i + n)"
      by simp
    have "chain Y''"
      apply (rule chainI)
      apply (rule iffD1[OF CValue.inverts(1)])
      apply (subst (1 2) Y''[symmetric])
      apply (rule snd_monofun)
      apply (rule *)
      done

    have "similar'_step s (Fn\<cdot>(\<Squnion> i. (Y' i))) (CFn \<cdot> (\<Squnion> i. Y'' i))"
    proof (rule Fun_similar'_step)
      fix x y
      from prems(2) Y' Y''
      have "\<And>i. similar'_step s (Fn\<cdot>(Y' i)) (CFn\<cdot>(Y'' i))" by metis
      moreover
      assume "s x (y\<cdot>C\<^sup>\<infinity>)"
      ultimately
      have "\<And>i. s (Y' i\<cdot>x) (Y'' i\<cdot>y\<cdot>C\<^sup>\<infinity>)" by auto
      hence "case_prod s (\<Squnion> i. ((Y' i)\<cdot>x, (Y'' i)\<cdot>y\<cdot>C\<^sup>\<infinity>))"
        apply -
        apply (rule admD[OF adm_case_prod[where P = "\<lambda>_ . s", OF assms]])
        apply (simp add:  \<open>chain Y'\<close>  \<open>chain Y''\<close>)
        apply simp
        done
      thus "s ((\<Squnion> i. Y' i)\<cdot>x) ((\<Squnion> i. Y'' i)\<cdot>y\<cdot>C\<^sup>\<infinity>)"
        by (simp add: lub_Pair  ch2ch_Rep_cfunL contlub_cfun_fun  \<open>chain Y'\<close>  \<open>chain Y''\<close>)
    qed
    hence "similar'_step s (fst (\<Squnion> i. Y (i+n))) (snd (\<Squnion> i. Y (i+n)))"
      by (simp add: Y' Y''
          cont2contlubE[OF cont_fst chain_shift[OF prems(1)]]  cont2contlubE[OF cont_snd chain_shift[OF prems(1)]]
           contlub_cfun_arg[OF \<open>chain Y''\<close>] contlub_cfun_arg[OF \<open>chain Y'\<close>])
    thus "similar'_step s (fst (\<Squnion> i. Y i)) (snd (\<Squnion> i. Y i))"
      by (simp add: lub_range_shift[OF \<open>chain Y\<close>])
  qed
qed


lemma similar'_adm: "adm (\<lambda>x. fst x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> snd x)"
  by (induct n) (auto simp add: similar'.simps intro: similar'_base_adm similar'_step_adm)

lemma similar'_admI: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> g x)"
  by (rule adm_subst[OF _ similar'_adm, where t = "\<lambda>x. (f x, g x)", simplified]) auto

subsubsection \<open>The real similarity relation\<close>

text \<open>
This is the goal of the theory: A relation between @{typ Value} and @{typ CValue}.
\<close>

definition similar :: "Value \<Rightarrow> CValue \<Rightarrow> bool" (infix "\<triangleleft>\<triangleright>" 50) where
  "x \<triangleleft>\<triangleright> y \<longleftrightarrow> (\<forall>n. \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>y)"

lemma similarI:
  "(\<And> n. \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>y) \<Longrightarrow> x \<triangleleft>\<triangleright> y"
  unfolding similar_def by blast

lemma similarE:
  "x \<triangleleft>\<triangleright> y \<Longrightarrow> \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>y"
  unfolding similar_def by blast

lemma similar_bot[simp]: "\<bottom> \<triangleleft>\<triangleright> \<bottom>" by (auto intro: similarI)

lemma similar_bool[simp]: "B\<cdot>b \<triangleleft>\<triangleright> CB\<cdot>b"
  by (rule similarI, case_tac n, auto)
 
lemma [elim_format, elim!]: "x \<triangleleft>\<triangleright> \<bottom> \<Longrightarrow> x = \<bottom>"
  unfolding similar_def
  apply (cases x)
  apply auto
  apply (erule_tac x = "Suc 0" in allE, auto)+
  done

lemma [elim_format, elim!]: "x \<triangleleft>\<triangleright> CB\<cdot>b \<Longrightarrow> x = B\<cdot>b"
  unfolding similar_def
  apply (cases x)
  apply auto
  apply (erule_tac x = "Suc 0" in allE, auto)+
  done

lemma [elim_format, elim!]: "\<bottom> \<triangleleft>\<triangleright> y \<Longrightarrow> y = \<bottom>"
  unfolding similar_def
  apply (cases y)
  apply auto
  apply (erule_tac x = "Suc 0" in allE, auto)+
  done

lemma [elim_format, elim!]: "B\<cdot>b \<triangleleft>\<triangleright> y \<Longrightarrow> y = CB\<cdot>b"
  unfolding similar_def
  apply (cases y)
  apply auto
  apply (erule_tac x = "Suc 0" in allE, auto)+
  done

lemma take_similar'_similar:
  assumes "x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y"
  shows  "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x \<triangleleft>\<triangleright> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>y"
proof(rule similarI)
  fix m
  from assms
  have "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>y" by (rule similar'_take)
  moreover
  have "n \<le> m \<or> m \<le> n" by auto
  ultimately
  show "\<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>(\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x) \<triangleleft>\<triangleright>\<^bsub>m\<^esub> \<psi>\<^sup>E\<^bsub>m\<^esub>\<cdot>(\<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>y)"
    by (auto elim: similar'_up_le similar'_down_le dest: similar'_take
        simp add: min_absorb2 min_absorb1 Value.take_take CValue.take_take)
qed

lemma bot_or_not_bot:
  "x \<triangleleft>\<triangleright> y \<Longrightarrow> (x = \<bottom> \<longleftrightarrow> y = \<bottom>)"
  by (cases x y rule:value_CValue_cases) auto

lemma bool_or_not_bool:
  "x \<triangleleft>\<triangleright> y \<Longrightarrow> (x = B\<cdot>b) \<longleftrightarrow> (y = CB\<cdot>b)"
  by (cases x y rule:value_CValue_cases) auto

lemma slimilar_bot_cases[consumes 1, case_names bot bool Fn]:
  assumes "x \<triangleleft>\<triangleright> y"
  obtains "x = \<bottom>" "y = \<bottom>" |
  b where "x = B\<cdot>(Discr b)" "y = CB\<cdot>(Discr b)" |
  f g where "x = Fn\<cdot>f" "y = CFn \<cdot> g"
using assms
by (metis CValue.exhaust Value.exhaust bool_or_not_bool bot_or_not_bot discr.exhaust)

lemma similar_adm: "adm (\<lambda>x. fst x \<triangleleft>\<triangleright> snd x)"
  unfolding similar_def
  by (intro adm_lemmas similar'_admI cont2cont)

lemma similar_admI: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f x \<triangleleft>\<triangleright> g x)"
  by (rule adm_subst[OF _ similar_adm, where t = "\<lambda>x. (f x, g x)", simplified]) auto

text \<open>
Having constructed the relation we can how show that it indeed is the desired relation,
relating $|bot$ with $|bot$ and functions with functions, if they take related arguments to related values.
This corresponds to Proposition 9 in |cite{functionspaces}.
\<close>

lemma similar_nice_def: "x \<triangleleft>\<triangleright> y \<longleftrightarrow> (x = \<bottom> \<and> y = \<bottom> \<or> (\<exists> b. x = B\<cdot>(Discr b) \<and> y = CB\<cdot>(Discr b)) \<or> (\<exists> f g. x = Fn\<cdot>f \<and> y = CFn\<cdot>g \<and> (\<forall> a b. a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity> \<longrightarrow> f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>)))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  thus "?R"
  proof (cases x y rule:slimilar_bot_cases)
    case bot thus ?thesis by simp
  next
    case bool thus ?thesis by simp
  next 
    case (Fn f g)
    note \<open>?L\<close>[unfolded Fn]
    have "\<forall>a b. a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity> \<longrightarrow> f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>"
    proof(intro impI allI)
      fix a b
      assume "a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity>"

      show "f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>" 
      proof(rule similarI)
        fix n
        have "adm (\<lambda>(b, a). \<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(f\<cdot>b) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>(g\<cdot>a\<cdot>C\<^sup>\<infinity>))"
          by (intro adm_case_prod similar'_admI cont2cont)
        thus "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(f\<cdot>a) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>(g\<cdot>b\<cdot>C\<^sup>\<infinity>)"
        proof (induct a b rule: Value_CValue_take_induct[consumes 1])
          txt \<open>This take induction is required to avoid the wrong equation shown above.\<close>
          fix m

          from \<open>a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity>\<close>
          have "\<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>a \<triangleleft>\<triangleright>\<^bsub>m\<^esub> \<psi>\<^sup>E\<^bsub>m\<^esub>\<cdot>(b\<cdot>C\<^sup>\<infinity>)" by (rule similarE)
          hence "\<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>a \<triangleleft>\<triangleright>\<^bsub>max m n\<^esub> \<psi>\<^sup>E\<^bsub>m\<^esub>\<cdot>(b\<cdot>C\<^sup>\<infinity>)" by (rule similar'_up_le[rotated]) auto
          moreover
          from \<open>Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g\<close>
          have "\<psi>\<^sup>D\<^bsub>Suc (max m n)\<^esub>\<cdot>(Fn\<cdot>f) \<triangleleft>\<triangleright>\<^bsub>Suc (max m n)\<^esub> \<psi>\<^sup>E\<^bsub>Suc (max m n)\<^esub>\<cdot>(CFn\<cdot>g)" by (rule similarE)
          ultimately
          have "\<psi>\<^sup>D\<^bsub>max m n\<^esub>\<cdot>(f\<cdot>(\<psi>\<^sup>D\<^bsub>max m n\<^esub>\<cdot>(\<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>a))) \<triangleleft>\<triangleright>\<^bsub>max m n\<^esub> \<psi>\<^sup>E\<^bsub>max m n\<^esub>\<cdot>(g\<cdot>(\<psi>\<^sup>A\<^bsub>max m n\<^esub>\<cdot>(\<psi>\<^sup>A\<^bsub>m\<^esub>\<cdot>b))\<cdot>C\<^sup>\<infinity>)"
            by auto
          hence " \<psi>\<^sup>D\<^bsub>max m n\<^esub>\<cdot>(f\<cdot>(\<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>a)) \<triangleleft>\<triangleright>\<^bsub>max m n\<^esub> \<psi>\<^sup>E\<^bsub>max m n\<^esub>\<cdot>(g\<cdot>(\<psi>\<^sup>A\<^bsub>m\<^esub>\<cdot>b)\<cdot>C\<^sup>\<infinity>)"
            by (simp add: Value.take_take cfun_map_map CValue.take_take ID_def eta_cfun min_absorb2 min_absorb1)
          thus "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(f\<cdot>(\<psi>\<^sup>D\<^bsub>m\<^esub>\<cdot>a)) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>(g\<cdot>(\<psi>\<^sup>A\<^bsub>m\<^esub>\<cdot>b)\<cdot>C\<^sup>\<infinity>)"
            by (rule similar'_down_le[rotated]) auto
        qed
      qed
    qed
    thus ?thesis unfolding Fn by simp
  qed
next
  assume "?R"
  thus "?L"
  proof(elim conjE disjE exE ssubst)
    show "\<bottom> \<triangleleft>\<triangleright> \<bottom>" by simp
  next
    fix b
    show "B\<cdot>(Discr b) \<triangleleft>\<triangleright> CB\<cdot>(Discr b)" by simp
  next
    fix f g
    assume imp: "\<forall>a b. a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity> \<longrightarrow> f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>"
    show "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
    proof (rule similarI)
      fix n
      show "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(Fn\<cdot>f) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>(CFn\<cdot>g)"
      proof(cases n)
        case 0 thus ?thesis by simp
      next
        case (Suc n)
        { fix x y
          assume "x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y\<cdot>C\<^sup>\<infinity>"
          hence "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x \<triangleleft>\<triangleright> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>(y\<cdot>C\<^sup>\<infinity>)" by (rule take_similar'_similar)
          hence "f\<cdot>(\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x) \<triangleleft>\<triangleright> g\<cdot>(\<psi>\<^sup>A\<^bsub>n\<^esub>\<cdot>y)\<cdot>C\<^sup>\<infinity>" using imp by auto
          hence "\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>(f\<cdot>(\<psi>\<^sup>D\<^bsub>n\<^esub>\<cdot>x)) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<psi>\<^sup>E\<^bsub>n\<^esub>\<cdot>(g\<cdot>(\<psi>\<^sup>A\<^bsub>n\<^esub>\<cdot>y)\<cdot>C\<^sup>\<infinity>)"
            by (rule similarE)
        }
        with Suc
        show ?thesis by auto
      qed
    qed
  qed
qed

lemma similar_FnI[intro]:
  assumes "\<And>x y.  x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright> g\<cdot>y\<cdot>C\<^sup>\<infinity>"
  shows "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
by (metis assms similar_nice_def)

lemma similar_FnD[elim!]:
  assumes "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
  assumes "x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>"
  shows "f\<cdot>x \<triangleleft>\<triangleright> g\<cdot>y\<cdot>C\<^sup>\<infinity>"
using assms 
by (subst (asm) similar_nice_def) auto

lemma similar_FnE[elim!]:
  assumes "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
  assumes "(\<And>x y.  x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright> g\<cdot>y\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> P"
  shows P
by (metis assms similar_FnD)

subsubsection \<open>The similarity relation lifted pointwise to functions.\<close>

abbreviation fun_similar :: "('a::type \<Rightarrow> Value) \<Rightarrow> ('a \<Rightarrow> (C \<rightarrow> CValue)) \<Rightarrow> bool"  (infix "\<triangleleft>\<triangleright>\<^sup>*" 50) where
  "fun_similar \<equiv> pointwise (\<lambda>x y. x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>)"

lemma fun_similar_fmap_bottom[simp]: "\<bottom> \<triangleleft>\<triangleright>\<^sup>* \<bottom>"
  by auto

lemma fun_similarE[elim]:
  assumes "m \<triangleleft>\<triangleright>\<^sup>* m'"
  assumes "(\<And>x. (m  x) \<triangleleft>\<triangleright> (m' x)\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> Q"
  shows Q
  using assms unfolding pointwise_def by blast

end