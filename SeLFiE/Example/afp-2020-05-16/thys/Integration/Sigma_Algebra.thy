(*  Title:      Sigma_Algebra.thy

    Author:     Stefan Richter, Markus Wenzel, TU Muenchen
    License:    LGPL

Changes for Accordance to Joe Hurd's conventions
and additions by Stefan Richter 2002
*)

subsection \<open>Sigma algebras \label{sec:sigma}\<close>

theory Sigma_Algebra imports Main begin

text \<open>The $\isacommand {theory}$ command commences a formal document and enumerates the
  theories it depends on. With the \<open>Main\<close> theory, a standard
  selection of useful HOL theories excluding the real
  numbers is loaded. This theory includes and builds upon a tiny theory of the
  same name by Markus Wenzel. This theory as well as \<open>Measure\<close>
  in \ref{sec:measure-spaces} is heavily
  influenced by Joe Hurd's thesis \cite{hurd2002} and has been designed to keep the terminology as
  consistent as possible with that work.

  Sigma algebras are an elementary concept in measure
  theory. To measure --- that is to integrate --- functions, we first have
  to measure sets. Unfortunately, when dealing with a large universe,
  it is often not possible to consistently assign a measure to every
  subset. Therefore it is necessary to define the set of measurable
  subsets of the universe. A sigma algebra is such a set that has
  three very natural and desirable properties.\<close>

definition
  sigma_algebra:: "'a set set \<Rightarrow> bool" where
  "sigma_algebra A \<longleftrightarrow>
  {} \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> -a \<in> A) \<and>
  (\<forall>a. (\<forall> i::nat. a i \<in> A) \<longrightarrow> (\<Union>i. a i) \<in> A)"

text \<open>
  The $\isacommand {definition}$ command defines new constants, which
  are just named functions in HOL. Mind that the third condition
  expresses the fact that the union of countably many sets in $A$ is
  again a set in $A$ without explicitly defining the notion of
  countability.

  Sigma algebras can naturally be created as the closure of any set of
  sets with regard to the properties just postulated. Markus Wenzel
  wrote the following
  inductive definition of the $\isa {sigma}$ operator.\<close>


inductive_set
  sigma :: "'a set set \<Rightarrow> 'a set set"
  for A :: "'a set set"
  where
    basic: "a \<in> A \<Longrightarrow> a \<in> sigma A"
  | empty: "{} \<in> sigma A"
  | complement: "a \<in> sigma A \<Longrightarrow> -a \<in> sigma A"
  | Union: "(\<And>i::nat. a i \<in> sigma A) \<Longrightarrow> (\<Union>i. a i) \<in> sigma A"


text \<open>He also proved the following basic facts. The easy proofs are omitted.
\<close>

theorem sigma_UNIV: "UNIV \<in> sigma A"
(*<*)proof -
  have "{} \<in> sigma A" by (rule sigma.empty)
  hence "-{} \<in> sigma A" by (rule sigma.complement)
  also have "-{} = UNIV" by simp
  finally show ?thesis .
qed(*>*)


theorem sigma_Inter:
  "(\<And>i::nat. a i \<in> sigma A) \<Longrightarrow> (\<Inter>i. a i) \<in> sigma A"
(*<*) proof -
  assume "\<And>i::nat. a i \<in> sigma A"
  hence "\<And>i::nat. -(a i) \<in> sigma A" by (rule sigma.complement)
  hence "(\<Union>i. -(a i)) \<in> sigma A" by (rule sigma.Union)
  hence "-(\<Union>i. -(a i)) \<in> sigma A" by (rule sigma.complement)
  also have "-(\<Union>i. -(a i)) = (\<Inter>i. a i)" by simp
  finally show ?thesis .
qed(*>*)

text \<open>It is trivial to show the connection between our first
  definitions. We use the opportunity to introduce the proof syntax.\<close>


theorem assumes sa: "sigma_algebra A"
  \<comment> \<open>Named premises are introduced like this.\<close>

  shows sigma_sigma_algebra: "sigma A = A"
proof

  txt \<open>The $\isacommand {proof}$ command alone invokes a single standard rule to
    simplify the goal. Here the following two subgoals emerge.\<close>

  show "A \<subseteq> sigma A"
    \<comment> \<open>The $\isacommand {show}$ command starts the proof of a subgoal.\<close>

    by (auto simp add: sigma.basic)

  txt \<open>This is easy enough to be solved by an automatic step,
    indicated by the keyword $\isacommand {by}$. The method $\isacommand {auto}$ is stated in parentheses, with attributes to it following.  In
    this case, the first introduction rule for the $\isacommand {sigma}$
    operator is given as an extra simplification rule.\<close>

  show "sigma A \<subseteq> A"
  proof

    txt \<open>Because this goal is not quite as trivial, another proof is
      invoked, delimiting a block as in a programming language.\<close>

    fix x
    \<comment> \<open>A new named variable is introduced.\<close>

    assume "x \<in> sigma A"

    txt \<open>An assumption is made that must be justified by the current proof
      context. In this case the corresponding fact had been generated
      by a rule automatically invoked by the inner $\isacommand {proof}$
      command.\<close>

    from this sa show "x \<in> A"

      txt \<open>Named facts can explicitly be given to the proof methods using
        $\isacommand {from}$. A special name is \<open>this\<close>, which denotes
        current facts generated by the last command. Usually $\isacommand
        {from}$ \<open>this sa\<close> --- remember that \<open>sa\<close> is an assumption from above
        --- is abbreviated to $\isacommand {with}$ \<open>sa\<close>, but in this case the order of
        facts is relevant for the following method and $\isacommand
        {with}$
        would have put the current facts last.\<close>

      by (induct rule: sigma.induct) (auto simp add: sigma_algebra_def)

    txt \<open>Two methods may be carried out at $\isacommand {by}$. The first
      one applies induction here via the canonical rule generated by the
      inductive definition above, while the latter solves the
      resulting subgoals by an automatic step involving
      simplification.\<close>

  qed
qed

text "These two steps finish their respective proofs, checking
  that all subgoals have been proven."

text \<open>To end this theory we prove a special case of the \<open>sigma_Inter\<close> theorem above. It seems trivial that
  the fact holds for two sets as well as for countably many.
  We get a first taste of the cost of formal reasoning here, however. The
  idea must be made precise by exhibiting a concrete sequence of
  sets.\<close>

primrec trivial_series:: "'a set \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'a set)"
where
  "trivial_series a b 0 = a"
| "trivial_series a b (Suc n) = b"

text \<open>Using $\isacommand {primrec}$, primitive recursive functions over
  inductively defined data types --- the natural numbers in this case ---
  may be constructed.\<close>


theorem assumes s: "sigma_algebra A" and a: "a \<in> A" and b: "b \<in> A"
  shows sigma_algebra_inter: "a \<inter> b \<in> A"
proof -
    \<comment> \<open>This form of $\isacommand {proof}$ foregoes the application of a rule.\<close>

  have "a \<inter> b = (\<Inter>i::nat. trivial_series a b i)"

    txt \<open>Intermediate facts that do not solve any subgoals yet are established this way.\<close>

  proof (rule set_eqI)

    txt \<open>The  $\isacommand {proof}$ command may also take one explicit method
      as an argument like the single rule application in this instance.\<close>

    fix x

    {
      fix i
      assume "x \<in> a \<inter> b"
      hence "x \<in> trivial_series a b i" by (cases i) auto
        \<comment> \<open>This is just an abbreviation for $\isacommand {"from this have"}$.\<close>
    }

    txt \<open>Curly braces can be used to explicitly delimit
      blocks. In conjunction with $\isacommand {fix}$, universal
      quantification over the fixed variable $i$ is achieved
      for the last statement in the block, which is exported to the
      enclosing block.\<close>

    hence "x \<in> a \<inter> b \<Longrightarrow> \<forall>i. x \<in> trivial_series a b i"
      by fast
    also

    txt \<open>The statement $\isacommand {also}$ introduces calculational
      reasoning. This basically amounts to collecting facts. With
      $\isacommand {also}$, the current fact is added to a special list of
      theorems called the calculation and
      an automatically selected transitivity rule
      is additionally applied from the second collected fact on.\<close>

    { assume "\<And>i. x \<in> trivial_series a b i"
      hence "x \<in> trivial_series a b 0" and "x \<in> trivial_series a b 1"
        by this+
      hence "x \<in> a \<inter> b"
        by simp
    }
    hence "\<forall>i. x \<in> trivial_series a b i \<Longrightarrow> x \<in> a \<inter> b"
      by blast

    ultimately have "x \<in> a \<inter> b = (\<forall>i::nat. x \<in> trivial_series a b i)" ..

    txt \<open>The accumulated calculational facts including the current one
      are exposed to the next statement by  $\isacommand {ultimately}$ and
      the calculation list is then erased. The two dots after the
      statement here indicate proof by a single automatically
      selected rule.\<close>

    also have "\<dots> =  (x \<in> (\<Inter>i::nat. trivial_series a b i))"
      by simp
    finally show "x \<in> a \<inter> b = (x \<in> (\<Inter>i::nat. trivial_series a b i))" .

    txt \<open>The $\isacommand {finally}$ directive behaves like $\isacommand {ultimately}$
      with the addition of a further transitivity rule application. A
      single dot stands for proof by assumption.\<close>

  qed

  moreover have "(\<Inter>i::nat. trivial_series a b i) \<in> A"
  proof -
    { fix i
      from a b have "trivial_series a b i \<in> A"
        by (cases i) auto
    }
    hence "\<And>i. trivial_series a b i \<in> sigma A"
      by (simp only: sigma.basic)
    hence "(\<Inter>i::nat. trivial_series a b i) \<in> sigma A"
      by (simp only: sigma_Inter)
    with s show ?thesis
      by (simp only: sigma_sigma_algebra)
  qed

  ultimately show ?thesis by simp
qed

text \<open>Of course, a like theorem holds for union instead of
  intersection.  But as we will not need it in what follows, the
  theory is finished with the following easy properties instead.
  Note that the former is a kind of generalization of the last result and
  could be used to  shorten its proof. Unfortunately, this one was needed ---
  and therefore found --- only late in the development.
\<close>

theorem sigma_INTER:
  assumes a:"(\<And>i::nat. i \<in> S \<Longrightarrow> a i \<in> sigma A)"
  shows "(\<Inter>i\<in>S. a i) \<in> sigma A"(*<*)
proof -
  from a have "\<And>i. (if i\<in>S then {} else UNIV) \<union> a i \<in> sigma A"
    by (simp add: sigma.intros sigma_UNIV)
  hence "(\<Inter>i. (if i\<in>S then {} else UNIV) \<union> a i) \<in> sigma A"
    by (rule sigma_Inter)
  also have "(\<Inter>i. (if i\<in>S then {} else UNIV) \<union> a i) = (\<Inter>i\<in>S. a i)"
    by force
  finally show ?thesis .
qed(*>*)


lemma assumes s: "sigma_algebra a" shows sigma_algebra_UNIV: "UNIV \<in> a"(*<*)
proof -
  from s have "{}\<in>a" by (unfold sigma_algebra_def) blast
  with s show ?thesis by (unfold sigma_algebra_def) auto
qed(*>*)


end
