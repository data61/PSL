(*  Author:     Tobias Nipkow, 2002  *)

section "Arrow's Theorem for Utility Functions"

theory Arrow_Utility imports Complex_Main
begin

text\<open>This theory formalizes the first proof due to
Geanakoplos~\cite{Geanakoplos05}.  In contrast to the standard model
of preferences as linear orders, we model preferences as \emph{utility
functions} mapping each alternative to a real number. The type of
alternatives and voters is assumed to be finite.\<close>

typedecl alt
typedecl indi

axiomatization where
  alt3: "\<exists>a b c::alt. distinct[a,b,c]" and
  finite_alt: "finite(UNIV:: alt set)" and

  finite_indi: "finite(UNIV:: indi set)"

lemma third_alt: "a \<noteq> b \<Longrightarrow> \<exists>c::alt. distinct[a,b,c]"
using alt3 by simp metis

lemma alt2: "\<exists>b::alt. b \<noteq> a"
using alt3 by simp metis

type_synonym pref = "alt \<Rightarrow> real"
type_synonym prof = "indi \<Rightarrow> pref"

definition
 top :: "pref \<Rightarrow> alt \<Rightarrow> bool" (infixr "<\<cdot>" 60) where
"p <\<cdot> b  \<equiv>  \<forall>a. a \<noteq> b \<longrightarrow> p a < p b"

definition
 bot :: "alt \<Rightarrow> pref \<Rightarrow> bool" (infixr "\<cdot><" 60) where
"b \<cdot>< p  \<equiv>  \<forall>a. a \<noteq> b \<longrightarrow> p b < p a"

definition
 extreme :: "pref \<Rightarrow> alt \<Rightarrow> bool" where
"extreme p b  \<equiv>  b \<cdot>< p \<or> p <\<cdot> b"

abbreviation
"Extreme P b == \<forall>i. extreme (P i) b"

lemma [simp]: "r <= s \<Longrightarrow> r < s+(1::real)"
by arith
lemma [simp]: "r < s \<Longrightarrow> r < s+(1::real)"
by arith
lemma [simp]: "r <= s \<Longrightarrow> \<not> s+(1::real) < r"
by arith
lemma [simp]: "(r < s-(1::real)) = (r+1 < s)"
by arith
lemma [simp]: "(s-(1::real) < r) = (s < r+1)"
by arith

lemma less_if_bot[simp]: "\<lbrakk> b \<cdot>< p; x \<noteq> b \<rbrakk> \<Longrightarrow> p b < p x"
by(simp add:bot_def)

lemma [simp]: "\<lbrakk> p <\<cdot> b; x \<noteq> b \<rbrakk> \<Longrightarrow> p x < p b"
by(simp add:top_def)

lemma [simp]: assumes top: "p <\<cdot> b" shows "\<not> p b < p c"
proof (cases)
  assume "b = c" thus ?thesis by simp
next
  assume "b \<noteq> c"
  with top have "p c < p b" by (simp add:eq_sym_conv)
  thus ?thesis by simp
qed

lemma not_less_if_bot[simp]:
  assumes bot: "b \<cdot>< p" shows "\<not> p c < p b"
proof (cases)
  assume "b = c" thus ?thesis by simp
next
  assume "b \<noteq> c"
  with bot have "p b < p c" by (simp add:eq_sym_conv)
  thus ?thesis by simp
qed

lemma top_impl_not_bot[simp]: "p <\<cdot> b \<Longrightarrow> \<not> b \<cdot>< p"
by(unfold bot_def, simp add:alt2)

lemma [simp]: "extreme p b \<Longrightarrow> (\<not> p <\<cdot> b) = (b \<cdot>< p)"
apply(unfold extreme_def)
apply(fastforce dest:top_impl_not_bot)
done

lemma [simp]: "extreme p b \<Longrightarrow> (\<not> b \<cdot>< p) = (p <\<cdot> b)"
apply(unfold extreme_def)
apply(fastforce dest:top_impl_not_bot)
done

text\<open>Auxiliary construction to hide details of preference model.\<close>

definition
 mktop :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
"mktop p b \<equiv> p(b := Max(range p) + 1)"

definition
 mkbot :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
"mkbot p b \<equiv> p(b := Min(range p) - 1)"

definition
 between :: "pref \<Rightarrow> alt \<Rightarrow> alt \<Rightarrow> alt \<Rightarrow> pref" where
"between p a b c \<equiv> p(b := (p a + p c)/2)"

text\<open>To make things simpler:\<close>
declare between_def[simp]

lemma [simp]: "a \<noteq> b \<Longrightarrow> mktop p b a = p a"
by(simp add:mktop_def)

lemma [simp]: "a \<noteq> b \<Longrightarrow> mkbot p b a = p a"
by(simp add:mkbot_def)

lemma [simp]: "a \<noteq> b \<Longrightarrow> p a < mktop p b b"
by(simp add:mktop_def finite_alt)

lemma [simp]: "a \<noteq> b \<Longrightarrow> mkbot p b b < p a"
by(simp add:mkbot_def finite_alt)

lemma [simp]: "mktop p b <\<cdot> b"
by(simp add:mktop_def top_def finite_alt)

lemma [simp]: "\<not> b \<cdot>< mktop p b"
by(simp add:mktop_def bot_def alt2 finite_alt)

lemma [simp]: "a \<noteq> b \<Longrightarrow> \<not> P p a < mkbot (P p) b b"
proof (simp add:mkbot_def finite_alt)
  have "\<not> P p a + 1 < P p a" by simp
  thus "\<exists>x. \<not> P p a + 1 < P p x" ..
qed

text\<open>The proof starts here.\<close>

locale arrow =
fixes F :: "prof \<Rightarrow> pref"
assumes unanimity: "(\<And>i. P i a < P i b) \<Longrightarrow> F P a < F P b"
and IIA:
"(\<And>i. (P i a < P i b) = (P' i a < P' i b)) \<Longrightarrow>
 (F P a < F P b) = (F P' a < F P' b)"
begin

lemmas IIA' = IIA[THEN iffD1]

definition
 dictates :: "indi \<Rightarrow> alt \<Rightarrow> alt \<Rightarrow> bool" ("_ dictates _ < _") where
"(i dictates a < b)  \<equiv>  \<forall>P. P i a < P i b \<longrightarrow> F P a < F P b"
definition
 dictates2 :: "indi \<Rightarrow> alt \<Rightarrow> alt \<Rightarrow> bool" ("_ dictates _,_") where
"(i dictates a,b)  \<equiv>  (i dictates a < b) \<and> (i dictates b < a)"
definition
 dictatesx:: "indi \<Rightarrow> alt \<Rightarrow> bool" ("_ dictates'_except _") where
"(i dictates_except c)  \<equiv>  \<forall>a b. c \<notin> {a,b} \<longrightarrow> (i dictates a<b)"
definition
 dictator :: "indi \<Rightarrow> bool" where
"dictator i  \<equiv>  \<forall>a b. (i dictates a<b)"

definition
 pivotal :: "indi \<Rightarrow> alt \<Rightarrow> bool" where
"pivotal i b \<equiv>
 \<exists>P. Extreme P b  \<and>  b \<cdot>< P i  \<and>  b \<cdot>< F P  \<and>
     F (P(i := mktop (P i) b)) <\<cdot> b"

lemma all_top[simp]: "\<forall>i. P i <\<cdot> b \<Longrightarrow> F P <\<cdot> b"
by (unfold top_def) (simp add: unanimity)

lemma not_extreme:
  assumes nex: "\<not> extreme p b"
  shows "\<exists>a c. distinct[a,b,c] \<and> \<not> p a < p b \<and> \<not> p b < p c"
proof -
  obtain a c where abc: "a \<noteq> b \<and> \<not> p a < p b" "b \<noteq> c \<and> \<not> p b < p c"
    using nex by (unfold extreme_def top_def bot_def) fastforce
  show ?thesis
  proof (cases "a = c")
    assume "a \<noteq> c" thus ?thesis using abc by simp blast
  next
    assume ac: "a = c"
    obtain d where d: "distinct[a,b,d]" using abc third_alt by blast
    show ?thesis
    proof (cases "p b < p d")
      case False thus ?thesis using abc d by blast
    next
      case True
      hence db: "\<not> p d < p b" by arith
      from d have "distinct[d,b,c]" by(simp add:ac eq_sym_conv)
      thus ?thesis using abc db by blast
    qed
  qed
qed

lemma extremal:
  assumes extremes: "Extreme P b" shows "extreme (F P) b"
proof (rule ccontr)
  assume nec: "\<not> extreme (F P) b"
  hence "\<exists>a c. distinct[a,b,c] \<and> \<not> F P a < F P b \<and> \<not> F P b < F P c"
    by(rule not_extreme)
  then obtain a c where d: "distinct[a,b,c]" and
    ab: "\<not> F P a < F P b" and bc: "\<not> F P b < F P c" by blast
  let ?P = "\<lambda>i. if P i <\<cdot> b then between (P i) a c b
                else (P i)(c := P i a + 1)"
  have "\<not> F ?P a < F ?P b"
    using extremes d by(simp add:IIA[of _ _ _ P] ab)
  moreover have "\<not> F ?P b < F ?P c"
    using extremes d by(simp add:IIA[of _ _ _ P] bc eq_sym_conv)
  moreover have "F ?P a < F ?P c" by(rule unanimity)(insert d, simp)
  ultimately show False by arith
qed


lemma pivotal_ind: assumes fin: "finite D"
  shows "\<And>P. \<lbrakk> D = {i. b \<cdot>< P i}; Extreme P b; b \<cdot>< F P \<rbrakk>
  \<Longrightarrow> \<exists>i. pivotal i b" (is "\<And>P. ?D D P \<Longrightarrow> ?E P \<Longrightarrow> ?B P \<Longrightarrow> _")
using fin
proof (induct)
  case (empty P)
  from empty(1,2) have "\<forall>i. P i <\<cdot> b" by simp
  hence "F P <\<cdot> b" by simp
  hence False using empty by(blast dest:top_impl_not_bot)
  thus ?case ..
next
  fix D i P
  assume IH: "\<And>P. ?D D P \<Longrightarrow> ?E P \<Longrightarrow> ?B P \<Longrightarrow> \<exists>i. pivotal i b"
    and "?E P" and "?B P" and insert: "insert i D = {i. b \<cdot>< P i}" and "i \<notin> D"
  from insert have "b \<cdot>< P i" by blast
  let ?P = "P(i := mktop (P i) b)"
  show "\<exists>i. pivotal i b"
  proof (cases "F ?P <\<cdot> b")
    case True
    have "pivotal i b"
    proof -
      from \<open>?E P\<close> \<open>?B P\<close> \<open>b \<cdot>< P i\<close> True
      show ?thesis by(unfold pivotal_def, blast)
    qed
    thus ?thesis ..
  next
    case False
    have "D = {i. b \<cdot>< ?P i}"
      by (rule set_eqI) (simp add:\<open>i \<notin> D\<close>, insert insert, blast)
    moreover have "Extreme ?P b"
      using \<open>?E P\<close> by (simp add:extreme_def)
    moreover have "b \<cdot>< F ?P"
      using extremal[OF \<open>Extreme ?P b\<close>] False by(simp del:fun_upd_apply)
    ultimately show ?thesis by(rule IH)
  qed
qed

lemma pivotal_exists: "\<exists>i. pivotal i b"
proof -
  let ?P = "(\<lambda>_ a. if a=b then 0 else 1)::prof"
  have "Extreme ?P b" by(simp add:extreme_def bot_def)
  moreover have "b \<cdot>< F ?P"
    by(simp add:bot_def unanimity del: less_if_bot not_less_if_bot)
  ultimately show "\<exists>i. pivotal i b"
    by (rule pivotal_ind[OF finite_subset[OF subset_UNIV finite_indi] refl])
qed


lemma pivotal_xdictates: assumes pivo: "pivotal i b"
  shows "i dictates_except b"
proof -
  have "\<And>a c. \<lbrakk> a \<noteq> b; b \<noteq> c \<rbrakk> \<Longrightarrow> i dictates a < c"
  proof (unfold dictates_def, intro allI impI)
    fix a c and P::prof
    assume abc: "a \<noteq> b" "b \<noteq> c" and
           ac: "P i a < P i c"
    show "F P a < F P c"
    proof -
      obtain P1 P2 where
        "Extreme P1 b" and "b \<cdot>< F P1" and "b \<cdot>< P1 i" and "F P2 <\<cdot> b" and
        [simp]: "P2 = P1(i := mktop (P1 i) b)"
        using pivo by (unfold pivotal_def) fast
      let ?P = "\<lambda>j. if j=i then between (P j) a b c
                    else if P1 j <\<cdot> b then mktop (P j) b else mkbot (P j) b"
      have eq: "(F P a < F P c) = (F ?P a < F ?P c)"
        using abc by - (rule IIA, auto)
      have "F ?P a < F ?P b"
      proof (rule IIA')
        fix j show "(P2 j a < P2 j b) = (?P j a < ?P j b)"
          using \<open>Extreme P1 b\<close> by(simp add: ac)
      next
        show "F P2 a < F P2 b"
          using \<open>F P2 <\<cdot> b\<close> abc by(simp add: eq_sym_conv)
      qed
      also have "\<dots> < F ?P c"
      proof (rule IIA')
        fix j show "(P1 j b < P1 j c) = (?P j b < ?P j c)"
          using \<open>Extreme P1 b\<close> \<open>b \<cdot>< P1 i\<close> by(simp add: ac)
      next
        show "F P1 b < F P1 c"
          using \<open>b \<cdot>< F P1\<close> abc by(simp add: eq_sym_conv)
      qed
      finally show ?thesis by(simp add:eq)
    qed
  qed
  thus ?thesis  by(unfold dictatesx_def) fast
qed

lemma pivotal_is_dictator:
  assumes pivo: "pivotal i b" and ab: "a \<noteq> b" and d: "j dictates a,b"
  shows "i = j"
proof (rule ccontr)
  assume pd: "i \<noteq> j"
  obtain P1 P2 where "Extreme P1 b" and "b \<cdot>< F P1" and "F P2 <\<cdot> b" and
    P2: "P2 = P1(i := mktop (P1 i) b)"
    using pivo by (unfold pivotal_def) fast
  have "~(P1 j a < P1 j b)" (is "~ ?ab")
  proof
    assume "?ab"
    hence "F P1 a < F P1 b" using d by(simp add: dictates_def dictates2_def)
    with \<open>b \<cdot>< F P1\<close> show False by simp
  qed
  hence "P1 j b < P1 j a" using \<open>Extreme P1 b\<close>[THEN spec, of j] ab
    unfolding extreme_def top_def bot_def by metis
  hence "P2 j b < P2 j a" using pd by (simp add:P2)
  hence "F P2 b < F P2 a" using d by(simp add: dictates_def dictates2_def)
  with \<open>F P2 <\<cdot> b\<close> show False by simp
qed


theorem dictator: "\<exists>i. dictator i"
proof-
  from pivotal_exists[of b] obtain i where pivo: "pivotal i b" ..
  { fix a assume neq: "a \<noteq> b" have "i dictates a,b"
    proof -
      obtain c where dist: "distinct[a,b,c]"
        using neq third_alt by blast
      obtain j where "pivotal j c" using pivotal_exists by fast
      hence "j dictates_except c" by(rule pivotal_xdictates)
      hence b: "j dictates a,b" 
        using dist by(simp add:dictatesx_def dictates2_def eq_sym_conv)
      with pivo neq have "i = j" by(rule pivotal_is_dictator)
      thus ?thesis using b by simp
    qed
  }
  with pivotal_xdictates[OF pivo] have "dictator i"
    by(simp add: dictates_def dictatesx_def dictates2_def dictator_def)
      (metis less_le)
  thus ?thesis ..
qed

end

end
