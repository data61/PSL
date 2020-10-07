subsubsection\<open>Completeness\<close>
theory Resolution_Compl
imports Resolution CNF_Sema
begin
  
text\<open>Completeness proof following Schöning~\cite{schoening1987logik}.\<close>

definition "make_lit v a \<equiv> case v of True \<Rightarrow> Pos a | False \<Rightarrow> Neg a"

definition "restrict_cnf_atom a v C \<equiv> {c - {make_lit (\<not>v) a} | c. c \<in> C \<and> make_lit v a \<notin> c}"


lemma restrict_cnf_remove: "atoms_of_cnf (restrict_cnf_atom a v c) \<subseteq>
  atoms_of_cnf c - {a}"
  unfolding  restrict_cnf_atom_def atoms_of_cnf_alt lit_atoms_cases make_lit_def
  by (force split: literal.splits bool.splits)

lemma cnf_substitution_lemma:
  "cnf_semantics A (restrict_cnf_atom a v S) = cnf_semantics (A(a := v)) S"
  unfolding restrict_cnf_atom_def cnf_semantics_def clause_semantics_def lit_semantics_cases make_lit_def
  apply (clarsimp split: bool.splits literal.splits)
  apply safe
     subgoal for s by(fastforce elim!: allE[of _ "s - {Neg a}"]) 
    subgoal by (metis DiffI singletonD)
   subgoal for s by(fastforce elim!: allE[of _ "s - {Pos a}"])
  subgoal by (metis DiffI singletonD)
done

lemma finite_restrict: "finite S \<Longrightarrow> finite (restrict_cnf_atom a v S)"
  unfolding restrict_cnf_atom_def by(simp add: image_iff)

text\<open>The next lemma describes what we have to (or can) do to a CNF after it has been mangled by @{const restrict_cnf_atom} to get back to
(a subset of) the original CNF.
The idea behind this will be clearer upon usage.\<close>
lemma unrestrict_effects:
  "(\<lambda>c. if {make_lit (\<not>v) a} \<union> c \<in> S then {make_lit (\<not>v) a} \<union> c else c) ` restrict_cnf_atom a v S \<subseteq> S"
proof -
  have "\<lbrakk>xa \<in> restrict_cnf_atom a v S; {make_lit (\<not> v) a} \<union> xa \<notin> S; x = xa\<rbrakk> \<Longrightarrow> xa \<in> S" for x xa
    unfolding restrict_cnf_atom_def using insert_Diff by fastforce
  hence "x \<in> (\<lambda>c. if {make_lit (\<not> v) a} \<union> c \<in> S then {make_lit (\<not> v) a} \<union> c else c) ` restrict_cnf_atom a v S \<Longrightarrow> x \<in> S" for x
    unfolding image_iff by(elim bexE) simp
  thus ?thesis ..
qed

lemma can_cope_with_unrestrict_effects:
  assumes pr: "S \<turnstile> \<box>"
  assumes su: "S \<subseteq> T"
  shows "\<exists>R \<subseteq> {make_lit v a}. (\<lambda>c. if c \<in> n then {make_lit v a} \<union> c else c) ` T \<turnstile> R"
proof -
  from Resolution_taint_assumptions[where D="{make_lit v a}"]
  have taint: "\<Gamma> \<union> \<Lambda> \<turnstile> \<box> \<Longrightarrow> \<exists>R\<subseteq>{make_lit v a}. insert (make_lit v a) ` \<Gamma> \<union> \<Lambda> \<turnstile> R"
    for \<Gamma> \<Lambda> by (metis image_cong insert_def sup_bot.right_neutral)
  have S: "S = {c \<in> S. c \<in> n} \<union> {c \<in> S. c \<notin> n}" by blast
  hence SI: "(\<lambda>c. if c \<in> n then {make_lit v a} \<union> c else c) ` S =
    (insert (make_lit v a) ` {c \<in> S. c \<in> n}) \<union> {c \<in> S. c \<notin> n}
  " by auto
  from pr have "\<exists>R \<subseteq> {make_lit v a}.
  (\<lambda>c. if c \<in> n then {make_lit v a} \<union> c else c) ` S \<turnstile> R"
    apply(subst SI)
    apply(subst(asm) S)
    apply(elim taint)
  done
  thus ?thesis using Resolution_weaken su by (metis (no_types, lifting) image_Un sup.order_iff)
qed

lemma unrestrict': 
  fixes R :: "'a clause"
  assumes rp: "restrict_cnf_atom a v S \<turnstile> \<box>"
  shows "\<exists>R \<subseteq> {make_lit (\<not>v) a}. S \<turnstile> R"
proof -
  fix C :: "'a clause" fix k :: 'a
  from unrestrict_effects[of v a S]
  text\<open>The idea is that the restricted set lost some clauses, and that some others were crippled.
    So, there must be a set of clauses to heal and a set of clauses to reinsert to get the original.
    (Mind you, this is not exactly what is happening, because e.g. both
   @{term C} and @{term "{k\<inverse>} \<union> C"} might be in there and get reduced to one @{term C}.
    You then heal that @{term C} to @{term "{k\<inverse>} \<union> C"} and insert the shadowed @{term C}\<open>\<dots>\<close> Details.)
 \<close>
  obtain n where S:
    "(\<lambda>c. if c \<in> n then {make_lit (\<not> v) a} \<union> c else c) ` restrict_cnf_atom a v S \<subseteq> S"
    using exI[where x="{c. {make_lit (\<not>v) a} \<union> c \<in> S}"] by force
  note  finite_restrict S
  show ?thesis using can_cope_with_unrestrict_effects[OF rp]
    by (metis (no_types) S Resolution_weaken subset_refl sup.order_iff)
qed

lemma Resolution_complete_standalone_finite:
  assumes ns: "\<forall>\<A>. \<not>cnf_semantics \<A> S"
  assumes fin: "finite (atoms_of_cnf S)"
  shows "S \<turnstile> \<box>"
using fin ns
proof(induction "atoms_of_cnf S" arbitrary: S rule: finite_psubset_induct)
  case psubset
  show ?case proof(cases)
    assume e: "atoms_of_cnf S = {}"
    from \<open>\<forall>\<A>. \<not> cnf_semantics \<A> S\<close> have "S \<noteq> {}" unfolding cnf_semantics_def by blast
    with e have "S = {\<box>}" unfolding atoms_of_cnf_def by simp fast
    thus ?case using Resolution.Ass by blast
  next
    have unsat_restrict: "\<forall>\<A>. \<not> cnf_semantics \<A> (restrict_cnf_atom a v S)" for a v
      using \<open>\<forall>\<A>. \<not> cnf_semantics \<A> S\<close> by(simp add: cnf_substitution_lemma)
    assume ne: "atoms_of_cnf S \<noteq> {}"
    then obtain a where "a \<in> atoms_of_cnf S" by blast
    hence "atoms_of_cnf (restrict_cnf_atom a v S) \<subset> atoms_of_cnf S" for v
      using restrict_cnf_remove[where 'a='a] by blast
    from psubset(2)[OF this unsat_restrict]
    have IH: "restrict_cnf_atom a v S \<turnstile> \<box>" for v .
    from unrestrict'[OF IH, of "\<not> _"] have unr_IH: "\<exists>R\<subseteq>{make_lit v a}. S \<turnstile> R"
        for v by simp (* unbelievable, how much worry finding that "\<not> _" cost\<dots> otherwise, you get weird sledgehammer results. *)
    from this[of False] this[of True] show ?case using Resolution.R[OF _ _ singletonI singletonI]
      by (simp add: make_lit_def) (fast dest: subset_singletonD)
  qed
qed

text\<open>What you might actually want is  @{term "\<forall>\<A>. \<not>cnf_semantics \<A> S \<Longrightarrow> S \<turnstile> \<box>"}.
  Unfortunately, applying compactness (to get a finite set with a finite number of atoms) here is problematic:
  You would need to convert all clauses to disjunction-formulas, but there might be clauses with an infinite number of atoms. 
  Removing those has to be done before applying compactness, we would possibly have to remove an infinite number of infinite clauses.
  Since the notion of a formula with an infinite number of atoms is not exactly standard, it is probably better to just skip this.
 \<close>

end
