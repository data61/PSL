theory Temporal imports Main
begin
  section\<open>Linear Temporal Logic\<close>
  text\<open>
    In this section we introduce an algebraic axiomatization of Linear Temporal Logic (LTL).
    We model LTL formulas semantically as predicates on traces. For example the LTL formula
    $\alpha = \Box\; \diamondsuit\; (x = 1)$ is modeled as a predicate 
    $\alpha : (nat \Rightarrow nat) \Rightarrow bool$, where 
    $\alpha \;x = True$ if $x\;i=1$ for infinitely many $i:nat$. In this formula $\Box$
    and $\diamondsuit$ denote the always and eventually operators, respectively. 
    Formulas with multiple variables are modeled similarly. For example a formula $\alpha$ in two 
    variables is modeled as $\alpha : (nat \Rightarrow \tv a) \Rightarrow (nat \Rightarrow \tv b) \Rightarrow bool$,
    and for example $(\Box\; \alpha) \; x\; y$ is defined as $(\forall i . \alpha \; x[i..]\; y[i..])$,
    where $x[i..]\;j = x\;(i+j)$. We would like to construct an algebraic structure (Isabelle class) 
    which has the temporal operators as operations, and which has instatiations to 
    $(nat \Rightarrow \tv a) \Rightarrow bool$, $(nat \Rightarrow \tv a) \Rightarrow (nat \Rightarrow \tv b) \Rightarrow bool$,
    and so on. Ideally our structure should be such that if we have this structure on a type $\tv a::temporal$,
    then we could extend it to $(nat \Rightarrow \tv b) \Rightarrow \tv a$ in a way similar to the
    way Boolean algebras are extended from a type $\tv a::boolean\_algebra$ to $\tv b\Rightarrow \tv a$.
    Unfortunately, if we use for example $\Box$ as primitive operation on our temporal structure,
    then we cannot extend $\Box$ from $\tv a::temporal$ to $(nat \Rightarrow \tv b) \Rightarrow \tv a$. A
    possible extension of $\Box$ could be
      $$(\Box\; \alpha)\;x = \bigwedge_{i:nat} \Box (\alpha\; x[i..]) \mbox{ and } \Box \; b = b$$
    where $\alpha: (nat \Rightarrow \tv b) \Rightarrow \tv a$ and $b:bool$. However, if we apply this
    definition to $\alpha : (nat \Rightarrow \tv a) \Rightarrow (nat \Rightarrow \tv b) \Rightarrow bool$,
    then we get
      $$(\Box\; \alpha) \; x\; y = (\forall i\;j. \alpha \; x[i..]\; y[j..])$$
    which is not correct.

    To evercome this problem we introduce as a primitive operation $!!:\tv a \Rightarrow nat \Rightarrow \tv a$,
    where $\tv a$ is the type of temporal formulas, and $\alpha !! i$ is the formula $\alpha$ at time point $i$.
    If $\alpha$ is a formula in two variables as before, then
      $$(\alpha !! i)\; x\;y = \alpha\; x[i..]\;y[i..].$$
    and we define for example the the operator always by
      $$\Box \alpha = \bigwedge_{i:nat} \alpha !! i$$
\<close>
  notation
    bot ("\<bottom>") and
    top ("\<top>") and
    inf (infixl "\<sqinter>" 70)
    and sup (infixl "\<squnion>" 65)

  class temporal = complete_boolean_algebra +
    fixes at :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 150)
    assumes [simp]: "a !! i !! j = a !! (i + j)"
    assumes [simp]: "a !! 0 = a"
    assumes [simp]: "\<top> !! i = \<top>"
    assumes [simp]: "-(a !! i) = (-a) !! i"
    assumes [simp]: "(a \<sqinter> b) !! i = (a !! i) \<sqinter> (b !! i)"
    begin
      definition always :: "'a \<Rightarrow> 'a"  ("\<box> (_)" [900] 900) where
        "\<box> p = (INF i . p !! i)"

      definition eventually :: "'a \<Rightarrow> 'a"  ("\<diamond> (_)" [900] 900) where
        "\<diamond> p = (SUP i . p !! i)"

      definition "next" :: "'a \<Rightarrow> 'a"  ("\<circle> (_)" [900] 900) where
        "\<circle> p = p !! (Suc 0)"

      definition until :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "until" 65) where 
        "(p until q) = (SUP n . (Inf (at p ` {i . i < n})) \<sqinter> (q !! n))"
    end

text\<open>
Next lemma, in the context of complete boolean algebras, will be used 
to prove $-(p\ until\ -p) = \Box\; p$.
\<close>
  context complete_boolean_algebra
    begin
      lemma until_always: "(INF n. (SUP i \<in> {i. i < n} . - p i) \<squnion> ((p :: nat \<Rightarrow> 'a) n)) \<le> p n"
        proof -
          have "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (INF i\<in>{i. i \<le> n}. p i)"
            proof (induction n)
              have "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (SUP i\<in>{i. i < 0}. - p i) \<squnion> p 0"
                by (rule INF_lower, simp)
              also have "... \<le> (INF i\<in>{i. i \<le> 0}. p i)"
                by simp
              finally show "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (INF i\<in>{i. i \<le> 0}. p i)"
                by simp
            next
              fix n::nat assume "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (INF i \<in> {i. i \<le> n}. p i)"
              also have "\<And> i . i \<le> n \<Longrightarrow> ... \<le> p i" by (rule INF_lower, simp)
              finally have [simp]: "\<And> i . i \<le> n \<Longrightarrow> (INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> p i"
                by simp
              show "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (INF i \<in> {i. i \<le> Suc n}. p i)"
                proof (rule INF_greatest, safe, cases)
                  fix i::nat
                    assume "i \<le> n" from this show "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> p i" by simp
                next
                  fix i::nat
                    have A: "{i. i \<le> n} = {i . i < Suc n}" by auto
                    have B: "(SUP i\<in>{i. i \<le> n}. - p i) \<le> - (INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n)"
                      by (metis (lifting, mono_tags) \<open>(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (INF i\<in>{i. i \<le> n}. p i)\<close> compl_mono uminus_INF)
                    assume "i \<le> Suc n" and "\<not> i \<le> n"
                    from this have [simp]: "i = Suc n" by simp
                    have "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> (INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<sqinter> ((SUP i\<in>{i. i \<le> n}. - p i) \<squnion> p (Suc n))"
                      by (simp add: A, rule INF_lower, simp)
                    also have "... \<le> ((INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<sqinter> ((- (INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n)) \<squnion> p (Suc n)))"
                      by (rule inf_mono, simp_all, rule_tac y = "- (INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n)" in order_trans, simp_all add: B)
                    also have "... \<le> p i"
                      by (simp add: inf_sup_distrib1 inf_compl_bot)
                    finally show "(INF n. (SUP i\<in>{i. i < n}. - p i) \<squnion> p n) \<le> p i" by simp
                qed
            qed
        also have "(INF i\<in>{i. i \<le> n}. p i) \<le> p n" by (rule INF_lower, auto)
        finally show "(INF n. (SUP i \<in> {i. i < n} . - p i) \<squnion> ((p :: nat \<Rightarrow> 'a) n)) \<le> p n" by simp
        qed

     end

text\<open>
  We prove now a number of results of the temporal class.
\<close>
  context temporal
    begin   
      lemma [simp]: "(a \<squnion> b) !! i = (a !! i) \<squnion> (b !! i)"
        by (subst compl_eq_compl_iff [THEN sym], simp)

      lemma always_less [simp]: "\<box> p \<le> p"
        proof -
          have "\<box> p \<le> p !! 0"
            by (unfold always_def, rule INF_lower, simp)
          also have "p !! 0 = p" by simp
          finally show "\<box> p \<le> p" by simp
        qed

      lemma always_and: "\<box> (p \<sqinter> q) = (\<box> p) \<sqinter> (\<box> q)"
        by (simp add: always_def INF_inf_distrib)

      lemma eventually_or: "\<diamond> (p \<squnion> q) = (\<diamond> p) \<squnion> (\<diamond> q)"
        by (simp add: eventually_def SUP_sup_distrib)

      lemma neg_until_always: "-(p until -p) = \<box> p"
        proof (rule antisym)
          show "- (p until - p) \<le> \<box> p"
           by (simp add: until_def always_def uminus_SUP uminus_INF, rule INF_greatest, cut_tac p = "\<lambda> n . p !! n" in until_always, simp)
        next
          have "\<And> n . \<box> p \<le> p !! n"
            by (simp add: always_def INF_lower)
          also have "\<And> n . p !! n \<le> (SUP x\<in>{i. i < n}. (- p) !! x) \<squnion> p !! n"
            by simp
          finally show "\<box> p \<le> -(p until -p)"
            apply (simp add: until_def uminus_SUP uminus_INF)
            by (rule INF_greatest, simp)
        qed

      lemma neg_always_eventually: "\<box> p = - \<diamond> (- p)"
        by (simp add: fun_eq_iff always_def eventually_def until_def uminus_SUP)
        
      lemma neg_true_until_always: "-(\<top> until -p) = \<box> p"
        by (simp add: fun_eq_iff always_def until_def uminus_SUP uminus_INF)

      lemma true_until_eventually: "(\<top> until p) = \<diamond> p"
        by (cut_tac p = "-p" in neg_always_eventually, cut_tac p = "-p" in neg_true_until_always, simp)
    end

text\<open>
  Boolean algebras with $b!!i = b$ form a temporal class.
\<close>

  instantiation bool :: temporal
    begin
      definition at_bool_def [simp]: "(p::bool) !! i = p"
    instance proof 
      qed auto
    end

  type_synonym 'a trace = "nat \<Rightarrow> 'a"

text\<open>
  Asumming that $\tv a::temporal$ is a type of class $temporal$, and $\tv b$ is an arbitrary type,
  we would like to create the instantiation of $\tv b\ trace \Rightarrow \tv a$ as a temporal
  class. However Isabelle allows only instatiations of functions from a class to another 
  class. To solve this problem we introduce a new class called trace with an operation
  $\mathit{suffix}::\tv a \Rightarrow nat \Rightarrow \tv a$ where 
  $\mathit{suffix}\;a\;i\;j = (a[i..])\; j = a\;(i+j)$ when
  $a$ is a trace with elements of some type $\tv b$ ($\tv a = nat \Rightarrow \tv b$). 
\<close>

  class trace =
    fixes suffix :: "'a \<Rightarrow> nat \<Rightarrow> 'a" ("_[_ ..]" [80, 15] 80)
    assumes [simp]: "a[i..][j..] = a[i + j..]"
    assumes [simp]: "a[0..] = a"
    begin
      definition "next_trace" :: "'a \<Rightarrow> 'a"  ("\<odot> (_)" [900] 900) where
        "\<odot> p = p[Suc 0..]"
    end

  instantiation "fun" :: (trace, temporal) temporal
    begin
      definition at_fun_def: "(P:: 'a \<Rightarrow> 'b) !! i = (\<lambda> x . (P (x[i..])) !! i)"
      instance proof qed  (simp_all add: at_fun_def add.commute fun_eq_iff le_fun_def)
    end

text\<open>
  In the last part of our formalization, we need to instantiate the functions
  from $nat$ to some arbitrary type $\tv a$ as a trace class. However, this again is not
  possible using the instatiation mechanism of Isabelle. We solve this problem
  by creating another class called $nat$, and then we instatiate the functions
  from $\tv a::nat$ to $\tv b$ as traces. The class $nat$ is defined such that if we
  have a type $\tv a::nat$, then $\tv a$ is isomorphic to the type $nat$. 
\<close>

  class nat = zero + plus + minus +
    fixes RepNat :: "'a \<Rightarrow> nat"
    fixes AbsNat :: "nat \<Rightarrow> 'a"
    assumes [simp]: "RepNat (AbsNat n) = n"
    and [simp]: "AbsNat (RepNat x) = x"
    and zero_Nat_def: "0 = AbsNat 0"
    and plus_Nat_def: "a + b = AbsNat (RepNat a + RepNat b)"
    and minus_Nat_def: "a - b = AbsNat (RepNat a - RepNat b)"
  begin
    lemma AbsNat_plus: "AbsNat (i + j) = AbsNat i + AbsNat j"
      by (simp add: plus_Nat_def)
    lemma AbsNat_zero [simp]: "AbsNat 0 + i = i"
      by (simp add: plus_Nat_def)

    subclass comm_monoid_diff 
      apply (unfold_locales)
        apply (simp_all add: plus_Nat_def zero_Nat_def minus_Nat_def add.assoc)
        by (simp add: add.commute)
  end

text\<open>
  The type natural numbers is an instantiation of the class $nat$.
\<close>

  instantiation nat :: nat
    begin
      definition RepNat_nat_def [simp]: "(RepNat:: nat \<Rightarrow> nat) = id"
      definition AbsNat_nat_def [simp]: "(AbsNat:: nat \<Rightarrow> nat) = id"
      instance proof 
        qed auto
    end

text\<open>
  Finally, functions from $\tv a::nat$ to some arbitrary type $\tv b$ are instatiated
  as a trace class. 
\<close>

  instantiation "fun" :: (nat, type) trace
    begin
      definition at_trace_def [simp]: "((t :: 'a \<Rightarrow> 'b)[i..]) j = (t  (AbsNat i + j))"
    instance proof
      qed (simp_all add: fun_eq_iff AbsNat_plus add.assoc)
    end

text\<open>
  By putting together all class definitions and instatiations introduced so far, we obtain the
  temporal class structure for predicates on traces with arbitrary number of parameters.

  For example in the next lemma $r$ and $r'$ are predicate relations, and the operator
  always is available for them as a consequence of the above construction.
\<close>


  lemma "(\<box> r) OO (\<box> r') \<le> (\<box> (r OO r'))"
    by (simp add: le_fun_def always_def at_fun_def, auto)

  end
