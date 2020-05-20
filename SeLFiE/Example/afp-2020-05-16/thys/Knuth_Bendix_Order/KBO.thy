section \<open>KBO\<close>

text \<open>
  Below, we formalize a variant of KBO that includes subterm coefficient functions.

  A more standard definition is obtained by setting all subterm coefficients to 1.
  For this special case it would be possible to define more efficient code-equations that
  do not have to evaluate subterm coefficients at all.
\<close>

theory KBO
  imports
    Lexicographic_Extension
    Term_Aux
    Polynomial_Factorization.Missing_List
begin

subsection \<open>Subterm Coefficient Functions\<close>

text \<open>
  Given a function @{term scf}, associating positions with subterm coefficients, and
  a list @{term xs}, the function @{term scf_list} yields an expanded list where  each
  element of @{term xs} is replicated a number of times according to its subterm coefficient.
\<close>
definition scf_list :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "scf_list scf xs = concat (map (\<lambda>(x, i). replicate (scf i) x) (zip xs [0 ..< length xs]))"

lemma set_scf_list [simp]:
  assumes "\<forall>i < length xs. scf i > 0"
  shows "set (scf_list scf xs) = set xs"
  using assms by (auto simp: scf_list_def set_zip set_conv_nth[of xs])

lemma scf_list_subset: "set (scf_list scf xs) \<subseteq> set xs"
  by (auto simp: scf_list_def set_zip)

lemma scf_list_empty [simp]:
  "scf_list scf [] = []" by (auto simp: scf_list_def)

lemma scf_list_bef_i_aft [simp]:
  "scf_list scf (bef @ i # aft) =
    scf_list scf bef @ replicate (scf (length bef)) i @
    scf_list (\<lambda> i. scf (Suc (length bef + i))) aft"
  unfolding scf_list_def
proof (induct aft rule: List.rev_induct)
  case (snoc a aft)
  define bia where "bia = bef @ i # aft"
  have bia: "bef @ i # aft @ [a] = bia @ [a]" by (simp add: bia_def)
  have zip: "zip (bia @ [a]) [0..<length (bia @ [a])]
   = zip bia [0..<length bia] @ [(a, length bia)]" by simp
  have concat:
    "concat (map (\<lambda>(x, i). replicate (scf i) x) (zip bia [0..<length bia] @ [(a, length bia)])) =
      concat (map (\<lambda>(x, i). replicate (scf i) x) (zip bia [0..<length bia])) @
      replicate (scf (length bia)) a" by simp
  show ?case
    unfolding bia zip concat
    unfolding bia_def snoc
    by simp
qed simp

lemma scf_list_map [simp]:
  "scf_list scf (map f xs) = map f (scf_list scf xs)"
  by (induct xs rule: List.rev_induct) (auto simp: scf_list_def)

text \<open>
  The function @{term scf_term} replicates each argument a number of times according to its
  subterm coefficient function.
\<close>
fun scf_term :: "('f \<times> nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
  where
    "scf_term scf (Var x) = (Var x)" |
    "scf_term scf (Fun f ts) = Fun f (scf_list (scf (f, length ts)) (map (scf_term scf) ts))"

lemma vars_term_scf_subset:
  "vars_term (scf_term scf s) \<subseteq> vars_term s"
proof (induct s)
  case (Fun f ss)
  have "vars_term (scf_term scf (Fun f ss)) =
    (\<Union>x\<in>set (scf_list (scf (f, length ss)) ss). vars_term (scf_term scf x))" by auto
  also have "\<dots> \<subseteq> (\<Union>x\<in>set ss. vars_term (scf_term scf x))"
    using scf_list_subset [of _ ss] by blast
  also have "\<dots> \<subseteq> (\<Union>x\<in>set ss. vars_term x)" using Fun by auto
  finally show ?case by auto
qed auto

lemma scf_term_subst:
  "scf_term scf (t \<cdot> \<sigma>) = scf_term scf t \<cdot> (\<lambda> x. scf_term scf (\<sigma> x))"
proof (induct t)
  case (Fun f ts)
  { fix t
    assume "t \<in> set (scf_list (scf (f, length ts)) ts)"
    with scf_list_subset [of _ ts] have "t \<in> set ts" by auto
    then have "scf_term scf (t \<cdot> \<sigma>) = scf_term scf t \<cdot> (\<lambda>x. scf_term scf (\<sigma> x))"  by (rule Fun) }
  then show ?case by auto
qed auto


subsection \<open>Weight Functions\<close>

locale weight_fun =
  fixes w :: "'f \<times> nat \<Rightarrow> nat"
    and w0 :: nat
    and scf :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> nat"
begin

text \<open>
  The \<^emph>\<open>weight\<close> of a term is computed recursively, where variables have weight @{term w0}
  and the weight of a compound term is computed by adding the weight of its root symbol
  @{term "w (f, n)"} to the weighted sum where weights of arguments are multiplied
  according to their subterm coefficients.
\<close>
fun weight :: "('f, 'v) term \<Rightarrow> nat"
  where
    "weight (Var x) = w0" |
    "weight (Fun f ts) =
    (let n = length ts; scff = scf (f, n) in
    w (f, n) + sum_list (map (\<lambda> (ti, i). weight ti * scff i) (zip ts [0 ..< n])))"

text \<open>
  Alternatively, we can replicate arguments via @{const scf_list}.
  The advantage is that then both @{const weight} and @{const scf_term} are defined
  via @{const scf_list}.
\<close>
lemma weight_simp [simp]:
  "weight (Fun f ts) = w (f, length ts) + sum_list (map weight (scf_list (scf (f, length ts)) ts))"
proof -
  define scff where "scff = (scf (f, length ts) :: nat \<Rightarrow> nat)"
  have "(\<Sum>(ti, i) \<leftarrow> zip ts [0..<length ts]. weight ti * scff i) =
   sum_list (map weight (scf_list scff ts))"
  proof (induct ts rule: List.rev_induct)
    case (snoc t ts)
    moreover
    { fix n
      have "sum_list (replicate n (weight t)) = n * weight t" by (induct n) auto }
    ultimately show ?case by (simp add: scf_list_def)
  qed simp
  then show ?thesis by (simp add: Let_def scff_def)
qed

declare weight.simps(2)[simp del]

abbreviation "SCF \<equiv> scf_term scf"

lemma sum_list_scf_list:
  assumes "\<And> i. i < length ts \<Longrightarrow> f i > 0"
  shows "sum_list (map weight ts) \<le> sum_list (map weight (scf_list f ts))"
  using assms unfolding scf_list_def
proof (induct ts rule: List.rev_induct)
  case (snoc t ts)
  have "sum_list (map weight ts) \<le>
    sum_list (map weight (concat (map (\<lambda>(x, i). replicate (f i) x) (zip ts [0..<length ts]))))"
    by (auto intro!: snoc)
  moreover
  from snoc(2) [of "length ts"] obtain n where "f (length ts) = Suc n" by (auto elim: lessE)
  ultimately show ?case by simp
qed simp

end


subsection \<open>Definition of KBO\<close>

text \<open>
  The precedence is given by three parameters:

  \<^item> a predicate @{term pr_strict} for strict decrease between two function symbols,
  \<^item> a predicate @{term pr_weak} for weak decrease between two function symbols, and
  \<^item> a function indicating whether a symbol is least in the precedence.
\<close>
locale kbo = weight_fun w w0 scf
  for w w0 and scf :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> nat" +
  fixes least :: "'f \<Rightarrow> bool"
    and pr_strict :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
    and pr_weak :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
begin

text \<open>
  The result of @{term kbo} is a pair of Booleans encoding strict/weak decrease.

  Interestingly, the bound on the lengths of the lists in the lexicographic extension is not 
  required for KBO.
\<close>
fun kbo :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool"
  where
    "kbo s t = (if (vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s)
      then if (weight t < weight s)
        then (True, True)
        else (case s of
          Var y \<Rightarrow> (False, (case t of Var x \<Rightarrow> x = y | Fun g ts \<Rightarrow> ts = [] \<and> least g))
        | Fun f ss \<Rightarrow> (case t of
            Var x \<Rightarrow> (True, True)
          | Fun g ts \<Rightarrow> if pr_strict (f, length ss) (g, length ts)
            then (True, True)
            else if pr_weak (f, length ss) (g, length ts)
            then lex_ext_unbounded kbo ss ts
            else (False, False)))
      else (False, False))"

text \<open>Abbreviations for strict (S) and nonstrict (NS) KBO.\<close>
abbreviation "S \<equiv> \<lambda> s t. fst (kbo s t)"
abbreviation "NS \<equiv> \<lambda> s t. snd (kbo s t)"

text \<open>
  For code-generation we do not compute the weights of @{term s} and @{term t} repeatedly.
\<close>
lemma kbo_code: "kbo s t = (let wt = weight t; ws = weight s in
    if (vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> wt \<le> ws)
    then if wt < ws
      then (True, True)
      else (case s of
        Var y \<Rightarrow> (False, (case t of Var x \<Rightarrow> True | Fun g ts \<Rightarrow> ts = [] \<and> least g))
      | Fun f ss \<Rightarrow> (case t of
          Var x \<Rightarrow> (True, True)
        | Fun g ts \<Rightarrow> let ff = (f, length ss); gg = (g, length ts) in
          if pr_strict ff gg
          then (True, True)
          else if pr_weak ff gg
            then lex_ext_unbounded kbo ss ts
            else (False, False)))
    else (False, False))"
  unfolding kbo.simps[of s t] Let_def
  by (auto simp del: kbo.simps split: term.splits)

end

declare kbo.kbo_code[code]
declare weight_fun.weight.simps[code]

lemma mset_replicate_mono:
  assumes "m1 \<subseteq># m2"
  shows "\<Union># (mset (replicate n m1)) \<subseteq># \<Union># (mset (replicate n m2))"
proof (induct n)
  case (Suc n)
  have "\<Union># (mset (replicate (Suc n) m1)) =
    \<Union># (mset (replicate n m1)) + m1" by simp
  also have "\<dots> \<subseteq># \<Union># (mset (replicate n m1)) + m2" using \<open>m1 \<subseteq># m2\<close> by auto
  also have "\<dots> \<subseteq># \<Union># (mset (replicate n m2)) + m2" using Suc by auto
  finally show ?case by (simp add: union_commute)
qed simp

text \<open>
  While the locale @{locale kbo} only fixes its parameters, we now demand that these
  parameters are sensible, e.g., encoding a well-founded precedence, etc.
\<close>
locale admissible_kbo =
  kbo w w0 scf least pr_strict pr_weak
  for w w0 pr_strict pr_weak and least :: "'f \<Rightarrow> bool" and scf +
  assumes w0: "w (f, 0) \<ge> w0" "w0 > 0"
    and adm: "w (f, 1) = 0 \<Longrightarrow> pr_weak (f, 1) (g, n)"
    and least: "least f = (w (f, 0) = w0 \<and> (\<forall> g. w (g, 0) = w0 \<longrightarrow> pr_weak (g, 0) (f, 0)))"
    and scf: "i < n \<Longrightarrow> scf (f, n) i > 0"
    and pr_weak_refl [simp]: "pr_weak fn fn"
    and pr_weak_trans: "pr_weak fn gm \<Longrightarrow> pr_weak gm hk \<Longrightarrow> pr_weak fn hk"
    and pr_strict: "pr_strict fn gm \<longleftrightarrow> pr_weak fn gm \<and> \<not> pr_weak gm fn"
    and pr_SN: "SN {(fn, gm). pr_strict fn gm}"
begin

lemma weight_w0: "weight t \<ge> w0"
proof (induct t)
  case (Fun f ts)
  show ?case
  proof (cases ts)
    case Nil
    with w0(1) have "w0 \<le> w (f, length ts)" by auto
    then show ?thesis by auto
  next
    case (Cons s ss)
    then obtain i where i: "i < length ts" by auto
    from scf[OF this] have scf: "0 < scf (f, length ts) i" by auto
    then obtain n where scf: "scf (f, length ts) i = Suc n" by (auto elim: lessE)
    from id_take_nth_drop[OF i] i obtain bef aft where ts: "ts = bef @ ts ! i # aft" and ii: "length bef = i" by auto
    define tsi where "tsi = ts ! i"
    note ts = ts[folded tsi_def]
    from i have tsi: "tsi \<in> set ts" unfolding tsi_def by auto
    from Fun[OF this] have w0: "w0 \<le> weight tsi" .
    show ?thesis using scf ii w0 unfolding ts
      by simp
  qed
qed simp

lemma weight_gt_0: "weight t > 0"
  using weight_w0 [of t] and w0 by arith

lemma weight_0 [iff]: "weight t = 0 \<longleftrightarrow> False"
  using weight_gt_0 [of t] by auto

lemma not_S_Var: "\<not> S (Var x) t"
  using weight_w0[of t] by (cases t, auto)

lemma S_imp_NS: "S s t \<Longrightarrow> NS s t"
proof (induct s t rule: kbo.induct)
  case (1 s t)
  from 1(2) have S: "S s t" .
  from S have w: "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s"
    by (auto split: if_splits)
  note S = S w
  note IH = 1(1)[OF w]
  show ?case
  proof (cases "weight t < weight s")
    case True
    with S show ?thesis by simp
  next
    case False
    note IH = IH[OF False]
    note S = S False
    from not_S_Var[of _ t] S
    obtain f ss where s: "s = Fun f ss" by (cases s, auto)
    note IH = IH[OF s]
    show ?thesis
    proof (cases t)
      case (Var x)
      from S show ?thesis by (auto, insert Var s, auto)
    next
      case (Fun g ts)
      note IH = IH[OF Fun]
      let ?f = "(f, length ss)"
      let ?g = "(g, length ts)"
      let ?lex = "lex_ext_unbounded kbo ss ts"
      from S[simplified, unfolded s Fun] have disj: "pr_strict ?f ?g \<or> pr_weak ?f ?g \<and> fst ?lex" by (auto split: if_splits)
      show ?thesis
      proof (cases "pr_strict ?f ?g")
        case True
        then show ?thesis using S s Fun by auto
      next
        case False
        with disj have fg: "pr_weak ?f ?g" and lex: "fst ?lex" by auto
        note IH = IH[OF False fg]
        from lex have "fst (lex_ext kbo (length ss + length ts) ss ts)"
          unfolding lex_ext_def Let_def by auto
        from lex_ext_stri_imp_nstri[OF this] have lex: "snd ?lex"
          unfolding lex_ext_def Let_def by auto
        with False fg S s Fun show ?thesis by auto
      qed
    qed
  qed
qed


subsection \<open>Reflexivity and Irreflexivity\<close>

lemma NS_refl: "NS s s"
proof (induct s)
  case (Fun f ss)
  have "snd (lex_ext kbo (length ss) ss ss)"
    by (rule all_nstri_imp_lex_nstri, insert Fun[unfolded set_conv_nth], auto)
  then have "snd (lex_ext_unbounded kbo ss ss)" unfolding lex_ext_def Let_def by simp
  then show ?case by auto
qed simp

lemma pr_strict_irrefl: "\<not> pr_strict fn fn"
  unfolding pr_strict by auto

lemma S_irrefl: "\<not> S t t"
proof (induct t)
  case (Var x) then show ?case by (rule not_S_Var)
next
  case (Fun f ts)
  from pr_strict_irrefl have "\<not> pr_strict (f, length ts) (f, length ts)" .
  moreover
  { assume "fst (lex_ext_unbounded kbo ts ts)"
    then obtain i where "i < length ts" and "S (ts ! i) (ts ! i)"
      unfolding lex_ext_unbounded_iff by auto
    with Fun have False by auto }
  ultimately show ?case by auto
qed


subsection \<open>Monotonicity (a.k.a. Closure under Contexts)\<close>

lemma S_mono_one:
  assumes S: "S s t"
  shows "S (Fun f (ss1 @ s # ss2)) (Fun f (ss1 @ t # ss2))"
proof -
  let ?ss = "ss1 @ s # ss2"
  let ?ts = "ss1 @ t # ss2"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"
  from S have w: "weight t \<le> weight s" and v: "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s)" 
    by (auto split: if_splits)
  have v': "vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF ?s)" using mset_replicate_mono[OF v] by simp
  have w': "weight ?t \<le> weight ?s" using sum_list_replicate_mono[OF w] by simp
  have lex: "fst (lex_ext_unbounded kbo ?ss ?ts)"
    unfolding lex_ext_unbounded_iff fst_conv
    by (rule disjI1, rule exI[of _ "length ss1"], insert S NS_refl, auto simp del: kbo.simps simp: nth_append)
  show ?thesis using v' w' lex by simp
qed

lemma S_ctxt: "S s t \<Longrightarrow> S (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
  by (induct C, auto simp del: kbo.simps intro: S_mono_one)

lemma NS_mono_one:
  assumes NS: "NS s t" shows "NS (Fun f (ss1 @ s # ss2)) (Fun f (ss1 @ t # ss2))"
proof -
  let ?ss = "ss1 @ s # ss2"
  let ?ts = "ss1 @ t # ss2"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"
  from NS have w: "weight t \<le> weight s" and v: "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s)"
    by (auto split: if_splits)
  have v': "vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF ?s)" using mset_replicate_mono[OF v] by simp
  have w': "weight ?t \<le> weight ?s" using sum_list_replicate_mono[OF w] by simp
  have lex: "snd (lex_ext_unbounded kbo ?ss ?ts)"
    unfolding lex_ext_unbounded_iff snd_conv
  proof (intro disjI2 conjI allI impI)
    fix i
    assume "i < length (ss1 @ t # ss2)"
    then show "NS (?ss ! i) (?ts ! i)" using NS NS_refl
      by (cases "i = length ss1", auto simp del: kbo.simps simp: nth_append)
  qed simp
  show ?thesis using v' w' lex by simp
qed

lemma NS_ctxt: "NS s t \<Longrightarrow> NS (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
  by (induct C, auto simp del: kbo.simps intro: NS_mono_one)


subsection \<open>The Subterm Property\<close>

lemma NS_Var_imp_eq_least: "NS (Var x) t \<Longrightarrow> t = Var x \<or> (\<exists> f. t = Fun f [] \<and> least f)"
  by (cases t, insert weight_w0[of t], auto split: if_splits)

lemma kbo_supt_one: "NS s (t :: ('f, 'v) term) \<Longrightarrow> S (Fun f (bef @ s # aft)) t"
proof (induct t arbitrary: f s bef aft)
  case (Var x)
  note NS = this
  let ?ss = "bef @ s # aft"
  let ?t = "Var x"
  have "length bef < length ?ss" by auto
  from scf[OF this, of f] obtain n where scf:"scf (f, length ?ss) (length bef) = Suc n" by (auto elim: lessE)
  obtain X where "vars_term_ms (SCF (Fun f ?ss)) = vars_term_ms (SCF s) + X"
    by (simp add: o_def scf[simplified])
  then have vs: "vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF (Fun f ?ss))" by simp
  from NS have vt: "vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF s)" by (auto split: if_splits)
  from vt vs have v: "vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF (Fun f ?ss))" by (rule subset_mset.order_trans)
  from weight_w0[of "Fun f ?ss"] v show ?case by simp
next
  case (Fun g ts f s bef aft)
  let ?t = "Fun g ts"
  let ?ss = "bef @ s # aft"
  note NS = Fun(2)
  note IH = Fun(1)
  have "length bef < length ?ss" by auto
  from scf[OF this, of f] obtain n where scff:"scf (f, length ?ss) (length bef) = Suc n" by (auto elim: lessE)
  note scff = scff[simplified]
  obtain X where "vars_term_ms (SCF (Fun f ?ss)) = vars_term_ms (SCF s) + X"
    by (simp add: o_def scff)
  then have vs: "vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF (Fun f ?ss))" by simp
  have ws: "weight s \<le> sum_list (map weight (scf_list (scf (f, length ?ss)) ?ss))"
    by (simp add: scff)
  from NS have wt: "weight ?t \<le> weight s" and
    vt: "vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF s)" by (auto split: if_splits)
  from ws wt have w: "weight ?t \<le> sum_list (map weight (scf_list (scf (f, length ?ss)) ?ss))" by simp
  from vt vs have v: "vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF (Fun f ?ss))" by auto
  then have v': "(vars_term_ms (SCF ?t) \<subseteq># vars_term_ms (SCF (Fun f ?ss))) = True" by simp
  show ?case
  proof (cases "weight ?t = weight (Fun f ?ss)")
    case False
    with w v show ?thesis by auto
  next
    case True
    from wt[unfolded True] weight_gt_0[of s]
    have wf: "w (f, length ?ss) = 0"
      and lsum: "sum_list (map weight (scf_list (scf (f, length ?ss)) bef)) = 0"
      "sum_list (map weight (scf_list (\<lambda> i. (scf (f, length ?ss) (Suc (length bef) + i))) aft)) = 0"
      and n: "n = 0"
      by (auto simp: scff)
    have "sum_list (map weight bef) \<le> sum_list (map weight (scf_list (scf (f, length ?ss)) bef))"
      by (rule sum_list_scf_list, rule scf, auto)
    with lsum(1) have "sum_list (map weight bef) = 0" by arith
    then have bef: "bef = []" using weight_gt_0[of "hd bef"] by (cases bef, auto)
    have "sum_list (map weight aft) \<le> sum_list (map weight (scf_list (\<lambda> i. (scf (f, length ?ss) (Suc (length bef) + i))) aft))"
      by (rule sum_list_scf_list, rule scf, auto)
    with lsum(2) have "sum_list (map weight aft) = 0" by arith
    then have aft: "aft = []" using weight_gt_0[of "hd aft"] by (cases aft, auto)
    note scff = scff[unfolded bef aft n, simplified]
    from bef aft
    have ba: "bef @ s # aft = [s]" by simp
    with wf have wf: "w (f, 1) = 0" by auto
    from wf have wst: "weight s = weight ?t" using scff unfolding True[unfolded ba]
      by (simp add: scf_list_def)
    let ?g = "(g, length ts)"
    let ?f = "(f, 1)"
    show ?thesis
    proof (cases "pr_strict ?f ?g")
      case True
      with w v show ?thesis unfolding ba by simp
    next
      case False
      note admf = adm[OF wf]
      from admf have pg: "pr_weak ?f ?g" .
      from pg False[unfolded pr_strict] have "pr_weak ?g ?f" by auto
      from pr_weak_trans[OF this admf] have g: "\<And> h k. pr_weak ?g (h, k)" .
      show ?thesis
      proof (cases ts)
        case Nil
        have "fst (lex_ext_unbounded kbo [s] ts)"
          unfolding Nil lex_ext_unbounded_iff by auto
        with pg w v show ?thesis unfolding ba by simp
      next
        case (Cons t tts)
        {
          fix x
          assume s: "s = Var x"
          from NS_Var_imp_eq_least[OF NS[unfolded s Cons]] have False by auto
        }
        then obtain h ss where s: "s = Fun h ss" by (cases s, auto)
        from NS wst g[of h "length ss"] pr_strict[of "(h, length ss)" "(g, length ts)"] have lex: "snd (lex_ext_unbounded kbo ss ts)"
          unfolding s by (auto split: if_splits)
        from lex obtain s0 sss where ss: "ss = s0 # sss" unfolding Cons lex_ext_unbounded_iff snd_conv by (cases ss, auto)
        from lex[unfolded ss Cons] have "S s0 t \<or> NS s0 t"
          by (cases "kbo s0 t", simp add: lex_ext_unbounded.simps del: kbo.simps split: if_splits)
        with S_imp_NS[of s0 t] have "NS s0 t" by blast
        from IH[OF _ this, of h Nil sss] have S: "S s t" unfolding Cons s ss by simp
        have "fst (lex_ext_unbounded kbo [s] ts)" unfolding Cons
          unfolding lex_ext_unbounded_iff fst_conv
          by (rule disjI1[OF exI[of _ 0]], insert S, auto simp del: kbo.simps)
        then have lex: "fst (lex_ext_unbounded kbo [s] ts) = True" by simp
        note all = lex wst[symmetric] S pg scff v'
        note all = all[unfolded ba, unfolded s ss Cons]
        have w: "weight (Fun f [t]) = weight (t :: ('f, 'v) term)" for t
          using wf scff by (simp add: scf_list_def)
        show ?thesis unfolding ba unfolding s ss Cons
          unfolding kbo.simps[of "Fun f [Fun h (s0 # sss)]"]
          unfolding all w using all by simp
      qed
    qed
  qed
qed

lemma S_supt:
  assumes supt: "s \<rhd> t"
  shows "S s t"
proof -
  from supt obtain C where s: "s = C\<langle>t\<rangle>" and C: "C \<noteq> \<box>" by auto
  show ?thesis unfolding s using C
  proof (induct C arbitrary: t)
    case (More f bef C aft t)
    show ?case
    proof (cases "C = \<box>")
      case True
      from kbo_supt_one[OF NS_refl, of f bef t aft] show ?thesis unfolding True by simp
    next
      case False
      from kbo_supt_one[OF S_imp_NS[OF More(1)[OF False]], of f bef t aft]
      show ?thesis by simp
    qed
  qed simp
qed

lemma NS_supteq:
  assumes "s \<unrhd> t"
  shows "NS s t"
  using S_imp_NS[OF S_supt[of s t]] NS_refl[of s] using assms[unfolded subterm.le_less]
  by blast

subsection \<open>Least Elements\<close>

lemma NS_all_least:
  assumes l: "least f"
  shows "NS t (Fun f [])"
proof (induct t)
  case (Var x)
  show ?case using l[unfolded least] l
    by auto
next
  case (Fun g ts)
  show ?case
  proof (cases ts)
    case (Cons s ss)
    with Fun[of s] have "NS s (Fun f [])" by auto
    from S_imp_NS[OF kbo_supt_one[OF this, of g Nil ss]] show ?thesis unfolding Cons by simp
  next
    case Nil
    from weight_w0[of "Fun g []"] have w: "weight (Fun g []) \<ge> weight (Fun f [])"
      using l[unfolded least] by auto
    from lex_ext_least_1
    have "snd (lex_ext kbo 0 [] [])" .
    then have lex: "snd (lex_ext_unbounded kbo [] [])" unfolding lex_ext_def Let_def by simp
    then show ?thesis using w l[unfolded least] unfolding Fun Nil by (auto simp: empty_le)
  qed
qed

lemma not_S_least:
  assumes l: "least f"
  shows "\<not> S (Fun f []) t"
proof (cases t)
  case (Fun g ts)
  show ?thesis unfolding Fun
  proof
    assume S: "S (Fun f []) (Fun g ts)"
    from S[unfolded Fun, simplified]
    have w: "w (g, length ts) + sum_list (map weight (scf_list (scf (g, length ts)) ts)) \<le> weight (Fun f [])"
      by (auto split: if_splits)
    show False
    proof (cases ts)
      case Nil
      with w have "w (g, 0) \<le> weight (Fun f [])" by simp
      also have "weight (Fun f []) \<le> w0" using l[unfolded least] by simp
      finally have g: "w (g, 0) = w0" using  w0(1)[of g] by auto
      with w Nil l[unfolded least] have gf: "w (g, 0) = w (f, 0)" by simp
      with S have p: "pr_weak (f, 0) (g, 0)" unfolding Nil
        by (simp split: if_splits add: pr_strict)
      with l[unfolded least, THEN conjunct2, rule_format, OF g] have p2: "pr_weak (g, 0) (f, 0)" by auto
      from p p2 gf S have "fst (lex_ext_unbounded kbo [] ts)" unfolding Nil
        by (auto simp: pr_strict)
      then show False unfolding lex_ext_unbounded_iff by auto
    next
      case (Cons s ss)
      then have ts: "ts = [] @ s # ss" by auto
      from scf[of 0 "length ts" g] obtain n where scff: "scf (g, length ts) 0 = Suc n" unfolding Cons by (auto elim: lessE)
      let ?e = "sum_list (map weight (
          scf_list (\<lambda>i. scf (g, Suc (length ss)) (Suc i)) ss
          ))"
      have "w0 + sum_list (map weight (replicate n s)) \<le> weight s + sum_list (map weight (replicate n s))"
        using weight_w0[of s] by auto
      also have "\<dots> = sum_list (map weight (replicate (scf (g, length ts) 0) s))" unfolding scff by simp
      also have "w (g, length ts) + \<dots> + ?e \<le> w0" using w l[unfolded least] unfolding ts scf_list_bef_i_aft by auto
      finally have "w0 + sum_list (map weight (replicate n s)) + w (g, length ts) + ?e \<le> w0" by arith
      then have wg: "w (g, length ts) = 0" and null: "?e = 0" "sum_list (map weight (replicate n s)) = 0" by auto
      from null(2) weight_gt_0[of s] have n: "n = 0" by (cases n, auto)
      have "sum_list (map weight ss) \<le> ?e"
        by (rule sum_list_scf_list, rule scf, auto)
      from this[unfolded null] weight_gt_0[of "hd ss"] have ss: "ss = []" by (cases ss, auto)
      with Cons have ts: "ts = [s]" by simp
      note scff = scff[unfolded ts n, simplified]
      from wg ts have wg: "w (g, 1) = 0" by auto
      from adm[OF wg, rule_format, of f] have "pr_weak (g, 1) (f, 0)" by auto
      with S[unfolded Fun ts] l[unfolded least] weight_w0[of s] scff
      have "fst (lex_ext_unbounded kbo [] [s])"
        by (auto split: if_splits simp: scf_list_def pr_strict)
      then show ?thesis unfolding lex_ext_unbounded_iff by auto
    qed
  qed
qed simp

lemma NS_least_least:
  assumes l: "least f"
    and NS: "NS (Fun f []) t"
  shows "\<exists> g. t = Fun g [] \<and> least g"
proof (cases t)
  case (Var x)
  show ?thesis using NS unfolding Var by simp
next
  case (Fun g ts)
  from NS[unfolded Fun, simplified]
  have w: "w (g, length ts) + sum_list (map weight (scf_list (scf (g, length ts)) ts)) \<le> weight (Fun f [])"
    by (auto split: if_splits)
  show ?thesis
  proof (cases ts)
    case Nil
    with w have "w (g, 0) \<le> weight (Fun f [])" by simp
    also have "weight (Fun f []) \<le> w0" using l[unfolded least] by simp
    finally have g: "w (g, 0) = w0" using  w0(1)[of g] by auto
    with w Nil l[unfolded least] have gf: "w (g, 0) = w (f, 0)" by simp
    with NS[unfolded Fun] have p: "pr_weak (f, 0) (g, 0)" unfolding Nil
      by (simp split: if_splits add: pr_strict)
    have least: "least g" unfolding least
    proof (rule conjI[OF g], intro allI)
      fix h
      from l[unfolded least] have "w (h, 0) = w0 \<longrightarrow> pr_weak (h, 0) (f, 0)" by blast
      with pr_weak_trans p show "w (h, 0) = w0 \<longrightarrow> pr_weak (h, 0) (g, 0)" by blast
    qed
    show ?thesis
      by (rule exI[of _ g], unfold Fun Nil, insert least, auto)
  next
    case (Cons s ss)
    then have ts: "ts = [] @ s # ss" by auto
    from scf[of 0 "length ts" g] obtain n where scff: "scf (g, length ts) 0 = Suc n" unfolding Cons by (auto elim: lessE)
    let ?e = "sum_list (map weight (
        scf_list (\<lambda>i. scf (g, Suc (length ss)) (Suc i)) ss
      ))"
    have "w0 + sum_list (map weight (replicate n s)) \<le> weight s + sum_list (map weight (replicate n s))"
      using weight_w0[of s] by auto
    also have "\<dots> = sum_list (map weight (replicate (scf (g, length ts) 0) s))" unfolding scff by simp
    also have "w (g, length ts) + \<dots> + ?e \<le> w0" using w l[unfolded least] unfolding ts scf_list_bef_i_aft by auto
    finally have "w0 + sum_list (map weight (replicate n s)) + w (g, length ts) + ?e \<le> w0" by arith
    then have wg: "w (g, length ts) = 0" and null: "?e = 0" "sum_list (map weight (replicate n s)) = 0" by auto
    from null(2) weight_gt_0[of s] have n: "n = 0" by (cases n, auto)
    have "sum_list (map weight ss) \<le> ?e"
      by (rule sum_list_scf_list, rule scf, auto)
    from this[unfolded null] weight_gt_0[of "hd ss"] have ss: "ss = []" by (cases ss, auto)
    with Cons have ts: "ts = [s]" by simp
    note scff = scff[unfolded ts n, simplified]
    from wg ts have wg: "w (g, 1) = 0" by auto
    from adm[OF wg, rule_format, of f] have "pr_weak (g, 1) (f, 0)" by auto
    with NS[unfolded Fun ts] l[unfolded least] weight_w0[of s] scff
    have "snd (lex_ext_unbounded kbo [] [s])"
      by (auto split: if_splits simp: scf_list_def pr_strict)
    then show ?thesis unfolding lex_ext_unbounded_iff snd_conv by auto
  qed
qed


subsection \<open>Stability (a.k.a. Closure under Substitutions\<close>

lemma weight_subst: "weight (t \<cdot> \<sigma>) =
  weight t + sum_mset (image_mset (\<lambda> x. weight (\<sigma> x) - w0) (vars_term_ms (SCF t)))"
proof (induct t)
  case (Var x)
  show ?case using weight_w0[of "\<sigma> x"] by auto
next
  case (Fun f ts)
  let ?ts = "scf_list (scf (f, length ts)) ts"
  define sts where "sts = ?ts"
  have id: "map (\<lambda> t. weight (t \<cdot> \<sigma>)) ?ts = map (\<lambda> t. weight t + sum_mset (image_mset (\<lambda> x. weight (\<sigma> x) - w0) (vars_term_ms (scf_term scf t)))) ?ts"
    by (rule map_cong[OF refl Fun], insert scf_list_subset[of _ ts], auto)
  show ?case
    by (simp add: o_def id, unfold sts_def[symmetric], induct sts, auto)
qed

lemma weight_stable_le:
  assumes ws: "weight s \<le> weight t"
    and vs: "vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF t)"
  shows "weight (s \<cdot> \<sigma>) \<le> weight (t \<cdot> \<sigma>)"
proof -
  from vs[unfolded mset_subset_eq_exists_conv] obtain u where vt: "vars_term_ms (SCF t) = vars_term_ms (SCF s) + u" ..
  show ?thesis unfolding weight_subst vt using ws by auto
qed

lemma weight_stable_lt:
  assumes ws: "weight s < weight t"
    and vs: "vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF t)"
 shows "weight (s \<cdot> \<sigma>) < weight (t \<cdot> \<sigma>)"
proof -
  from vs[unfolded mset_subset_eq_exists_conv] obtain u where vt: "vars_term_ms (SCF t) = vars_term_ms (SCF s) + u" ..
  show ?thesis unfolding weight_subst vt using ws by auto
qed

text \<open>KBO is stable, i.e., closed under substitutions.\<close>
lemma kbo_stable:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "NS s t"
  shows "(S s t \<longrightarrow> S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) \<and> NS (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" (is "?P s t")
  using assms
proof (induct s arbitrary: t)
  case (Var y t)
  then have not: "\<not> S (Var y) t" using not_S_Var[of y t] by auto
  from NS_Var_imp_eq_least[OF Var]
  have "t = Var y \<or> (\<exists> f. t = Fun f [] \<and> least f)" by simp
  then obtain f where "t = Var y \<or> t = Fun f [] \<and> least f" by auto
  then have "NS (Var y \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  proof
    assume "t = Var y"
    then show ?thesis using NS_refl[of "t \<cdot> \<sigma>"] by auto
  next
    assume "t = Fun f [] \<and> least f"
    with NS_all_least[of f "Var y \<cdot> \<sigma>"] show ?thesis by auto
  qed
  with not show ?case by blast
next
  case (Fun f ss t)
  note NS = Fun(2)
  note IH = Fun(1)
  let ?s = "Fun f ss"
  define s where "s = ?s"
  let ?ss = "map (\<lambda> s. s \<cdot> \<sigma>) ss"
  from NS have v: "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF ?s)" and w: "weight t \<le> weight ?s"
    by (auto split: if_splits)
  from weight_stable_le[OF w v] have w\<sigma>: "weight (t \<cdot> \<sigma>) \<le> weight (?s \<cdot> \<sigma>)" by auto
  from vars_term_ms_subst_mono[OF v, of "\<lambda> x. SCF (\<sigma> x)"] have v\<sigma>: "vars_term_ms (SCF (t \<cdot> \<sigma>)) \<subseteq># vars_term_ms (SCF (?s \<cdot> \<sigma>))"
    unfolding scf_term_subst .
  show ?case
  proof (cases "weight (t \<cdot> \<sigma>) < weight (?s \<cdot> \<sigma>)")
    case True
    with v\<sigma> show ?thesis by auto
  next
    case False
    with weight_stable_lt[OF _ v, of \<sigma>] w have w: "weight t = weight ?s" by arith
    show ?thesis
    proof (cases t)
      case (Var y)
      from set_mset_mono[OF v, folded s_def]
      have "y \<in> vars_term (SCF s)" unfolding Var by (auto simp: o_def)
      also have "\<dots> \<subseteq> vars_term s" by (rule vars_term_scf_subset)
      finally have "y \<in> vars_term s" by auto
      from supteq_Var[OF this] have "?s \<rhd> Var y" unfolding s_def Fun by auto
      from S_supt[OF supt_subst[OF this]] have S: "S (?s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" unfolding Var .
      from S_imp_NS[OF S] S show ?thesis by auto
    next
      case (Fun g ts) note t = this
      let ?f = "(f, length ss)"
      let ?g = "(g, length ts)"
      let ?ts = "map (\<lambda> s. s \<cdot> \<sigma>) ts"
      show ?thesis
      proof (cases "pr_strict ?f ?g")
        case True
        then have S: "S (?s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" using w\<sigma> v\<sigma> unfolding t by simp
        from S S_imp_NS[OF S] show ?thesis by simp
      next
        case False note prec = this
        show ?thesis
        proof (cases "pr_weak ?f ?g")
          case False
          with v w prec have "\<not> NS ?s t" unfolding t by (auto simp del: vars_term_ms.simps)
          with NS show ?thesis by blast
        next
          case True
          from v w have "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF ?s) \<and> weight t \<le> weight ?s" "\<not> weight t < weight ?s" by auto
          {
            fix i
            assume i: "i < length ss" "i < length ts"
              and S: "S (ss ! i) (ts ! i)"
            have "S (map (\<lambda>s. s \<cdot> \<sigma>) ss ! i) (map (\<lambda>s. s \<cdot> \<sigma>) ts ! i)"
              using IH[OF _ S_imp_NS[OF S]] S i unfolding set_conv_nth by (force simp del: kbo.simps)
          } note IH_S = this
          {
            fix i
            assume i: "i < length ss" "i < length ts"
              and NS: "NS (ss ! i) (ts ! i)"
            have "NS (map (\<lambda>s. s \<cdot> \<sigma>) ss ! i) (map (\<lambda>s. s \<cdot> \<sigma>) ts ! i)"
              using IH[OF _ NS] i unfolding set_conv_nth by (force simp del: kbo.simps)
          } note IH_NS = this
          {
            assume "S ?s t"
            with prec v w True have lex: "fst (lex_ext_unbounded kbo ss ts)"
              unfolding s_def t by simp
            have "fst (lex_ext_unbounded kbo ?ss ?ts)"
              by (rule lex_ext_unbounded_map_S[OF _ _ lex], insert IH_NS IH_S, blast+)
            with v\<sigma> w\<sigma> prec True have "S (?s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
              unfolding t by auto
          }
          moreover
          {
            from NS prec v w True have lex: "snd (lex_ext_unbounded kbo ss ts)"
              unfolding t by simp
            have "snd (lex_ext_unbounded kbo ?ss ?ts)"
              by (rule lex_ext_unbounded_map_NS[OF _ _ lex], insert IH_S IH_NS, blast)
            with v\<sigma> w\<sigma> prec True have "NS (?s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
              unfolding t by auto
          }
          ultimately show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma S_subst:
  "S s t \<Longrightarrow> S (s \<cdot> (\<sigma> :: ('f, 'v) subst)) (t \<cdot> \<sigma>)"
  using kbo_stable[OF S_imp_NS, of s t \<sigma>] by auto

lemma NS_subst: "NS s t \<Longrightarrow> NS (s \<cdot> (\<sigma> :: ('f, 'v) subst)) (t \<cdot> \<sigma>)" using kbo_stable[of s t \<sigma>] by auto


subsection \<open>Transitivity and Compatibility\<close>

lemma kbo_trans: "(S s t \<longrightarrow> NS t u \<longrightarrow> S s u) \<and>
  (NS s t \<longrightarrow> S t u \<longrightarrow> S s u) \<and>
  (NS s t \<longrightarrow> NS t u \<longrightarrow> NS s u)"
  (is "?P s t u")
proof (induct s arbitrary: t u)
  case (Var x t u)
  from not_S_Var[of x t] have nS: "\<not> S (Var x) t" .
  show ?case
  proof (cases "NS (Var x) t")
    case False
    with nS show ?thesis by blast
  next
    case True
    from NS_Var_imp_eq_least[OF this] obtain f where
      "t = Var x \<or> t = Fun f [] \<and> least f" by blast
    then show ?thesis
    proof
      assume "t = Var x"
      then show ?thesis using nS by blast
    next
      assume "t = Fun f [] \<and> least f"
      then have t: "t = Fun f []" and least: "least f" by auto
      from not_S_least[OF least] have nS': "\<not> S t u" unfolding t .
      show ?thesis
      proof (cases "NS t u")
        case True
        with NS_least_least[OF least, of u] t obtain h where
          u: "u = Fun h []" and least: "least h" by auto
        from NS_all_least[OF least] have NS: "NS (Var x) u" unfolding u .
        with nS nS' show ?thesis by blast
      next
        case False
        with S_imp_NS[of t u] show ?thesis by blast
      qed
    qed
  qed
next
  case (Fun f ss t u) note IH = this
  let ?s = "Fun f ss"
  show ?case
  proof (cases "NS ?s t")
    case False
    with S_imp_NS[of ?s t] show ?thesis by blast
  next
    case True note st = this
    then have vst: "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF ?s)" and wst: "weight t \<le> weight ?s"
      by (auto split: if_splits)
    show ?thesis
    proof (cases "NS t u")
      case False
      with S_imp_NS[of t u] show ?thesis by blast
    next
      case True note tu = this
      then have vtu: "vars_term_ms (SCF u) \<subseteq># vars_term_ms (SCF t)" and wtu: "weight u \<le> weight t"
        by (auto split: if_splits)
      from vst vtu have v: "vars_term_ms (SCF u) \<subseteq># vars_term_ms (SCF ?s)" by simp
      from wst wtu have w: "weight u \<le> weight ?s" by simp
      show ?thesis
      proof (cases "weight u < weight ?s")
        case True
        with v show ?thesis by auto
      next
        case False
        with wst wtu have wst: "weight t = weight ?s" and wtu: "weight u = weight t" and w: "weight u = weight ?s" by arith+
        show ?thesis
        proof (cases u)
          case (Var z)
          with v w show ?thesis by auto
        next
          case (Fun h us) note u = this
          show ?thesis
          proof (cases t)
            case (Fun g ts) note t = this
            let ?f = "(f, length ss)"
            let ?g = "(g, length ts)"
            let ?h = "(h, length us)"
            from st t wst have fg: "pr_weak ?f ?g" by (simp split: if_splits add: pr_strict)
            from tu t u wtu have gh: "pr_weak ?g ?h" by (simp split: if_splits add: pr_strict)
            from pr_weak_trans[OF fg gh] have fh: "pr_weak ?f ?h" .
            show ?thesis
            proof (cases "pr_strict ?f ?h")
              case True
              with w v u show ?thesis by auto
            next
              case False
              let ?lex = "lex_ext_unbounded kbo"
              from False fh have hf: "pr_weak ?h ?f" unfolding pr_strict by auto
              from pr_weak_trans[OF hf fg] have hg: "pr_weak ?h ?g" .
              from hg have gh2: "\<not> pr_strict ?g ?h" unfolding pr_strict by auto
              from pr_weak_trans[OF gh hf] have gf: "pr_weak ?g ?f" .
              from gf have fg2: "\<not> pr_strict ?f ?g" unfolding pr_strict by auto
              from st t wst fg2 have st: "snd (?lex ss ts)"
                by (auto split: if_splits)
              from tu t u wtu gh2 have tu: "snd (?lex ts us)"
                by (auto split: if_splits)
              {
                fix s t u
                assume "s \<in> set ss"
                from IH[OF this, of t u]
                have "(NS s t \<and> S t u \<longrightarrow> S s u) \<and>
                  (S s t \<and> NS t u \<longrightarrow> S s u) \<and>
                  (NS s t \<and> NS t u \<longrightarrow> NS s u) \<and>
                  (S s t \<and> S t u \<longrightarrow> S s u)"
                  using S_imp_NS[of s t] by blast
              } note IH = this
              let ?b = "length ss + length ts + length us"
              note lex = lex_ext_compat[of ss ts us kbo ?b, OF IH]
              let ?lexb = "lex_ext kbo ?b"
              note conv = lex_ext_def Let_def
              from st have st: "snd (?lexb ss ts)" unfolding conv by simp
              from tu have tu: "snd (?lexb ts us)" unfolding conv by simp
              from lex st tu have su: "snd (?lexb ss us)" by blast
              then have su: "snd (?lex ss us)" unfolding conv by simp
              from w v u su fh have NS: "NS ?s u" by simp
              {
                assume st: "S ?s t"
                with t wst fg fg2 have st: "fst (?lex ss ts)"
                  by (auto split: if_splits)
                then have st: "fst (?lexb ss ts)" unfolding conv by simp
                from lex st tu have su: "fst (?lexb ss us)" by blast
                then have su: "fst (?lex ss us)" unfolding conv by simp
                from w v u su fh have S: "S ?s u" by simp
              } note S_left = this
              {
                assume tu: "S t u"
                with t u wtu gh2 have tu: "fst (?lex ts us)"
                  by (auto split: if_splits)
                then have tu: "fst (?lexb ts us)" unfolding conv by simp
                from lex st tu have su: "fst (?lexb ss us)" by blast
                then have su: "fst (?lex ss us)" unfolding conv by simp
                from w v u su fh have S: "S ?s u" by simp
              } note S_right = this
              from NS S_left S_right show ?thesis by blast
            qed
          next
            case (Var x) note t = this
            from tu weight_w0[of u] have least: "least h" and u: "u = Fun h []" unfolding t u
              by (auto split: if_splits)
            from NS_all_least[OF least] have NS: "NS ?s u" unfolding u .
            from not_S_Var have nS': "\<not> S t u" unfolding t .
            show ?thesis
            proof (cases "S ?s t")
              case False
              with nS' NS show ?thesis by blast
            next
              case True
              then have "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF ?s)"
                by (auto split: if_splits)
              from set_mset_mono[OF this, unfolded set_mset_vars_term_ms t]
              have "x \<in> vars_term (SCF ?s)" by simp
              also have "\<dots> \<subseteq> vars_term ?s" by (rule vars_term_scf_subset)
              finally obtain s sss where ss: "ss = s # sss" by (cases ss, auto)
              from kbo_supt_one[OF NS_all_least[OF least, of s], of f Nil sss]
              have "S ?s u" unfolding ss u by simp
              with NS show ?thesis by blast
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma S_trans: "S s t \<Longrightarrow> S t u \<Longrightarrow> S s u" using S_imp_NS[of s t] kbo_trans[of s t u] by blast
lemma NS_trans: "NS s t \<Longrightarrow> NS t u \<Longrightarrow> NS s u" using kbo_trans[of s t u] by blast
lemma NS_S_compat: "NS s t \<Longrightarrow> S t u \<Longrightarrow> S s u" using kbo_trans[of s t u] by blast
lemma S_NS_compat: "S s t \<Longrightarrow> NS t u \<Longrightarrow> S s u" using kbo_trans[of s t u] by blast


subsection \<open>Strong Normalization (a.k.a. Well-Foundedness)\<close>

lemma kbo_strongly_normalizing:
  fixes s :: "('f, 'v) term"
  shows "SN_on {(s, t). S s t} {s}"
proof -
  let ?SN = "\<lambda> t :: ('f, 'v) term. SN_on {(s, t). S s t} {t}"
  let ?m1 = "\<lambda> (f, ss). weight (Fun f ss)"
  let ?m2 = "\<lambda> (f, ss). (f, length ss)"
  let ?rel' = "lex_two {(fss, gts). ?m1 fss > ?m1 gts} {(fss, gts). ?m1 fss \<ge> ?m1 gts} {(fss, gts). pr_strict (?m2 fss) (?m2 gts)}"
  let ?rel = "inv_image ?rel' (\<lambda> x. (x, x))"
  have SN_rel: "SN ?rel"
    by (rule SN_inv_image, rule lex_two, insert SN_inv_image[OF pr_SN, of ?m2]  SN_inv_image[OF SN_nat_gt, of ?m1],
        auto simp: inv_image_def)
  note conv = SN_on_all_reducts_SN_on_conv
  show "?SN s"
  proof (induct s)
    case (Var x)
    show ?case unfolding conv[of _ "Var x"] using not_S_Var[of x] by auto
  next
    case (Fun f ss)
    then have subset: "set ss \<subseteq> {s. ?SN s}" by blast
    let ?P = "\<lambda> (f, ss). set ss \<subseteq> {s. ?SN s} \<longrightarrow> ?SN (Fun f ss)"
    {
      fix fss
      have "?P fss"
      proof (induct fss rule: SN_induct[OF SN_rel])
        case (1 fss)
        obtain f ss where fss: "fss = (f, ss)" by force
        {
          fix g ts
          assume "?m1 (f, ss) > ?m1 (g, ts) \<or> ?m1 (f, ss) \<ge> ?m1 (g, ts) \<and> pr_strict (?m2 (f, ss)) (?m2 (g, ts))"
            and "set ts \<subseteq> {s. ?SN s}"
          then have "?SN (Fun g ts)"
            using 1[rule_format, of "(g, ts)", unfolded fss split] by auto
        } note IH = this[unfolded split]
        show ?case unfolding fss split
        proof
          assume SN_s: "set ss \<subseteq> {s. ?SN s}"
          let ?f = "(f, length ss)"
          let ?s = "Fun f ss"
          let ?SNt = "\<lambda> g ts. ?SN (Fun g ts)"
          let ?sym = "\<lambda> g ts. (g, length ts)"
          let ?lex = "lex_ext kbo (weight ?s)"
          let ?lexu = "lex_ext_unbounded kbo"
          let ?lex_SN = "{(ys, xs). (\<forall> y \<in> set ys. ?SN y) \<and> fst (?lex ys xs)}"
          from lex_ext_SN[of kbo "weight ?s", OF NS_S_compat]
          have SN: "SN ?lex_SN" .
          {
            fix g and ts :: "('f, 'v) term list"
            assume "pr_weak ?f (?sym g ts) \<and> weight (Fun g ts) \<le> weight ?s \<and> set ts \<subseteq> {s. ?SN s}"
            then have "?SNt g ts"
            proof (induct ts arbitrary: g rule: SN_induct[OF SN])
              case (1 ts g)
              note inner_IH = 1(1)
              let ?g = "(g, length ts)"
              let ?t = "Fun g ts"
              from 1(2) have fg: "pr_weak ?f ?g" and w: "weight ?t \<le> weight ?s"  and SN: "set ts \<subseteq> {s. ?SN s}" by auto
              show "?SNt g ts" unfolding conv[of _ ?t]
              proof (intro allI impI)
                fix u
                assume "(?t, u) \<in> {(s, t). S s t}"
                then have tu: "S ?t u" by auto
                then show "?SN u"
                proof (induct u)
                  case (Var x)
                  then show ?case using not_S_Var[of x] unfolding conv[of _ "Var x"] by auto
                next
                  case (Fun h us)
                  let ?h = "(h, length us)"
                  let ?u = "Fun h us"
                  note tu = Fun(2)
                  {
                    fix u
                    assume u: "u \<in> set us"
                    then have "?u \<rhd> u" by auto
                    from S_trans[OF tu S_supt[OF this]] have "S ?t u" by auto
                    from Fun(1)[OF u this] have "?SN u" .
                  } then have SNu: "set us \<subseteq> {s . ?SN s}" by blast
                  note IH = IH[OF _ this]
                  from tu have wut: "weight ?u \<le> weight ?t" by (simp split: if_splits)
                  show ?case
                  proof (cases "?m1 (f, ss) > ?m1 (h, us) \<or> ?m1 (f, ss) \<ge> ?m1 (h, us) \<and> pr_strict (?m2 (f, ss)) (?m2 (h, us))")
                    case True
                    from IH[OF True[unfolded split]] show ?thesis by simp
                  next
                    case False
                    with wut w have wut: "weight ?t = weight ?u" "weight ?s = weight ?u" by auto
                    note False = False[unfolded split wut]
                    note tu = tu[unfolded kbo.simps[of ?t] wut, unfolded Fun term.simps, simplified]
                    from tu have gh: "pr_weak ?g ?h" unfolding pr_strict by (auto split: if_splits)
                    from pr_weak_trans[OF fg gh] have fh: "pr_weak ?f ?h" .
                    from False wut fh have "\<not> pr_strict ?f ?h" unfolding pr_strict by auto
                    with fh have hf: "pr_weak ?h ?f" unfolding pr_strict by auto
                    from pr_weak_trans[OF hf fg] have hg: "pr_weak ?h ?g" .
                    from hg have gh2: "\<not> pr_strict ?g ?h" unfolding pr_strict by auto
                    from tu gh2 have lex: "fst (?lexu ts us)" by (auto split: if_splits)
                    from fh wut SNu have "pr_weak ?f ?h \<and> weight ?u \<le> weight ?s \<and> set us \<subseteq> {s. ?SN s}"
                      by auto
                    note inner_IH = inner_IH[OF _ this]
                    show ?thesis
                    proof (rule inner_IH, rule, unfold split, intro conjI ballI)
                      have "fst (?lexu ts us)" by (rule lex)
                      moreover have "length us \<le> weight ?s"
                      proof -
                        have "length us \<le> sum_list (map weight us)"
                        proof (induct us)
                          case (Cons u us)
                          from Cons have "length (u # us) \<le> Suc (sum_list (map weight us))" by auto
                          also have "... \<le> sum_list (map weight (u # us))" using weight_gt_0[of u]
                            by auto
                          finally show ?case .
                        qed simp
                        also have "\<dots> \<le> sum_list (map weight (scf_list (scf (h, length us)) us))"
                          by (rule sum_list_scf_list[OF scf])
                        also have "... \<le> weight ?s" using wut by simp
                        finally show ?thesis .
                      qed
                      ultimately show "fst (?lex ts us)" unfolding lex_ext_def Let_def by auto
                    qed (insert SN, blast)
                  qed
                qed
              qed
            qed
          }
          from this[of f ss] SN_s  show "?SN ?s" by auto
        qed
      qed
    }
    from this[of "(f, ss)", unfolded split]
    show ?case using Fun by blast
  qed
qed

lemma S_SN: "SN {(x, y). S x y}"
  using kbo_strongly_normalizing unfolding SN_defs by blast


subsection \<open>Ground Totality\<close>

lemma ground_SCF [simp]:
  "ground (SCF t) = ground t"
proof -
  have *: "\<forall>i<length xs. scf (f, length xs) i > 0"
    for f :: 'f and xs :: "('f, 'v) term list" using scf by simp
  show ?thesis by (induct t) (auto simp: set_scf_list [OF *])
qed

declare kbo.simps[simp del]

lemma ground_vars_term_ms: "ground t \<Longrightarrow> vars_term_ms t = {#}"
  by (induct t) auto

context
  fixes F :: "('f \<times> nat) set"
  assumes pr_weak: "pr_weak = pr_strict\<^sup>=\<^sup>="
    and pr_gtotal: "\<And>f g. f \<in> F \<Longrightarrow> g \<in> F \<Longrightarrow> f = g \<or> pr_strict f g \<or> pr_strict g f"
begin

lemma S_ground_total:
  assumes "funas_term s \<subseteq> F" and "ground s" and "funas_term t \<subseteq> F" and "ground t"
  shows "s = t \<or> S s t \<or> S t s"
  using assms
proof (induct s arbitrary: t)
  case IH: (Fun f ss)
  note [simp] = ground_vars_term_ms
  let ?s = "Fun f ss"
  have *: "(vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF ?s)) = True"
    "(vars_term_ms (SCF ?s) \<subseteq># vars_term_ms (SCF t)) = True"
    using \<open>ground ?s\<close> and \<open>ground t\<close> by (auto simp: scf)
  from IH(5) obtain g ts where t[simp]: "t = Fun g ts" by (cases t, auto)
  let ?t = "Fun g ts"
  let ?f = "(f, length ss)"
  let ?g = "(g, length ts)"
  from IH have f: "?f \<in> F" and g: "?g \<in> F" by auto
  {
    assume "\<not> ?case"
    note contra = this[unfolded kbo.simps[of ?s] kbo.simps[of t] *, unfolded t term.simps]
    from pr_gtotal[OF f g] contra have fg: "?f = ?g" by (auto split: if_splits)
    have IH: "\<forall>(s, t)\<in>set (zip ss ts). s = t \<or> S s t \<or> S t s"
      using IH by (auto elim!: in_set_zipE) blast
    from fg have len: "length ss = length ts" by auto
    from lex_ext_unbounded_total[OF IH NS_refl len] contra fg
    have False by (auto split: if_splits)
  }
  then show ?case by blast
qed auto
end


subsection \<open>Summary\<close>

text \<open>
  At this point we have shown well-foundedness @{thm [source] S_SN},
  transitivity and compatibility @{thm [source] S_trans NS_trans NS_S_compat S_NS_compat},
  closure under substitutions @{thm [source] S_subst NS_subst},
  closure under contexts @{thm [source] S_ctxt NS_ctxt},
  the subterm property @{thm [source] S_supt NS_supteq},
  reflexivity of the weak @{thm [source] NS_refl} and irreflexivity of the strict
  part @{thm [source] S_irrefl},
  and ground-totality @{thm [source] S_ground_total}.

  In particular, this allows us to show that KBO is an instance of
  strongly normalizing order pairs (@{locale SN_order_pair}).
\<close>

sublocale SN_order_pair "{(x, y). S x y}" "{(x, y). NS x y}"
  by (unfold_locales, insert NS_refl NS_trans S_trans S_SN NS_S_compat S_NS_compat)
    (auto simp: refl_on_def trans_def, blast+)
end

end
