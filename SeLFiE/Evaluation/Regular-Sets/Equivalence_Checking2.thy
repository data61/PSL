section \<open>Deciding Equivalence of Extended Regular Expressions\<close>

theory Equivalence_Checking2
imports Regular_Exp2 "HOL-Library.While_Combinator"
begin

subsection \<open>Term ordering\<close>

fun le_rexp :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> bool"
where
  "le_rexp Zero _ = True"
| "le_rexp _ Zero = False"
| "le_rexp One _ = True"
| "le_rexp _ One = False"
| "le_rexp (Atom a) (Atom b) = (a <= b)"
| "le_rexp (Atom _) _ = True"
| "le_rexp _ (Atom _) = False"
| "le_rexp (Star r) (Star s) = le_rexp r s"
| "le_rexp (Star _) _ = True"
| "le_rexp _ (Star _) = False"
| "le_rexp (Not r) (Not s) = le_rexp r s"
| "le_rexp (Not _) _ = True"
| "le_rexp _ (Not _) = False"
| "le_rexp (Plus r r') (Plus s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"
| "le_rexp (Plus _ _) _ = True"
| "le_rexp _ (Plus _ _) = False"
| "le_rexp (Times r r') (Times s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"
| "le_rexp (Times _ _) _ = True"
| "le_rexp _ (Times _ _) = False"
| "le_rexp (Inter r r') (Inter s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"

subsection \<open>Normalizing operations\<close>

text \<open>associativity, commutativity, idempotence, zero\<close>

fun nPlus :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nPlus Zero r = r"
| "nPlus r Zero = r"
| "nPlus (Plus r s) t = nPlus r (nPlus s t)"
| "nPlus r (Plus s t) =
     (if r = s then (Plus s t)
     else if le_rexp r s then Plus r (Plus s t)
     else Plus s (nPlus r t))"
| "nPlus r s =
     (if r = s then r
      else if le_rexp r s then Plus r s
      else Plus s r)"

lemma lang_nPlus[simp]: "lang S (nPlus r s) = lang S (Plus r s)"
by (induct r s rule: nPlus.induct) auto

text \<open>associativity, zero, one\<close>

fun nTimes :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nTimes Zero _ = Zero"
| "nTimes _ Zero = Zero"
| "nTimes One r = r"
| "nTimes r One = r"
| "nTimes (Times r s) t = Times r (nTimes s t)"
| "nTimes r s = Times r s"

lemma lang_nTimes[simp]: "lang S (nTimes r s) = lang S (Times r s)"
by (induct r s rule: nTimes.induct) (auto simp: conc_assoc)

text \<open>more optimisations:\<close>

fun nInter :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nInter Zero _ = Zero"
| "nInter _ Zero = Zero"
| "nInter r s = Inter r s"

lemma lang_nInter[simp]: "lang S (nInter r s) = lang S (Inter r s)"
by (induct r s rule: nInter.induct) (auto)

primrec norm :: "nat rexp \<Rightarrow> nat rexp"
where
  "norm Zero = Zero"
| "norm One = One"
| "norm (Atom a) = Atom a"
| "norm (Plus r s) = nPlus (norm r) (norm s)"
| "norm (Times r s) = nTimes (norm r) (norm s)"
| "norm (Star r) = Star (norm r)"
| "norm (Not r) = Not (norm r)"
| "norm (Inter r1 r2) = nInter (norm r1) (norm r2)"

lemma lang_norm[simp]: "lang S (norm r) = lang S r"
by (induct r) auto


subsection \<open>Derivative\<close>

primrec nderiv :: "nat \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nderiv _ Zero = Zero"
| "nderiv _ One = Zero"
| "nderiv a (Atom b) = (if a = b then One else Zero)"
| "nderiv a (Plus r s) = nPlus (nderiv a r) (nderiv a s)"
| "nderiv a (Times r s) =
    (let r's = nTimes (nderiv a r) s
     in if nullable r then nPlus r's (nderiv a s) else r's)"
| "nderiv a (Star r) = nTimes (nderiv a r) (Star r)"
| "nderiv a (Not r) = Not (nderiv a r)"
| "nderiv a (Inter r1 r2) = nInter (nderiv a r1) (nderiv a r2)"

lemma lang_nderiv: "a:S \<Longrightarrow> lang S (nderiv a r) = Deriv a (lang S r)"
by (induct r) (auto simp: Let_def nullable_iff[where S=S])

lemma atoms_nPlus[simp]: "atoms (nPlus r s) = atoms r \<union> atoms s"
by (induct r s rule: nPlus.induct) auto

lemma atoms_nTimes: "atoms (nTimes r s) \<subseteq> atoms r \<union> atoms s"
by (induct r s rule: nTimes.induct) auto

lemma atoms_nInter: "atoms (nInter r s) \<subseteq> atoms r \<union> atoms s"
by (induct r s rule: nInter.induct) auto

lemma atoms_norm: "atoms (norm r) \<subseteq> atoms r"
by (induct r) (auto dest!:subsetD[OF atoms_nTimes]subsetD[OF atoms_nInter])

lemma atoms_nderiv: "atoms (nderiv a r) \<subseteq> atoms r"
by (induct r) (auto simp: Let_def dest!:subsetD[OF atoms_nTimes]subsetD[OF atoms_nInter])


subsection \<open>Bisimulation between languages and regular expressions\<close>

context
fixes S :: "'a set"
begin

coinductive bisimilar :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> bool" where
"K \<subseteq> lists S \<Longrightarrow> L \<subseteq> lists S
 \<Longrightarrow> ([] \<in> K \<longleftrightarrow> [] \<in> L) 
 \<Longrightarrow> (\<And>x. x:S \<Longrightarrow> bisimilar (Deriv x K) (Deriv x L))
 \<Longrightarrow> bisimilar K L"

lemma equal_if_bisimilar:
assumes "K \<subseteq> lists S" "L \<subseteq> lists S" "bisimilar K L" shows "K = L"
proof (rule set_eqI)
  fix w
  from assms show "w \<in> K \<longleftrightarrow> w \<in> L"
  proof (induction w arbitrary: K L)
    case Nil thus ?case by (auto elim: bisimilar.cases)
  next
    case (Cons a w K L)
    show ?case
    proof cases
      assume "a : S"
      with \<open>bisimilar K L\<close> have "bisimilar (Deriv a K) (Deriv a L)"
        by (auto elim: bisimilar.cases)
      then have "w \<in> Deriv a K \<longleftrightarrow> w \<in> Deriv a L"
        by (metis Cons.IH bisimilar.cases)
      thus ?case by (auto simp: Deriv_def)
    next
      assume "a \<notin> S"
      thus ?case using Cons.prems by auto
    qed
  qed
qed

lemma language_coinduct:
fixes R (infixl "\<sim>" 50)
assumes "\<And>K L. K \<sim> L \<Longrightarrow> K \<subseteq> lists S \<and> L \<subseteq> lists S"
assumes "K \<sim> L"
assumes "\<And>K L. K \<sim> L \<Longrightarrow> ([] \<in> K \<longleftrightarrow> [] \<in> L)"
assumes "\<And>K L x. K \<sim> L \<Longrightarrow> x : S \<Longrightarrow> Deriv x K \<sim> Deriv x L"
shows "K = L"
apply (rule equal_if_bisimilar)
apply (metis assms(1) assms(2))
apply (metis assms(1) assms(2))
apply (rule bisimilar.coinduct[of R, OF \<open>K \<sim> L\<close>])
apply (auto simp: assms)
done

end

type_synonym rexp_pair = "nat rexp * nat rexp"
type_synonym rexp_pairs = "rexp_pair list"

definition is_bisimulation :: "nat list \<Rightarrow> rexp_pairs \<Rightarrow> bool"
where
"is_bisimulation as ps =
  (\<forall>(r,s)\<in> set ps. (atoms r \<union> atoms s \<subseteq> set as) \<and> (nullable r \<longleftrightarrow> nullable s) \<and>
    (\<forall>a\<in>set as. (nderiv a r, nderiv a s) \<in> set ps))"


lemma bisim_lang_eq:
assumes bisim: "is_bisimulation as ps"
assumes "(r, s) \<in> set ps"
shows "lang (set as) r = lang (set as) s"
proof -
  let ?R = "\<lambda>K L. (\<exists>(r,s)\<in>set ps. K = lang (set as) r \<and> L = lang (set as) s)"
  show ?thesis
  proof (rule language_coinduct[where R="?R" and S = "set as"])
    from \<open>(r, s) \<in> set ps\<close> show "?R (lang (set as) r) (lang (set as) s)"
      by auto
  next
    fix K L assume "?R K L"
    then obtain r s where rs: "(r, s) \<in> set ps"
      and KL: "K = lang (set as) r" "L = lang (set as) s" by auto
    with bisim have "nullable r \<longleftrightarrow> nullable s"
      by (auto simp: is_bisimulation_def)
    thus "[] \<in> K \<longleftrightarrow> [] \<in> L" by (auto simp: nullable_iff[where S="set as"] KL)
  txt\<open>next case, but shared context\<close>
    from bisim rs KL lang_subset_lists[of _ "set as"]
    show "K \<subseteq> lists (set as) \<and> L \<subseteq> lists (set as)"
      unfolding is_bisimulation_def by blast
  txt\<open>next case, but shared context\<close>
    fix a assume "a \<in> set as"
    with rs bisim
    have "(nderiv a r, nderiv a s) \<in> set ps"
      by (auto simp: is_bisimulation_def)
    thus "?R (Deriv a K) (Deriv a L)" using \<open>a \<in> set as\<close>
      by (force simp: KL lang_nderiv)
  qed
qed

subsection \<open>Closure computation\<close>

fun test :: "rexp_pairs * rexp_pairs \<Rightarrow> bool"
where "test (ws, ps) = (case ws of [] \<Rightarrow>  False | (p,q)#_ \<Rightarrow> nullable p = nullable q)"

fun step :: "nat list \<Rightarrow> rexp_pairs * rexp_pairs \<Rightarrow> rexp_pairs * rexp_pairs"
where "step as (ws,ps) =
    (let 
      (r, s) = hd ws;
      ps' = (r, s) # ps;
      succs = map (\<lambda>a. (nderiv a r, nderiv a s)) as;
      new = filter (\<lambda>p. p \<notin> set ps' \<union> set ws) succs
    in (new @ tl ws, ps'))"

definition closure ::
  "nat list \<Rightarrow> rexp_pairs * rexp_pairs
   \<Rightarrow> (rexp_pairs * rexp_pairs) option" where
"closure as = while_option test (step as)"

definition pre_bisim :: "nat list \<Rightarrow> nat rexp \<Rightarrow> nat rexp \<Rightarrow>
 rexp_pairs * rexp_pairs \<Rightarrow> bool"
where
"pre_bisim as r s = (\<lambda>(ws,ps).
 ((r, s) \<in> set ws \<union> set ps) \<and>
 (\<forall>(r,s)\<in> set ws \<union> set ps. atoms r \<union> atoms s \<subseteq> set as) \<and>
 (\<forall>(r,s)\<in> set ps. (nullable r \<longleftrightarrow> nullable s) \<and>
   (\<forall>a\<in>set as. (nderiv a r, nderiv a s) \<in> set ps \<union> set ws)))"

theorem closure_sound:
assumes result: "closure as ([(r,s)],[]) = Some([],ps)"
and atoms: "atoms r \<union> atoms s \<subseteq> set as"
shows "lang (set as) r = lang (set as) s"
proof-
  { fix st have "pre_bisim as r s st \<Longrightarrow> test st \<Longrightarrow> pre_bisim as r s (step as st)"
      unfolding pre_bisim_def
      by (cases st) (auto simp: split_def split: list.splits prod.splits
        dest!: subsetD[OF atoms_nderiv]) }
  moreover
  from atoms
  have "pre_bisim as r s ([(r,s)],[])" by (simp add: pre_bisim_def)
  ultimately have pre_bisim_ps: "pre_bisim as r s ([],ps)"
    by (rule while_option_rule[OF _ result[unfolded closure_def]])
  then have "is_bisimulation as ps" "(r, s) \<in> set ps"
    by (auto simp: pre_bisim_def is_bisimulation_def)
  thus "lang (set as) r = lang (set as) s" by (rule bisim_lang_eq)
qed


subsection \<open>The overall procedure\<close>

primrec add_atoms :: "nat rexp \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "add_atoms Zero = id"
| "add_atoms One = id"
| "add_atoms (Atom a) = List.insert a"
| "add_atoms (Plus r s) = add_atoms s o add_atoms r"
| "add_atoms (Times r s) = add_atoms s o add_atoms r"
| "add_atoms (Not r) = add_atoms r"
| "add_atoms (Inter r s) = add_atoms s o add_atoms r"
| "add_atoms (Star r) = add_atoms r"

lemma set_add_atoms: "set (add_atoms r as) = atoms r \<union> set as"
by (induct r arbitrary: as) auto

definition check_eqv :: "nat list \<Rightarrow> nat rexp \<Rightarrow> nat rexp \<Rightarrow> bool"
where
"check_eqv as r s \<longleftrightarrow> set(add_atoms r (add_atoms s [])) \<subseteq> set as \<and>
  (case closure as ([(norm r, norm s)], []) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: 
assumes "check_eqv as r s" shows "lang (set as) r = lang (set as) s"
proof -
  obtain ps where cl: "closure as ([(norm r,norm s)],[]) = Some([],ps)"
    and at: "atoms r \<union> atoms s \<subseteq> set as"
    using assms
    by (auto simp: check_eqv_def set_add_atoms split:option.splits list.splits)
  hence "atoms(norm r) \<union> atoms(norm s) \<subseteq> set as"
    using atoms_norm by blast
  hence "lang (set as) (norm r) = lang (set as) (norm s)"
    by (rule closure_sound[OF cl])
  thus "lang (set as) r = lang (set as) s" by simp
qed

lemma "check_eqv [0] (Plus One (Times (Atom 0) (Star(Atom 0)))) (Star(Atom 0))"
by eval

lemma "check_eqv [0,1] (Not(Atom 0))
  (Plus One (Times (Plus (Atom 1) (Times (Atom 0) (Plus (Atom 0) (Atom 1))))
                   (Star(Plus (Atom 0) (Atom 1)))))"
by eval

lemma "check_eqv [0] (Atom 0) (Inter (Star (Atom 0)) (Atom 0))"
by eval

end
