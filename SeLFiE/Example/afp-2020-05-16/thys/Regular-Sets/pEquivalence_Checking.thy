section \<open>Deciding Regular Expression Equivalence (2)\<close>

theory pEquivalence_Checking
imports Equivalence_Checking Derivatives
begin

text\<open>\noindent Similar to theory @{theory "Regular-Sets.Equivalence_Checking"}, but
with partial derivatives instead of derivatives.\<close>

text\<open>Lifting many notions to sets:\<close>

definition "Lang R == UN r:R. lang r"
definition "Nullable R == EX r:R. nullable r"
definition "Pderiv a R == UN r:R. pderiv a r"
definition "Atoms R == UN r:R. atoms r"

(* FIXME: rename pderiv_set in Derivatives to Pderiv and drop the one above *)

lemma Atoms_pderiv: "Atoms(pderiv a r) \<subseteq> atoms r"
apply (induct r)
apply (auto simp: Atoms_def UN_subset_iff)
apply (fastforce)+
done

lemma Atoms_Pderiv: "Atoms(Pderiv a R) \<subseteq> Atoms R"
using Atoms_pderiv by (fastforce simp: Atoms_def Pderiv_def)

lemma pderiv_no_occurrence: 
  "x \<notin> atoms r \<Longrightarrow> pderiv x r = {}"
by (induct r) auto

lemma Pderiv_no_occurrence: 
  "x \<notin> Atoms R \<Longrightarrow> Pderiv x R = {}"
by(auto simp:pderiv_no_occurrence Atoms_def Pderiv_def)

lemma Deriv_Lang: "Deriv c (Lang R) = Lang (Pderiv c R)"
by(auto simp: Deriv_pderiv Pderiv_def Lang_def)

lemma Nullable_pderiv[simp]: "Nullable(pderivs w r) = (w : lang r)"
apply(induction w arbitrary: r)
apply (simp add: Nullable_def nullable_iff singleton_iff)
using eqset_imp_iff[OF Deriv_pderiv[where 'a = 'a]]
apply (simp add: Nullable_def Deriv_def)
done


type_synonym 'a Rexp_pair = "'a rexp set * 'a rexp set"
type_synonym 'a Rexp_pairs = "'a Rexp_pair list"

definition is_Bisimulation :: "'a list \<Rightarrow> 'a Rexp_pairs \<Rightarrow> bool"
where
"is_Bisimulation as ps =
  (\<forall>(R,S)\<in> set ps. Atoms R \<union> Atoms S \<subseteq> set as \<and>
    (Nullable R \<longleftrightarrow> Nullable S) \<and>
    (\<forall>a\<in>set as. (Pderiv a R, Pderiv a S) \<in> set ps))"

lemma Bisim_Lang_eq:
assumes Bisim: "is_Bisimulation as ps"
assumes "(R, S) \<in> set ps"
shows "Lang R = Lang S"
proof -
  define ps' where "ps' = ({}, {}) # ps"
  from Bisim have Bisim': "is_Bisimulation as ps'"
    by (fastforce simp: ps'_def is_Bisimulation_def UN_subset_iff Pderiv_def Atoms_def)
  let ?R = "\<lambda>K L. (\<exists>(R,S)\<in>set ps'. K = Lang R \<and> L = Lang S)"
  show ?thesis
  proof (rule language_coinduct[where R="?R"])
    from \<open>(R,S) \<in> set ps\<close>
    have "(R,S) \<in> set ps'" by (auto simp: ps'_def)
    thus "?R (Lang R) (Lang S)" by auto
  next
    fix K L assume "?R K L"
    then obtain R S where rs: "(R, S) \<in> set ps'"
      and KL: "K = Lang R" "L = Lang S" by auto
    with Bisim' have "Nullable R \<longleftrightarrow> Nullable S"
      by (auto simp: is_Bisimulation_def)
    thus "[] \<in> K \<longleftrightarrow> [] \<in> L"
      by (auto simp: nullable_iff KL Nullable_def Lang_def)
    fix a
    show "?R (Deriv a K) (Deriv a L)"
    proof cases
      assume "a \<in> set as"
      with rs Bisim'
      have "(Pderiv a R, Pderiv a S) \<in> set ps'"
        by (auto simp: is_Bisimulation_def)
      thus ?thesis by (fastforce simp: KL Deriv_Lang)
    next
      assume "a \<notin> set as"
      with Bisim' rs
      have "a \<notin> Atoms R \<union> Atoms S"
        by (fastforce simp: is_Bisimulation_def UN_subset_iff)
      then have "Pderiv a R = {}" "Pderiv a S = {}"
        by (metis Pderiv_no_occurrence Un_iff)+
      then have "Deriv a K = Lang {}" "Deriv a L = Lang {}" 
        unfolding KL Deriv_Lang by auto
      thus ?thesis by (auto simp: ps'_def)
    qed
  qed
qed


subsection \<open>Closure computation\<close>

fun test :: "'a Rexp_pairs * 'a Rexp_pairs \<Rightarrow> bool" where
"test (ws, ps) = (case ws of [] \<Rightarrow>  False | (R,S)#_ \<Rightarrow> Nullable R = Nullable S)"

fun step :: "'a list \<Rightarrow>
  'a Rexp_pairs * 'a Rexp_pairs \<Rightarrow> 'a Rexp_pairs * 'a Rexp_pairs"
where "step as (ws,ps) =
    (let
      (R,S) = hd ws;
      ps' = (R,S) # ps;
      succs = map (\<lambda>a. (Pderiv a R, Pderiv a S)) as;
      new = filter (\<lambda>p. p \<notin> set ps \<union> set ws) succs
    in (remdups new @ tl ws, ps'))"

definition closure ::
  "'a list \<Rightarrow> 'a Rexp_pairs * 'a Rexp_pairs
   \<Rightarrow> ('a Rexp_pairs * 'a Rexp_pairs) option" where
"closure as = while_option test (step as)"

definition pre_Bisim :: "'a list \<Rightarrow> 'a rexp set \<Rightarrow> 'a rexp set \<Rightarrow>
 'a Rexp_pairs * 'a Rexp_pairs \<Rightarrow> bool"
where
"pre_Bisim as R S = (\<lambda>(ws,ps).
 ((R,S) \<in> set ws \<union> set ps) \<and>
 (\<forall>(R,S)\<in> set ws \<union> set ps. Atoms R \<union> Atoms S \<subseteq> set as) \<and>
 (\<forall>(R,S)\<in> set ps. (Nullable R \<longleftrightarrow> Nullable S) \<and>
   (\<forall>a\<in>set as. (Pderiv a R, Pderiv a S) \<in> set ps \<union> set ws)))"

lemma step_set_eq: "\<lbrakk> test (ws,ps); step as (ws,ps) = (ws',ps') \<rbrakk>
  \<Longrightarrow> set ws' \<union> set ps' =
     set ws \<union> set ps
     \<union> (\<Union>a\<in>set as. {(Pderiv a (fst(hd ws)), Pderiv a (snd(hd ws)))})"
by(auto split: list.splits)

theorem closure_sound:
assumes result: "closure as ([(R,S)],[]) = Some([],ps)"
and atoms: "Atoms R \<union> Atoms S \<subseteq> set as"
shows "Lang R = Lang S"
proof-
  { fix st
    have "pre_Bisim as R S st \<Longrightarrow> test st \<Longrightarrow> pre_Bisim as R S (step as st)"
    unfolding pre_Bisim_def
    proof(split prod.splits, elim case_prodE conjE, intro allI impI conjI, goal_cases)
      case 1 thus ?case by(auto split: list.splits)
    next
      case prems: (2 ws ps ws' ps')
      note prems(2)[simp]
      from \<open>test st\<close> obtain wstl R S where [simp]: "ws = (R,S)#wstl"
        by (auto split: list.splits)
      from \<open>step as st = (ws',ps')\<close> obtain P where [simp]: "ps' = (R,S) # ps"
        and [simp]: "ws' = remdups(filter P (map (\<lambda>a. (Pderiv a R, Pderiv a S)) as)) @ wstl"
        by auto
      have "\<forall>(R',S')\<in>set wstl \<union> set ps'. Atoms R' \<union> Atoms S' \<subseteq> set as"
        using prems(4) by auto
      moreover
      have "\<forall>a\<in>set as. Atoms(Pderiv a R) \<union> Atoms(Pderiv a S) \<subseteq> set as"
        using prems(4) by simp (metis (lifting) Atoms_Pderiv order_trans)
      ultimately show ?case by simp blast
    next
      case 3 thus ?case
        apply (clarsimp simp: image_iff split: prod.splits list.splits)
        by hypsubst_thin metis
    qed
  }
  moreover
  from atoms
  have "pre_Bisim as R S ([(R,S)],[])" by (simp add: pre_Bisim_def)
  ultimately have pre_Bisim_ps: "pre_Bisim as R S ([],ps)"
    by (rule while_option_rule[OF _ result[unfolded closure_def]])
  then have "is_Bisimulation as ps" "(R,S) \<in> set ps"
    by (auto simp: pre_Bisim_def is_Bisimulation_def)
  thus "Lang R = Lang S" by (rule Bisim_Lang_eq)
qed


subsection \<open>The overall procedure\<close>

definition check_eqv :: "'a rexp \<Rightarrow> 'a rexp \<Rightarrow> bool"
where
"check_eqv r s =
  (case closure (add_atoms r (add_atoms s [])) ([({r}, {s})], []) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?as = "add_atoms r (add_atoms s [])"
  obtain ps where 1: "closure ?as ([({r},{s})],[]) = Some([],ps)"
    using assms by (auto simp: check_eqv_def split:option.splits list.splits)
  then have "lang r = lang s"
    by(rule closure_sound[of _ "{r}" "{s}", simplified Lang_def, simplified])
      (auto simp: set_add_atoms Atoms_def)
  thus "lang r = lang s" by simp
qed

text\<open>Test:\<close>
lemma "check_eqv
  (Plus One (Times (Atom 0) (Star(Atom 0))))
  (Star(Atom(0::nat)))"
by eval


subsection "Termination and Completeness"

definition PDERIVS :: "'a rexp set => 'a rexp set" where
"PDERIVS R = (UN r:R. pderivs_lang UNIV r)"

lemma PDERIVS_incr[simp]: "R \<subseteq> PDERIVS R"
apply(auto simp add: PDERIVS_def pderivs_lang_def)
by (metis pderivs.simps(1) insertI1)

lemma Pderiv_PDERIVS: assumes "R' \<subseteq> PDERIVS R" shows "Pderiv a R' \<subseteq> PDERIVS R"
proof
  fix r assume "r : Pderiv a R'"
  then obtain r' where "r' : R'" "r : pderiv a r'" by(auto simp: Pderiv_def)
  from \<open>r' : R'\<close> \<open>R' \<subseteq> PDERIVS R\<close> obtain s w where "s : R" "r' : pderivs w s"
    by(auto simp: PDERIVS_def pderivs_lang_def)
  hence "r \<in> pderivs (w @ [a]) s" using \<open>r : pderiv a r'\<close> by(auto simp add:pderivs_snoc)
  thus "r : PDERIVS R" using \<open>s : R\<close> by(auto simp: PDERIVS_def pderivs_lang_def)
qed

lemma finite_PDERIVS: "finite R \<Longrightarrow> finite(PDERIVS R)"
by(simp add: PDERIVS_def finite_pderivs_lang_UNIV)

lemma closure_Some: assumes "finite R0" "finite S0" shows "\<exists>p. closure as ([(R0,S0)],[]) = Some p"
proof(unfold closure_def)
  let ?Inv = "%(ws,bs).  distinct ws \<and> (ALL (R,S) : set ws. R \<subseteq> PDERIVS R0 \<and> S \<subseteq> PDERIVS S0 \<and> (R,S) \<notin> set bs)"
  let ?m1 = "%bs. Pow(PDERIVS R0) \<times> Pow(PDERIVS S0) - set bs"
  let ?m2 = "%(ws,bs). card(?m1 bs)"
  have Inv0: "?Inv ([(R0, S0)], [])" by simp
  { fix s assume "test s" "?Inv s"
    obtain ws bs where [simp]: "s = (ws,bs)" by fastforce
    from \<open>test s\<close> obtain R S ws' where [simp]: "ws = (R,S)#ws'"
      by(auto split: prod.splits list.splits)
    let ?bs' = "(R,S) # bs"
    let ?succs = "map (\<lambda>a. (Pderiv a R, Pderiv a S)) as"
    let ?new = "filter (\<lambda>p. p \<notin> set bs \<union> set ws) ?succs"
    let ?ws' = "remdups ?new @ ws'"
    have *: "?Inv (step as s)"
    proof -
      from \<open>?Inv s\<close> have "distinct ?ws'" by auto
      have "ALL (R,S) : set ?ws'. R \<subseteq> PDERIVS R0 \<and> S \<subseteq> PDERIVS S0 \<and> (R,S) \<notin> set ?bs'" using \<open>?Inv s\<close>
        by(simp add: Ball_def image_iff) (metis Pderiv_PDERIVS)
      with \<open>distinct ?ws'\<close> show ?thesis by(simp)
    qed
    have "?m2(step as s) < ?m2 s"
    proof -
      have "finite(?m1 bs)"
        by(metis assms finite_Diff finite_PDERIVS finite_cartesian_product finite_Pow_iff)
      moreover have "?m2(step as s) < ?m2 s" using \<open>?Inv s\<close>
        by(auto intro: psubset_card_mono[OF \<open>finite(?m1 bs)\<close>])
      then show ?thesis using \<open>?Inv s\<close> by simp
    qed
    note * and this
  } note step = this
  show "\<exists>p. while_option test (step as) ([(R0, S0)], []) = Some p" 
    by(rule measure_while_option_Some [where P = ?Inv and f = ?m2, OF _ Inv0])(simp add: step)
qed

theorem closure_Some_Inv: assumes "closure as ([({r},{s})],[]) = Some p"
shows "\<forall>(R,S)\<in>set(fst p). \<exists>w. R = pderivs w r \<and> S = pderivs w s" (is "?Inv p")
proof-
  from assms have 1: "while_option test (step as) ([({r},{s})],[]) = Some p"
    by(simp add: closure_def)
  have Inv0: "?Inv ([({r},{s})],[])" by simp (metis pderivs.simps(1))
  { fix p assume "?Inv p" "test p"
    obtain ws bs where [simp]: "p = (ws,bs)" by fastforce
    from \<open>test p\<close> obtain R S ws' where [simp]: "ws = (R,S)#ws'"
      by(auto split: prod.splits list.splits)
    let ?succs = "map (\<lambda>a. (Pderiv a R, Pderiv a S)) as"
    let ?new = "filter (\<lambda>p. p \<notin> set bs \<union> set ws) ?succs"
    let ?ws' = "remdups ?new @ ws'"
    from \<open>?Inv p\<close> obtain w where [simp]: "R = pderivs w r" "S = pderivs w s"
      by auto
    { fix x assume "x : set as"
      have "EX w. Pderiv x R = pderivs w r \<and> Pderiv x S = pderivs w s"
        by(rule_tac x="w@[x]" in exI)(simp add: pderivs_append Pderiv_def)
    }
    with \<open>?Inv p\<close> have "?Inv (step as p)" by auto
  } note Inv_step = this
  show ?thesis
    apply(rule while_option_rule[OF _ 1])
    apply(erule (1) Inv_step)
    apply(rule Inv0)
    done
qed

lemma closure_complete: assumes "lang r = lang s"
 shows "EX bs. closure as ([({r},{s})],[]) = Some([],bs)" (is ?C)
proof(rule ccontr)
  assume "\<not> ?C"
  then obtain R S ws bs
    where cl: "closure as ([({r},{s})],[]) = Some((R,S)#ws,bs)"
    using closure_Some[of "{r}" "{s}", simplified]
    by (metis (hide_lams, no_types) list.exhaust prod.exhaust)
  from assms closure_Some_Inv[OF this]
    while_option_stop[OF cl[unfolded closure_def]]
  show "False" by auto
qed

corollary completeness: "lang r = lang s \<Longrightarrow> check_eqv r s"
by(auto simp add: check_eqv_def dest!: closure_complete
      split: option.split list.split)

end
