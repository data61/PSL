(*  Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)
section {* Manual construction of a resumption codatatype *}

theory Resumption imports 
  "HOL-Library.Old_Datatype"
begin

text {*
  This theory defines the following codatatype:

\begin{verbatim}
codatatype ('a,'b,'c,'d) resumption =
    Terminal 'a
  | Linear 'b "('a,'b,'c,'d) resumption"
  | Branch 'c "'d => ('a,'b,'c,'d) resumption"
\end{verbatim}

*}

subsection {* Auxiliary definitions and lemmata similar to @{theory "HOL-Library.Old_Datatype"} *}

lemma Lim_mono: "(\<And>d. rs d \<subseteq> rs' d) \<Longrightarrow> Old_Datatype.Lim rs \<subseteq> Old_Datatype.Lim rs'"
by(simp add: Lim_def) blast

lemma Lim_UN1:  "Old_Datatype.Lim (\<lambda>x. \<Union>y. f x y) = (\<Union>y. Old_Datatype.Lim (\<lambda>x. f x y))"
by(simp add: Old_Datatype.Lim_def) blast

text {*
  Inverse for @{term "Old_Datatype.Lim"} like @{term "Old_Datatype.Split"} and @{term "Old_Datatype.Case"}
  for @{term "Old_Datatype.Scons"} and @{term "In0"}/@{term "In1"}
*}

definition DTBranch :: "(('b \<Rightarrow> ('a, 'b) Old_Datatype.dtree) \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) Old_Datatype.dtree \<Rightarrow> 'c"
where "DTBranch f M = (THE u. \<exists>x. M = Old_Datatype.Lim x \<and> u = f x)"

lemma DTBranch_Lim [simp]: "DTBranch f (Old_Datatype.Lim M) = f M"
by(auto simp add: DTBranch_def dest: Lim_inject)

text {* Lemmas for @{term Old_Datatype.ntrunc} and @{term "Old_Datatype.Lim"} *}

lemma ndepth_Push_Node_Inl_aux:
     "case_nat (Inl n) f k = Inr 0 \<Longrightarrow> Suc (LEAST x. f x = Inr 0) <= k"
apply (induct "k", auto)
apply (erule Least_le)
done

lemma ndepth_Push_Node_Inl:
  "ndepth (Push_Node (Inl a) n) = Suc (ndepth n)"
using Rep_Node[of n, unfolded Node_def]
apply(simp add: ndepth_def Push_Node_def Abs_Node_inverse[OF Node_Push_I[OF Rep_Node]])
apply(simp add: Push_def split_beta)
apply(rule Least_equality)
apply(auto elim: LeastI intro: ndepth_Push_Node_Inl_aux)
done

lemma ntrunc_Lim [simp]: "ntrunc (Suc k) (Old_Datatype.Lim rs) = Old_Datatype.Lim (\<lambda>x. ntrunc k (rs x))"
unfolding Lim_def ntrunc_def
apply(rule equalityI)
apply clarify
apply(auto simp add: ndepth_Push_Node_Inl)
done

subsection {* Definition for the codatatype universe *}

text {* Constructors *}

definition TERMINAL :: "'a \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree"
where "TERMINAL a = In0 (Old_Datatype.Leaf (Inr (Inr a)))"

definition LINEAR :: "'b \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree"
  where "LINEAR b r = In1 (In0 (Scons (Old_Datatype.Leaf (Inr (Inl b))) r))"

definition BRANCH :: "'c \<Rightarrow> ('d \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree) \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree"
 where "BRANCH c rs = In1 (In1 (Scons (Old_Datatype.Leaf (Inl c)) (Old_Datatype.Lim rs)))"

text {* case operator *}

definition case_RESUMPTION :: "('a \<Rightarrow> 'e) \<Rightarrow> ('b \<Rightarrow> (('c + 'b + 'a, 'd) Old_Datatype.dtree) \<Rightarrow> 'e) \<Rightarrow> ('c \<Rightarrow> ('d \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree) \<Rightarrow> 'e) \<Rightarrow> ('c + 'b + 'a, 'd) Old_Datatype.dtree \<Rightarrow> 'e"
where 
  "case_RESUMPTION t l br =
   Old_Datatype.Case (t o inv (Old_Datatype.Leaf o Inr o Inr))
                 (Old_Datatype.Case (Old_Datatype.Split (\<lambda>x. l (inv (Old_Datatype.Leaf o Inr o Inl) x)))
                                (Old_Datatype.Split (\<lambda>x. DTBranch (br (inv (Old_Datatype.Leaf o Inl) x)))))"

lemma [iff]:
  shows TERMINAL_not_LINEAR: "TERMINAL a \<noteq> LINEAR b r"
  and LINEAR_not_TERMINAL: "LINEAR b R \<noteq> TERMINAL a"
  and TERMINAL_not_BRANCH: "TERMINAL a \<noteq> BRANCH c rs"
  and BRANCH_not_TERMINAL: "BRANCH c rs \<noteq> TERMINAL a"
  and LINEAR_not_BRANCH: "LINEAR b r \<noteq> BRANCH c rs"
  and BRANCH_not_LINEAR: "BRANCH c rs \<noteq> LINEAR b r"
  and TERMINAL_inject: "TERMINAL a = TERMINAL a' \<longleftrightarrow> a = a'"
  and LINEAR_inject: "LINEAR b r = LINEAR b' r' \<longleftrightarrow> b = b' \<and> r = r'"
  and BRANCH_inject: "BRANCH c rs = BRANCH c' rs' \<longleftrightarrow> c = c' \<and> rs = rs'"
by(auto simp add: TERMINAL_def LINEAR_def BRANCH_def dest: Lim_inject)

lemma case_RESUMPTION_simps [simp]:
  shows case_RESUMPTION_TERMINAL: "case_RESUMPTION t l br (TERMINAL a) = t a"
  and case_RESUMPTION_LINEAR: "case_RESUMPTION t l br (LINEAR b r) = l b r"
  and case_RESUMPTION_BRANCH: "case_RESUMPTION t l br (BRANCH c rs) = br c rs"
apply(simp_all add: case_RESUMPTION_def TERMINAL_def LINEAR_def BRANCH_def o_def)
apply(rule arg_cong) back
apply(blast intro: injI inv_f_f)
apply(rule arg_cong) back
apply(blast intro: injI inv_f_f)
apply(rule arg_cong) back
apply(blast intro: injI inv_f_f)
done

lemma LINEAR_mono: "r \<subseteq> r' \<Longrightarrow> LINEAR b r \<subseteq> LINEAR b r'"
by(simp add: LINEAR_def In1_mono In0_mono Scons_mono)

lemma BRANCH_mono: "(\<And>d. rs d \<subseteq> rs' d) \<Longrightarrow> BRANCH c rs \<subseteq> BRANCH c rs'"
by(simp add: BRANCH_def In1_mono Scons_mono Lim_mono)

lemma LINEAR_UN: "LINEAR b (\<Union>x. f x) = (\<Union>x. LINEAR b (f x))"
by (simp add: LINEAR_def In1_UN1 In0_UN1 Scons_UN1_y)

lemma BRANCH_UN: "BRANCH b (\<lambda>d. \<Union>x. f d x) = (\<Union>x. BRANCH b (\<lambda>d. f d x))"
by (simp add: BRANCH_def Lim_UN1 In1_UN1 In0_UN1 Scons_UN1_y)

text {* The codatatype universe *}

coinductive_set resumption :: "('c + 'b + 'a, 'd) Old_Datatype.dtree set"
where
resumption_TERMINAL:
  "TERMINAL a \<in> resumption"
| resumption_LINEAR:
  "r \<in> resumption \<Longrightarrow> LINEAR b r \<in> resumption"
| resumption_BRANCH:
  "(\<And>d. rs d \<in> resumption) \<Longrightarrow> BRANCH c rs \<in> resumption"

subsection {* Definition of the codatatype as a type *}

typedef ('a,'b,'c,'d) resumption = "resumption :: ('c + 'b + 'a, 'd) Old_Datatype.dtree set"
proof
  show "TERMINAL undefined \<in> ?resumption" by(blast intro: resumption.intros)
qed

text {* Constructors *}

definition Terminal :: "'a \<Rightarrow> ('a,'b,'c,'d) resumption"
where "Terminal a = Abs_resumption (TERMINAL a)"

definition Linear :: "'b \<Rightarrow> ('a,'b,'c,'d) resumption \<Rightarrow> ('a,'b,'c,'d) resumption"
where "Linear b r = Abs_resumption (LINEAR b (Rep_resumption r))"

definition Branch :: "'c \<Rightarrow> ('d \<Rightarrow> ('a,'b,'c,'d) resumption) \<Rightarrow> ('a,'b,'c,'d) resumption"
where "Branch c rs = Abs_resumption (BRANCH c (\<lambda>d. Rep_resumption (rs d)))"

lemma [iff]:
  shows Terminal_not_Linear: "Terminal a \<noteq> Linear b r"
  and Linear_not_Terminal: "Linear b R \<noteq> Terminal a"
  and Termina_not_Branch: "Terminal a \<noteq> Branch c rs"
  and Branch_not_Terminal: "Branch c rs \<noteq> Terminal a"
  and Linear_not_Branch: "Linear b r \<noteq> Branch c rs"
  and Branch_not_Linear: "Branch c rs \<noteq> Linear b r"
  and Terminal_inject: "Terminal a = Terminal a' \<longleftrightarrow> a = a'"
  and Linear_inject: "Linear b r = Linear b' r' \<longleftrightarrow> b = b' \<and> r = r'"
  and Branch_inject: "Branch c rs = Branch c' rs' \<longleftrightarrow> c = c' \<and> rs = rs'"
apply(auto simp add: Terminal_def Linear_def Branch_def simp add: Rep_resumption resumption.intros Abs_resumption_inject Rep_resumption_inject)
apply(subst (asm) fun_eq_iff, auto simp add: Rep_resumption_inject)
done

lemma Rep_resumption_constructors:
  shows Rep_resumption_Terminal: "Rep_resumption (Terminal a) = TERMINAL a"
  and Rep_resumption_Linear: "Rep_resumption (Linear b r) = LINEAR b (Rep_resumption r)"
  and Rep_resumption_Branch: "Rep_resumption (Branch c rs) = BRANCH c (\<lambda>d. Rep_resumption (rs d))"
by(simp_all add: Terminal_def Linear_def Branch_def Abs_resumption_inverse resumption.intros Rep_resumption)

text {* Case operator *}

definition case_resumption :: "('a \<Rightarrow> 'e) \<Rightarrow> ('b \<Rightarrow> ('a,'b,'c,'d) resumption \<Rightarrow> 'e) \<Rightarrow>
                            ('c \<Rightarrow> ('d \<Rightarrow> ('a,'b,'c,'d) resumption) \<Rightarrow> 'e) \<Rightarrow> ('a,'b,'c,'d) resumption \<Rightarrow> 'e"
where [code del]:
  "case_resumption t l br r =
   case_RESUMPTION t (\<lambda>b r. l b (Abs_resumption r)) (\<lambda>c rs. br c (\<lambda>d. Abs_resumption (rs d))) (Rep_resumption r)"

lemma case_resumption_simps [simp, code]:
  shows case_resumption_Terminal: "case_resumption t l br (Terminal a) = t a"
  and case_resumption_Linear: "case_resumption t l br (Linear b r) = l b r"
  and case_resumption_Branch: "case_resumption t l br (Branch c rs) = br c rs"
by(simp_all add: Terminal_def Linear_def Branch_def case_resumption_def Abs_resumption_inverse resumption.intros Rep_resumption Rep_resumption_inverse)

declare [[case_translation case_resumption Terminal Linear Branch]]

lemma case_resumption_cert:
  assumes "CASE \<equiv> case_resumption t l br"
  shows "(CASE (Terminal a) \<equiv> t a) &&& (CASE (Linear b r) \<equiv> l b r) &&& (CASE (Branch c rs) \<equiv> br c rs)"
using assms by simp_all

code_datatype Terminal Linear Branch

setup \<open>Code.declare_case_global @{thm case_resumption_cert}\<close>

setup {*
  Nitpick.register_codatatype @{typ "('a,'b,'c,'d) resumption"} @{const_name case_resumption}
                              (map dest_Const [@{term Terminal}, @{term Linear}, @{term Branch}])
*}

lemma resumption_exhaust [cases type: resumption]:
  obtains (Terminal) a where "x = Terminal a"
  | (Linear) b r where "x = Linear b r"
  | (Branch) c rs where "x = Branch c rs"
proof(cases x)
  case (Abs_resumption y)
  note [simp] = `x = Abs_resumption y`
  from `y \<in> resumption` show thesis
  proof(cases rule: resumption.cases)
    case resumption_TERMINAL thus ?thesis
      by -(rule Terminal, simp add: Terminal_def)
  next
    case (resumption_LINEAR r b) 
    from `r \<in> resumption` have "Rep_resumption (Abs_resumption r) = r"
      by(simp add: Abs_resumption_inverse)
    hence "y = LINEAR b (Rep_resumption (Abs_resumption r))"
      using `y = LINEAR b r` by simp
    thus ?thesis by -(rule Linear, simp add: Linear_def)
  next
    case (resumption_BRANCH rs c)
    from `\<And>d. rs d \<in> resumption`
    have eq: "rs = (\<lambda>d. Rep_resumption (Abs_resumption (rs d)))"
      by(subst Abs_resumption_inverse) blast+
    show ?thesis using `y = BRANCH c rs` 
      by -(rule Branch, simp add: Branch_def, subst eq, simp)
  qed
qed

lemma resumption_split:
  "P (case_resumption t l br r) \<longleftrightarrow> 
  (\<forall>a. r = Terminal a \<longrightarrow> P (t a)) \<and>
  (\<forall>b r'. r = Linear b r' \<longrightarrow> P (l b r')) \<and>
  (\<forall>c rs. r = Branch c rs \<longrightarrow> P (br c rs))"
by(cases r) simp_all

lemma resumption_split_asm:
  "P (case_resumption t l br r) \<longleftrightarrow>
  \<not> ((\<exists>a. r = Terminal a \<and> \<not> P (t a)) \<or>
     (\<exists>b r'. r = Linear b r' \<and> \<not> P (l b r')) \<or>
     (\<exists>c rs. r = Branch c rs \<and> \<not> P (br c rs)))"
by(cases r) simp_all

lemmas resumption_splits = resumption_split resumption_split_asm


text {* corecursion operator *}

datatype (dead 'a, dead 'b, dead 'c, dead 'd, dead 'e) resumption_corec =
    Terminal_corec 'a
  | Linear_corec 'b 'e
  | Branch_corec 'c "'d \<Rightarrow> 'e"
  | Resumption_corec "('a, 'b, 'c, 'd) resumption"

primrec RESUMPTION_corec_aux :: "nat \<Rightarrow> ('e \<Rightarrow> ('a,'b,'c,'d,'e) resumption_corec) \<Rightarrow> 'e \<Rightarrow> ('c + 'b + 'a,'d) Old_Datatype.dtree"
where
  "RESUMPTION_corec_aux 0 f e = {}"
| "RESUMPTION_corec_aux (Suc n) f e =
  (case f e of Terminal_corec a \<Rightarrow> TERMINAL a
            | Linear_corec b e' \<Rightarrow> LINEAR b (RESUMPTION_corec_aux n f e')
            | Branch_corec c es \<Rightarrow> BRANCH c (\<lambda>d. RESUMPTION_corec_aux n f (es d))
            | Resumption_corec r \<Rightarrow> Rep_resumption r)"

definition RESUMPTION_corec :: "('e \<Rightarrow> ('a,'b,'c,'d,'e) resumption_corec) \<Rightarrow> 'e \<Rightarrow> ('c + 'b + 'a,'d) Old_Datatype.dtree"
where
  "RESUMPTION_corec f e = (\<Union>n. RESUMPTION_corec_aux n f e)"

lemma RESUMPTION_corec [nitpick_simp]:
  "RESUMPTION_corec f e =
  (case f e of Terminal_corec a \<Rightarrow> TERMINAL a
            | Linear_corec b e' \<Rightarrow> LINEAR b (RESUMPTION_corec f e')
            | Branch_corec c es \<Rightarrow> BRANCH c (\<lambda>d. RESUMPTION_corec f (es d))
            | Resumption_corec r \<Rightarrow> Rep_resumption r)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" unfolding RESUMPTION_corec_def
  proof(rule UN_least)
    fix n
    show "RESUMPTION_corec_aux n f e
        \<subseteq> (case f e of Terminal_corec a \<Rightarrow> TERMINAL a
           | Linear_corec b e' \<Rightarrow> LINEAR b (\<Union>n. RESUMPTION_corec_aux n f e')
           | Branch_corec c es \<Rightarrow> BRANCH c (\<lambda>d. \<Union>n. RESUMPTION_corec_aux n f (es d))
           | Resumption_corec r \<Rightarrow> Rep_resumption r)"
      apply(cases n, simp_all split: resumption_corec.split)
      by(rule conjI strip LINEAR_mono[OF UN_upper] BRANCH_mono[OF UN_upper] UNIV_I)+
  qed
next
  show "?rhs \<subseteq> ?lhs" unfolding RESUMPTION_corec_def
    apply(simp split: resumption_corec.split add: LINEAR_UN BRANCH_UN)
    by safe(rule_tac a="Suc n" for n in UN_I, rule UNIV_I, simp)+
qed

lemma RESUMPTION_corec_type: "RESUMPTION_corec f e \<in> resumption"
proof -
  have "\<exists>x. RESUMPTION_corec f e = RESUMPTION_corec f x" by blast
  thus ?thesis
  proof coinduct
    case (resumption x)
    then obtain e where x: "x = RESUMPTION_corec f e" by blast
    thus ?case 
    proof(cases "f e")
      case (Resumption_corec r)
      thus ?thesis using x
        by(cases r)(simp_all add: RESUMPTION_corec Rep_resumption_constructors Rep_resumption)
    qed(auto simp add: RESUMPTION_corec)
  qed
qed

text {* corecursion operator for the resumption type *}

definition resumption_corec :: "('e \<Rightarrow> ('a,'b,'c,'d,'e) resumption_corec) \<Rightarrow> 'e \<Rightarrow> ('a,'b,'c,'d) resumption"
where
  "resumption_corec f e = Abs_resumption (RESUMPTION_corec f e)"

lemma resumption_corec:
  "resumption_corec f e =
  (case f e of Terminal_corec a \<Rightarrow> Terminal a
            | Linear_corec b e' \<Rightarrow> Linear b (resumption_corec f e')
            | Branch_corec c es \<Rightarrow> Branch c (\<lambda>d. resumption_corec f (es d))
            | Resumption_corec r \<Rightarrow> r)"
unfolding resumption_corec_def
apply(subst RESUMPTION_corec)
apply(auto split: resumption_corec.splits simp add: Terminal_def Linear_def Branch_def RESUMPTION_corec_type Abs_resumption_inverse Rep_resumption_inverse)
done

text {* Equality as greatest fixpoint *}

coinductive Eq_RESUMPTION :: "('c+'b+'a, 'd) Old_Datatype.dtree \<Rightarrow> ('c+'b+'a, 'd) Old_Datatype.dtree \<Rightarrow> bool"
where
  EqTERMINAL: "Eq_RESUMPTION (TERMINAL a) (TERMINAL a)"
| EqLINEAR: "Eq_RESUMPTION r r' \<Longrightarrow> Eq_RESUMPTION (LINEAR b r) (LINEAR b r')"
| EqBRANCH: "(\<And>d. Eq_RESUMPTION (rs d) (rs' d)) \<Longrightarrow> Eq_RESUMPTION (BRANCH c rs) (BRANCH c rs')"

lemma Eq_RESUMPTION_implies_ntrunc_equality:
  "Eq_RESUMPTION r r' \<Longrightarrow> ntrunc k r = ntrunc k r'"
proof(induct k arbitrary: r r' rule: less_induct)
  case (less k)
  note IH = `\<And>k' r r'. \<lbrakk>k' < k; Eq_RESUMPTION r r'\<rbrakk> \<Longrightarrow> ntrunc k' r = ntrunc k' r'`
  from `Eq_RESUMPTION r r'` show ?case
  proof cases
    case EqTERMINAL
    thus ?thesis by simp
  next
    case (EqLINEAR R R' b)
    thus ?thesis unfolding LINEAR_def
      apply(cases k, simp)
      apply(rename_tac k', case_tac k', simp)
      apply(rename_tac k'', case_tac k'', simp_all add: IH)
      done
  next
    case (EqBRANCH rs rs' c)
    thus ?thesis unfolding BRANCH_def
      apply(cases k, simp)
      apply(rename_tac k', case_tac k', simp)
      apply(rename_tac k'', case_tac k'', simp)
      apply(rename_tac k''', case_tac k''', simp_all)
      apply(rule arg_cong[where f=Old_Datatype.Lim])
      apply(rule ext)
      apply(simp add: IH)
      done
  qed
qed

lemma Eq_RESUMPTION_refl:
  assumes "r \<in> resumption"
  shows "Eq_RESUMPTION r r"
proof -
  define r' where "r' = r"
  with assms have "r = r' \<and> r \<in> resumption" by auto
  thus "Eq_RESUMPTION r r'"
  proof(coinduct)
    case (Eq_RESUMPTION r r')
    hence [simp]: "r = r'" and "r \<in> resumption" by auto
    from `r \<in> resumption` show ?case
      by(cases rule: resumption.cases) auto
  qed
qed

lemma Eq_RESUMPTION_into_resumption:
  assumes "Eq_RESUMPTION r r"
  shows "r \<in> resumption"
using assms
proof(coinduct)
  case resumption thus ?case by cases auto
qed

lemma Eq_RESUMPTION_eq:
  "Eq_RESUMPTION r r' \<longleftrightarrow> r = r' \<and> r \<in> resumption"
proof(rule iffI)
  assume "Eq_RESUMPTION r r'"
  hence "\<And>k. ntrunc k r = ntrunc k r'" by(rule Eq_RESUMPTION_implies_ntrunc_equality)
  hence "r = r'" by(rule ntrunc_equality)
  moreover with `Eq_RESUMPTION r r'` have "r \<in> resumption"
    by(auto intro: Eq_RESUMPTION_into_resumption)
  ultimately show "r = r' \<and> r \<in> resumption" ..
next
  assume "r = r' \<and> r \<in> resumption"
  thus "Eq_RESUMPTION r r'" by(blast intro: Eq_RESUMPTION_refl)
qed

lemma Eq_RESUMPTION_I [consumes 1, case_names Eq_RESUMPTION, case_conclusion Eq_RESUMPTION EqTerminal EqLinear EqBranch]:
  assumes "X r r'"
  and step: "\<And>r r'. X r r' \<Longrightarrow>
             (\<exists>a. r = TERMINAL a \<and> r' = TERMINAL a) \<or>
             (\<exists>R R' b. r = LINEAR b R \<and> r' = LINEAR b R' \<and> (X R R' \<or> Eq_RESUMPTION R R')) \<or>
             (\<exists>rs rs' c. r = BRANCH c rs \<and> r' = BRANCH c rs' \<and> (\<forall>d. X (rs d) (rs' d) \<or> Eq_RESUMPTION (rs d) (rs' d)))"
  shows "r = r'"
proof -
  from `X r r'` have "Eq_RESUMPTION r r'"
    by(coinduct)(rule step)
  thus ?thesis by(simp add: Eq_RESUMPTION_eq)
qed

lemma resumption_equalityI [consumes 1, case_names Eq_resumption, case_conclusion Eq_resumption EqTerminal EqLinear EqBranch]:
  assumes "X r r'"
  and step: "\<And>r r'. X r r' \<Longrightarrow>
             (\<exists>a. r = Terminal a \<and> r' = Terminal a) \<or>
             (\<exists>R R' b. r = Linear b R \<and> r' = Linear b R' \<and> (X R R' \<or> R = R')) \<or>
             (\<exists>rs rs' c. r = Branch c rs \<and> r' = Branch c rs' \<and> (\<forall>d. X (rs d) (rs' d) \<or> rs d = rs' d))"
  shows "r = r'"
proof -
  define M N where "M = Rep_resumption r" and "N = Rep_resumption r'"
  with `X r r'` have "\<exists>r r'. M = Rep_resumption r \<and> N = Rep_resumption r' \<and> X r r'" by blast
  hence "M = N"
  proof(coinduct rule: Eq_RESUMPTION_I)
    case (Eq_RESUMPTION M N)
    then obtain r r' where [simp]: "M = Rep_resumption r" "N = Rep_resumption r'"
      and "X r r'" by blast
    { assume "\<exists>a. r = Terminal a \<and> r' = Terminal a"
      hence ?EqTerminal by(auto simp add: Rep_resumption_constructors)
      hence ?case .. }
    moreover
    { assume "\<exists>R R' b. r = Linear b R \<and> r' = Linear b R' \<and> (X R R' \<or> R = R')"
      hence ?EqLinear
        by(clarsimp simp add: Rep_resumption_constructors Eq_RESUMPTION_eq Rep_resumption_inject Rep_resumption)
      hence ?case by blast }
    moreover
    { assume "\<exists>rs rs' c. r = Branch c rs \<and> r' = Branch c rs' \<and> (\<forall>d. X (rs d) (rs' d) \<or> rs d = rs' d)"
      hence ?EqBranch
        by(clarsimp simp add: Rep_resumption_constructors Eq_RESUMPTION_eq Rep_resumption_inject Rep_resumption)
      hence ?case by blast }
    ultimately show ?case using step[OF `X r r'`] by blast
  qed
  thus ?thesis unfolding M_def N_def by(simp add: Rep_resumption_inject)
qed

text {*
  Finality of @{text "resumption"}: Uniqueness of functions defined by corecursion.
*}

lemma equals_RESUMPTION_corec:
  assumes h: "\<And>x. h x = (case f x of Terminal_corec a \<Rightarrow> TERMINAL a
                                   | Linear_corec b x' \<Rightarrow> LINEAR b (h x')
                                   | Branch_corec c xs \<Rightarrow> BRANCH c (\<lambda>d. h (xs d))
                                   | Resumption_corec r \<Rightarrow> Rep_resumption r)"
  shows "h = RESUMPTION_corec f"
proof
  fix x
  define h' where "h' = RESUMPTION_corec f"
  have h': "\<And>x. h' x = (case f x of Terminal_corec a \<Rightarrow> TERMINAL a
                                   | Linear_corec b x' \<Rightarrow> LINEAR b (h' x')
                                   | Branch_corec c xs \<Rightarrow> BRANCH c (\<lambda>d. h' (xs d))
                                   | Resumption_corec r \<Rightarrow> Rep_resumption r)"
    unfolding h'_def by(simp add: RESUMPTION_corec)
  define M N where "M = h x" and "N = h' x"
  hence "\<exists>x. M = h x \<and> N = h' x" by blast
  thus "M = N"
  proof(coinduct rule: Eq_RESUMPTION_I)
    case (Eq_RESUMPTION M N)
    then obtain x where [simp]: "M = h x" "N = h' x" by blast
    show ?case
    proof(cases "f x")
      case (Terminal_corec a)
      with h h' have ?EqTerminal by simp
      thus ?thesis ..
    next
      case (Linear_corec b x')
      with h h' have ?EqLinear by auto
      thus ?thesis by blast
    next
      case (Branch_corec c xs)
      with h h' have ?EqBranch by auto
      thus ?thesis by blast
    next
      case (Resumption_corec r)
      thus ?thesis
        by(cases r)(simp_all add: h h' Rep_resumption_constructors Eq_RESUMPTION_refl Rep_resumption)
    qed
  qed
qed

lemma equals_resumption_corec:
  assumes h: "\<And>x. h x = (case f x of Terminal_corec a \<Rightarrow> Terminal a
                                   | Linear_corec b x' \<Rightarrow> Linear b (h x')
                                   | Branch_corec c xs \<Rightarrow> Branch c (\<lambda>d. h (xs d))
                                   | Resumption_corec r \<Rightarrow> r)"
  shows "h = resumption_corec f"
proof(rule ext)
  fix x
  { fix x
    from h[of x]
    have "Rep_resumption (h x) =
      (case f x of Terminal_corec a \<Rightarrow> TERMINAL a
                | Linear_corec b x' \<Rightarrow> LINEAR b (Rep_resumption (h x'))
                | Branch_corec c xs \<Rightarrow> BRANCH c (\<lambda>d. Rep_resumption (h (xs d)))
                | Resumption_corec r \<Rightarrow> Rep_resumption r)"
      by(auto split: resumption_corec.split simp add: Rep_resumption_constructors) }
  hence eq: "(\<lambda>x. Rep_resumption (h x)) = RESUMPTION_corec f" by(rule equals_RESUMPTION_corec)
  hence "Abs_resumption (Rep_resumption (h x)) = Abs_resumption (RESUMPTION_corec f x)"
    by(subst (asm) fun_eq_iff)(auto)
  from this[symmetric] show "h x = resumption_corec f x"
    unfolding resumption_corec_def by(simp add: Rep_resumption_inverse)
qed

end
