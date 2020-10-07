(*
  Boolean Expression Checkers Based on Binary Decision Trees
  Author: Tobias Nipkow
*)

theory Boolean_Expression_Checkers
  imports Main "HOL-Library.Mapping"
begin

section \<open>Tautology (etc) Checking via Binary Decision Trees\<close>

subsection \<open>Binary Decision Trees\<close>

datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex"

fun val_ifex :: "'a ifex \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "val_ifex Trueif s = True"
| "val_ifex Falseif s = False"
| "val_ifex (IF n t1 t2) s = (if s n then val_ifex t1 s else val_ifex t2 s)"

subsubsection \<open>Environment\<close>

text \<open>Environments are substitutions of values for variables:\<close>

type_synonym 'a env_bool = "('a, bool) mapping"

definition agree :: "('a \<Rightarrow> bool) \<Rightarrow> 'a env_bool \<Rightarrow> bool"
where
  "agree s env = (\<forall>x b. Mapping.lookup env x = Some b \<longrightarrow> s x = b)"

lemma agree_Nil: 
  "agree s Mapping.empty"
  by (simp add: agree_def lookup_empty)

lemma lookup_update_unfold: 
  "Mapping.lookup (Mapping.update k v m) k' = (if k = k' then Some v else Mapping.lookup m k')"
  using lookup_update lookup_update_neq by metis

lemma agree_Cons: 
  "x \<notin> Mapping.keys env \<Longrightarrow> agree s (Mapping.update x b env) = ((if b then s x else \<not> s x) \<and> agree s env)"
  by (simp add: agree_def lookup_update_unfold; unfold keys_is_none_rep lookup_update_unfold Option.is_none_def; blast)

lemma agreeDT:
  "agree s env \<Longrightarrow> Mapping.lookup env x = Some True \<Longrightarrow> s x"
  by (simp add: agree_def)

lemma agreeDF:
  "agree s env \<Longrightarrow> Mapping.lookup env x = Some False \<Longrightarrow> \<not>s x"
  by (auto simp add: agree_def)

subsection \<open>Recursive Tautology Checker\<close>

text \<open>Provided for completeness. However, it is recommend to use the checkers based on reduced trees.\<close>

fun taut_test_rec :: "'a ifex \<Rightarrow> 'a env_bool \<Rightarrow> bool" 
where
  "taut_test_rec Trueif env = True" 
| "taut_test_rec Falseif env = False" 
| "taut_test_rec (IF x t1 t2) env = (case Mapping.lookup env x of
  Some b \<Rightarrow> taut_test_rec (if b then t1 else t2) env |
  None \<Rightarrow> taut_test_rec t1 (Mapping.update x True env) \<and> taut_test_rec t2 (Mapping.update x False env))"

lemma taut_test_rec: 
  "taut_test_rec t env = (\<forall>s. agree s env \<longrightarrow> val_ifex t s)"
proof (induction t arbitrary: env)
  case Falseif
    have "agree (\<lambda>x. the (Mapping.lookup env x)) env" 
      by (auto simp: agree_def)
    thus ?case 
      by auto
next
  case (IF x t1 t2) 
    thus ?case
    proof (cases "Mapping.lookup env x")
      case None 
        with IF show ?thesis 
          by simp (metis is_none_simps(1) agree_Cons keys_is_none_rep)
    qed (simp add: agree_def)
qed simp

definition taut_test_ifex :: "'a ifex \<Rightarrow> bool" 
where
  "taut_test_ifex t = taut_test_rec t Mapping.empty"

corollary taut_test_ifex: 
  "taut_test_ifex t = (\<forall>s. val_ifex t s)"
  by (auto simp: taut_test_ifex_def taut_test_rec agree_Nil)

subsection \<open>Reduced Binary Decision Trees\<close>

subsubsection \<open>Normalisation\<close>

text \<open>A normalisation avoiding duplicate variables and collapsing @{term "If x t t"} to \<open>t\<close>.\<close>

definition mkIF :: "'a \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" 
where
  "mkIF x t1 t2 = (if t1=t2 then t1 else IF x t1 t2)"

fun reduce :: "'a env_bool \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex"
where
  "reduce env (IF x t1 t2) = (case Mapping.lookup env x of
     None \<Rightarrow> mkIF x (reduce (Mapping.update x True env) t1) (reduce (Mapping.update x False env) t2) |
     Some b \<Rightarrow> reduce env (if b then t1 else t2))" 
| "reduce _ t = t"

primrec normif :: "'a env_bool \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" 
where
  "normif env Trueif t1 t2 = reduce env t1" 
| "normif env Falseif t1 t2 = reduce env t2" 
| "normif env (IF x t1 t2) t3 t4 =
    (case Mapping.lookup env x of
       None \<Rightarrow> mkIF x (normif (Mapping.update x True env) t1 t3 t4) (normif (Mapping.update x False env) t2 t3 t4) |
       Some b \<Rightarrow> if b then normif env t1 t3 t4 else normif env t2 t3 t4)"

subsubsection \<open>Functional Correctness Proof\<close>

lemma val_mkIF: 
  "val_ifex (mkIF x t1 t2) s = val_ifex (IF x t1 t2) s"
  by (auto simp: mkIF_def Let_def)

theorem val_reduce: 
  "agree s env \<Longrightarrow> val_ifex (reduce env t) s = val_ifex t s"
  by (induction t arbitrary: s env)
     (auto simp: map_of_eq_None_iff val_mkIF agree_Cons Let_def keys_is_none_rep
           dest: agreeDT agreeDF split: option.splits) 

lemma val_normif: 
  "agree s env \<Longrightarrow> val_ifex (normif env t t1 t2) s = val_ifex (if val_ifex t s then t1 else t2) s"
  by (induct t arbitrary: t1 t2 s env)
     (auto simp: val_reduce val_mkIF agree_Cons map_of_eq_None_iff keys_is_none_rep
           dest: agreeDT agreeDF split: option.splits)   

subsubsection \<open>Reduced If-Expressions\<close>

text \<open>An expression reduced iff no variable appears twice on any branch and there is no subexpression @{term "IF x t t"}.\<close>

fun reduced :: "'a ifex \<Rightarrow> 'a set \<Rightarrow> bool" where
"reduced (IF x t1 t2) X =
  (x \<notin> X \<and> t1 \<noteq> t2 \<and> reduced t1 (insert x X) \<and> reduced t2 (insert x X))" |
"reduced _ _ = True"

lemma reduced_antimono: 
  "X \<subseteq> Y \<Longrightarrow> reduced t Y \<Longrightarrow> reduced t X"
  by (induction t arbitrary: X Y)
     (auto, (metis insert_mono)+)

lemma reduced_mkIF: 
  "x \<notin> X \<Longrightarrow> reduced t1 (insert x X) \<Longrightarrow> reduced t2 (insert x X) \<Longrightarrow> reduced (mkIF x t1 t2) X"
  by (auto simp: mkIF_def intro:reduced_antimono)

lemma reduced_reduce:
  "reduced (reduce env t) (Mapping.keys env)"
proof(induction t arbitrary: env)
  case (IF x t1 t2)
    thus ?case 
      using IF.IH(1) IF.IH(2)
      apply (auto simp: map_of_eq_None_iff image_iff reduced_mkIF split: option.split) 
      by (metis is_none_code(1) keys_is_none_rep keys_update reduced_mkIF)
qed auto

lemma reduced_normif:
  "reduced (normif env t t1 t2) (Mapping.keys env)"
proof(induction t arbitrary: t1 t2 env)
  case (IF x s1 s2)
  thus ?case using IF.IH
    apply (auto simp: reduced_mkIF map_of_eq_None_iff split: option.split) 
    by (metis is_none_code(1) keys_is_none_rep keys_update reduced_mkIF)
qed (auto simp: reduced_reduce)

subsubsection \<open>Checkers Based on Reduced Binary Decision Trees\<close>

text \<open>The checkers are parameterized over the translation function to binary decision trees. 
  They rely on the fact that @{term ifex_of} produces reduced trees\<close>

definition taut_test :: "('a \<Rightarrow> 'b ifex) \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "taut_test ifex_of b = (ifex_of b = Trueif)"

definition sat_test :: "('a \<Rightarrow> 'b ifex) \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "sat_test ifex_of b = (ifex_of b \<noteq> Falseif)"

definition impl_test :: "('a \<Rightarrow> 'b ifex) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "impl_test ifex_of b1 b2 = (normif Mapping.empty (ifex_of b1) (ifex_of b2) Trueif = Trueif)"

definition equiv_test :: "('a \<Rightarrow> 'b ifex) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "equiv_test ifex_of b1 b2 = (let t1 = ifex_of b1; t2 = ifex_of b2 
    in Trueif = normif Mapping.empty t1 t2 (normif Mapping.empty t2 Falseif Trueif))"

locale reduced_bdt_checkers = 
  fixes
    ifex_of :: "'b \<Rightarrow> 'a ifex"
  fixes
    val :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes
    val_ifex: "val_ifex (ifex_of b) s = val b s"
  assumes 
    reduced_ifex: "reduced (ifex_of b) {}"
begin

text \<open>Proof that reduced if-expressions are @{const Trueif}, @{const Falseif}
or can evaluate to both @{const True} and @{const False}.\<close>

lemma same_val_if_reduced:
  "reduced t X \<Longrightarrow> \<forall>x. x \<notin> X \<longrightarrow> s1 x = s2 x \<Longrightarrow> val_ifex t s1 = val_ifex t s2"
  by (induction t arbitrary: X) auto

lemma reduced_IF_depends: 
  "\<lbrakk> reduced t X; t \<noteq> Trueif; t \<noteq> Falseif \<rbrakk> \<Longrightarrow> \<exists>s1 s2. val_ifex t s1 \<noteq> val_ifex t s2"
proof(induction t arbitrary: X)
  case (IF x t1 t2)
  let ?t = "IF x t1 t2"
  have 1: "reduced t1 (insert x X)" using IF.prems(1) by simp
  have 2: "reduced t2 (insert x X)" using IF.prems(1) by simp
  show ?case
  proof(cases t1)
    case [simp]: Trueif
    show ?thesis
    proof (cases t2)
      case Trueif thus ?thesis using IF.prems(1) by simp
    next
      case Falseif
      hence "val_ifex ?t (\<lambda>_. True) \<noteq> val_ifex ?t (\<lambda>_. False)" by simp
      thus ?thesis by blast
    next
      case IF
      then obtain s1 s2 where "val_ifex t2 s1 \<noteq> val_ifex t2 s2"
        using IF.IH(2)[OF 2] IF.prems(1) by auto
      hence "val_ifex ?t (s1(x:=False)) \<noteq> val_ifex ?t (s2(x:=False))"
        using same_val_if_reduced[OF 2, of "s1(x:=False)" s1]
          same_val_if_reduced[OF 2, of "s2(x:=False)" s2] by simp
      thus ?thesis by blast
    qed
  next
    case [simp]: Falseif
    show ?thesis
    proof (cases t2)
      case Falseif thus ?thesis using IF.prems(1) by simp
    next
      case Trueif
      hence "val_ifex ?t (\<lambda>_. True) \<noteq> val_ifex ?t (\<lambda>_. False)" by simp
      thus ?thesis by blast
    next
      case IF
      then obtain s1 s2 where "val_ifex t2 s1 \<noteq> val_ifex t2 s2"
        using IF.IH(2)[OF 2] IF.prems(1) by auto
      hence "val_ifex ?t (s1(x:=False)) \<noteq> val_ifex ?t (s2(x:=False))"
        using same_val_if_reduced[OF 2, of "s1(x:=False)" s1]
          same_val_if_reduced[OF 2, of "s2(x:=False)" s2] by simp
      thus ?thesis by blast
    qed
  next
    case IF
    then obtain s1 s2 where "val_ifex t1 s1 \<noteq> val_ifex t1 s2"
      using IF.IH(1)[OF 1] IF.prems(1) by auto
    hence "val_ifex ?t (s1(x:=True)) \<noteq> val_ifex ?t (s2(x:=True))"
      using same_val_if_reduced[OF 1, of "s1(x:=True)" s1]
          same_val_if_reduced[OF 1, of "s2(x:=True)" s2] by simp
    thus ?thesis by blast
  qed
qed auto

corollary taut_test: 
  "taut_test ifex_of b = (\<forall>s. val b s)"    
  by (metis taut_test_def reduced_IF_depends[OF reduced_ifex] val_ifex val_ifex.simps(1,2))

corollary sat_test: 
  "sat_test ifex_of b = (\<exists>s. val b s)"
  by (metis sat_test_def reduced_IF_depends[OF reduced_ifex] val_ifex val_ifex.simps(1,2))

corollary impl_test: 
  "impl_test ifex_of b1 b2 = (\<forall>s. val b1 s \<longrightarrow> val b2 s)"
proof -
  have "impl_test ifex_of b1 b2 = (\<forall>s. val_ifex (normif Mapping.empty (ifex_of b1) (ifex_of b2) Trueif) s)"
    using reduced_IF_depends[OF reduced_normif] by (fastforce  simp: impl_test_def)
  also
  have "(\<forall>s. val_ifex (normif Mapping.empty (ifex_of b1) (ifex_of b2) Trueif) s) \<longleftrightarrow> (\<forall>s. val b1 s \<longrightarrow> val b2 s)"
    using reduced_IF_depends[OF reduced_ifex] val_ifex unfolding val_normif[OF agree_Nil] by simp
  finally
  show ?thesis .
qed

corollary equiv_test: 
  "equiv_test ifex_of b1 b2 = (\<forall>s. val b1 s = val b2 s)"
proof -
  have "equiv_test ifex_of b1 b2 = (\<forall>s. val_ifex (let t1 = ifex_of b1; t2 = ifex_of b2 in normif Mapping.empty t1 t2 (normif Mapping.empty t2 Falseif Trueif)) s)"
    by (simp add: equiv_test_def Let_def; insert reduced_IF_depends[OF reduced_normif]; force)
  moreover
  {
    fix s
    have "val_ifex (let t1 = ifex_of b1; t2 = ifex_of b2 in normif Mapping.empty t1 t2 (normif Mapping.empty t2 Falseif Trueif)) s
      = (val b1 s = val b2 s)"
      using val_ifex by (simp add: Let_def val_normif[OF agree_Nil]) 
  }
  ultimately
  show ?thesis 
    by blast
qed

end

subsection \<open>Boolean Expressions\<close>

text \<open>This is the simplified interface to the tautology checker. If you have your own type of Boolean 
expressions you can either define your own translation to reduced binary decision trees or you can just 
translate into this type.\<close>

datatype 'a bool_expr =
  Const_bool_expr bool |
  Atom_bool_expr 'a |
  Neg_bool_expr "'a bool_expr" |
  And_bool_expr "'a bool_expr" "'a bool_expr" |
  Or_bool_expr "'a bool_expr" "'a bool_expr" |
  Imp_bool_expr "'a bool_expr" "'a bool_expr" |
  Iff_bool_expr "'a bool_expr" "'a bool_expr"

primrec val_bool_expr :: "'a bool_expr \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"val_bool_expr (Const_bool_expr b) s = b" |
"val_bool_expr (Atom_bool_expr x) s = s x" |
"val_bool_expr (Neg_bool_expr b) s = (\<not> val_bool_expr b s)" |
"val_bool_expr (And_bool_expr b1 b2) s = (val_bool_expr b1 s \<and> val_bool_expr b2 s)" |
"val_bool_expr (Or_bool_expr b1 b2) s = (val_bool_expr b1 s \<or> val_bool_expr b2 s)" |
"val_bool_expr (Imp_bool_expr b1 b2) s = (val_bool_expr b1 s \<longrightarrow> val_bool_expr b2 s)" |
"val_bool_expr (Iff_bool_expr b1 b2) s = (val_bool_expr b1 s = val_bool_expr b2 s)"

fun ifex_of :: "'a bool_expr \<Rightarrow> 'a ifex" where
"ifex_of (Const_bool_expr b) = (if b then Trueif else Falseif)" |
"ifex_of (Atom_bool_expr x)   = IF x Trueif Falseif" |
"ifex_of (Neg_bool_expr b)   = normif Mapping.empty (ifex_of b) Falseif Trueif" |
"ifex_of (And_bool_expr b1 b2) = normif Mapping.empty (ifex_of b1) (ifex_of b2) Falseif" |
"ifex_of (Or_bool_expr b1 b2) = normif Mapping.empty (ifex_of b1) Trueif (ifex_of b2)" |
"ifex_of (Imp_bool_expr b1 b2) = normif Mapping.empty (ifex_of b1) (ifex_of b2) Trueif" |
"ifex_of (Iff_bool_expr b1 b2) = (let t1 = ifex_of b1; t2 = ifex_of b2 in
   normif Mapping.empty t1 t2 (normif Mapping.empty t2 Falseif Trueif))"

theorem val_ifex:
  "val_ifex (ifex_of b) s = val_bool_expr b s"
  by (induct_tac b) (auto simp: val_normif agree_Nil Let_def)

theorem reduced_ifex: 
  "reduced (ifex_of b) {}"
  by (induction b) (simp add: Let_def; metis keys_empty reduced_normif)+

definition "bool_taut_test \<equiv> taut_test ifex_of"
definition "bool_sat_test \<equiv> sat_test ifex_of"
definition "bool_impl_test \<equiv> impl_test ifex_of"
definition "bool_equiv_test \<equiv> equiv_test ifex_of"

lemma bool_tests:
  "bool_taut_test b = (\<forall>s. val_bool_expr b s)" (is ?t1)
  "bool_sat_test b = (\<exists>s. val_bool_expr b s)" (is ?t2)
  "bool_impl_test b1 b2 = (\<forall>s. val_bool_expr b1 s \<longrightarrow> val_bool_expr b2 s)" (is ?t3)
  "bool_equiv_test b1 b2 = (\<forall>s. val_bool_expr b1 s \<longleftrightarrow> val_bool_expr b2 s)" (is ?t4)
proof -
  interpret reduced_bdt_checkers ifex_of val_bool_expr
    by (unfold_locales; insert val_ifex reduced_ifex; blast)
  show ?t1 ?t2 ?t3 ?t4
    by (simp_all add: bool_taut_test_def bool_sat_test_def bool_impl_test_def bool_equiv_test_def taut_test sat_test impl_test equiv_test) 
qed

end
