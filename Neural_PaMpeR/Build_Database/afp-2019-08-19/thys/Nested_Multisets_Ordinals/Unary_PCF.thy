(*  Title:       Towards Decidability of Behavioral Equivalence for Unary PCF
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Towards Decidability of Behavioral Equivalence for Unary PCF\<close>

theory Unary_PCF
  imports
    "HOL-Library.FSet"
    "HOL-Library.Countable_Set_Type"
    "HOL-Library.Nat_Bijection"
    Hereditary_Multiset
    "List-Index.List_Index"
begin

subsection \<open>Preliminaries\<close>

lemma prod_UNIV: "UNIV = UNIV \<times> UNIV"
  by auto

lemma infinite_cartesian_productI1: "infinite A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> infinite (A \<times> B)"
  by (auto dest!: finite_cartesian_productD1)


subsection \<open>Types\<close>

datatype type = \<B> ("\<B>") | Fun type type (infixr "\<rightarrow>" 65)

definition mk_fun  (infixr "\<rightarrow>\<rightarrow>" 65) where
  "Ts \<rightarrow>\<rightarrow> T = fold (\<rightarrow>) (rev Ts) T"

primrec dest_fun where
  "dest_fun \<B> = []"
| "dest_fun (T \<rightarrow> U) = T # dest_fun U"

definition arity where
  "arity T = length (dest_fun T)"

lemma mk_fun_dest_fun[simp]: "dest_fun T \<rightarrow>\<rightarrow> \<B> = T"
  by (induct T) (auto simp: mk_fun_def)

lemma dest_fun_mk_fun[simp]: "dest_fun (Ts \<rightarrow>\<rightarrow> T) = Ts @ dest_fun T"
  by (induct Ts) (auto simp: mk_fun_def)

primrec \<delta> where
  "\<delta> \<B> = HMSet {#}"
| "\<delta> (T \<rightarrow> U) = HMSet (add_mset (\<delta> T) (hmsetmset (\<delta> U)))"

lemma \<delta>_mk_fun: "\<delta> (Ts \<rightarrow>\<rightarrow> T) = HMSet (hmsetmset (\<delta> T) + mset (map \<delta> Ts))"
  by (induct Ts) (auto simp: mk_fun_def)

lemma type_induct [case_names Fun]:
  assumes
   "(\<And>T. (\<And>T1 T2. T = T1 \<rightarrow> T2 \<Longrightarrow> P T1) \<Longrightarrow>
    (\<And>T1 T2. T = T1 \<rightarrow> T2 \<Longrightarrow> P T2) \<Longrightarrow> P T)"
  shows "P T"
proof (induct T)
  case \<B>
  show ?case by (rule assms) simp_all
next
  case Fun
  show ?case by (rule assms) (insert Fun, simp_all)
qed


subsection \<open>Terms\<close>

type_synonym name = string
type_synonym idx = nat
datatype expr =
    Var "name * type" ("\<langle>_\<rangle>") | Bound idx | B bool
  | Seq expr expr  (infixr "?" 75) | App expr expr (infixl "\<cdot>" 75)
  | Abs type expr ("\<Lambda>\<langle>_\<rangle> _" [100, 100] 800)

declare [[coercion_enabled]]
declare [[coercion B]]
declare [[coercion Bound]]

notation (output) B ("_")
notation (output) Bound ("_")

primrec "open" :: "idx \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "open i t (j :: idx) = (if i = j then t else j)"
| "open i t \<langle>yU\<rangle> = \<langle>yU\<rangle>"
| "open i t (b :: bool) = b"
| "open i t (e1 ? e2) = open i t e1 ? open i t e2"
| "open i t (e1 \<cdot> e2) = open i t e1 \<cdot> open i t e2"
| "open i t (\<Lambda>\<langle>U\<rangle> e) = \<Lambda>\<langle>U\<rangle> (open (i + 1) t e)"

abbreviation "open0 \<equiv> open 0"
abbreviation "open_Var i xT \<equiv> open i \<langle>xT\<rangle>"
abbreviation "open0_Var xT \<equiv> open 0 \<langle>xT\<rangle>"

primrec "close_Var" :: "idx \<Rightarrow> name \<times> type \<Rightarrow> expr \<Rightarrow> expr" where
  "close_Var i xT (j :: idx) = j"
| "close_Var i xT \<langle>yU\<rangle> = (if xT = yU then i else \<langle>yU\<rangle>)"
| "close_Var i xT (b :: bool) = b"
| "close_Var i xT (e1 ? e2) = close_Var i xT e1 ? close_Var i xT e2"
| "close_Var i xT (e1 \<cdot> e2) = close_Var i xT e1 \<cdot> close_Var i xT e2"
| "close_Var i xT (\<Lambda>\<langle>U\<rangle> e) = \<Lambda>\<langle>U\<rangle> (close_Var (i + 1) xT e)"

abbreviation "close0_Var \<equiv> close_Var 0"

primrec "fv" :: "expr \<Rightarrow> (name \<times> type) fset" where
  "fv (j :: idx) = {||}"
| "fv \<langle>yU\<rangle> = {|yU|}"
| "fv (b :: bool) = {||}"
| "fv (e1 ? e2) = fv e1 |\<union>| fv e2"
| "fv (e1 \<cdot> e2) = fv e1 |\<union>| fv e2"
| "fv (\<Lambda>\<langle>U\<rangle> e) = fv e"

abbreviation "fresh x e \<equiv> x |\<notin>| fv e"

lemma ex_fresh: "\<exists>x. (x :: char list, T) |\<notin>| A"
proof (rule ccontr, unfold not_ex not_not)
  assume "\<forall>x. (x, T) |\<in>| A"
  then have "infinite {x. (x, T) |\<in>| A}" (is "infinite ?P")
    by (auto simp add: infinite_UNIV_listI)
  moreover
  have "?P \<subseteq> fst ` fset A"
    by (force simp: fmember.rep_eq)
  from finite_surj[OF _ this] have "finite ?P"
    by simp
  ultimately show False by blast
qed

inductive lc where
  lc_Var[simp]: "lc \<langle>xT\<rangle>"
| lc_B[simp]: "lc (b :: bool)"
| lc_Seq: "lc e1 \<Longrightarrow> lc e2 \<Longrightarrow> lc (e1 ? e2)"
| lc_App: "lc e1 \<Longrightarrow> lc e2 \<Longrightarrow> lc (e1 \<cdot> e2)"
| lc_Abs: "(\<forall>x. (x, T) |\<notin>| X \<longrightarrow> lc (open0_Var (x, T) e)) \<Longrightarrow> lc (\<Lambda>\<langle>T\<rangle> e)"

declare lc.intros[intro]

definition "body T t \<equiv> (\<exists>X. \<forall>x. (x, T) |\<notin>| X \<longrightarrow> lc (open0_Var (x, T) t))"

lemma lc_Abs_iff_body: "lc (\<Lambda>\<langle>T\<rangle> t) \<longleftrightarrow> body T t"
  unfolding body_def by (subst lc.simps) simp

lemma fv_open_Var: "fresh xT t \<Longrightarrow> fv (open_Var i xT t) |\<subseteq>| finsert xT (fv t)"
  by (induct t arbitrary: i) auto

lemma fv_close_Var[simp]: "fv (close_Var i xT t) = fv t |-| {|xT|}"
  by (induct t arbitrary: i) auto

lemma close_Var_open_Var[simp]: "fresh xT t \<Longrightarrow> close_Var i xT (open_Var i xT t) = t"
  by (induct t arbitrary: i) auto

lemma open_Var_inj: "fresh xT t \<Longrightarrow> fresh xT u \<Longrightarrow> open_Var i xT t = open_Var i xT u \<Longrightarrow> t = u"
  by (metis close_Var_open_Var)

context begin

private lemma open_Var_open_Var_close_Var: "i \<noteq> j \<Longrightarrow> xT \<noteq> yU \<Longrightarrow> fresh yU t \<Longrightarrow>
  open_Var i yU (open_Var j zV (close_Var j xT t)) = open_Var j zV (close_Var j xT (open_Var i yU t))"
  by (induct t arbitrary: i j) auto

lemma open_Var_close_Var[simp]: "lc t \<Longrightarrow> open_Var i xT (close_Var i xT t) = t"
proof (induction t arbitrary: i rule: lc.induct)
  case (lc_Abs T X e i)
  obtain x where x: "fresh (x, T) e" "(x, T) \<noteq> xT" "(x, T) |\<notin>| X"
    using ex_fresh[of _ "fv e |\<union>| finsert xT X"] by blast
  with lc_Abs.IH have "lc (open0_Var (x, T) e)"
    "open_Var (i + 1) xT (close_Var (i + 1) xT (open0_Var (x, T) e)) = open0_Var (x, T) e"
    by auto
  with x show ?case
    by (auto simp: open_Var_open_Var_close_Var
      dest: fset_mp[OF fv_open_Var, rotated]
      intro!: open_Var_inj[of "(x, T)" _ e 0])
qed auto

end

lemma close_Var_inj: "lc t \<Longrightarrow> lc u \<Longrightarrow> close_Var i xT t = close_Var i xT u \<Longrightarrow> t = u"
  by (metis open_Var_close_Var)

primrec Apps (infixl "\<bullet>" 75) where
  "f \<bullet> [] = f"
| "f \<bullet> (x # xs) = f \<cdot> x \<bullet> xs"

lemma Apps_snoc: "f \<bullet> (xs @ [x]) = f \<bullet> xs \<cdot> x"
  by (induct xs arbitrary: f) auto

lemma Apps_append: "f \<bullet> (xs @ ys) = f \<bullet>  xs \<bullet>  ys"
  by (induct xs arbitrary: f) auto

lemma Apps_inj[simp]: "f \<bullet> ts = g \<bullet> ts \<longleftrightarrow> f = g"
  by (induct ts arbitrary: f g) auto

lemma eq_Apps_conv[simp]:
  fixes i :: idx and b :: bool and f :: expr and ts :: "expr list"
  shows
    "(\<langle>m\<rangle> = f \<bullet> ts) = (\<langle>m\<rangle> = f \<and> ts = [])"
    "(f  \<bullet> ts = \<langle>m\<rangle>) = (\<langle>m\<rangle> = f \<and> ts = [])"
    "(i = f \<bullet> ts) = (i = f \<and> ts = [])"
    "(f \<bullet> ts = i) = (i = f \<and> ts = [])"
    "(b = f \<bullet> ts) = (b = f \<and> ts = [])"
    "(f \<bullet> ts = b) = (b = f \<and> ts = [])"
    "(e1 ? e2 = f \<bullet> ts) = (e1 ? e2 = f \<and> ts = [])"
    "(f \<bullet> ts = e1 ? e2) = (e1 ? e2 = f \<and> ts = [])"
    "(\<Lambda>\<langle>T\<rangle> t = f \<bullet> ts) = (\<Lambda>\<langle>T\<rangle> t = f \<and> ts = [])"
    "(f \<bullet> ts = \<Lambda>\<langle>T\<rangle> t) = (\<Lambda>\<langle>T\<rangle> t = f \<and> ts = [])"
  by (induct ts arbitrary: f) auto

lemma Apps_Var_eq[simp]: "\<langle>xT\<rangle> \<bullet> ss = \<langle>yU\<rangle> \<bullet> ts \<longleftrightarrow> xT = yU \<and> ss = ts"
proof (induct ss arbitrary: ts rule: rev_induct)
  case snoc
  then show ?case by (induct ts rule: rev_induct) (auto simp: Apps_snoc)
qed auto

lemma Apps_Abs_neq_Apps[simp, symmetric, simp]:
  "\<Lambda>\<langle>T\<rangle> r \<cdot> t \<noteq> \<langle>xT\<rangle> \<bullet> ss"
  "\<Lambda>\<langle>T\<rangle> r \<cdot> t \<noteq> (i :: idx) \<bullet> ss"
  "\<Lambda>\<langle>T\<rangle> r \<cdot> t \<noteq> (b :: bool) \<bullet> ss"
  "\<Lambda>\<langle>T\<rangle> r \<cdot> t \<noteq> (e1 ? e2) \<bullet> ss"
  by (induct ss rule: rev_induct) (auto simp: Apps_snoc)

lemma App_Abs_eq_Apps_Abs[simp]: "\<Lambda>\<langle>T\<rangle> r \<cdot> t = \<Lambda>\<langle>T'\<rangle> r' \<bullet> ss \<longleftrightarrow> T = T' \<and> r = r' \<and> ss = [t]"
  by (induct ss rule: rev_induct) (auto simp: Apps_snoc)

lemma Apps_Var_neq_Apps_Abs[simp, symmetric, simp]: "\<langle>xT\<rangle> \<bullet> ss \<noteq> \<Lambda>\<langle>T\<rangle> r \<bullet> ts"
proof (induct ss arbitrary: ts rule: rev_induct)
  case (snoc a ss)
  then show ?case by (induct ts rule: rev_induct) (auto simp: Apps_snoc)
qed simp

lemma Apps_Var_neq_Apps_beta[simp, THEN not_sym, simp]:
  "\<langle>xT\<rangle> \<bullet> ss \<noteq> \<Lambda>\<langle>T\<rangle> r \<cdot> s \<bullet> ts"
  by (metis Apps_Var_neq_Apps_Abs Apps_append Apps_snoc eq_Apps_conv(9))

lemma [simp]:
  "(\<Lambda>\<langle>T\<rangle> r \<bullet> ts = \<Lambda>\<langle>T'\<rangle> r' \<cdot> s' \<bullet> ts') = (T = T' \<and> r = r' \<and> ts = s' # ts')"
proof (induct ts arbitrary: ts' rule: rev_induct)
  case Nil
  then show ?case by (induct ts' rule: rev_induct) (auto simp: Apps_snoc)
next
  case snoc
  then show ?case by (induct ts' rule: rev_induct) (auto simp: Apps_snoc)
qed

lemma fold_eq_Bool_iff[simp]:
  "fold (\<rightarrow>) (rev Ts) T = \<B> \<longleftrightarrow> Ts = [] \<and> T = \<B>"
  "\<B> = fold (\<rightarrow>) (rev Ts) T \<longleftrightarrow> Ts = [] \<and> T = \<B>"
  by (induct Ts) auto

lemma fold_eq_Fun_iff[simp]:
  "fold (\<rightarrow>) (rev Ts) T = U \<rightarrow> V \<longleftrightarrow>
   (Ts = [] \<and> T = U \<rightarrow> V \<or> (\<exists>Us. Ts = U # Us \<and> fold (\<rightarrow>) (rev Us) T = V))"
  by (induct Ts) auto


subsection \<open>Substitution\<close>

primrec subst where
  "subst xT t \<langle>yU\<rangle> = (if xT = yU then t else \<langle>yU\<rangle>)"
| "subst xT t (i :: idx) = i"
| "subst xT t (b :: bool) = b"
| "subst xT t (e1 ? e2) = subst xT t e1 ? subst xT t e2"
| "subst xT t (e1 \<cdot> e2) = subst xT t e1 \<cdot> subst xT t e2"
| "subst xT t (\<Lambda>\<langle>T\<rangle> e) = \<Lambda>\<langle>T\<rangle> (subst xT t e)"

lemma fv_subst:
  "fv (subst xT t u) = fv u |-| {|xT|} |\<union>| (if xT |\<in>| fv u then fv t else {||})"
  by (induct u) auto

lemma subst_fresh: "fresh xT u \<Longrightarrow> subst xT t u = u"
  by (induct u) auto

context begin

private lemma open_open_id: "i \<noteq> j \<Longrightarrow> open i t (open j t' u) = open j t' u \<Longrightarrow> open i t u = u"
  by (induct u arbitrary: i j) (auto 6 0)

lemma lc_open_id: "lc u \<Longrightarrow> open k t u = u"
proof (induct u arbitrary: k rule: lc.induct)
  case (lc_Abs T X e)
  obtain x where x: "fresh (x, T) e" "(x, T) |\<notin>| X"
    using ex_fresh[of _ "fv e |\<union>| X"] by blast
  with lc_Abs show ?case
    by (auto intro: open_open_id dest: spec[of _ x] spec[of _ "Suc k"])
qed auto

lemma subst_open: "lc u \<Longrightarrow> subst xT u (open i t v) = open i (subst xT u t) (subst xT u v)"
  by (induction v arbitrary: i) (auto intro: lc_open_id[symmetric])

lemma subst_open_Var:
  "xT \<noteq> yU \<Longrightarrow> lc u \<Longrightarrow> subst xT u (open_Var i yU v) = open_Var i yU (subst xT u v)"
  by (auto simp: subst_open)

lemma subst_Apps[simp]:
  "subst xT u (f \<bullet> xs) = subst xT u f \<bullet> map (subst xT u) xs"
  by (induct xs arbitrary: f) auto

end

context begin

private lemma fresh_close_Var_id: "fresh xT t \<Longrightarrow> close_Var k xT t = t"
  by (induct t arbitrary: k) auto

lemma subst_close_Var:
  "xT \<noteq> yU \<Longrightarrow> fresh yU u \<Longrightarrow> subst xT u (close_Var i yU t) = close_Var i yU (subst xT u t)"
  by (induct t arbitrary: i) (auto simp: fresh_close_Var_id)

end

lemma subst_intro: "fresh xT t \<Longrightarrow> lc u \<Longrightarrow> open0 u t = subst xT u (open0_Var xT t)"
  by (auto simp: subst_fresh subst_open)

lemma lc_subst[simp]: "lc u \<Longrightarrow> lc t \<Longrightarrow> lc (subst xT t u)"
proof (induct u rule: lc.induct)
  case (lc_Abs T X e)
  then show ?case
    by (auto simp: subst_open_Var intro!: lc.lc_Abs[of _ "fv e |\<union>| X |\<union>| {|xT|}"])
qed auto

lemma body_subst[simp]: "body U u \<Longrightarrow> lc t \<Longrightarrow> body U (subst xT t u)"
proof (subst (asm) body_def, elim conjE exE)
  fix X
  assume [simp]: "lc t" "\<forall>x. (x, U) |\<notin>| X \<longrightarrow> lc (open0_Var (x, U) u)"
  show "body U (subst xT t u)"
  proof (unfold body_def, intro exI[of _ "finsert xT X"] conjI allI impI)
    fix x
    assume "(x, U) |\<notin>| finsert xT X"
    then show "lc (open0_Var (x, U) (subst xT t u))"
      by (auto simp: subst_open_Var[symmetric])
  qed
qed

lemma lc_open_Var: "lc u \<Longrightarrow> lc (open_Var i xT u)"
  by (simp add: lc_open_id)

lemma lc_open[simp]: "body U u \<Longrightarrow> lc t \<Longrightarrow> lc (open0 t u)"
proof (unfold body_def, elim conjE exE)
  fix X
  assume [simp]: "lc t" "\<forall>x. (x, U) |\<notin>| X \<longrightarrow> lc (open0_Var (x, U) u)"
  with ex_fresh[of _ "fv u |\<union>| X"] obtain x where [simp]: "fresh (x, U) u" "(x, U) |\<notin>| X" by blast
  show ?thesis by (subst subst_intro[of "(x, U)"]) auto
qed


subsection \<open>Typing\<close>

inductive welltyped :: "expr \<Rightarrow> type \<Rightarrow> bool" (infix ":::" 60) where
  welltyped_Var[intro!]: "\<langle>(x, T)\<rangle> ::: T"
| welltyped_B[intro!]: "(b :: bool) ::: \<B>"
| welltyped_Seq[intro!]: "e1 ::: \<B> \<Longrightarrow> e2 ::: \<B> \<Longrightarrow> e1 ? e2 ::: \<B>"
| welltyped_App[intro]: "e1 ::: T \<rightarrow> U \<Longrightarrow> e2 ::: T \<Longrightarrow> e1 \<cdot> e2 ::: U"
| welltyped_Abs[intro]: "(\<forall>x. (x, T) |\<notin>| X \<longrightarrow> open0_Var (x, T) e ::: U) \<Longrightarrow> \<Lambda>\<langle>T\<rangle> e ::: T \<rightarrow> U"

inductive_cases welltypedE[elim!]:
   "\<langle>x\<rangle> ::: T"
   "(i :: idx) ::: T"
   "(b :: bool) ::: T"
   "e1 ? e2 ::: T"
   "e1 \<cdot> e2 ::: T"
   "\<Lambda>\<langle>T\<rangle> e ::: U"

lemma welltyped_unique: "t ::: T \<Longrightarrow> t ::: U \<Longrightarrow> T = U"
proof (induction t T arbitrary: U rule: welltyped.induct)
  case (welltyped_Abs T X t U T')
  from welltyped_Abs.prems show ?case
  proof (elim welltypedE)
    fix Y U'
    obtain x where [simp]: "(x, T) |\<notin>| X" "(x, T) |\<notin>| Y"
      using ex_fresh[of _ "X |\<union>| Y"] by blast
    assume [simp]: "T' = T \<rightarrow> U'" "\<forall>x. (x, T) |\<notin>| Y \<longrightarrow> open0_Var (x, T) t ::: U'"
    show "T \<rightarrow> U = T'"
      by (auto intro: conjunct2[OF welltyped_Abs.IH[rule_format], rule_format, of x])
  qed
qed blast+

lemma welltyped_lc[simp]: "t ::: T \<Longrightarrow> lc t"
  by (induction t T rule: welltyped.induct) auto

lemma welltyped_subst[intro]:
  "u ::: U \<Longrightarrow> t ::: snd xT \<Longrightarrow> subst xT t u ::: U"
proof (induction u U rule: welltyped.induct)
  case (welltyped_Abs T' X u U)
  then show ?case unfolding subst.simps
    by (intro welltyped.welltyped_Abs[of _ "finsert xT X"]) (auto simp: subst_open_Var[symmetric])
qed auto

lemma rename_welltyped: "u ::: U \<Longrightarrow> subst (x, T) \<langle>(y, T)\<rangle> u ::: U"
  by (rule welltyped_subst) auto

lemma welltyped_Abs_fresh:
  assumes "fresh (x, T) u" "open0_Var (x, T) u ::: U"
  shows "\<Lambda>\<langle>T\<rangle> u ::: T \<rightarrow> U"
proof (intro welltyped_Abs[of _ "fv u"] allI impI)
  fix y
  assume "fresh (y, T) u"
  with assms(2) have "subst (x, T) \<langle>(y, T)\<rangle> (open0_Var (x, T) u) ::: U" (is "?t ::: _")
    by (auto intro: rename_welltyped)
  also have "?t = open0_Var (y, T) u"
    by (subst subst_intro[symmetric]) (auto simp: assms(1))
  finally show "open0_Var (y, T) u ::: U" .
qed

lemma Apps_alt: "f \<bullet> ts ::: T \<longleftrightarrow>
  (\<exists>Ts. f ::: fold (\<rightarrow>) (rev Ts) T \<and> list_all2 (:::) ts Ts)"
proof (induct ts arbitrary: f)
  case (Cons t ts)
  from Cons(1)[of "f \<cdot> t"] show ?case
    by (force simp: list_all2_Cons1)
qed simp


subsection \<open>Definition 10 and Lemma 11 from Schmidt-Schauß's paper\<close>

abbreviation "closed t \<equiv> fv t = {||}"

primrec constant0 where
  "constant0 \<B> = Var (''bool'', \<B>)"
| "constant0 (T \<rightarrow> U) = \<Lambda>\<langle>T\<rangle> (constant0 U)"

definition "constant T = \<Lambda>\<langle>\<B>\<rangle> (close0_Var (''bool'', \<B>) (constant0 T))"

lemma fv_constant0[simp]: "fv (constant0 T) = {|(''bool'', \<B>)|}"
  by (induct T) auto

lemma closed_constant[simp]: "closed (constant T)"
  unfolding constant_def by auto

lemma welltyped_constant0[simp]: "constant0 T ::: T"
  by (induct T) (auto simp: lc_open_id)

lemma lc_constant0[simp]: "lc (constant0 T)"
  using welltyped_constant0 welltyped_lc by blast

lemma welltyped_constant[simp]: "constant T ::: \<B> \<rightarrow> T"
  unfolding constant_def by (auto intro: welltyped_Abs_fresh[of "''bool''"])

definition nth_drop where
  "nth_drop i xs \<equiv> take i xs @ drop (Suc i) xs"

definition nth_arg (infixl "!-" 100) where
  "nth_arg T i \<equiv> nth (dest_fun T) i"

abbreviation ar where
  "ar T \<equiv> length (dest_fun T)"

lemma size_nth_arg[simp]: "i < ar T \<Longrightarrow> size (T !- i) < size T"
  by (induct T arbitrary: i) (force simp: nth_Cons' nth_arg_def gr0_conv_Suc)+

fun \<pi> :: "type \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> type" where
  "\<pi> T i 0 = (if i < ar T then nth_drop i (dest_fun T) \<rightarrow>\<rightarrow> \<B> else \<B>)"
| "\<pi> T i (Suc j) = (if i < ar T \<and> j < ar (T!-i)
    then \<pi> (T!-i) j 0 \<rightarrow>
      map (\<pi> (T!-i) j o Suc) [0 ..< ar (T!-i!-j)] \<rightarrow>\<rightarrow> \<pi> T i 0 else \<B>)"

theorem \<pi>_induct[rotated -2, consumes 2, case_names 0 Suc]:
  assumes "\<And>T i. i < ar T \<Longrightarrow> P T i 0"
    and "\<And>T i j. i < ar T \<Longrightarrow> j < ar (T !- i) \<Longrightarrow> P (T !- i) j 0 \<Longrightarrow>
       (\<forall>x < ar (T !- i !- j). P (T !- i) j (x + 1)) \<Longrightarrow> P T i (j + 1)"
  shows "i < ar T \<Longrightarrow> j \<le> ar (T !- i) \<Longrightarrow> P T i j"
  by (induct T i j rule: \<pi>.induct) (auto intro: assms[simplified])

definition \<epsilon> :: "type \<Rightarrow> nat \<Rightarrow> type" where
  "\<epsilon> T i = \<pi> T i 0 \<rightarrow> map (\<pi> T i o Suc) [0 ..< ar (T!-i)] \<rightarrow>\<rightarrow> T"

definition Abss ("\<Lambda>[_] _" [100, 100] 800) where
  "\<Lambda>[xTs] b = fold (\<lambda>xT t. \<Lambda>\<langle>snd xT\<rangle> close0_Var xT t) (rev xTs) b"

definition Seqs (infixr "??" 75) where
  "ts ?? t = fold (\<lambda>u t. u ? t) (rev ts) t"

definition "variant k base = base @ replicate k CHR ''*''"

lemma variant_inj: "variant i base = variant j base \<Longrightarrow> i = j"
  unfolding variant_def by auto

lemma variant_inj2:
  "CHR ''*'' \<notin> set b1 \<Longrightarrow> CHR ''*'' \<notin> set b2 \<Longrightarrow> variant i b1 = variant j b2 \<Longrightarrow> b1 = b2"
  unfolding variant_def
  by (auto simp: append_eq_append_conv2)
    (metis Nil_is_append_conv hd_append2 hd_in_set hd_rev last_ConsR
     last_snoc replicate_append_same rev_replicate)+

fun E :: "type \<Rightarrow> nat \<Rightarrow> expr" and P :: "type \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> expr" where
  "E T i = (if i < ar T then (let
       Ti = T!-i;
       x = \<lambda>k. (variant k ''x'', T!-k);
       xs = map x [0 ..< ar T];
       xx_var = \<langle>nth xs i\<rangle>;
       x_vars = map (\<lambda>x. \<langle>x\<rangle>) (nth_drop i xs);
       yy = (''z'', \<pi> T i 0);
       yy_var = \<langle>yy\<rangle>;
       y = \<lambda>j. (variant j ''y'', \<pi> T i (j + 1));
       ys = map y [0 ..< ar Ti];
       e = \<lambda>j. \<langle>y j\<rangle> \<bullet> (P Ti j 0 \<cdot> xx_var # map (\<lambda>k. P Ti j (k + 1) \<cdot> xx_var) [0 ..< ar (Ti!-j)]);
       guards = map (\<lambda>i. xx_var \<bullet>
           map (\<lambda>j. constant (Ti!-j) \<cdot> (if i = j then e i \<bullet> x_vars else True)) [0 ..< ar Ti])
         [0 ..< ar Ti]
     in \<Lambda>[(yy # ys @ xs)] (guards ?? (yy_var \<bullet> x_vars))) else constant (\<epsilon> T i) \<cdot> False)"
| "P T i 0 =
     (if i < ar T then (let
       f = (''f'', T);
       f_var = \<langle>f\<rangle>;
       x = \<lambda>k. (variant k ''x'', T!-k);
       xs = nth_drop i (map x [0 ..< ar T]);
       x_vars = insert_nth i (constant (T!-i) \<cdot> True) (map (\<lambda>x. \<langle>x\<rangle>) xs)
     in \<Lambda>[(f # xs)] (f_var \<bullet> x_vars)) else constant (T \<rightarrow> \<pi> T i 0) \<cdot> False)"
| "P T i (Suc j) = (if i < ar T \<and> j < ar (T!-i) then (let
       Ti = T!-i;
       Tij = Ti!-j;
       f = (''f'', T);
       f_var = \<langle>f\<rangle>;
       x = \<lambda>k. (variant k ''x'', T!-k);
       xs = nth_drop i (map x [0 ..< ar T]);
       yy = (''z'', \<pi> Ti j 0);
       yy_var = \<langle>yy\<rangle>;
       y = \<lambda>k. (variant k ''y'', \<pi> Ti j (k + 1));
       ys = map y [0 ..< ar Tij];
       y_vars = yy_var # map (\<lambda>x. \<langle>x\<rangle>) ys;
       x_vars = insert_nth i (E Ti j \<bullet> y_vars) (map (\<lambda>x. \<langle>x\<rangle>) xs)
     in \<Lambda>[(f # yy # ys @ xs)] (f_var \<bullet> x_vars)) else constant (T \<rightarrow> \<pi> T i (j + 1)) \<cdot> False)"

lemma Abss_Nil[simp]: "\<Lambda>[[]] b = b"
  unfolding Abss_def by simp

lemma Abss_Cons[simp]: "\<Lambda>[(x#xs)] b = \<Lambda>\<langle>snd x\<rangle> (close0_Var x (\<Lambda>[xs] b))"
  unfolding Abss_def by simp

lemma welltyped_Abss: "b ::: U \<Longrightarrow> T = map snd xTs \<rightarrow>\<rightarrow> U \<Longrightarrow> \<Lambda>[xTs] b ::: T"
  by (hypsubst_thin, induct xTs) (auto simp: mk_fun_def intro!: welltyped_Abs_fresh)

lemma welltyped_Apps: "list_all2 (:::) ts Ts \<Longrightarrow> f ::: Ts \<rightarrow>\<rightarrow> U \<Longrightarrow> f \<bullet> ts ::: U"
  by (induct ts Ts arbitrary: f rule: list.rel_induct) (auto simp: mk_fun_def)

lemma welltyped_open_Var_close_Var[intro!]:
  "t ::: T \<Longrightarrow> open0_Var xT (close0_Var xT t) ::: T"
  by auto

lemma welltyped_Var_iff[simp]:
  "\<langle>(x, T)\<rangle> ::: U \<longleftrightarrow> T = U"
  by auto

lemma welltyped_bool_iff[simp]: "(b :: bool) ::: T \<longleftrightarrow> T = \<B>"
  by auto

lemma welltyped_constant0_iff[simp]: "constant0 T ::: U \<longleftrightarrow> (U = T)"
  by (induct T arbitrary: U) (auto simp: ex_fresh lc_open_id)

lemma welltyped_constant_iff[simp]: "constant T ::: U \<longleftrightarrow> (U = \<B> \<rightarrow> T)"
  unfolding constant_def
proof (intro iffI, elim welltypedE, hypsubst_thin, unfold type.inject simp_thms)
  fix X U
  assume "\<forall>x. (x, \<B>) |\<notin>| X \<longrightarrow> open0_Var (x, \<B>) (close0_Var (''bool'', \<B>) (constant0 T)) ::: U"
  moreover obtain x where "(x, \<B>) |\<notin>| X" using ex_fresh[of \<B> X] by blast
  ultimately have "open0_Var (x, \<B>) (close0_Var (''bool'', \<B>) (constant0 T)) ::: U" by simp
  then have "open0_Var (''bool'', \<B>) (close0_Var (''bool'', \<B>) (constant0 T)) ::: U"
    using rename_welltyped[of \<open>open0_Var (x, \<B>) (close0_Var (''bool'', \<B>) (constant0 T))\<close>
       U x \<B> "''bool''"]
    by (auto simp: subst_open subst_fresh)
  then show "U = T" by auto
qed (auto intro!: welltyped_Abs_fresh)

lemma welltyped_Seq_iff[simp]: "e1 ? e2 ::: T \<longleftrightarrow> (T = \<B> \<and> e1 ::: \<B> \<and> e2 ::: \<B>)"
  by auto

lemma welltyped_Seqs_iff[simp]: "es ?? e ::: T \<longleftrightarrow>
  ((es \<noteq> [] \<longrightarrow> T = \<B>) \<and> (\<forall>e \<in> set es. e ::: \<B>) \<and> e ::: T)"
  by (induct es arbitrary: e) (auto simp: Seqs_def)

lemma welltyped_App_iff[simp]: "f \<cdot> t ::: U \<longleftrightarrow> (\<exists>T. f ::: T \<rightarrow> U \<and> t ::: T)"
  by auto

lemma welltyped_Apps_iff[simp]: "f \<bullet> ts ::: U \<longleftrightarrow> (\<exists>Ts. f ::: Ts \<rightarrow>\<rightarrow> U \<and> list_all2 (:::) ts Ts)"
  by (induct ts arbitrary: f) (auto 0 3 simp: mk_fun_def list_all2_Cons1 intro: exI[of _ "_ # _"])

lemma eq_mk_fun_iff[simp]: "T = Ts \<rightarrow>\<rightarrow> \<B> \<longleftrightarrow> Ts = dest_fun T"
  by auto

lemma map_nth_eq_drop_take[simp]: "j \<le> length xs \<Longrightarrow> map (nth xs) [i ..< j] = drop i (take j xs)"
  by (induct j) (auto simp: take_Suc_conv_app_nth)

lemma dest_fun_\<pi>_0: "i < ar T \<Longrightarrow> dest_fun (\<pi> T i 0) = nth_drop i (dest_fun T)"
  by auto

lemma welltyped_E: "E T i ::: \<epsilon> T i" and welltyped_P: "P T i j ::: T \<rightarrow> \<pi> T i j"
proof (induct T i and T i j rule: E_P.induct)
  case (1 T i)
  note P.simps[simp del] \<pi>.simps[simp del] \<epsilon>_def[simp] nth_drop_def[simp] nth_arg_def[simp]
  from 1(1)[OF _ refl refl refl refl refl refl refl refl refl]
       1(2)[OF _ refl refl refl refl refl refl refl refl refl]
  show ?case
    by (auto 0 4 simp: Let_def o_def take_map[symmetric] drop_map[symmetric]
      list_all2_conv_all_nth nth_append min_def dest_fun_\<pi>_0 \<pi>.simps[of T i]
      intro!: welltyped_Abs_fresh welltyped_Abss[of _ \<B>])
next
  case (2 T i)
  show ?case
    by (auto simp: Let_def take_map drop_map o_def list_all2_conv_all_nth nth_append nth_Cons'
       nth_drop_def nth_arg_def
      intro!: welltyped_constant welltyped_Abs_fresh welltyped_Abss[of _ \<B>])
next
  case (3 T i j)
  note E.simps[simp del] \<pi>.simps[simp del] Abss_Cons[simp del] \<epsilon>_def[simp]
    nth_drop_def[simp] nth_arg_def[simp]
  from 3(1)[OF _ refl refl refl refl refl refl refl refl refl refl refl]
  show ?case
    by (auto 0 3 simp: Let_def o_def take_map[symmetric] drop_map[symmetric]
      list_all2_conv_all_nth nth_append nth_Cons' min_def \<pi>.simps[of T i]
      intro!: welltyped_Abs_fresh welltyped_Abss[of _ \<B>])
qed

lemma \<delta>_gt_0[simp]: "T \<noteq> \<B> \<Longrightarrow> HMSet {#} < \<delta> T"
  by (cases T) auto

lemma mset_nth_drop_less: "i < length xs \<Longrightarrow> mset (nth_drop i xs) < mset xs"
  by (induct xs arbitrary: i) (auto simp: take_Cons' nth_drop_def gr0_conv_Suc)

lemma map_nth_drop: "i < length xs \<Longrightarrow> map f (nth_drop i xs) = nth_drop i (map f xs)"
  by (induct xs arbitrary: i) (auto simp: take_Cons' nth_drop_def gr0_conv_Suc)

lemma empty_less_mset: "{#} < mset xs \<longleftrightarrow> xs \<noteq> []"
  by auto

lemma dest_fun_alt: "dest_fun T = map (\<lambda>i. T !- i) [0..<ar T]"
  unfolding list_eq_iff_nth_eq nth_arg_def by auto

context notes \<pi>.simps[simp del] notes One_nat_def[simp del] begin

lemma \<delta>_\<pi>:
  assumes "i < ar T" "j \<le> ar (T !- i)"
  shows "\<delta> (\<pi> T i j) < \<delta> T"
using assms proof (induct T i j rule: \<pi>_induct)
  fix T i
  assume "i < ar T"
  then show "\<delta> (\<pi> T i 0) < \<delta> T"
    by (subst (2) mk_fun_dest_fun[symmetric, of T], unfold \<delta>_mk_fun)
      (auto simp: \<delta>_mk_fun mset_map[symmetric] take_map[symmetric] drop_map[symmetric] \<pi>.simps
        mset_nth_drop_less map_nth_drop simp del: mset_map)
next
  fix T i j
  let ?Ti = "T !- i"
  assume [rule_format, simp]: "i < ar T" "j < ar ?Ti" "\<delta> (\<pi> ?Ti j 0) < \<delta> ?Ti"
    "\<forall>k < ar (?Ti !- j). \<delta> (\<pi> ?Ti j (k + 1)) < \<delta> ?Ti"
  define X and Y and M where
    [simp]: "X = {#\<delta> ?Ti#}" and
    [simp]: "Y = {#\<delta> (\<pi> ?Ti j 0)#} + {#\<delta> (\<pi> ?Ti j (k + 1)). k \<in># mset [0 ..< ar (?Ti !- j)]#}" and
    [simp]: "M \<equiv> {# \<delta> z. z \<in># mset (nth_drop i (dest_fun T))#}"
  have "\<delta> (\<pi> T i (j + 1)) = HMSet (Y + M)"
    by (auto simp: One_nat_def \<pi>.simps \<delta>_mk_fun)
  also have "Y + M < X + M"
    unfolding less_multiset\<^sub>D\<^sub>M by (rule exI[of _ "X"], rule exI[of _ "Y"]) auto
  also have "HMSet (X + M) = \<delta> T"
    unfolding M_def
    by (subst (2) mk_fun_dest_fun[symmetric, of T], subst (2) id_take_nth_drop[of i "dest_fun T"])
      (auto simp: \<delta>_mk_fun nth_arg_def nth_drop_def)
  finally show "\<delta> (\<pi> T i (j + 1)) < \<delta> T" by simp
qed

end

end
