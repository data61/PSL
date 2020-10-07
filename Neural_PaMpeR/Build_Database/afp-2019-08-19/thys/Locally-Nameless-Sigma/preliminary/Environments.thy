(*  Title:      Environments.thy
    Author:     Florian Kammuller and Henry Sudhof, 2008
*)

theory Environments imports Main begin 

subsection \<open>Type Environments\<close>
text\<open>Some basic properties of our variable environments.\<close>

(* We use a wrapped map and an error element *)
datatype 'a environment = 
  Env "(string \<rightharpoonup> 'a)"
| Malformed

(* Adding an entry to an environment. Overwriting an entry switches to the error state*)
primrec
  add :: "('a environment) \<Rightarrow> string \<Rightarrow> 'a \<Rightarrow> 'a environment"    
  ("_\<lparr>_:_\<rparr>" [90, 0, 0] 91)
where
  add_def: "(Env e)\<lparr>x:a\<rparr> = 
     (if (x \<notin> dom e) then (Env (e(x \<mapsto> a))) else Malformed)" 
| add_mal: "Malformed\<lparr>x:a\<rparr> = Malformed"

(* domains of environments, i.e. the set of used variable names *)
primrec
  env_dom :: "('a environment) \<Rightarrow> string set"
where
  env_dom_def: "env_dom (Env e) = dom e" 
| env_dom_mal: "env_dom (Malformed) = {}" 

(* Retrieving an entry from an environment *)
primrec
  env_get :: "('a environment) \<Rightarrow> string  \<Rightarrow> 'a option" ("_!_")
where
  env_get_def: "env_get (Env e) x = e x " 
| env_get_mal: "env_get (Malformed) x = None " 

(* Environment well-formedness. For now weaker than usually recommended for LN; just finiteness and not being the error value *)
primrec ok::"('a environment) \<Rightarrow> bool"
where
  OK_Env [intro]: "ok (Env e) = (finite (dom e))"
| OK_Mal [intro]: "ok Malformed = False"

(* commutativity of add *)
lemma subst_add:
  fixes x y
  assumes "x \<noteq> y"
  shows "e\<lparr>x:a\<rparr>\<lparr>y:b\<rparr> = e\<lparr>y:b\<rparr>\<lparr>x:a\<rparr>"
proof (cases e)
  case Malformed thus ?thesis by simp
next
  case (Env f) with assms show ?thesis
  proof (cases "x \<in> dom f", simp)
    case False with assms Env show ?thesis
    proof (cases "y \<in> dom f", simp_all, intro ext)
      fix xa :: string
      case False with assms show "(f(x \<mapsto> a,y \<mapsto> b)) xa = (f(y \<mapsto> b,x \<mapsto> a)) xa"
      proof (cases "xa = x", simp)
        case False with assms show ?thesis
          by (cases "xa = y", simp_all)
      qed
    qed
  qed
qed

(* A well-formed environment is finite *)
lemma ok_finite[simp]: "ok e \<Longrightarrow> finite (env_dom e)"
  by (cases e, simp+)

(* A well-formed environment is not malformed *)
lemma ok_ok[simp]: "ok e \<Longrightarrow> \<exists>x. e = (Env x)"
  by (cases e, simp+)

(* If something is in the set of variable names, then it has a value assigned to it *)
lemma env_defined:
  fixes x :: string and e :: "'a environment"
  assumes "x \<in> env_dom e"
  shows "\<exists>T . e!x = Some T"
proof (cases e)
  case Malformed with assms show ?thesis by simp (* contradiction *)
next
  case Env with assms show ?thesis by (simp, force)
qed

(* adding of new elements does not remove elements *)
lemma env_bigger: "\<lbrakk> a \<notin> env_dom e; x \<in> (env_dom e) \<rbrakk> \<Longrightarrow> x \<in> env_dom (e\<lparr>a:X\<rparr>)"
  by (cases e, simp_all)

(* Added for convenience *)
lemma env_bigger2: 
  "\<lbrakk> a \<notin> env_dom e; b \<notin> (env_dom e); x \<in> (env_dom e); a \<noteq> b \<rbrakk> 
  \<Longrightarrow> x \<in> env_dom (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
  by (cases e, simp_all)

(* If there is an entry, then the environment is sane. *)
lemma not_malformed: "x \<in> (env_dom e) \<Longrightarrow> \<exists>fun. e = Env fun"
  by (cases e, simp_all)

(* Smaller environments are well formed. *)
lemma not_malformed_smaller: 
  fixes e :: "'a environment" and a :: string and X :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>)"
  shows "ok e"
proof (cases e)
  case Malformed with assms show ?thesis by simp (* contradiction *)
next
  case (Env f) with ok_finite[OF assms] assms show ?thesis
    by (cases "a \<notin> dom f", simp_all)
qed

(* Elements not in a bigger environment are not in a smaller one either *)
lemma not_in_smaller:
  fixes e :: "'a environment" and a :: string and X :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>)"
  shows "a \<notin> env_dom e"
proof (cases e)
  case Malformed thus ?thesis by simp
next
  case (Env f) with assms show ?thesis
    by (cases "a \<notin> dom f", simp_all)
qed

(* A variable that got added is in the environment *)
lemma in_add:
  fixes e :: "'a environment" and a :: string and X :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>)"
  shows "a \<in> env_dom (e\<lparr>a:X\<rparr>)"
proof (cases e)
  case Malformed with assms show ?thesis by simp (* contradiction *)
next
  case (Env f) with assms show ?thesis 
    by (cases "a \<notin> dom f", simp_all)
qed

(* Similar to subst_add, but using a more convenient premise *)
lemma ok_add_reverse:
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
  shows "(e\<lparr>b:Y\<rparr>\<lparr>a:X\<rparr>) = (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
proof (cases e)
  case Malformed with assms show ?thesis by simp (* contradiction *)
next
  case (Env f) 
  with 
    not_in_smaller[OF \<open>ok (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)\<close>] in_add[OF assms]
    not_in_smaller[OF not_malformed_smaller[OF assms]] 
    in_add[OF not_malformed_smaller[OF assms]]
  show ?thesis
    by (simp, intro conjI impI, elim conjE, auto simp: fun_upd_twist)
qed

lemma not_in_env_bigger: 
  fixes e :: "'a environment" and a :: string and X :: 'a and x :: string
  assumes "x \<notin> (env_dom e)" and "x \<noteq> a"
  shows "x \<notin> env_dom (e\<lparr>a:X\<rparr>)"
proof (cases e)
  case Malformed thus ?thesis by simp
next
  case (Env f) with assms show ?thesis 
    by (cases "a \<notin> dom f", simp_all)
qed

lemma not_in_env_bigger_2: 
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a and x :: string
  assumes "x \<notin> (env_dom e)" and "x \<noteq> a" and "x \<noteq> b"
  shows "x \<notin> env_dom (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
proof (cases e)
  case Malformed thus ?thesis by simp
next
  case (Env f) with assms show ?thesis 
    by (cases "a \<notin> dom f", simp_all)
qed

lemma not_in_env_smaller: 
  fixes e :: "'a environment" and a :: string and X :: 'a and x :: string
  assumes "x \<notin> (env_dom (e\<lparr>a:X\<rparr>))" and "x \<noteq> a" and "ok (e\<lparr>a:X\<rparr>)"
  shows "x \<notin> env_dom e"
proof (cases e)
  case Malformed with assms(3) show ?thesis by simp (* contradiction *)
next
  case (Env f) with assms show ?thesis 
    by (cases "a \<notin> dom f", simp_all)
qed

(* Conditions derivable from the well-formedness *)
lemma ok_add_2: 
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
  shows "ok e \<and> a \<notin> env_dom e \<and> b \<notin> env_dom e \<and> a \<noteq> b"
proof -
  {
    assume "ok (e\<lparr>b:X\<rparr>\<lparr>b:Y\<rparr>)" 
    from not_in_smaller[OF this] in_add[OF not_malformed_smaller[OF this]]
    have False by simp
  } with assms have "a \<noteq> b" by auto
  moreover
  from assms ok_add_reverse[OF assms] have "ok (e\<lparr>b:Y\<rparr>\<lparr>a:X\<rparr>)" by simp
  note not_in_smaller[OF not_malformed_smaller[OF this]]
  ultimately
  show ?thesis 
    using 
      not_malformed_smaller[OF not_malformed_smaller[OF assms]]
      not_in_smaller[OF not_malformed_smaller[OF assms]]
  by simp
qed

(* A variable that got added is in the environment *)
lemma in_add_2:
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
  shows "a \<in> env_dom (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>) \<and> b \<in> env_dom (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>)"
proof -
  from ok_add_2[OF assms] show ?thesis 
    by (elim conjE, intro conjI, (cases e, simp_all)+)
qed

(* Convenience version *)
lemma ok_add_3:
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a and c :: string and Z :: 'a
  assumes "ok (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>\<lparr>c:Z\<rparr>)"
  shows 
  "a \<notin> env_dom e \<and> b \<notin> env_dom e \<and> c \<notin> env_dom e \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
proof -
  {
    assume "ok (e\<lparr>a:X\<rparr>\<lparr>c:Y\<rparr>\<lparr>c:Z\<rparr>)" 
    from not_in_smaller[OF this] in_add[OF not_malformed_smaller[OF this]]
    have False by simp
  } with assms have "b \<noteq> c" by auto
  moreover
  from assms ok_add_reverse[OF assms] have "ok (e\<lparr>a:X\<rparr>\<lparr>c:Z\<rparr>\<lparr>b:Y\<rparr>)" by simp
  note ok_add_2[OF not_malformed_smaller[OF this]]
  ultimately
  show ?thesis using ok_add_2[OF not_malformed_smaller[OF assms]]
    by simp
qed

lemma in_env_smaller: 
  fixes e :: "'a environment" and a :: string and X :: 'a and x :: string 
  assumes "x \<in> (env_dom (e\<lparr>a:X\<rparr>))" and "x \<noteq> a"
  shows "x \<in> env_dom e"
proof -
  from not_malformed[OF assms(1)] obtain f where f: "e\<lparr>a:X\<rparr> = Env f" by auto
  with assms show ?thesis
  proof (cases e)
    case Malformed with \<open>e\<lparr>a:X\<rparr> = Env f\<close> 
    have False by simp
    then show ?thesis ..
  next
    case (Env f') with assms f show ?thesis
      by (simp, cases "a \<in> dom f'", simp_all, force)
  qed
qed

lemma in_env_smaller2:
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a and x :: string 
  assumes "x \<in> (env_dom (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>))" and "x \<noteq> a" and "x \<noteq> b"
  shows "x \<in> env_dom e"
  by (simp add: in_env_smaller[OF in_env_smaller[OF assms(1) assms(3)] assms(2)])

lemma get_env_bigger:
  fixes e :: "'a environment" and a :: string and X :: 'a and x :: string 
  assumes "x \<in> (env_dom (e\<lparr>a:X\<rparr>))" and "x \<noteq> a"
  shows "e!x = e\<lparr>a:X\<rparr>!x"
proof -
  from not_malformed[OF assms(1)] obtain f where f: "e\<lparr>a:X\<rparr> = Env f" by auto
  thus ?thesis proof (cases e)
    case Malformed with \<open>e\<lparr>a:X\<rparr> = Env f\<close>
    show ?thesis by simp (* contradiction *)
  next
    case (Env f') with assms f show ?thesis
      by (cases "a \<notin> dom f'", auto)
  qed
qed

lemma get_env_bigger2: 
  fixes 
  e :: "'a environment" and a :: string and X :: 'a and 
  b :: string and Y :: 'a and x :: string 
  assumes "x \<in> (env_dom (e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>))" and "x \<noteq> a" and "x \<noteq> b"
  shows "e!x = e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>!x"
  by (simp add: get_env_bigger[OF assms(1) assms(3)]
                get_env_bigger[OF in_env_smaller[OF assms(1) assms(3)] assms(2)])

lemma get_env_smaller: "\<lbrakk> x \<in> env_dom e; a \<notin> env_dom e \<rbrakk> \<Longrightarrow> e\<lparr>a:X\<rparr>!x = e!x"
  by (cases e, auto)

lemma get_env_smaller2: 
  "\<lbrakk> x \<in> env_dom e; a \<notin> env_dom e; b \<notin> env_dom e; a \<noteq> b \<rbrakk> 
  \<Longrightarrow> e\<lparr>a:X\<rparr>\<lparr>b:Y\<rparr>!x = e!x"
  by (cases e, auto)

lemma add_get_eq: "\<lbrakk> xa \<notin> env_dom e; ok e; the e\<lparr>xa:U\<rparr>!xa = T \<rbrakk> \<Longrightarrow> U = T" 
  by (cases e, auto)

lemma add_get: "\<lbrakk> xa \<notin> env_dom e; ok e \<rbrakk> \<Longrightarrow> the e\<lparr>xa:U\<rparr>!xa = U" 
  by (cases e, auto)

lemma add_get2_1: 
  fixes e :: "'a environment" and x :: string and A :: 'a and y :: string and B :: 'a
  assumes "ok (e\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>)"
  shows "the e\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>!x = A"
proof -
  from ok_add_2[OF assms] show ?thesis
    by (cases e, elim conjE, simp_all)
qed

lemma add_get2_2:
  fixes e :: "'a environment" and x :: string and A :: 'a and y :: string and B :: 'a
  assumes "ok (e\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>)"
  shows "the e\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>!y = B"
proof -
  from ok_add_2[OF assms] show ?thesis
    by (cases e, elim conjE, simp_all)
qed

lemma ok_add_ok: "\<lbrakk> ok e; x \<notin> env_dom e \<rbrakk> \<Longrightarrow> ok (e\<lparr>x:X\<rparr>)" 
  by (cases e, auto)

lemma env_add_dom: 
  fixes e :: "'a environment" and x :: string
  assumes "ok e" and "x \<notin> env_dom e" 
  shows "env_dom (e\<lparr>x:X\<rparr>) = env_dom e \<union> {x}"
proof (auto simp: in_add[OF ok_add_ok[OF assms]], rule ccontr)
  fix y assume "y \<in> env_dom (e\<lparr>x:X\<rparr>)" and "y \<notin> env_dom e" and "y \<noteq> x"
  from in_env_smaller[OF this(1) this(3)] this(2) show False by simp
next
  fix y assume "y \<in> env_dom e"
  from env_bigger[OF not_in_smaller[OF ok_add_ok[OF assms]] this]
  show "y \<in> env_dom (e\<lparr>x:X\<rparr>)" by assumption
qed

lemma env_add_dom_2:
  fixes e :: "'a environment" and x :: string and y :: string
  assumes "ok e" and "x \<notin> env_dom e" and "y \<notin> env_dom e" and "x \<noteq> y"
  shows "env_dom (e\<lparr>x:X\<rparr>\<lparr>y:Y\<rparr>) = env_dom e \<union> {x,y}"
proof -
  from env_add_dom[OF assms(1-2)] assms(3-4)
  have "y \<notin> env_dom (e\<lparr>x:X\<rparr>)" by simp
  from 
    env_add_dom[OF assms(1-2)] 
    env_add_dom[OF ok_add_ok[OF assms(1-2)] this]
  show ?thesis by auto
qed

fun
   env_app :: "('a environment) \<Rightarrow>  ('a environment) \<Rightarrow> ('a environment)" ("_+_")
where
  "env_app (Env a) (Env b) = 
  (if (ok (Env a) \<and> ok (Env b) \<and> env_dom (Env b) \<inter> env_dom (Env a) = {}) 
   then  Env (a ++ b) else Malformed )"

lemma env_app_dom:
  fixes e1 :: "'a environment" and e2 :: "'a environment"
  assumes "ok e1" and "env_dom e1 \<inter> env_dom e2 = {}" and "ok e2"
  shows "env_dom (e1+e2) = env_dom e1 \<union> env_dom e2"
proof -
  from ok_ok[OF \<open>ok e1\<close>] ok_ok[OF \<open>ok e2\<close>]
  obtain f1 f2 where "e1 = Env f1" and "e2 = Env f2" by auto
  with assms(2) ok_finite[OF \<open>ok e1\<close>] ok_finite[OF \<open>ok e2\<close>]
  show ?thesis by auto
qed

lemma env_app_same[simp]: 
  fixes e1 :: "'a environment" and e2 :: "'a environment" and x :: string
  assumes 
  "ok e1" and "x \<in> env_dom e1" and 
  "env_dom e1 \<inter> env_dom e2 = {}" and "ok e2"
  shows "the (e1+e2!x) = the e1!x"
proof -
  from ok_ok[OF \<open>ok e1\<close>] ok_ok[OF \<open>ok e2\<close>] 
  obtain f1 f2 where "e1 = Env f1" and "e2 = Env f2" by auto
  with assms(2-3) ok_finite[OF \<open>ok e1\<close>] ok_finite[OF \<open>ok e2\<close>]
  show ?thesis proof (auto) 
    fix y :: 'a assume "dom f1 \<inter> dom f2 = {}" and "f1 x = Some y"
    from map_add_comm[OF this(1)] this(2) have "(f1 ++ f2) x = Some y"
      by (simp add: map_add_Some_iff)
    thus "the ((f1 ++ f2) x) = y" by auto
  qed
qed

lemma env_app_ok[simp]: 
  fixes e1 :: "'a environment" and e2 :: "'a environment"
  assumes "ok e1" and "env_dom e1 \<inter> env_dom e2 = {}" and "ok e2"
  shows "ok (e1+e2)"
proof -
  from ok_ok[OF \<open>ok e1\<close>] ok_ok[OF \<open>ok e2\<close>] 
  obtain f1 f2 where "e1 = Env f1" and "e2 = Env f2" by auto
  with assms show ?thesis by (simp,force)
qed

lemma env_app_add[simp]:
  fixes e1 :: "'a environment" and e2 :: "'a environment" and x :: string
  assumes 
  "ok e1" and "env_dom e1 \<inter> env_dom e2 = {}" and "ok e2" and 
  "x \<notin> env_dom e1" and "x \<notin> env_dom e2"
  shows "(e1+e2)\<lparr>x:X\<rparr> = e1\<lparr>x:X\<rparr>+e2"
proof -
  from ok_ok[OF \<open>ok e1\<close>] ok_ok[OF \<open>ok e2\<close>] 
  obtain f1 f2 where "e1 = Env f1" and "e2 = Env f2" by auto
  with assms show ?thesis proof (clarify, simp, intro impI ext)
    fix xa :: string
    assume "x \<notin> dom f1" and "x \<notin> dom f2"
    thus "((f1 ++ f2)(x \<mapsto> X)) xa = (f1(x \<mapsto> X) ++ f2) xa"
    proof (cases "x = xa", simp_all)
      case False thus "(f1 ++ f2) xa = (f1(x \<mapsto> X) ++ f2) xa" 
        by (simp add: map_add_def split: option.split)
    next
      case True with \<open>x \<notin> dom f1\<close> \<open>x \<notin> dom f2\<close> 
      have "(f1(xa \<mapsto> X) ++ f2) xa = Some X"
        by (auto simp: map_add_Some_iff)
      thus "Some X = (f1(xa \<mapsto> X) ++ f2) xa" by simp
    qed
  qed
qed

lemma env_app_add2[simp]:
  fixes 
  e1 :: "'a environment" and e2 :: "'a environment" and 
  x :: string and y :: string
  assumes 
  "ok e1" and "env_dom e1 \<inter> env_dom e2 = {}" and "ok e2" and
  "x \<notin> env_dom e1" and "x \<notin> env_dom e2" and "y \<notin> env_dom e1" and
  "y \<notin> env_dom e2" and "x \<noteq> y"
  shows "(e1+e2)\<lparr>x:X\<rparr>\<lparr>y:Y\<rparr> = e1\<lparr>x:X\<rparr>\<lparr>y:Y\<rparr>+e2"
proof -
  from ok_ok[OF \<open>ok e1\<close>] ok_ok[OF \<open>ok e2\<close>] 
  obtain f1 f2 where "e1 = Env f1" and "e2 = Env f2" by auto
  with assms show ?thesis proof (clarify, simp, intro impI ext)
    fix xa :: string
    assume "x \<notin> dom f1" and "x \<notin> dom f2" and "y \<notin> dom f1" and "y \<notin> dom f2"
    with \<open>x \<noteq> y\<close>
    show "((f1 ++ f2)(x \<mapsto> X, y \<mapsto> Y)) xa = (f1(x \<mapsto> X, y \<mapsto> Y) ++ f2) xa"
    proof (cases "x = xa", simp)
      case True 
      with \<open>x \<noteq> y\<close> \<open>x \<notin> dom f1\<close> \<open>x \<notin> dom f2\<close> \<open>y \<notin> dom f1\<close> \<open>y \<notin> dom f2\<close>
      have "(f1(xa \<mapsto> X,y \<mapsto> Y) ++ f2) xa = Some X"
        by (auto simp: map_add_Some_iff)
      thus "Some X = (f1(xa \<mapsto> X,y \<mapsto> Y) ++ f2) xa" by simp
    next
      case False thus ?thesis
      proof (cases "y = xa", simp_all)
        case False with \<open>x \<noteq> xa\<close> 
        show "(f1 ++ f2) xa = (f1(x \<mapsto> X,y \<mapsto> Y) ++ f2) xa" 
          by (simp add: map_add_def split: option.split)
      next
        case True 
        with \<open>x \<noteq> y\<close> \<open>x \<notin> dom f1\<close> \<open>x \<notin> dom f2\<close> \<open>y \<notin> dom f1\<close> \<open>y \<notin> dom f2\<close>
        have "(f1(x \<mapsto> X,xa \<mapsto> Y) ++ f2) xa = Some Y"
          by (auto simp: map_add_Some_iff)
        thus "Some Y = (f1(x \<mapsto> X, xa \<mapsto> Y) ++ f2) xa" by simp
      qed
    qed
  qed
qed

end
