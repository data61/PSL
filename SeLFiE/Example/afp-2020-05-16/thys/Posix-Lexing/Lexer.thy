(*  Title:       POSIX Lexing with Derivatives of Regular Expressions
    Authors:     Fahad Ausaf <fahad.ausaf at icloud.com>, 2016
                 Roy Dyckhoff <roy.dyckhoff at st-andrews.ac.uk>, 2016
                 Christian Urban <christian.urban at kcl.ac.uk>, 2016
    Maintainer:  Christian Urban <christian.urban at kcl.ac.uk>
*) 

theory Lexer
  imports "Regular-Sets.Derivatives"
begin

section \<open>Values\<close>

datatype 'a val = 
  Void
| Atm 'a
| Seq "'a val" "'a val"
| Right "'a val"
| Left "'a val"
| Stars "('a val) list"


section \<open>The string behind a value\<close>

fun 
  flat :: "'a val \<Rightarrow> 'a list"
where
  "flat (Void) = []"
| "flat (Atm c) = [c]"
| "flat (Left v) = flat v"
| "flat (Right v) = flat v"
| "flat (Seq v1 v2) = (flat v1) @ (flat v2)"
| "flat (Stars []) = []"
| "flat (Stars (v#vs)) = (flat v) @ (flat (Stars vs))" 

lemma flat_Stars [simp]:
 "flat (Stars vs) = concat (map flat vs)"
by (induct vs) (auto)

section \<open>Relation between values and regular expressions\<close>

inductive 
  Prf :: "'a val \<Rightarrow> 'a rexp \<Rightarrow> bool" ("\<turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<turnstile> Seq v1 v2 : Times r1 r2"
| "\<turnstile> v1 : r1 \<Longrightarrow> \<turnstile> Left v1 : Plus r1 r2"
| "\<turnstile> v2 : r2 \<Longrightarrow> \<turnstile> Right v2 : Plus r1 r2"
| "\<turnstile> Void : One"
| "\<turnstile> Atm c : Atom c"
| "\<turnstile> Stars [] : Star r"
| "\<lbrakk>\<turnstile> v : r; \<turnstile> Stars vs : Star r\<rbrakk> \<Longrightarrow> \<turnstile> Stars (v # vs) : Star r"

inductive_cases Prf_elims:
  "\<turnstile> v : Zero"
  "\<turnstile> v : Times r1 r2"
  "\<turnstile> v : Plus r1 r2"
  "\<turnstile> v : One"
  "\<turnstile> v : Atom c"
(*  "\<turnstile> vs : Star r"*)

lemma Prf_flat_lang:
  assumes "\<turnstile> v : r" shows "flat v \<in> lang r"
using assms
by(induct v r rule: Prf.induct) (auto)

lemma Prf_Stars:
  assumes "\<forall>v \<in> set vs. \<turnstile> v : r"
  shows "\<turnstile> Stars vs : Star r"
using assms
by(induct vs) (auto intro: Prf.intros)

lemma Star_string:
  assumes "s \<in> star A"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A)"
using assms
by (metis in_star_iff_concat subsetD)

lemma Star_val:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<turnstile> v : r"
  shows "\<exists>vs. concat (map flat vs) = concat ss \<and> (\<forall>v\<in>set vs. \<turnstile> v : r)"
using assms
apply(induct ss)
apply(auto)
apply (metis empty_iff list.set(1))
by (metis concat.simps(2) list.simps(9) set_ConsD)

lemma L_flat_Prf1:
  assumes "\<turnstile> v : r" shows "flat v \<in> lang r"
using assms
by (induct)(auto)

lemma L_flat_Prf2:
  assumes "s \<in> lang r" shows "\<exists>v. \<turnstile> v : r \<and> flat v = s"
using assms
apply(induct r arbitrary: s)
apply(auto intro: Prf.intros)
using Prf.intros(2) flat.simps(3) apply blast
using Prf.intros(3) flat.simps(4) apply blast
apply (metis Prf.intros(1) concE flat.simps(5))
apply(subgoal_tac "\<exists>vs::('a val) list. concat (map flat vs) = s \<and> (\<forall>v \<in> set vs. \<turnstile> v : r)")
apply(auto)[1]
apply(rule_tac x="Stars vs" in exI)
apply(simp)
apply (simp add: Prf_Stars)
apply(drule Star_string)
apply(auto)
apply(rule Star_val)
apply(auto)
done

lemma L_flat_Prf:
  "lang r = {flat v | v. \<turnstile> v : r}"
using L_flat_Prf1 L_flat_Prf2 by blast


section \<open>Sulzmann and Lu functions\<close>

fun 
  mkeps :: "'a rexp \<Rightarrow> 'a val"
where
  "mkeps(One) = Void"
| "mkeps(Times r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(Plus r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(Star r) = Stars []"

fun injval :: "'a rexp \<Rightarrow> 'a \<Rightarrow> 'a val \<Rightarrow> 'a val"
where
  "injval (Atom d) c Void = Atm d"
| "injval (Plus r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (Plus r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (Times r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (Times r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (Times r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"
| "injval (Star r) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 


section \<open>Mkeps, injval\<close>

lemma mkeps_nullable:
  assumes "nullable r" 
  shows "\<turnstile> mkeps r : r"
using assms
by (induct r) 
   (auto intro: Prf.intros)

lemma mkeps_flat:
  assumes "nullable r" 
  shows "flat (mkeps r) = []"
using assms
by (induct r) (auto)


lemma Prf_injval:
  assumes "\<turnstile> v : deriv c r" 
  shows "\<turnstile> (injval r c v) : r"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims split: if_splits)
(* Star *)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)
apply (metis Prf.intros(6) Prf.intros(7))
by (metis Prf.intros(7))

lemma Prf_injval_flat:
  assumes "\<turnstile> v : deriv c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct r arbitrary: v c)
apply(auto elim!: Prf_elims split: if_splits)
apply(metis mkeps_flat)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[7]
done

(* HERE *)

section \<open>Our Alternative Posix definition\<close>

inductive 
  Posix :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> 'a val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  Posix_One: "[] \<in> One \<rightarrow> Void"
| Posix_Atom: "[c] \<in> (Atom c) \<rightarrow> (Atm c)"
| Posix_Plus1: "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (Plus r1 r2) \<rightarrow> (Left v)"
| Posix_Plus2: "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> lang r1\<rbrakk> \<Longrightarrow> s \<in> (Plus r1 r2) \<rightarrow> (Right v)"
| Posix_Times: "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (Times r1 r2) \<rightarrow> (Seq v1 v2)"
| Posix_Star1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> Star r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> Star r \<rightarrow> Stars (v # vs)"
| Posix_Star2: "[] \<in> Star r \<rightarrow> Stars []"

inductive_cases Posix_elims:
  "s \<in> Zero \<rightarrow> v"
  "s \<in> One \<rightarrow> v"
  "s \<in> Atom c \<rightarrow> v"
  "s \<in> Plus r1 r2 \<rightarrow> v"
  "s \<in> Times r1 r2 \<rightarrow> v"
  "s \<in> Star r \<rightarrow> v"

lemma Posix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> lang r" "flat v = s"
using assms
by (induct s r v rule: Posix.induct) (auto)


lemma Posix1a:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r"
using assms
by (induct s r v rule: Posix.induct)(auto intro: Prf.intros)


lemma Posix_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
using assms
apply(induct r)
apply(auto intro: Posix.intros simp add: nullable_iff)
apply(subst append.simps(1)[symmetric])
apply(rule Posix.intros)
apply(auto)
done


lemma Posix_determ:
  assumes "s \<in> r \<rightarrow> v1" "s \<in> r \<rightarrow> v2"
  shows "v1 = v2"
using assms
proof (induct s r v1 arbitrary: v2 rule: Posix.induct)
  case (Posix_One v2)
  have "[] \<in> One \<rightarrow> v2" by fact
  then show "Void = v2" by cases auto
next 
  case (Posix_Atom c v2)
  have "[c] \<in> Atom c \<rightarrow> v2" by fact
  then show "Atm c = v2" by cases auto
next 
  case (Posix_Plus1 s r1 v r2 v2)
  have "s \<in> Plus r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<in> r1 \<rightarrow> v" by fact
  then have "s \<in> lang r1" by (simp add: Posix1)
  ultimately obtain v' where eq: "v2 = Left v'" "s \<in> r1 \<rightarrow> v'" by cases auto 
  moreover
  have IH: "\<And>v2. s \<in> r1 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Left v = v2" using eq by simp
next 
  case (Posix_Plus2 s r2 v r1 v2)
  have "s \<in> Plus r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<notin> lang r1" by fact
  ultimately obtain v' where eq: "v2 = Right v'" "s \<in> r2 \<rightarrow> v'" 
    by cases (auto simp add: Posix1) 
  moreover
  have IH: "\<And>v2. s \<in> r2 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Right v = v2" using eq by simp
next
  case (Posix_Times s1 r1 v1 s2 r2 v2 v')
  have "(s1 @ s2) \<in> Times r1 r2 \<rightarrow> v'" 
       "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" by fact+
  then obtain v1' v2' where "v' = Seq v1' v2'" "s1 \<in> r1 \<rightarrow> v1'" "s2 \<in> r2 \<rightarrow> v2'"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) by fastforce+
  moreover
  have IHs: "\<And>v1'. s1 \<in> r1 \<rightarrow> v1' \<Longrightarrow> v1 = v1'"
            "\<And>v2'. s2 \<in> r2 \<rightarrow> v2' \<Longrightarrow> v2 = v2'" by fact+
  ultimately show "Seq v1 v2 = v'" by simp
next
  case (Posix_Star1 s1 r v s2 vs v2)
  have "(s1 @ s2) \<in> Star r \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> Star r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (Star r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) apply fastforce
  apply (metis Posix1(1) Posix_Star1.hyps(6) append_Nil append_Nil2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> Star r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_Star2 r v2)
  have "[] \<in> Star r \<rightarrow> v2" by fact
  then show "Stars [] = v2" by cases (auto simp add: Posix1)
qed


lemma Posix_injval:
  assumes "s \<in> (deriv c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (injval r c v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case Zero
  have "s \<in> deriv c Zero \<rightarrow> v" by fact
  then have "s \<in> Zero \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> Zero \<rightarrow> (injval Zero c v)" by simp
next
  case One
  have "s \<in> deriv c One \<rightarrow> v" by fact
  then have "s \<in> Zero \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> One \<rightarrow> (injval One c v)" by simp
next 
  case (Atom d)
  consider (eq) "c = d" | (ineq) "c \<noteq> d" by blast
  then show "(c # s) \<in> (Atom d) \<rightarrow> (injval (Atom d) c v)"
  proof (cases)
    case eq
    have "s \<in> deriv c (Atom d) \<rightarrow> v" by fact
    then have "s \<in> One \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> Atom d \<rightarrow> injval (Atom d) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> deriv c (Atom d) \<rightarrow> v" by fact
    then have "s \<in> Zero \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> Atom d \<rightarrow> injval (Atom d) c v" by simp
  qed
next
  case (Plus r1 r2)
  have IH1: "\<And>s v. s \<in> deriv c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> deriv c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> deriv c (Plus r1 r2) \<rightarrow> v" by fact
  then have "s \<in> Plus (deriv c r1) (deriv c r2) \<rightarrow> v" by simp
  then consider (left) v' where "v = Left v'" "s \<in> deriv c r1 \<rightarrow> v'" 
              | (right) v' where "v = Right v'" "s \<notin> lang (deriv c r1)" "s \<in> deriv c r2 \<rightarrow> v'" 
              by cases auto
  then show "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c v"
  proof (cases)
    case left
    have "s \<in> deriv c r1 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r1 \<rightarrow> injval r1 c v'" using IH1 by simp
    then have "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c (Left v')" by (auto intro: Posix.intros)
    then show "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c v" using left by simp
  next 
    case right
    have "s \<notin> lang (deriv c r1)" by fact
    then have "c # s \<notin> lang r1" by (simp add: lang_deriv Deriv_def)
    moreover 
    have "s \<in> deriv c r2 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r2 \<rightarrow> injval r2 c v'" using IH2 by simp
    ultimately have "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c (Right v')" 
      by (auto intro: Posix.intros)
    then show "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c v" using right by simp
  qed
next
  case (Times r1 r2)
  have IH1: "\<And>s v. s \<in> deriv c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> deriv c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> deriv c (Times r1 r2) \<rightarrow> v" by fact
  then consider 
        (left_nullable) v1 v2 s1 s2 where 
        "v = Left (Seq v1 v2)"  "s = s1 @ s2" 
        "s1 \<in> deriv c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)"
      | (right_nullable) v1 s1 s2 where 
        "v = Right v1" "s = s1 @ s2"  
        "s \<in> deriv c r2 \<rightarrow> v1" "nullable r1" "s1 @ s2 \<notin> lang (Times (deriv c r1) r2)"
      | (not_nullable) v1 v2 s1 s2 where
        "v = Seq v1 v2" "s = s1 @ s2" 
        "s1 \<in> deriv c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "\<not>nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)"
        by (force split: if_splits elim!: Posix_elims simp add: lang_deriv Deriv_def)   
  then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" 
    proof (cases)
      case left_nullable
      have "s1 \<in> deriv c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" 
         by (simp add: lang_deriv Deriv_def)
      ultimately have "((c # s1) @ s2) \<in> Times r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using left_nullable by (rule_tac Posix.intros)
      then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" using left_nullable by simp
    next
      case right_nullable
      have "nullable r1" by fact
      then have "[] \<in> r1 \<rightarrow> (mkeps r1)" by (rule Posix_mkeps)
      moreover
      have "s \<in> deriv c r2 \<rightarrow> v1" by fact
      then have "(c # s) \<in> r2 \<rightarrow> (injval r2 c v1)" using IH2 by simp
      moreover
      have "s1 @ s2 \<notin> lang (Times (deriv c r1) r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" 
        using right_nullable 
        apply (auto simp add: lang_deriv Deriv_def append_eq_Cons_conv)
        by (metis concI mem_Collect_eq)
      ultimately have "([] @ (c # s)) \<in> Times r1 r2 \<rightarrow> Seq (mkeps r1) (injval r2 c v1)"
      by(rule Posix.intros)
      then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" using right_nullable by simp
    next
      case not_nullable
      have "s1 \<in> deriv c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" by (simp add: lang_deriv Deriv_def)
      ultimately have "((c # s1) @ s2) \<in> Times r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using not_nullable 
        by (rule_tac Posix.intros) (simp_all) 
      then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" using not_nullable by simp
    qed
next
  case (Star r)
  have IH: "\<And>s v. s \<in> deriv c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> deriv c (Star r) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> deriv c r \<rightarrow> v1" "s2 \<in> (Star r) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Star r))" 
        apply(auto elim!: Posix_elims(1-5) simp add: lang_deriv Deriv_def intro: Posix.intros)
        apply(rotate_tac 3)
        apply(erule_tac Posix_elims(6))
        apply (simp add: Posix.intros(6))
        using Posix.intros(7) by blast
    then show "(c # s) \<in> Star r \<rightarrow> injval (Star r) c v" 
    proof (cases)
      case cons
          have "s1 \<in> deriv c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> Star r \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Star r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" 
            by (simp add: lang_deriv Deriv_def)
        ultimately 
        have "((c # s1) @ s2) \<in> Star r \<rightarrow> Stars (injval r c v1 # vs)" by (rule Posix.intros)
        then show "(c # s) \<in> Star r \<rightarrow> injval (Star r) c v" using cons by(simp)
    qed
qed


section \<open>The Lexer by Sulzmann and Lu\<close>

fun 
  lexer :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> ('a val) option"
where
  "lexer r [] = (if nullable r then Some(mkeps r) else None)"
| "lexer r (c#s) = (case (lexer (deriv c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"


lemma lexer_correct_None:
  shows "s \<notin> lang r \<longleftrightarrow> lexer r s = None"
apply(induct s arbitrary: r)
apply(simp add: nullable_iff)
apply(drule_tac x="deriv a r" in meta_spec)
apply(auto simp add: lang_deriv Deriv_def)
done

lemma lexer_correct_Some:
  shows "s \<in> lang r \<longleftrightarrow> (\<exists>v. lexer r s = Some(v) \<and> s \<in> r \<rightarrow> v)"
apply(induct s arbitrary: r)
apply(auto simp add: Posix_mkeps nullable_iff)[1]
apply(drule_tac x="deriv a r" in meta_spec)
apply(simp add: lang_deriv Deriv_def)
apply(rule iffI)
apply(auto intro: Posix_injval simp add: Posix1(1))
done 

lemma lexer_correctness:
  shows "(lexer r s = Some v) \<longleftrightarrow> s \<in> r \<rightarrow> v"
  and   "(lexer r s = None) \<longleftrightarrow> \<not>(\<exists>v. s \<in> r \<rightarrow> v)"
apply(auto)
using lexer_correct_None lexer_correct_Some apply fastforce
using Posix1(1) Posix_determ lexer_correct_Some apply blast
using Posix1(1) lexer_correct_None apply blast
using lexer_correct_None lexer_correct_Some by blast


end
