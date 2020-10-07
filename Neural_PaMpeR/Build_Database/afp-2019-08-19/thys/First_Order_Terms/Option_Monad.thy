(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>The Option Monad\<close>

theory Option_Monad
  imports "HOL-Library.Monad_Syntax"
begin

declare Option.bind_cong [fundef_cong]

definition guard :: "bool \<Rightarrow> unit option"
  where
    "guard b = (if b then Some () else None)"

lemma guard_cong [fundef_cong]:
  "b = c \<Longrightarrow> (c \<Longrightarrow> m = n) \<Longrightarrow> guard b >> m = guard c >> n"
  by (simp add: guard_def)

lemma guard_simps:
  "guard b = Some x \<longleftrightarrow> b"
  "guard b = None \<longleftrightarrow> \<not> b"
  by (cases b) (simp_all add: guard_def)

lemma guard_elims[elim]:
  "guard b = Some x \<Longrightarrow> (b \<Longrightarrow> P) \<Longrightarrow> P"
  "guard b = None \<Longrightarrow> (\<not> b \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp_all add: guard_simps)

lemma guard_intros [intro, simp]:
  "b \<Longrightarrow> guard b = Some ()"
  "\<not> b \<Longrightarrow> guard b = None"
  by (simp_all add: guard_simps)

lemma guard_True [simp]: "guard True = Some ()" by simp
lemma guard_False [simp]: "guard False = None" by simp

lemma guard_and_to_bind: "guard (a \<and> b) = guard a \<bind> (\<lambda> _. guard b)" by (cases a; cases b; auto)
    
fun zip_option :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list option"
  where
    "zip_option [] [] = Some []"
  | "zip_option (x#xs) (y#ys) = do { zs \<leftarrow> zip_option xs ys; Some ((x, y) # zs) }"
  | "zip_option (x#xs) [] = None"
  | "zip_option [] (y#ys) = None"

text \<open>induction scheme for zip\<close>
lemma zip_induct [case_names Cons_Cons Nil1 Nil2]:
  assumes "\<And>x xs y ys. P xs ys \<Longrightarrow> P (x # xs) (y # ys)"
    and "\<And>ys. P [] ys"
    and "\<And>xs. P xs []"
  shows "P xs ys"
  using assms by (induction_schema) (pat_completeness, lexicographic_order)

lemma zip_option_zip_conv:
  "zip_option xs ys = Some zs \<longleftrightarrow> length ys = length xs \<and> length zs = length xs \<and> zs = zip xs ys"
proof -
  {
    assume "zip_option xs ys = Some zs"
    hence "length ys = length xs \<and> length zs = length xs \<and> zs = zip xs ys"
    proof (induct xs ys arbitrary: zs rule: zip_option.induct)
      case (2 x xs y ys)
      then obtain zs' where "zip_option xs ys = Some zs'"
        and "zs = (x, y) # zs'" by (cases "zip_option xs ys") auto
      from 2(1) [OF this(1)] and this(2) show ?case by simp
    qed simp_all
  } moreover {
    assume "length ys = length xs" and "zs = zip xs ys"
    hence "zip_option xs ys = Some zs"
      by (induct xs ys arbitrary: zs rule: zip_induct) force+
  }
  ultimately show ?thesis by blast
qed

lemma zip_option_None:
  "zip_option xs ys = None \<longleftrightarrow> length xs \<noteq> length ys"
proof -
  {
    assume "zip_option xs ys = None"
    have "length xs \<noteq> length ys"
    proof (rule ccontr)
      assume "\<not> length xs \<noteq> length ys"
      hence "length xs = length ys" by simp
      hence "zip_option xs ys = Some (zip xs ys)" by (simp add: zip_option_zip_conv)
      with \<open>zip_option xs ys = None\<close> show False by simp
    qed
  } moreover {
    assume "length xs \<noteq> length ys"
    hence "zip_option xs ys = None"
      by (induct xs ys rule: zip_option.induct) simp_all
  }
  ultimately show ?thesis by blast
qed

declare zip_option.simps [simp del]

lemma zip_option_intros [intro]:
  "\<lbrakk>length ys = length xs; length zs = length xs; zs = zip xs ys\<rbrakk>
    \<Longrightarrow> zip_option xs ys = Some zs"
  "length xs \<noteq> length ys \<Longrightarrow> zip_option xs ys = None"
  by (simp_all add: zip_option_zip_conv zip_option_None)

lemma zip_option_elims [elim]:
  "zip_option xs ys = Some zs
    \<Longrightarrow> (\<lbrakk>length ys = length xs; length zs = length xs; zs = zip xs ys\<rbrakk> \<Longrightarrow> P)
    \<Longrightarrow> P"
  "zip_option xs ys = None \<Longrightarrow> (length xs \<noteq> length ys \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp_all add: zip_option_zip_conv zip_option_None)

lemma zip_option_simps [simp]:
  "zip_option xs ys = None \<Longrightarrow> length xs = length ys \<Longrightarrow> False"
  "zip_option xs ys = None \<Longrightarrow> length xs \<noteq> length ys"
  "zip_option xs ys = Some zs \<Longrightarrow> zs = zip xs ys"
  by (simp_all add: zip_option_None zip_option_zip_conv)


fun mapM :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option"
  where
    "mapM f [] = Some []"
  | "mapM f (x#xs) = do {
      y \<leftarrow> f x;
      ys \<leftarrow> mapM f xs;
      Some (y # ys)
    }"

lemma mapM_None:
  "mapM f xs = None \<longleftrightarrow> (\<exists>x\<in>set xs. f x = None)" 
proof (induct xs)
  case (Cons x xs) thus ?case 
    by (cases "f x", simp, cases "mapM f xs", auto)
qed simp

lemma mapM_Some:
  "mapM f xs = Some ys \<Longrightarrow> ys = map (\<lambda>x. the (f x)) xs \<and> (\<forall>x\<in>set xs. f x \<noteq> None)"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys)   
  thus ?case 
    by (cases "f x", simp, cases "mapM f xs", auto)
qed simp

lemma mapM_Some_idx:
  assumes some: "mapM f xs = Some ys" and i: "i < length xs" 
  shows "\<exists>y. f (xs ! i) = Some y \<and> ys ! i = y"
proof -
  note m = mapM_Some [OF some]
  from m[unfolded set_conv_nth] i have "f (xs ! i) \<noteq> None" by auto
  then obtain y where "f (xs ! i) = Some y" by auto
  then have "f (xs ! i) = Some y \<and> ys ! i = y" unfolding m [THEN conjunct1] using i by auto
  then show ?thesis ..
qed

lemma mapM_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "mapM f xs = mapM g ys"
  unfolding assms(1) using assms(2) by (induct ys) auto

lemma mapM_map:
  "mapM f xs = (if (\<forall>x\<in>set xs. f x \<noteq> None) then Some (map (\<lambda>x. the (f x)) xs) else None)"
proof (cases "mapM f xs")
  case None
  thus ?thesis using mapM_None by auto
next
  case (Some ys)
  with mapM_Some [OF Some] show ?thesis by auto
qed

lemma mapM_mono [partial_function_mono]:
  fixes C :: "'a \<Rightarrow> ('b \<Rightarrow> 'c option) \<Rightarrow> 'd option"
  assumes C: "\<And>y. mono_option (C y)"
  shows "mono_option (\<lambda>f. mapM (\<lambda>y. C y f) B)" 
proof (induct B)
  case Nil
  show ?case unfolding mapM.simps 
    by (rule option.const_mono)
next
  case (Cons b B)
  show ?case unfolding mapM.simps
    by (rule bind_mono [OF C bind_mono [OF Cons option.const_mono]])
qed

end
