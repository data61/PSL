(* Title:     Error_Monad
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>The Sum Type as Error Monad\<close>

theory Error_Monad
imports
  "HOL-Library.Monad_Syntax"
  Error_Syntax
begin

text \<open>Make monad syntax (including do-notation) available for the sum type.\<close>
definition bind :: "'e + 'a \<Rightarrow> ('a \<Rightarrow> 'e + 'b) \<Rightarrow> 'e + 'b"
where
  "bind m f = (case m of Inr x \<Rightarrow> f x | Inl e \<Rightarrow> Inl e)"

adhoc_overloading
  Monad_Syntax.bind bind

abbreviation (input) "return \<equiv> Inr"
abbreviation (input) "error \<equiv> Inl"
abbreviation (input) "run \<equiv> projr"


subsection \<open>Monad Laws\<close>

lemma return_bind [simp]:
  "(return x \<bind> f) = f x"
  by (simp add: bind_def)

lemma bind_return [simp]:
  "(m \<bind> return) = m"
  by (cases m) (simp_all add: bind_def)

lemma error_bind [simp]:
  "(error e \<bind> f) = error e"
  by (simp add: bind_def)

lemma bind_assoc [simp]:
  fixes m :: "'a + 'b"
  shows "((m \<bind> f) \<bind> g) = (m \<bind> (\<lambda>x. f x \<bind> g))"
  by (cases m) (simp_all add: bind_def)

lemma bind_cong [fundef_cong]:
  fixes m1 m2 :: "'e + 'a"
    and f1 f2 :: "'a \<Rightarrow> 'e + 'b"
  assumes "m1 = m2"
    and "\<And>y. m2 = Inr y \<Longrightarrow> f1 y = f2 y"
  shows "(m1 \<bind> f1) = (m2 \<bind> f2)"
  using assms by (cases "m1") (auto simp: bind_def)

definition catch_error :: "'e + 'a \<Rightarrow> ('e \<Rightarrow> 'f + 'a) \<Rightarrow> 'f + 'a"
where
  catch_def: "catch_error m f = (case m of Inl e \<Rightarrow> f e | Inr x \<Rightarrow> Inr x)"

adhoc_overloading
  Error_Syntax.catch catch_error

lemma catch_splits:
  "P (try m catch f) \<longleftrightarrow> (\<forall>e. m = Inl e \<longrightarrow> P (f e)) \<and> (\<forall>x. m = Inr x \<longrightarrow> P (Inr x))"
  "P (try m catch f) \<longleftrightarrow> (\<not> ((\<exists>e. m = Inl e \<and> \<not> P (f e)) \<or> (\<exists>x. m = Inr x \<and> \<not> P (Inr x))))"
  by (case_tac [!] m) (simp_all add: catch_def)

abbreviation update_error :: "'e + 'a \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> 'f + 'a"
where
  "update_error m f \<equiv> try m catch (\<lambda>x. error (f x))"

adhoc_overloading
  Error_Syntax.update_error update_error

lemma catch_return [simp]:
  "(try return x catch f) = return x" by (simp add: catch_def)

lemma catch_error [simp]:
  "(try error e catch f) = f e" by (simp add: catch_def)

lemma update_error_return [simp]:
  "(m <+? c = return x) \<longleftrightarrow> (m = return x)"
  by (cases m) simp_all

definition "isOK m \<longleftrightarrow> (case m of Inl e \<Rightarrow> False | Inr x \<Rightarrow> True)"

lemma isOK_E [elim]:
  assumes "isOK m"
  obtains x where "m = return x"
  using assms by (cases m) (simp_all add: isOK_def)

lemma isOK_I [simp, intro]:
  "m = return x \<Longrightarrow> isOK m"
  by (cases m) (simp_all add: isOK_def)

lemma isOK_iff:
  "isOK m \<longleftrightarrow> (\<exists>x. m = return x)"
  by blast

lemma isOK_error [simp]:
  "isOK (error x) = False"
  by blast

lemma isOK_bind [simp]:
  "isOK (m \<bind> f) \<longleftrightarrow> isOK m \<and> isOK (f (run m))"
  by (cases m) simp_all

lemma isOK_update_error [simp]:
  "isOK (m <+? f) \<longleftrightarrow> isOK m"
  by (cases m) simp_all

lemma isOK_case_prod [simp]:
  "isOK (case lr of (l, r) \<Rightarrow> P l r) = (case lr of (l, r) \<Rightarrow> isOK (P l r))"
  by (rule prod.case_distrib)

lemma isOK_case_option [simp]:
  "isOK (case x of None \<Rightarrow> P | Some v \<Rightarrow> Q v) = (case x of None \<Rightarrow> isOK P | Some v \<Rightarrow> isOK (Q v))"
  by (cases x) (auto)        

lemma isOK_Let [simp]:
  "isOK (Let s f) = isOK (f s)"
  by (simp add: Let_def)

lemma run_bind [simp]:
  "isOK m \<Longrightarrow> run (m \<bind> f) = run (f (run m))"
  by auto

lemma run_catch [simp]:
  "isOK m \<Longrightarrow> run (try m catch f) = run m"
  by auto

fun foldM :: "('a \<Rightarrow> 'b \<Rightarrow> 'e + 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'e + 'a"
where 
  "foldM f d [] = return d" |
  "foldM f d (x # xs) = do { y \<leftarrow> f d x; foldM f y xs }"

fun forallM_index_aux :: "('a \<Rightarrow> nat \<Rightarrow> 'e + unit) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (('a \<times> nat) \<times> 'e) + unit"
where
  "forallM_index_aux P i [] = return ()" |
  "forallM_index_aux P i (x # xs) = do {
    P x i <+? Pair (x, i);
    forallM_index_aux P (Suc i) xs
  }"

lemma isOK_forallM_index_aux [simp]:
  "isOK (forallM_index_aux P n xs) = (\<forall>i < length xs. isOK (P (xs ! i) (i + n)))"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  have "(\<forall>i < length (x # xs). isOK (P ((x # xs) ! i) (i + n))) \<longleftrightarrow>
    (isOK (P x n) \<and> (\<forall>i < length xs. isOK (P (xs ! i) (i + Suc n))))"
    by (auto, case_tac i) (simp_all)
  then show ?case
    unfolding Cons [of "Suc n", symmetric] by simp
qed auto

definition forallM_index :: "('a \<Rightarrow> nat \<Rightarrow> 'e + unit) \<Rightarrow> 'a list \<Rightarrow> (('a \<times> nat) \<times> 'e) + unit"
where
  "forallM_index P xs = forallM_index_aux P 0 xs"

lemma isOK_forallM_index [simp]:
  "isOK (forallM_index P xs) \<longleftrightarrow> (\<forall>i < length xs. isOK (P (xs ! i) i))"
  unfolding forallM_index_def isOK_forallM_index_aux by simp

lemma forallM_index [fundef_cong]:
  fixes c :: "'a \<Rightarrow> nat \<Rightarrow> 'e + unit"
  assumes "\<And>x i. x \<in> set xs \<Longrightarrow> c x i = d x i"
  shows "forallM_index c xs = forallM_index d xs"
proof -
  { fix n
    have "forallM_index_aux c n xs = forallM_index_aux d n xs"
      using assms by (induct xs arbitrary: n) simp_all }
  then show ?thesis by (simp add: forallM_index_def)
qed

hide_const forallM_index_aux

text \<open>
  Check whether @{term f} succeeds for all elements of a given list. In case it doesn't,
  return the first offending element together with the produced error.
\<close>
fun forallM :: "('a \<Rightarrow> 'e + unit) \<Rightarrow> 'a list \<Rightarrow> ('a * 'e) + unit"
where
  "forallM f [] = return ()" |
  "forallM f (x # xs) = f x <+? Pair x \<then> forallM f xs"

lemma isOK_forallM [simp]:
  "isOK (forallM f xs) \<longleftrightarrow> (\<forall>x \<in> set xs. isOK (f x))"
  by (induct xs) (simp_all)

text \<open>
  Check whether @{term f} succeeds for at least one element of a given list.
  In case it doesn't, return the list of produced errors.
\<close>
fun existsM :: "('a \<Rightarrow> 'e + unit) \<Rightarrow> 'a list \<Rightarrow> 'e list + unit"
where
  "existsM f [] = error []" |
  "existsM f (x # xs) = (try f x catch (\<lambda>e. existsM f xs <+? Cons e))"

lemma isOK_existsM [simp]:
  "isOK (existsM f xs) \<longleftrightarrow> (\<exists>x\<in>set xs. isOK (f x))"
proof (induct xs)
  case (Cons x xs)
  show ?case
  proof (cases "f x")
    case (Inl e)
    with Cons show ?thesis by simp
  qed (auto simp add: catch_def)
qed simp

lemma is_OK_if_return [simp]:
  "isOK (if b then return x else m) \<longleftrightarrow> b \<or> isOK m"
  "isOK (if b then m else return x) \<longleftrightarrow> \<not> b \<or> isOK m"
  by simp_all

lemma isOK_if_error [simp]:
  "isOK (if b then error e else m) \<longleftrightarrow> \<not> b \<and> isOK m"
  "isOK (if b then m else error e) \<longleftrightarrow> b \<and> isOK m"
  by simp_all

lemma isOK_if:
  "isOK (if b then x else y) \<longleftrightarrow> b \<and> isOK x \<or> \<not> b \<and> isOK y"
  by simp

fun sequence :: "('e + 'a) list \<Rightarrow> 'e + 'a list"
where
  "sequence [] = Inr []" |
  "sequence (m # ms) = do {
    x \<leftarrow> m;
    xs \<leftarrow> sequence ms;
    return (x # xs)
  }"


subsection \<open>Monadic Map for Error Monad\<close>

fun mapM :: "('a \<Rightarrow> 'e + 'b) \<Rightarrow> 'a list \<Rightarrow> 'e + 'b list"
where
  "mapM f [] = return []" |
  "mapM f (x#xs) = do {
    y \<leftarrow> f x;
    ys \<leftarrow> mapM f xs;
    Inr (y # ys)
  }"

lemma mapM_error:
  "(\<exists>e. mapM f xs = error e) \<longleftrightarrow> (\<exists>x\<in>set xs. \<exists>e. f x = error e)"
proof (induct xs)
  case (Cons x xs)
  then show ?case
    by (cases "f x", simp_all, cases "mapM f xs", simp_all)
qed simp

lemma mapM_return:
  assumes "mapM f xs = return ys"
  shows "ys = map (run \<circ> f) xs \<and> (\<forall>x\<in>set xs. \<forall>e. f x \<noteq> error e)"
using assms
proof (induct xs arbitrary: ys)
  case (Cons x xs ys)   
  then show ?case
    by (cases "f x", simp, cases "mapM f xs", simp_all)
qed simp

lemma mapM_return_idx:
  assumes *: "mapM f xs = Inr ys" and "i < length xs" 
  shows "\<exists>y. f (xs ! i) = Inr y \<and> ys ! i = y"
proof -
  note ** = mapM_return [OF *, unfolded set_conv_nth]
  with assms have "\<And>e. f (xs ! i) \<noteq> Inl e" by auto
  then obtain y where "f (xs ! i) = Inr y" by (cases "f (xs ! i)") auto
  then have "f (xs ! i) = Inr y \<and> ys ! i = y" unfolding ** [THEN conjunct1] using assms by auto
  then show ?thesis ..
qed

lemma mapM_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "mapM f xs = mapM g ys"
  unfolding assms(1) using assms(2) by (induct ys) auto

lemma bindE [elim]:
  assumes "(p \<bind> f) = return x"
  obtains y where "p = return y" and "f y = return x"
  using assms by (cases p) simp_all

lemma then_return_eq [simp]:
  "(p \<then> q) = return f \<longleftrightarrow> isOK p \<and> q = return f"
  by (cases p) simp_all

fun choice :: "('e + 'a) list \<Rightarrow> 'e list + 'a"
where
  "choice [] = error []" |
  "choice (x # xs) = (try x catch (\<lambda>e. choice xs <+? Cons e))"

declare choice.simps [simp del]

lemma isOK_mapM:
  assumes "isOK (mapM f xs)"
  shows "(\<forall>x. x \<in> set xs \<longrightarrow> isOK (f x)) \<and> run (mapM f xs) = map (\<lambda>x. run (f x)) xs"
  using assms mapM_return[of f xs] by (force simp: isOK_def split: sum.splits)+

fun firstM
  where
    "firstM f [] = error []"
  | "firstM f (x # xs) = (try f x \<then> return x catch (\<lambda>e. firstM f xs <+? Cons e))"

lemma firstM:
  "isOK (firstM f xs) \<longleftrightarrow> (\<exists>x\<in>set xs. isOK (f x))"
  by (induct xs) (auto simp: catch_def split: sum.splits)

lemma firstM_return:
  assumes "firstM f xs = return y"
  shows "isOK (f y) \<and> y \<in> set xs"
  using assms by (induct xs) (auto simp: catch_def split: sum.splits)


end

