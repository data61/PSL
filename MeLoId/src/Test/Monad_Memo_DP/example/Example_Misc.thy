section \<open>Examples\<close>

subsection \<open>Misc\<close>

theory Example_Misc
imports Main
begin

paragraph \<open>Lists\<close>

fun min_list :: "'a::ord list \<Rightarrow> 'a" where
  "min_list (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> min x (min_list xs))"

lemma fold_min_commute:
  "fold min xs (min a b) = min a (fold min xs b)" for a :: "'a :: linorder"
  by (induction xs arbitrary: a; auto; metis min.commute min.assoc)

lemma min_list_fold:
  "min_list (x # xs) = fold min xs x" for x :: "'a :: linorder"
  by (induction xs arbitrary: x; auto simp: fold_min_commute[symmetric]; metis min.commute)

(* FIXME mv List *)
lemma induct_list012:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P (y # zs) \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
by induction_schema (pat_completeness, lexicographic_order)

lemma min_list_Min: "xs \<noteq> [] \<Longrightarrow> min_list xs = Min (set xs)"
by (induction xs rule: induct_list012)(auto)

(*
paragraph \<open>Code Setup\<close>

definition map1\<^sub>T' where
  "map1\<^sub>T' f xs \<equiv> \<langle>rec_list \<langle>[]\<rangle> (\<lambda>x xs a. \<langle>\<lambda>y. \<langle>\<lambda>ys. \<langle>y#ys\<rangle>\<rangle>\<rangle> . (f x) . a)\<rangle> . \<langle>xs\<rangle> "

lemma map1\<^sub>T_map1\<^sub>T':
  "map1\<^sub>T = \<langle>\<lambda>f. \<langle>\<lambda>xs. map1\<^sub>T' f xs\<rangle>\<rangle>"
  unfolding map1\<^sub>T_def map1\<^sub>T'_def ..

lemmas [code] =
  mem_defs.checkmem'_def

lemmas [code_unfold] =
  map\<^sub>T_def
  map1\<^sub>T_map1\<^sub>T'


paragraph \<open>Simplifying monad expressions\<close>

lemma app_return_right:
  "f . \<langle>g\<rangle> = do {f \<leftarrow> f; f g}"
  unfolding fun_app_lifted_def left_identity ..

lemma app_return_left:
  "\<langle>f\<rangle> . g = g \<bind> f"
  unfolding fun_app_lifted_def left_identity ..

lemma get_return:
  "(do {m \<leftarrow> get; \<langle>f m\<rangle>}) = State (\<lambda> mem. (f mem, mem))"
  unfolding get_def bind_def return_def by simp

lemma get_put:
  "do {m \<leftarrow> get; put (f m)} = State (\<lambda> mem. ((), f mem))"
  unfolding get_def put_def bind_def return_def by simp

lemma bind_return_assoc:
  "(do {
       x \<leftarrow> a;
       \<langle>f x\<rangle>
     }) \<bind>
    b =
    do {
      x \<leftarrow> a;
      b (f x)
    }"
  by (auto split: prod.split simp add: bind_def return_def)

lemma app_lifted_return_assoc:
  "(do {
       x \<leftarrow> a;
       \<langle>f x\<rangle>
     }) .
    b =
    do {
      x \<leftarrow> a;
      b \<bind> f x
    }"
  unfolding fun_app_lifted_def bind_return_assoc ..

(* There could be a simpproc for this pattern *)
lemma bind_return_assoc2:
  "(do {
       x \<leftarrow> a;
       y \<leftarrow> b;
       \<langle>f x y\<rangle>
     }) \<bind>
    c =
    do {
      x \<leftarrow> a;
      y \<leftarrow> b;
      c (f x y)
    }"
  by (auto split: prod.split simp add: bind_def return_def)

lemma bind_return_assoc3:
  "(do {
       x \<leftarrow> a;
       y \<leftarrow> b;
       z \<leftarrow> c;
       \<langle>f x y z\<rangle>
     }) \<bind>
    d =
    do {
      x \<leftarrow> a;
      y \<leftarrow> b;
      z \<leftarrow> c;
      d (f x y z)
    }"
  by (auto split: prod.split simp add: bind_def return_def)

lemma if\<^sub>T_return:
  "if\<^sub>T \<langle>b\<rangle> x\<^sub>T y\<^sub>T \<equiv> if b then x\<^sub>T else y\<^sub>T"
  unfolding if\<^sub>T_def return_def bind_def by simp

(* Would it be a good idea to just unfold fun_app_lifted? *)
lemmas monad_unfolds =
  app_return_right app_return_left Monad.left_identity Monad.right_identity
  app_lifted_return_assoc bind_return_assoc bind_return_assoc2 bind_return_assoc3
  get_return get_put
  map1\<^sub>T_map1\<^sub>T'
  if\<^sub>T_return
*)
end