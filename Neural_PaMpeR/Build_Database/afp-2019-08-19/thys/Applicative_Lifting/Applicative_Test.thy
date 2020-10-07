(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Regression tests for applicative lifting\<close>

theory Applicative_Test imports
  Stream_Algebra
  Applicative_Environment
  Applicative_List
  Applicative_Option
  Applicative_Set
  Applicative_Sum
  Abstract_AF
begin

unbundle applicative_syntax

subsection \<open>Normal form conversion\<close>

notepad
begin
  have "\<forall>x. x = af_pure (\<lambda>x. x) \<diamondop> x" by applicative_nf rule
  have "\<forall>x. af_pure x = af_pure x" by applicative_nf rule
  have "\<forall>f x. af_pure f \<diamondop> x = af_pure f \<diamondop> x" by applicative_nf rule
  have "\<forall>f x y. af_pure f \<diamondop> x \<diamondop> y = af_pure f \<diamondop> x \<diamondop> y" by applicative_nf rule
  have "\<forall>g f x. af_pure g \<diamondop> (f \<diamondop> x) = af_pure (\<lambda>f x. g (f x)) \<diamondop> f \<diamondop> x" by applicative_nf rule
  have "\<forall>f x y. f \<diamondop> x \<diamondop> y = af_pure (\<lambda>f x y. f x y) \<diamondop> f \<diamondop> x \<diamondop> y" by applicative_nf rule
  have "\<forall>g f x. g \<diamondop> (f \<diamondop> x) = af_pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x" by applicative_nf rule
  have "\<forall>f x. f \<diamondop> af_pure x = af_pure (\<lambda>f. f x) \<diamondop> f" by applicative_nf rule
  have "\<forall>x y. af_pure x \<diamondop> af_pure y = af_pure (x y)" by applicative_nf rule
  have "\<forall>f x y. f \<diamondop> x \<diamondop> af_pure y = af_pure (\<lambda>f x. f x y) \<diamondop> f \<diamondop> x" by applicative_nf rule
  have "\<forall>f x y. af_pure f \<diamondop> x \<diamondop> af_pure y = af_pure (\<lambda>x. f x y) \<diamondop> x" by applicative_nf rule
  have "\<forall>f x y z. af_pure f \<diamondop> x \<diamondop> af_pure y \<diamondop> z = af_pure (\<lambda>x z. f x y z) \<diamondop> x \<diamondop> z" by applicative_nf rule
  have "\<forall>f x g y. af_pure f \<diamondop> x \<diamondop> (af_pure g \<diamondop> y) = af_pure (\<lambda>x y. f x (g y)) \<diamondop> x \<diamondop> y" by applicative_nf rule
  have "\<forall>f g x y. f \<diamondop> (g \<diamondop> x) \<diamondop> y = af_pure (\<lambda>f g x y. f (g x) y) \<diamondop> f \<diamondop> g \<diamondop> x \<diamondop> y" by applicative_nf rule
  have "\<forall>f g x y z. f \<diamondop> (g \<diamondop> x \<diamondop> y) \<diamondop> z = af_pure (\<lambda>f g x y z. f (g x y) z) \<diamondop> f \<diamondop> g \<diamondop> x \<diamondop> y \<diamondop> z" by applicative_nf rule
  have "\<forall>f g x y z. f \<diamondop> (g \<diamondop> (x \<diamondop> af_pure y)) \<diamondop> z = af_pure (\<lambda>f g x z. f (g (x y)) z) \<diamondop> f \<diamondop> g \<diamondop> x \<diamondop> z" by applicative_nf rule
  have "\<forall>f g x. f \<diamondop> (g \<diamondop> x \<diamondop> x) = af_pure (\<lambda>f g x x'. f (g x x')) \<diamondop> f \<diamondop> g \<diamondop> x \<diamondop> x" by applicative_nf rule
  have "\<forall>f x y. f x \<diamondop> y = af_pure (\<lambda>f x. f x) \<diamondop> f x \<diamondop> y" by applicative_nf rule
next
  fix f :: "('a \<Rightarrow> 'b) af" and g :: "('b \<Rightarrow> 'c) af" and x
  have "g \<diamondop> (f \<diamondop> x) = af_pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x" by applicative_nf rule
end
(* TODO automatic test for names of new variables *)

lemma "\<And>f x::'a af. f \<diamondop> x = x"
apply applicative_nf
oops

subsection \<open>Sets\<close>

instantiation set :: (plus) plus
begin
  definition set_plus_def[applicative_unfold]: "(X::('a::plus)set) + Y = {plus} \<diamondop> X \<diamondop> Y"
  instance ..
end

lemma "(X :: _ :: semigroup_add set) + Y + Z = X + (Y + Z)"
by (fact add.assoc[applicative_lifted set])

instantiation set :: (semigroup_add) semigroup_add begin
instance proof
  fix X Y Z :: "'a set"
  from add.assoc
  show "X + Y + Z = X + (Y + Z)" by applicative_lifting
qed
end

instantiation set :: (ab_semigroup_add) ab_semigroup_add begin
instance proof
  fix X Y :: "'a set"
  from add.commute
  show "X + Y = Y + X" by applicative_lifting
qed
end

subsection \<open>Sum type (a.k.a. either)\<close>

lemma "Inl plus \<diamondop> (x :: nat + 'e list) \<diamondop> x = Inl (\<lambda>x. 2 * x) \<diamondop> x"
by applicative_lifting simp

lemma "rel_sum (\<le>) (\<le>) (x :: nat + nat) (Inl Suc \<diamondop> x)"
proof -
  interpret either_af "(\<le>) :: nat \<Rightarrow> _" by unfold_locales (rule reflpI, simp)
  show ?thesis by applicative_lifting simp
qed


subsection \<open>Streams\<close>

lemma "(x::int stream) * sconst 0 = sconst 0"
by applicative_lifting simp

lemma "(x::int stream) * (y + z) = x * y + x * z"
by applicative_lifting algebra


definition "lift_streams xs = foldr (smap2 Cons) xs (sconst [])"

lemma lift_streams_Nil[applicative_unfold]: "lift_streams [] = sconst []"
unfolding lift_streams_def
by simp

lemma lift_streams_Cons[applicative_unfold]:
  "lift_streams (x # xs) = smap2 Cons x (lift_streams xs)"
unfolding lift_streams_def
by applicative_unfold

lemma stream_append_Cons: "smap2 append (smap2 Cons x ys) zs = smap2 Cons x (smap2 append ys zs)"
by applicative_lifting simp

lemma lift_streams_append[applicative_unfold]:
  "lift_streams (xs @ ys) = smap2 append (lift_streams xs) (lift_streams ys)"
proof (induction xs)
  case Nil
  (*
    case could be proved directly if "lift_streams ([] @ ys) = lift_streams ys" is solved
    in head_cong_tac (invoke simplifier?) -- but only with applicative_nf
  *)
  have "lift_streams ys = sconst append \<diamondop> lift_streams [] \<diamondop> lift_streams ys"
    by applicative_lifting simp
  thus ?case by applicative_unfold
next
  case (Cons x xs)
  with stream_append_Cons  (* the actual lifted fact *)
  show ?case by applicative_unfold (rule sym)
qed

lemma "lift_streams (rev x) = smap rev (lift_streams x)"
proof (induction x)
  case Nil
  have "lift_streams [] = smap rev (lift_streams [])"
    by applicative_lifting simp
  thus ?case by simp
next
  case (Cons x xs)
  have "\<forall>y ys. rev ys @ [y] = rev (y # ys)" by simp
  hence "\<forall>y ys. smap2 append (smap rev ys) (smap2 Cons y (sconst [])) = smap rev (smap2 Cons y ys)"
    by applicative_lifting simp
  with Cons.IH show ?case by applicative_unfold blast
qed

definition [applicative_unfold]: "sconcat xs = smap concat xs"

lemma "sconcat (lift_streams [sconst ''Hello '', sconst ''world!'']) = sconst ''Hello world!''"
by applicative_lifting simp


subsection \<open>Relators\<close>

lemma "rel_fun (=) (\<le>) (const (0::nat)) x"
by applicative_lifting simp

lemma "list_all2 (\<subseteq>) (map (\<lambda>_. {}) x) (map set x)"
by applicative_nf simp

lemma "x = Some a \<Longrightarrow> rel_option (\<le>) (map_option (\<lambda>_. a) x) (map_option Suc x)"
by applicative_lifting simp

schematic_goal "\<forall>g f x. rel_sum ?R (=) (ap_either f x) (ap_either (ap_either (Inl g) f) x)"
apply applicative_lifting
oops

schematic_goal "stream_all2 ?R (?f \<diamondop> (pure ?g \<diamondop> ?x + ?y)) (?x + ?z)"
apply applicative_lifting
oops


print_applicative

end
