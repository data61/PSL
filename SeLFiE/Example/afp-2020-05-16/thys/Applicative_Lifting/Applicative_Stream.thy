(* Author:     Andreas Lochbihler, ETH Zurich
   Author:     Joshua Schneider, ETH Zurich
*)

subsection \<open>Streams as an applicative functor\<close>

theory Applicative_Stream imports
  Applicative
  "HOL-Library.Stream"
  "HOL-Library.Adhoc_Overloading"
begin

primcorec (transfer) ap_stream :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream"
where
    "shd (ap_stream f x) = shd f (shd x)"
  | "stl (ap_stream f x) = ap_stream (stl f) (stl x)"

adhoc_overloading Applicative.pure sconst
adhoc_overloading Applicative.ap ap_stream

context includes lifting_syntax applicative_syntax
begin

lemma ap_stream_id: "pure (\<lambda>x. x) \<diamondop> x = x"
by (coinduction arbitrary: x) simp

lemma ap_stream_homo: "pure f \<diamondop> pure x = pure (f x)"
by coinduction simp

lemma ap_stream_interchange: "f \<diamondop> pure x = pure (\<lambda>f. f x) \<diamondop> f"
by (coinduction arbitrary: f) auto

lemma ap_stream_composition: "pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
by (coinduction arbitrary: g f x) auto

applicative stream (S, K)
for
  pure: sconst
  ap: ap_stream
  rel: stream_all2
  set: sset
proof -
  fix g :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) stream" and f x
  show "pure (\<lambda>g f x. g x (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> x \<diamondop> (f \<diamondop> x)"
    by (coinduction arbitrary: g f x) auto
next
  fix x :: "'b stream" and y :: "'a stream"
  show "pure (\<lambda>x y. x) \<diamondop> x \<diamondop> y = x"
    by (coinduction arbitrary: x y) auto
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "(R ===> stream_all2 R) pure pure"
  proof
    fix x y
    assume "R x y"
    then show "stream_all2 R (pure x) (pure y)"
      by coinduction simp
  qed
next
  fix R and f :: "('a \<Rightarrow> 'b) stream" and g :: "('a \<Rightarrow> 'c) stream" and x
  assume [transfer_rule]: "stream_all2 (eq_on (sset x) ===> R) f g"
  have [transfer_rule]: "stream_all2 (eq_on (sset x)) x x" by(simp add: stream.rel_refl_strong)
  show "stream_all2 R (f \<diamondop> x) (g \<diamondop> x)" by transfer_prover
qed (rule ap_stream_homo)

lemma smap_applicative[applicative_unfold]: "smap f x = pure f \<diamondop> x"
unfolding ap_stream_def by (coinduction arbitrary: x) auto

lemma smap2_applicative[applicative_unfold]: "smap2 f x y = pure f \<diamondop> x \<diamondop> y"
unfolding ap_stream_def by (coinduction arbitrary: x y) auto

end

end
