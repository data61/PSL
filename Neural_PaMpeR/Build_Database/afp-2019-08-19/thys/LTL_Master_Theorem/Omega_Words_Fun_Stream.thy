(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Convert between $\omega$-Words and Streams\<close>

theory Omega_Words_Fun_Stream
imports
  "HOL-Library.Omega_Words_Fun" "HOL-Library.Stream"
begin

(* TODO add to HOL-Library.Omega_Words_Fun *)

definition to_omega :: "'a stream \<Rightarrow> 'a word" where
  "to_omega \<equiv> snth"

definition to_stream :: "'a word \<Rightarrow> 'a stream" where
  "to_stream w \<equiv> smap w nats"


lemma to_omega_to_stream[simp]:
  "to_omega (to_stream w) = w"
  unfolding to_omega_def to_stream_def
  by auto

lemma to_stream_to_omega[simp]:
  "to_stream (to_omega s) = s"
  unfolding to_omega_def to_stream_def
  by (metis stream_smap_nats)

lemma bij_to_omega:
  "bij to_omega"
  by (metis bijI' to_omega_to_stream to_stream_to_omega)

lemma bij_to_stream:
  "bij to_stream"
  by (metis bijI' to_omega_to_stream to_stream_to_omega)

lemma image_intersection[simp]:
  "to_omega ` (A \<inter> B) = to_omega ` A \<inter> to_omega ` B"
  "to_stream ` (C \<inter> D) = to_stream ` C \<inter> to_stream ` D"
  by (simp_all add: bij_is_inj bij_to_omega bij_to_stream image_Int)

lemma to_stream_snth[simp]:
  "(to_stream w) !! k = w k"
  by (simp add: to_stream_def)

lemma to_omega_index[simp]:
  "(to_omega s) k = s !! k"
  by (metis to_stream_snth to_stream_to_omega)

lemma to_stream_stake[simp]:
  "stake k (to_stream w) = prefix k w"
  by (induction k) (simp add: to_stream_def)+

lemma to_omega_prefix[simp]:
  "prefix k (to_omega s) = stake k s"
  by (metis to_stream_stake to_stream_to_omega)

lemma in_image[simp]:
  "x \<in> to_omega ` X \<longleftrightarrow> to_stream x \<in> X"
  "y \<in> to_stream ` Y \<longleftrightarrow> to_omega y \<in> Y"
  by force+

end
