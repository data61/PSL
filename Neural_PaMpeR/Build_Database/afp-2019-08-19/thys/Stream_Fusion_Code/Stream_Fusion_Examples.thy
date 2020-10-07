(* Title: Stream_Fusion_Examples
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Examples and test cases for stream fusion\<close>

theory Stream_Fusion_Examples imports Stream_Fusion_LList begin

lemma fixes rhs z
  defines "rhs \<equiv> nth_cons (flatten (\<lambda>s'. s') (upto_prod 17) (upto_prod z)) (2, None) 8"
  shows "nth (List.maps (\<lambda>x. upto x 17) (upto 2 z)) 8 = rhs"
using [[simproc add: stream_fusion, stream_fusion_trace]]
apply(simp del: id_apply) \<comment> \<open>fuses\<close>
by(unfold rhs_def) rule

lemma fixes rhs z
  defines "rhs \<equiv> nth_cons (flatten (\<lambda>s. (s, 1)) (fix_gen (\<lambda>x. upto_prod (id x))) (upto_prod z)) (2, None) 8"
  shows "nth (List.maps (\<lambda>x. upto 1 (id x)) (upto 2 z)) 8 = rhs"
using [[simproc add: stream_fusion, stream_fusion_trace]]
apply(simp del: id_apply) \<comment> \<open>fuses\<close>
by(unfold rhs_def) rule

lemma fixes rhs n
  defines "rhs \<equiv> List.maps (\<lambda>x. [Suc 0..<sum_list_cons (replicate_prod x) x]) [2..<n]"
  shows "(concat (map (\<lambda>x. [1..<sum_list (replicate x x)]) [2..<n])) = rhs"
using [[simproc add: stream_fusion, stream_fusion_trace]]
apply(simp add: concat_map_maps) \<comment> \<open>fuses partially\<close>
by(unfold rhs_def) rule

subsection \<open>Micro-benchmarks from Farmer et al. \cite{FarmerHoenerGill2014PEPM}\<close>

definition test_enum :: "nat \<Rightarrow> nat" \<comment> \<open>@{const id} required to avoid eta contraction\<close>
where "test_enum n = foldl (+) 0 (List.maps (\<lambda>x. upt 1 (id x)) (upt 1 n))"

definition test_nested :: "nat \<Rightarrow> nat"
where "test_nested n = foldl (+) 0 (List.maps (\<lambda>x. List.maps (\<lambda>y. upt y x) (upt 1 x)) (upt 1 n))"

definition test_merge :: "integer \<Rightarrow> nat"
where "test_merge n = foldl (+) 0 (List.maps (\<lambda>x. if 2 dvd x then upt 1 x else upt 2 x) (upt 1 (nat_of_integer n)))"

text \<open>
  This rule performs the merge operation from \cite[\S 5.2]{FarmerHoenerGill2014PEPM} for \<open>if\<close>.
  In general, we would also need it for all case operators.
\<close>
lemma unstream_if [stream_fusion]:
  "unstream (if b then g else g') (if b then s else s') =
   (if b then unstream g s else unstream g' s')"
by simp

lemma if_same [code_unfold]: "(if b then x else x) = x"
by simp

code_thms test_enum
code_thms test_nested
code_thms test_merge

subsection \<open>Test stream fusion in the code generator\<close>

definition fuse_test :: integer
where "fuse_test = 
  integer_of_int (lhd (lfilter (\<lambda>x. x < 1) (lappend (lmap (\<lambda>x. x + 1) (llist_of (map (\<lambda>x. if x = 0 then undefined else x) [-3..5]))) (repeat 3))))"

ML_val \<open>val ~2 = @{code fuse_test}\<close> \<comment> \<open>If this test fails with exception Fail, then the stream fusion simproc failed. This test exploits
  that stream fusion introduces laziness.\<close>

end
