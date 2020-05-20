section \<open>Test cases for dictionary construction\<close>

theory Test_Dict_Construction
imports
  Dict_Construction
  "HOL-Library.ListVector"
begin

subsection \<open>Code equations with different number of explicit arguments\<close>

lemma [code]: "fold f [] = id" "fold f (x # xs) s = fold f xs (f x s)" "fold f [x, y] u \<equiv> f y (f x u)"
by auto

experiment begin

  declassify valid: fold
  thm valid
  lemma "List_fold = fold" by (rule valid)

end

subsection \<open>Complex class hierarchies\<close>

local_setup \<open>Class_Graph.ensure_class @{class zero} #> snd\<close>
local_setup \<open>Class_Graph.ensure_class @{class plus} #> snd\<close>

experiment begin

  local_setup \<open>Class_Graph.ensure_class @{class comm_monoid_add} #> snd\<close>
  local_setup \<open>Class_Graph.ensure_class @{class ring} #> snd\<close>

  typ "nat Rings_ring__dict"

end

text \<open>Check that \<open>Class_Graph\<close> does not leak out of locales\<close>

ML\<open>@{assert} (is_none (Class_Graph.node @{context} @{class ring}))\<close>


subsection \<open>Instances with non-trivial arity\<close>

fun f :: "'a::plus \<Rightarrow> 'a" where
"f x = x + x"

definition g :: "'a::{plus,zero} list \<Rightarrow> 'a list" where
"g x = f x"

datatype natt = Z | S natt

instantiation natt :: "{zero,plus}" begin
  definition zero_natt where
  "zero_natt = Z"

  fun plus_natt where
  "plus_natt Z x = x" |
  "plus_natt (S m) n = S (plus_natt m n)"

  instance ..
end

definition h :: "natt list" where
"h = g [Z,S Z]"

experiment begin

(* FIXME problem with smart_tac *)
declassify valid: h
thm valid
lemma "Test__Dict__Construction_h = h" by (fact valid)

ML\<open>Dict_Construction.the_info @{context} @{const_name plus_natt_inst.plus_natt}\<close>

end

text \<open>Check that @{command declassify} does not leak out of locales\<close>

ML\<open>
  can (Dict_Construction.the_info @{context}) @{const_name plus_natt_inst.plus_natt}
  |> not |> @{assert}
\<close>


subsection \<open>[@{attribute fundef_cong}] rules\<close>

datatype 'a seq = Cons 'a "'a seq" | Nil

experiment begin

declassify map_seq

text \<open>Check presence of derived [@{attribute fundef_cong}] rule\<close>

ML\<open>
  Dict_Construction.the_info @{context} @{const_name map_seq}
  |> #fun_info
  |> the
  |> #fs
  |> the_single
  |> dest_Const
  |> fst
  |> Dict_Construction.cong_of_const @{context}
  |> the
\<close>

end


subsection \<open>Mutual recursion\<close>

fun odd :: "nat \<Rightarrow> bool" and even where
"odd 0 \<longleftrightarrow> False" |
"even 0 \<longleftrightarrow> True" |
"odd (Suc n) \<longleftrightarrow> even n" |
"even (Suc n) \<longleftrightarrow> odd n"

experiment begin

declassify valid: odd even
thm valid

end

datatype 'a bin_tree = Leaf | Node 'a "'a bin_tree" "'a bin_tree"

experiment begin

declassify valid: map_bin_tree rel_bin_tree
thm valid

end

datatype 'v env = Env "'v list"
datatype v = Closure "v env"

context
  notes is_measure_trivial[where f = "size_env size", measure_function]
begin

(* FIXME order is important! *)
fun test_v :: "v \<Rightarrow> bool" and test_w :: "v env \<Rightarrow> bool" where
"test_v (Closure env) \<longleftrightarrow> test_w env" |
"test_w (Env vs) \<longleftrightarrow> list_all test_v vs"

fun test_v1 :: "v \<Rightarrow> 'a::{one,monoid_add}" and test_w1 :: "v env \<Rightarrow> 'a" where
"test_v1 (Closure env) = 1 + test_w1 env" |
"test_w1 (Env vs) = sum_list (map test_v1 vs)"

end

experiment begin

declassify valid: test_w test_v
thm valid

end

experiment begin

(* FIXME derive fundef_cong rule for sum_list *)
declassify valid: test_w1 test_v1
thm valid

end


subsection \<open>Non-trivial code dependencies; code equations where the head is not fully general\<close>

definition "c \<equiv> 0 :: nat"
definition "d x \<equiv> if x = 0 then 0 else x"

lemma contrived[code]: "c = d 0" unfolding c_def d_def by simp

experiment begin

declassify valid: c
thm valid
lemma "Test__Dict__Construction_c = c" by (fact valid)

end


subsection \<open>Pattern matching on @{term "0::nat"}\<close>

definition j where "j (n::nat) = (0::nat)"

lemma [code]: "j 0 = 0" "j (Suc n) = j n"
unfolding j_def by auto

fun k where
"k 0 = (0::nat)" |
"k (Suc n) = k n"

lemma f_code[code]: "k n = 0"
by (induct n) simp+

experiment begin

declassify valid: j k
thm valid
lemma
  "Test__Dict__Construction_j = j"
  "Test__Dict__Construction_k = k"
by (fact valid)+

end


subsection \<open>Complex termination arguments\<close>

fun fac :: "nat \<Rightarrow> nat" where
"fac n = (if n \<le> 1 then 1 else n * fac (n - 1))"

experiment begin

declassify valid: fac

end


subsection \<open>Combination of various things\<close>

experiment begin

declassify valid: sum_list

end


subsection \<open>Interaction with the code generator\<close>

declassify h
export_code Test__Dict__Construction_h in SML


end