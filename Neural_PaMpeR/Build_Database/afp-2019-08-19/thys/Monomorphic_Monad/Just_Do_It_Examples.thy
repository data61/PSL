theory Just_Do_It_Examples imports Monomorphic_Monad begin

text \<open>Examples adapted from Gibbons and Hinze (ICFP 2011)\<close>

subsection \<open>Towers of Hanoi\<close>

type_synonym 'm tick = "'m \<Rightarrow> 'm"

locale monad_count_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes tick :: "'m tick"

locale monad_count = monad_count_base return bind tick + monad return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and tick :: "'m tick"
  +
  assumes bind_tick: "bind (tick m) f = tick (bind m f)"

locale hanoi_base = monad_count_base return bind tick
  for return :: "(unit, 'm) return"
  and bind :: "(unit, 'm) bind"
  and tick :: "'m tick"
begin

primrec hanoi :: "nat \<Rightarrow> 'm" where
  "hanoi 0 = return ()"
| "hanoi (Suc n) = bind (hanoi n) (\<lambda>_. tick (hanoi n))"

primrec repeat :: "nat \<Rightarrow> 'm \<Rightarrow> 'm"
where 
  "repeat 0 mx = return ()"
| "repeat (Suc n) mx = bind mx (\<lambda>_. repeat n mx)"

end

locale hanoi = hanoi_base return bind tick + monad_count return bind tick
  for return :: "(unit, 'm) return"
  and bind :: "(unit, 'm) bind"
  and tick :: "'m tick"
begin

lemma repeat_1: "repeat 1 mx = mx"
by(simp add: bind_return)

lemma repeat_add: "repeat (n + m) mx = bind (repeat n mx) (\<lambda>_. repeat m mx)"
by(induction n)(simp_all add: return_bind bind_assoc)

lemma hanoi_correct: "hanoi n = repeat (2 ^ n - 1) (tick (return ()))"
proof(induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  have "hanoi (Suc n) = repeat ((2 ^ n - 1) + 1 + (2 ^ n - 1)) (tick (return ()))"
    by(simp only: hanoi.simps repeat_add repeat_1 Suc.IH bind_assoc bind_tick return_bind)
  also have "(2 ^ n - 1) + 1 + (2 ^ n - 1) = (2 ^ Suc n - 1 :: nat)" by simp
  finally show ?case .
qed

end

subsection \<open>Fast product\<close>

locale fast_product_base = monad_catch_base return bind fail catch
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and catch :: "'m catch"
begin

primrec work :: "int list \<Rightarrow> 'm"
where 
  "work [] = return 1"
| "work (x # xs) = (if x = 0 then fail else bind (work xs) (\<lambda>i. return (x * i)))"

definition fastprod :: "int list \<Rightarrow> 'm"
  where "fastprod xs = catch (work xs) (return 0)"

end

locale fast_product = fast_product_base return bind fail catch + monad_catch return bind fail catch
   for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and catch :: "'m catch"
begin 

lemma work_alt_def: "work xs = (if 0 \<in> set xs then fail else return (prod_list xs))"
by(induction xs)(simp_all add: fail_bind return_bind)

lemma fastprod_correct: "fastprod xs = return (prod_list xs)"
by(simp add: fastprod_def work_alt_def catch_fail catch_return prod_list_zero_iff[symmetric])

end

end
