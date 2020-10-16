theory Benchmark_Bool imports
  Containers.Set_Impl 
begin

definition bool_DList :: "bool set"
where "bool_DList = insert True (insert False (DList_set DList_Set.empty))"

definition bool_RBT :: "bool set"
where "bool_RBT = insert True (insert False (RBT_set RBT_Set2.empty))"

definition mem :: "bool \<Rightarrow> bool set \<Rightarrow> bool"
where "mem = (:)"

ML_val \<open>
fun bool_DList () = @{code bool_DList}
fun bool_RBT () = @{code bool_RBT}
val mem = @{code mem}

fun test s =
  let val _ = mem true s;
      val _ = mem false s;
  in () end;

fun repeat _ 0 = ()
  | repeat f n = let val _ = f () in repeat f (n - 1) end

val iters = 1000000;

let
  val t_start = Timing.start ();
  val _ = repeat (test o bool_DList) iters;
  val t_stop = Timing.result t_start;
in Timing.message t_stop  
end;

let
  val t_start = Timing.start ();
  val _ = repeat (test o bool_RBT) iters;
  val t_stop = Timing.result t_start;
in Timing.message t_stop  
end;
\<close>

text \<open>
Test on 05.12.2012 on i44pc43 (Linux i44pc43 2.6.32-38-generic #83-Ubuntu SMP Wed Jan 4 11:12:07 UTC 2012 x86_64 GNU/Linux)

Timings (elapsed)
for 10000000:
@{term bool_DList}: 0.469, 0.475, 0.466, 0.461 (avg 0.468)
@{term bool_RBT}: 2.058, 2.047, 2.076, 2.029 (avg 2.05)

for 1000000:
@{term bool_DList}: 0.048, 0.048, 0.048, 0.053 (avg 0.049)
@{term bool_RBT}: 0.205, 0.206, 0.206, 0.205 (avg 0.206)
\<close>

end
