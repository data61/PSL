(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Bound on Number of Arithmetic Operations for Integer Implementation\<close>

text \<open>In this section we define a version of the LLL algorithm which explicitly returns the
  costs of running the algorithm. Its soundness is mainly proven by stating that 
  projecting away yields the original result.

  The cost model counts the number of arithmetic operations that occur in vector-addition, scalar-products,
  and scalar multiplication and we prove a polynomial bound on this number.\<close>

theory LLL_Complexity
  imports 
    LLL_Impl
    Cost
    "HOL-Library.Discrete"
begin

definition round_num_denom_cost :: "int \<Rightarrow> int \<Rightarrow> int cost" where
  "round_num_denom_cost n d = ((2 * n + d) div (2 * d), 4)" \<comment> \<open>4 arith. operations\<close>

lemma round_num_denom_cost:  
  shows "result (round_num_denom_cost n d) = round_num_denom n d"  
   "cost (round_num_denom_cost n d) \<le> 4" 
  unfolding round_num_denom_cost_def round_num_denom_def by (auto simp: cost_simps) 

context LLL_with_assms
begin

context
  assumes \<alpha>_gt: "\<alpha> > 4/3" and m0: "m \<noteq> 0" 
begin


fun basis_reduction_add_rows_loop_cost where
  "basis_reduction_add_rows_loop_cost state i j [] = (state, 0)" 
| "basis_reduction_add_rows_loop_cost state i sj (fj # fjs) = (
     let fi = fi_state state;
         dsj = d_state state sj;
         j = sj - 1;
         (c,cost1) = round_num_denom_cost (dmu_ij_state state i j) dsj;
         state' = (if c = 0 then state else upd_fi_mu_state state i (vec n (\<lambda> i. fi $ i - c * fj $ i)) \<comment> \<open>2n arith. operations\<close>
             (IArray.of_fun (\<lambda> jj. let mu = dmu_ij_state state i jj in \<comment> \<open>3 sj arith. operations\<close>
                  if jj < j then mu - c * dmu_ij_state state j jj else 
                  if jj = j then mu - dsj * c else mu) i));
         local_cost = 2 * n + 3 * sj;
         (res,cost2) = basis_reduction_add_rows_loop_cost state' i j fjs
      in (res, cost1 + local_cost + cost2))"


lemma basis_reduction_add_rows_loop_cost: assumes "length fs = j" 
  shows "result (basis_reduction_add_rows_loop_cost state i j fs) = LLL_Impl.basis_reduction_add_rows_loop n state i j fs"  
   "cost (basis_reduction_add_rows_loop_cost state i j fs) \<le> sum (\<lambda> j. (2 * n + 4 + 3 * (Suc j))) {0..<j}" 
  using assms
proof (atomize(full), induct fs arbitrary: state j)
  case (Cons fj fs state j)
  let ?dm_ij = "dmu_ij_state state i (j - 1)" 
  let ?dj = "d_state state j" 
  obtain c1 fc where flc: "round_num_denom_cost ?dm_ij ?dj = (fc, c1)" by force
  from result_costD[OF round_num_denom_cost flc]
  have fl: "round_num_denom ?dm_ij ?dj = fc" and c1: "c1 \<le> 4" by auto
  obtain st where st: "(if fc = 0 then state
             else upd_fi_mu_state state i (vec n (\<lambda> i. fi_state state $ i - fc * fj $ i))
                   (IArray.of_fun
                     (\<lambda>jj. if jj < j - 1 then dmu_ij_state state i jj - fc * dmu_ij_state state (j - 1) jj
                           else if jj = j - 1 then dmu_ij_state state i jj - d_state state j * fc else dmu_ij_state state i jj)
                     i)) = st"  by auto
  obtain res c2 where rec: "basis_reduction_add_rows_loop_cost st i (j - 1) fs = (res,c2)" (is "?x = _") by (cases ?x, auto)
  from Cons(2) have "length fs = j - 1" by auto
  from result_costD'[OF Cons(1)[OF this] rec]
  have res: "LLL_Impl.basis_reduction_add_rows_loop n st i (j - 1) fs = res" 
    and c2: "c2 \<le> (\<Sum>j = 0..<j - 1. 2 * n + 4 + 3 * Suc j)" by auto
  show ?case unfolding basis_reduction_add_rows_loop_cost.simps Let_def flc split 
      LLL_Impl.basis_reduction_add_rows_loop.simps fl st rec res cost_simps
  proof (intro conjI refl, goal_cases)
    case 1 
    have "c1 + (2 * n + 3 * j) + c2 \<le> (\<Sum>j = 0..<j - 1. 2 * n + 4 + 3 * Suc j) + (2 * n + 4 + 3 * Suc (j - 1))" 
      using c1 c2 by auto
    also have "\<dots> = (\<Sum>j = 0..<j. 2 * n + 4 + 3 * (Suc j))" 
      by (subst (2) sum.remove[of _ "j - 1"], insert Cons(2), auto intro: sum.cong)
    finally show ?case .
  qed
qed (auto simp: cost_simps)

definition basis_reduction_add_rows_cost where
  "basis_reduction_add_rows_cost upw i state = 
     (if upw then basis_reduction_add_rows_loop_cost state i i (small_fs_state state) 
        else (state,0))" 

lemma basis_reduction_add_rows_cost: assumes impl: "LLL_impl_inv state i fs" and inv: "LLL_invariant upw i fs" 
  shows "result (basis_reduction_add_rows_cost upw i state) = LLL_Impl.basis_reduction_add_rows n upw i state"  
   "cost (basis_reduction_add_rows_cost upw i state) \<le> (2 * n + 2 * i + 7) * i"
proof (atomize (full), goal_cases)
  case 1
  note d = basis_reduction_add_rows_cost_def LLL_Impl.basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    thus ?thesis by (auto simp: d cost_simps)
  next
    case True
    hence upw: "upw = True" by simp
    obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
    from to_list_repr[OF impl inv state] 
    have len: "length (small_fs_state state) = i" 
      unfolding small_fs_state.simps state list_repr_def by auto
    let ?call = "basis_reduction_add_rows_cost upw i state" 
    have res: "result ?call = LLL_Impl.basis_reduction_add_rows n upw i state" 
      and cost: "cost ?call \<le> sum (\<lambda> j. (2 * n + 4 + 3 * (Suc j))) {0..<i}"
      unfolding d upw if_True using basis_reduction_add_rows_loop_cost[OF len, of state i] by auto
    note cost
    also have "sum (\<lambda> j. (2 * n + 4 + 3 * (Suc j))) {0..<i} = (2 * n + 7) * i + 3 * (\<Sum>j = 0..<i. j)" 
      by (auto simp: algebra_simps  sum.distrib sum_distrib_right sum_distrib_left)
    also have "(\<Sum>j = 0..<i. j) = (i * (i - 1) div 2)" 
    proof (induct i)
      case (Suc i)
      thus ?case by (cases i, auto)
    qed auto
    finally have "cost ?call \<le> (2 * n + 7) * i + 3 * (i * (i - 1) div 2)" .
    also have "\<dots> \<le> (2 * n + 7) * i + 2 * i * i" 
    proof (rule add_left_mono)
      have "3 * (i * (i - 1) div 2) \<le> 2 * i * (i - 1)" by simp
      also have "\<dots> \<le> 2 * i * i" by (intro mult_mono, auto)
      finally show "3 * (i * (i - 1) div 2) \<le> 2 * i * i" .
    qed
    also have "\<dots> = (2 * n + 2 * i + 7) * i" by (simp add: algebra_simps)
    finally have cost: "cost ?call \<le> (2 * n + 2 * i + 7) * i" .
    show ?thesis using res cost by simp
  qed
qed

definition swap_mu_cost :: "int iarray iarray \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int iarray iarray cost" where
  "swap_mu_cost dmu i dmu_i_im1 dim1 di dsi = (let im1 = i - 1;
       res = IArray.of_fun (\<lambda> ii. if ii < im1 then dmu !! ii else 
         if ii > i then let dmu_ii = dmu !! ii in 
             IArray.of_fun (\<lambda> j. let dmu_ii_j = dmu_ii !! j in   \<comment> \<open>8 arith. operations for whole line\<close>
                 if j = i then (dsi * dmu_ii !! im1 - dmu_i_im1 * dmu_ii_j) div di \<comment> \<open>4 arith. operations for this entry\<close>
                 else if j = im1 then (dmu_i_im1 * dmu_ii_j + dmu_ii !! i * dim1) div di \<comment> \<open>4 arith. operations for this entry\<close>
                 else dmu_ii_j) ii else 
         if ii = i then let mu_im1 = dmu !! im1 in 
             IArray.of_fun (\<lambda> j. if j = im1 then dmu_i_im1 else mu_im1 !! j) ii 
           else IArray.of_fun (\<lambda> j. dmu !! i !! j) ii) \<comment> \<open>ii = i - 1\<close>
         m; \<comment> \<open>in total, there are m - (i+1) many lines that require arithmetic operations: i + 1, ..., m - 1\<close>
       cost = 8 * (m - Suc i)
    in (res,cost))" 

lemma swap_mu_cost: 
   "result (swap_mu_cost dmu i dmu_i_im1 dim1 di dsi) = swap_mu m dmu i dmu_i_im1 dim1 di dsi"  
   "cost (swap_mu_cost dmu i dmu_i_im1 dim1 di dsi) \<le> 8 * (m - Suc i)" 
  by (auto simp: swap_mu_cost_def swap_mu_def Let_def cost_simps)

definition basis_reduction_swap_cost where
  "basis_reduction_swap_cost i state = (let 
       di = d_state state i;
       dsi = d_state state (Suc i);
       dim1 = d_state state (i - 1);
       fi = fi_state state;
       fim1 = fim1_state state;
       dmu_i_im1 = dmu_ij_state state i (i - 1);
       fi' = fim1;
       fim1' = fi;
       di' = (dsi * dim1 + dmu_i_im1 * dmu_i_im1) div di; \<comment> \<open>4 arith. operations\<close>
       local_cost = 4 
     in (case state of (f,dmus,djs) \<Rightarrow>
        case swap_mu_cost dmus i dmu_i_im1 dim1 di dsi of
          (swap_res, swap_cost) \<Rightarrow>
          let res = (False, i - 1, 
                     (dec_i (update_im1 (update_i f fi') fim1'), 
                      swap_res, 
                      iarray_update djs i di'));
              cost = local_cost + swap_cost 
         in (res, cost)))"

lemma basis_reduction_swap_cost: 
   "result (basis_reduction_swap_cost i state) = LLL_Impl.basis_reduction_swap m i state"  
   "cost (basis_reduction_swap_cost i state) \<le> 8 * (m - Suc i) + 4" 
proof (atomize(full), goal_cases)
  case 1
  obtain f dmus djs where state: "state = (f,dmus,djs)" by (cases state, auto)
  let ?mu = "dmu_ij_state (f, dmus, djs) i (i - 1)"
  let ?di1 = "d_state (f, dmus, djs) (i - 1)" 
  let ?di = "d_state (f, dmus, djs) i" 
  let ?dsi = "d_state (f, dmus, djs) (Suc i)" 
  show ?case unfolding basis_reduction_swap_cost_def LLL_Impl.basis_reduction_swap_def Let_def state split
    using swap_mu_cost[of dmus i ?mu ?di1 ?di ?dsi] 
    by (cases "swap_mu_cost dmus i ?mu ?di1 ?di ?dsi", auto simp: cost_simps)
qed

definition basis_reduction_step_cost where
  "basis_reduction_step_cost upw i state = (if i = 0 then ((True, Suc i, inc_state state), 0)
     else let 
       (state',cost_add) = basis_reduction_add_rows_cost upw i state;
       di = d_state state' i;
       dsi = d_state state' (Suc i);
       dim1 = d_state state' (i - 1);
       (num,denom) = quotient_of \<alpha>;
       cond = (di * di * denom \<le> num * dim1 * dsi); \<comment> \<open>5 arith. operations\<close>
       local_cost = 5
    in if cond then
          ((True, Suc i, inc_state state'), local_cost + cost_add) 
        else case basis_reduction_swap_cost i state' of (res, cost_swap) \<Rightarrow> (res, local_cost + cost_swap + cost_add))" 

definition "body_cost = 2 + (8 + 2 * n + 2 * m) * m" 

lemma basis_reduction_step_cost: assumes 
    impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and i: "i < m" 
  shows "result (basis_reduction_step_cost upw i state) = LLL_Impl.basis_reduction_step \<alpha> n m upw i state" (is ?g1)
     "cost (basis_reduction_step_cost upw i state) \<le> body_cost" (is ?g2)
proof -
  obtain state' c_add where add: "basis_reduction_add_rows_cost upw i state = (state',c_add)" 
    (is "?add = _") by (cases ?add, auto)
  obtain state'' c_swap where swapc: "basis_reduction_swap_cost i state' = (state'',c_swap)" 
    (is "?swap = _") by (cases ?swap, auto)
  note res = basis_reduction_step_cost_def[of upw i state, unfolded add split swap]
  from result_costD[OF basis_reduction_add_rows_cost[OF impl inv] add]
  have add: "LLL_Impl.basis_reduction_add_rows n upw i state = state'" 
    and c_add: "c_add \<le> (2 * n + 2 * i + 7) * i" 
    by auto
  from result_costD[OF basis_reduction_swap_cost swapc]
  have swap: "LLL_Impl.basis_reduction_swap m i state' = state''" 
    and c_swap: "c_swap \<le> 8 * (m - Suc i) + 4" by auto
  have "c_add + c_swap + 5 \<le> 8 * m + 2 + (2 * n + 2 * i) * i" 
    using c_add c_swap i by (auto simp: field_simps)
  also have "\<dots> \<le> 8 * m + 2 + (2 * n + 2 * m) * m" 
    by (intro add_left_mono mult_mono, insert i, auto)
  also have "\<dots> = 2 + (8 + 2 * n + 2 * m) * m" by (simp add: field_simps)
  finally have body: "c_add + c_swap + 5 \<le> body_cost" unfolding body_cost_def .
  obtain num denom where alpha: "quotient_of \<alpha> = (num,denom)" by force
  note res' = LLL_Impl.basis_reduction_step_def[of \<alpha> n m upw i state, unfolded add swap Let_def alpha split]
  note d = res res'
  show ?g1 unfolding d by (auto split: if_splits simp: cost_simps Let_def alpha swapc)
  show ?g2 unfolding d nat_distrib using body by (auto split: if_splits simp: cost_simps alpha Let_def swapc)
qed

partial_function (tailrec) basis_reduction_main_cost where
  "basis_reduction_main_cost upw i state c = (if i < m
     then let ((upw',i',state'), c_step) = basis_reduction_step_cost upw i state
       in basis_reduction_main_cost upw' i' state' (c + c_step)
     else (state, c))"

definition "num_loops = m + 2 * m * m * nat (ceiling (log base (real N)))"

lemma basis_reduction_main_cost: assumes impl: "LLL_impl_inv state i (fs_state state)" 
  and inv: "LLL_invariant upw i (fs_state state)" 
  and state: "state = initial_state m fs_init" 
  and i: "i = 0" 
  shows "result (basis_reduction_main_cost upw i state c) = LLL_Impl.basis_reduction_main \<alpha> n m upw i state" (is ?g1) 
   "cost (basis_reduction_main_cost upw i state c) \<le> c + body_cost * num_loops" (is ?g2)
proof -
  have ?g1 and cost: "cost (basis_reduction_main_cost upw i state c) \<le> c + body_cost * LLL_measure i (fs_state state)"
    using assms(1-2)
  proof (atomize (full), induct "LLL_measure i (fs_state state)" arbitrary: upw i state c rule: less_induct)
    case (less i state upw c)
    note inv = less(3)
    note impl = less(2)
    obtain i' upw' state' c_step where step: "basis_reduction_step_cost upw i state = ((upw',i',state'),c_step)" 
      (is "?step = _") by (cases ?step, auto)
    obtain state'' c_rec where rec: "basis_reduction_main_cost upw' i' state' (c + c_step) = (state'', c_rec)"
      (is "?rec = _") by (cases ?rec, auto)
    note step' = result_costD[OF basis_reduction_step_cost[OF impl inv] step]
    note d = basis_reduction_main_cost.simps[of upw] step split rec 
        LLL_Impl.basis_reduction_main.simps[of _ _ _ upw] 
    show ?case 
    proof (cases "i < m")
      case i: True
      from step' i have step': "LLL_Impl.basis_reduction_step \<alpha> n m upw i state = (upw',i',state')"
         and c_step: "c_step \<le> body_cost" 
        by auto
      note d = d step'
      from basis_reduction_step[OF impl inv step' i refl]
      have impl': "LLL_impl_inv state' i' (fs_state state')" 
        and inv': "LLL_invariant upw' i' (fs_state state')"
        and meas: "LLL_measure i' (fs_state state') < LLL_measure i (fs_state state)" 
        by auto
      from result_costD'[OF less(1)[OF meas impl' inv'] rec]
      have rec': "LLL_Impl.basis_reduction_main \<alpha> n m upw' i' state' = state''" 
        and c_rec: "c_rec \<le> c + c_step + body_cost * LLL_measure i' (fs_state state')" by auto
      from c_step c_rec have "c_rec \<le> c + body_cost * Suc (LLL_measure i' (fs_state state'))" 
        by auto
      also have "\<dots> \<le> c + body_cost * LLL_measure i (fs_state state)" 
        using meas by (intro plus_right_mono mult_left_mono) auto
      finally show ?thesis using i inv impl by (auto simp: cost_simps d rec')
    next
      case False
      thus ?thesis unfolding d by (auto simp: cost_simps)
    qed
  qed
  show ?g1 by fact
  note cost also have "body_cost * LLL_measure i (fs_state state) \<le> body_cost * num_loops" 
  proof (rule mult_left_mono; linarith?)
    define l where "l = log base (real N)" 
    define k where "k = 2 * m * m" 
    obtain f mu ds where init: "initial_state m fs_init = (f,mu,ds)" by (cases "initial_state m fs_init", auto)
    from initial_state
    have fs: "fs_state (initial_state m fs_init) = fs_init" by auto
    have "LLL_measure i (fs_state state) \<le> nat (ceiling (m + k * l))" unfolding l_def k_def
      using LLL_measure_approx_fs_init[OF LLL_inv_initial_state \<alpha>_gt m0] unfolding state fs i
      by linarith
    also have "\<dots> \<le> num_loops" unfolding num_loops_def l_def[symmetric] k_def[symmetric]
      by (simp add: of_nat_ceiling times_right_mono)
    finally show "LLL_measure i (fs_state state) \<le> num_loops" .
  qed
  finally show ?g2
    by auto
qed


context fixes
  fs :: "int vec iarray" 
begin 
fun sigma_array_cost where
  "sigma_array_cost dmus dmusi dmusj dll l = (if l = 0 then (dmusi !! l * dmusj !! l, 1)
      else let l1 = l - 1; dll1 = dmus !! l1 !! l1;
        (sig, cost_rec) = sigma_array_cost dmus dmusi dmusj dll1 l1;
        res = (dll * sig + dmusi !! l * dmusj !! l) div dll1; \<comment> \<open>4 arith. operations\<close>
        local_cost = (4 :: nat)
        in
      (res, local_cost + cost_rec))"

declare sigma_array_cost.simps[simp del]

lemma sigma_array_cost: 
  "result (sigma_array_cost dmus dmusi dmusj dll l) = sigma_array dmus dmusi dmusj dll l"
  "cost (sigma_array_cost dmus dmusi dmusj dll l) \<le> 4 * l + 1" 
proof (atomize(full), induct l arbitrary: dll)
  case 0
  show ?case unfolding sigma_array_cost.simps[of _ _ _ _ 0] sigma_array.simps[of _ _ _ _ 0]
    by (simp add: cost_simps)
next
  case (Suc l)
  let ?sl = "Suc l" 
  let ?dll = "dmus !! (Suc l - 1) !! (Suc l - 1)" 
  show ?case unfolding sigma_array_cost.simps[of _ _ _ _ ?sl] sigma_array.simps[of _ _ _ _ ?sl] Let_def
    using Suc[of ?dll]
    by (auto split: prod.splits simp: cost_simps)
qed

function dmu_array_row_main_cost where
  "dmu_array_row_main_cost fi i dmus j = (if j \<ge> i then (dmus, 0)
     else let sj = Suc j; 
       dmus_i = dmus !! i;
       djj = dmus !! j !! j;
       (sigma, cost_sigma) = sigma_array_cost dmus dmus_i (dmus !! sj) djj j;
       dmu_ij = djj * (fi \<bullet> fs !! sj) - sigma; \<comment> \<open>2n + 2 arith. operations\<close>
       dmus' = iarray_update dmus i (iarray_append dmus_i dmu_ij);
       (res, cost_rec) = dmu_array_row_main_cost fi i dmus' sj;
       local_cost = 2 * n + 2
      in (res, cost_rec + cost_sigma + local_cost))" 
  by pat_completeness auto

termination by (relation "measure (\<lambda> (fi,i,dmus,j). i - j)", auto)

declare dmu_array_row_main_cost.simps[simp del]

lemma dmu_array_row_main_cost: assumes "j \<le> i" 
  shows "result (dmu_array_row_main_cost fi i dmus j) = dmu_array_row_main fs fi i dmus j"
  "cost (dmu_array_row_main_cost fi i dmus j) \<le> (\<Sum> jj \<in> {j ..< i}. 2 * n + 2 + 4 * jj + 1)" 
  using assms
proof (atomize(full), induct "i - j" arbitrary: j dmus)
  case (0 j dmus)
  hence j: "j = i" by auto
  thus ?case unfolding dmu_array_row_main_cost.simps[of _ _ _ j] 
    dmu_array_row_main.simps[of _ _ _ _ j]
    by (simp add: cost_simps)
next
  case (Suc l j dmus)
  from Suc(2) have id: "(i \<le> j) = False" "(j = i) = False" by auto
  let ?sl = "Suc l" 
  let ?dll = "dmus !! (Suc l - 1) !! (Suc l - 1)" 
  obtain sig c_sig where 
    sig_c: "sigma_array_cost dmus (dmus !! i) (dmus !! Suc j) (dmus !! j !! j) j = (sig,c_sig)" by force
  from result_costD[OF sigma_array_cost sig_c]
  have sig: "sigma_array dmus (dmus !! i) (dmus !! Suc j) (dmus !! j !! j) j = sig" 
    and c_sig: "c_sig \<le> 4 * j + 1" by auto
  obtain dmus' where 
    dmus': "iarray_update dmus i (iarray_append (dmus !! i) (dmus !! j !! j * (fi \<bullet> fs !! Suc j) - sig)) = dmus'" 
    by auto
  obtain res c_rec where rec_c: "dmu_array_row_main_cost fi i dmus' (Suc j) = (res, c_rec)" by force
  let ?c = "\<lambda> j. 2 * n + 2 + 4 * j + 1" 
  from Suc(2-3) have "l = i - Suc j" "Suc j \<le> i" by auto
  from Suc(1)[OF this, of dmus', unfolded rec_c cost_simps]
  have rec: "dmu_array_row_main fs fi i dmus' (Suc j) = res" 
   and c_rec: "c_rec \<le> (\<Sum>jj = Suc j..<i. ?c jj)" by auto
  have "c_rec + c_sig + 2 * n + 2 \<le> ?c j + (\<Sum>jj = Suc j..<i. ?c jj)" 
    using c_rec c_sig by auto
  also have "\<dots> = (\<Sum>jj = j..<i. ?c jj)" 
    by (subst (2) sum.remove[of _ j], insert Suc(2-), auto intro: sum.cong)
  finally have cost: "c_rec + c_sig + 2 * n + 2 \<le> (\<Sum>jj = j..<i. ?c jj)" by auto
  thus ?case unfolding dmu_array_row_main_cost.simps[of _ _ _ j] dmu_array_row_main.simps[of _ _ _ _ j] Let_def
    id if_False sig_c split sig dmus' rec rec_c cost_simps by auto
qed

definition dmu_array_row_cost where
  "dmu_array_row_cost dmus i = (let fi = fs !! i;
      sp = fi \<bullet> fs !! 0 \<comment> \<open>2n arith. operations\<close>;
      local_cost = 2 * n;
      (res, main_cost) = dmu_array_row_main_cost fi i (iarray_append dmus (IArray [sp])) 0 in 
      (res, local_cost + main_cost))" 

lemma dmu_array_row_cost: 
   "result (dmu_array_row_cost dmus i) = dmu_array_row fs dmus i"  
   "cost (dmu_array_row_cost dmus i) \<le> 2 * n + (2 * n + 1 + 2 * i) * i" 
proof (atomize(full), goal_cases)
  case 1
  let ?fi = "fs !! i"
  let ?arr = "iarray_append dmus (IArray [?fi \<bullet> fs !! 0])" 
  obtain res c_main where res_c: "dmu_array_row_main_cost ?fi i ?arr 0 = (res, c_main)" by force
  from result_costD[OF dmu_array_row_main_cost res_c]
  have res: "dmu_array_row_main fs ?fi i ?arr 0 = res" 
    and c_main: "c_main \<le> (\<Sum>jj = 0..<i. 2 * n + 2 + 4 * jj + 1)" by auto
  have "2 * n + c_main \<le> 2 * n + (\<Sum>jj = 0..<i. 2 * n + 2 + 4 * jj + 1)" using c_main by auto
  also have "\<dots> = 2 * n + (2 * n + 3) * i + 2 * (\<Sum>jj < i. 2 * jj)" 
    unfolding sum.distrib by (auto simp: sum_distrib_left field_simps intro: sum.cong)
  also have "(\<Sum>jj < i. 2 * jj) = i * (i - 1)" 
    by (induct i, force, rename_tac i, case_tac i, auto)
  finally have "2 * n + c_main \<le> 2 * n + (2 * n + 3 + 2 * (i - 1)) * i" by (simp add: field_simps)
  also have "\<dots> = 2 * n + (2 * n + 1 + 2 * i) * i" by (cases i, auto simp: field_simps)
  finally have "2 * n + c_main \<le> 2 * n + (2 * n + 1 + 2 * i) * i" .
  thus ?case unfolding dmu_array_row_cost_def Let_def dmu_array_row_def res_c res split cost_simps 
    by auto
qed

function dmu_array_cost where 
  "dmu_array_cost dmus i = (if i \<ge> m then (dmus,0) else 
    let (dmus', cost_row) = dmu_array_row_cost dmus i;
        (res, cost_rec) = dmu_array_cost dmus' (Suc i)
     in (res, cost_row + cost_rec))"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (dmus, i). m - i)", auto)

declare dmu_array_cost.simps[simp del]

lemma dmu_array_cost: assumes "i \<le> m" 
  shows "result (dmu_array_cost dmus i) = dmu_array fs m dmus i"  
   "cost (dmu_array_cost dmus i) \<le> (\<Sum> ii \<in> {i ..< m}. 2 * n + (2 * n + 1 + 2 * ii) * ii)" 
  using assms
proof (atomize(full), induct "m - i" arbitrary: i dmus)
  case (0 i dmus)
  hence i: "i = m" by auto
  thus ?case unfolding dmu_array_cost.simps[of _ i] 
    dmu_array.simps[of _ _ _ i]
    by (simp add: cost_simps)
next
  case (Suc k i dmus)
  obtain dmus' c_row where row_c: "dmu_array_row_cost dmus i = (dmus',c_row)" by force
  from result_costD[OF dmu_array_row_cost row_c]
  have row: "dmu_array_row fs dmus i = dmus'" 
    and c_row: "c_row \<le> 2 * n + (2 * n + 1 + 2 * i) * i" (is "_ \<le> ?c i") by auto
  from Suc have "k = m - Suc i" "Suc i \<le> m" 
    and id: "(m \<le> i) = False" "(i = m) = False" by auto
  note IH = Suc(1)[OF this(1-2)]
  obtain res c_rec where rec_c: "dmu_array_cost dmus' (Suc i) = (res, c_rec)" by force
  from result_costD'[OF IH rec_c]
  have rec: "dmu_array fs m dmus' (Suc i) = res" 
    and c_rec: "c_rec \<le> (\<Sum>ii = Suc i..<m. ?c ii)" by auto
  have "c_row + c_rec \<le> ?c i + (\<Sum>ii = Suc i..<m. ?c ii)" 
    using c_rec c_row by auto
  also have "\<dots> = (\<Sum>ii = i..<m. ?c ii)" 
    by (subst sum.atLeast_Suc_lessThan [of i]) (use Suc in auto)
  finally show ?case unfolding dmu_array_cost.simps[of _ i] 
    dmu_array.simps[of _ _ _ i] id if_False Let_def rec_c row_c row rec split cost_simps by auto
qed  
end (* fs *)

definition d\<mu>_impl_cost :: "int vec list \<Rightarrow> int iarray iarray cost" where
  "d\<mu>_impl_cost fs = dmu_array_cost (IArray fs) (IArray []) 0"  

lemma d\<mu>_impl_cost: "result (d\<mu>_impl_cost fs_init) = d\<mu>_impl fs_init" 
  "cost (d\<mu>_impl_cost fs_init) \<le> m * (m * (m + n + 2) + 2 * n + 1)" 
proof (atomize(full), goal_cases)
  case 1
  let ?fs = "IArray fs_init" 
  let ?dmus = "IArray []" 
  obtain res cost where res_c: "dmu_array_cost ?fs ?dmus 0 = (res, cost)" by force
  from result_costD[OF dmu_array_cost res_c]
  have res: "dmu_array ?fs m ?dmus 0 = res" 
    and cost: "cost \<le> (\<Sum>ii = 0..<m. 2 * n + (2 * n + 1 + 2 * ii) * ii) " by auto 
  note cost
  also have "(\<Sum>ii = 0..<m. 2 * n + (2 * n + 1 + 2 * ii) * ii) 
     = 2 * n * m + (2 * n + 1) * (\<Sum>ii = 0..<m.  ii) + 2 * (\<Sum>ii = 0..<m. ii * ii)" 
    by (auto simp: field_simps sum.distrib sum_distrib_left intro: sum.cong)
  also have "\<dots> \<le> 2 * n * m + (2 * n + 2) * (\<Sum>ii = 0..<m.  ii) + 2 * (\<Sum>ii = 0..<m. ii * ii)" 
    by auto
  also have "(2 * n + 2) * (\<Sum>ii = 0..<m.  ii) = (n + 1) * (2 * (\<Sum>ii = 0..<m.  ii))" by auto
  also have "2 * (\<Sum>ii = 0..<m.  ii) = m * (m - 1)" 
    by (induct m, force, rename_tac i, case_tac i, auto)
  also have "2 * (\<Sum>ii = 0..<m.  ii * ii) = (6 * (\<Sum>ii = 0..<m.  ii * ii)) div 3" by simp
  also have "6 * (\<Sum>ii = 0..<m.  ii * ii) = 2 * (m - 1)*(m-1)*(m-1) + 3 * (m - 1) * (m - 1) + (m - 1)" 
    by (induct m, simp, rename_tac i, case_tac i, auto simp: field_simps)
  finally have "cost \<le> 2 * n * m + (n + 1) * (m * (m - 1)) 
    + (2 * (m - 1) * (m - 1) * (m - 1) + 3 * (m - 1) * (m - 1) + (m - 1)) div 3" .
  also have "\<dots> \<le> 2 * n * m + (n + 1) * (m * m) + (3 * m * m * m + 3 * m * m + 3 * m) div 3" 
    by (intro add_mono div_le_mono mult_mono, auto)  
  also have "\<dots> = 2 * n * m + (n + 1) * (m * m) + (m * m * m + m * m + m)" 
    by simp
  also have "\<dots> = m * (m * (m + n + 2) + 2 * n + 1)" 
    by (simp add: algebra_simps)
  finally 
  show ?case unfolding d\<mu>_impl_cost_def d\<mu>_impl_def len res res_c cost_simps by simp
qed
  
definition "initial_gso_cost = m * (m * (m + n + 2) + 2 * n + 1)" 

definition "initial_state_cost fs = (let
  (dmus, cost) = d\<mu>_impl_cost fs;
  ds = IArray.of_fun (\<lambda> i. if i = 0 then 1 else let i1 = i - 1 in dmus !! i1 !! i1) (Suc m);
  dmus' = IArray.of_fun (\<lambda> i. let row_i = dmus !! i in
       IArray.of_fun (\<lambda> j. row_i !! j) i) m
  in ((([], fs), dmus', ds), cost) :: LLL_dmu_d_state cost)" 


definition basis_reduction_cost :: "_ \<Rightarrow> LLL_dmu_d_state cost" where 
  "basis_reduction_cost fs = (
    case initial_state_cost fs of (state1, c1) \<Rightarrow> 
    case basis_reduction_main_cost True 0 state1 0 of (state2, c2) \<Rightarrow> 
      (state2, c1 + c2))" 

definition reduce_basis_cost :: "_ \<Rightarrow> int vec list cost" where
  "reduce_basis_cost fs = (case fs of Nil \<Rightarrow> (fs, 0) | Cons f _ \<Rightarrow> 
    case basis_reduction_cost fs of (state,c) \<Rightarrow> 
    (fs_state state, c))" 

lemma initial_state_cost: "result (initial_state_cost fs_init) = initial_state m fs_init" (is ?g1)
  "cost (initial_state_cost fs_init) \<le> initial_gso_cost" (is ?g2)
proof -
  obtain st c where dmu: "d\<mu>_impl_cost fs_init = (st,c)" by force
  from d\<mu>_impl_cost[unfolded dmu cost_simps]
  have dmu': "d\<mu>_impl fs_init = st" and c: "c \<le> initial_gso_cost" 
    unfolding initial_gso_cost_def by auto
  show ?g1 ?g2 using c unfolding initial_state_cost_def dmu dmu' split cost_simps 
    initial_state_def Let_def by auto
qed

lemma basis_reduction_cost: 
   "result (basis_reduction_cost fs_init) = basis_reduction \<alpha> n fs_init"  (is ?g1)
   "cost (basis_reduction_cost fs_init) \<le> initial_gso_cost + body_cost * num_loops" (is ?g2)
proof -
  obtain state1 c1 where init: "initial_state_cost fs_init = (state1, c1)" (is "?init = _") by (cases ?init, auto)
  obtain state2 c2 where main: "basis_reduction_main_cost True 0 state1 0 = (state2, c2)" (is "?main = _") by (cases ?main, auto)
  have res: "basis_reduction_cost fs_init = (state2, c1 + c2)" 
    unfolding basis_reduction_cost_def init main split by simp
  from result_costD[OF initial_state_cost init]
  have c1: "c1 \<le> initial_gso_cost" and init: "initial_state m fs_init = state1" by auto
  note inv = LLL_inv_initial_state(1)
  note impl = initial_state
  have fs: "fs_state (initial_state m fs_init) = fs_init" by fact
  from basis_reduction_main_cost[of "initial_state m fs_init" _ _ 0, unfolded fs, OF impl(1) inv,
    unfolded init main cost_simps] 
  have main: "LLL_Impl.basis_reduction_main \<alpha> n m True 0 state1 = state2" and c2: "c2 \<le> body_cost * num_loops" 
    by auto
  have res': "basis_reduction \<alpha> n fs_init = state2" unfolding basis_reduction_def len init main Let_def ..
  show ?g1 unfolding res res' cost_simps ..
  show ?g2 unfolding res cost_simps using c1 c2 by auto
qed

text \<open>The lemma for the LLL algorithm with explicit cost annotations @{const reduce_basis_cost}
  shows that the termination measure
  indeed gives rise to an explicit cost bound. Moreover, the computed result is
  the same as in the non-cost counting @{const reduce_basis}.\<close>

lemma reduce_basis_cost: 
   "result (reduce_basis_cost fs_init) = LLL_Impl.reduce_basis \<alpha> fs_init"  (is ?g1)
   "cost (reduce_basis_cost fs_init) \<le> initial_gso_cost + body_cost * num_loops" (is ?g2)
proof (atomize(full), goal_cases)
  case 1
  note d = reduce_basis_cost_def LLL_Impl.reduce_basis_def
  show ?case
  proof (cases fs_init)
    case Nil
    show ?thesis unfolding d unfolding Nil by (auto simp: cost_simps)
  next
    case (Cons f)
    obtain state c where b: "basis_reduction_cost fs_init = (state,c)" (is "?b = _") by (cases ?b, auto)
    from result_costD[OF basis_reduction_cost b]
    have bb: "basis_reduction \<alpha> n fs_init = state" and c: "c \<le> initial_gso_cost + body_cost * num_loops" 
      by auto
    from fs_init[unfolded Cons] have dim: "dim_vec f = n" by auto
    show ?thesis unfolding d b split unfolding Cons list.simps unfolding Cons[symmetric] dim bb
      using c by (auto simp: cost_simps)
  qed
qed

lemma mn: "m \<le> n"
  unfolding len[symmetric] using lin_dep length_map unfolding gs.lin_indpt_list_def
  by (metis distinct_card gs.dim_is_n gs.fin_dim gs.li_le_dim(2))

text \<open>Theorem with expanded costs: $O(n\cdot m^3 \cdot \log (\mathit{maxnorm}\ F))$ arithmetic operations\<close>
lemma reduce_basis_cost_expanded: 
  assumes "Lg \<ge> nat \<lceil>log (of_rat (4 * \<alpha> / (4 + \<alpha>))) N\<rceil>"   
  shows "cost (reduce_basis_cost fs_init)
  \<le> 4 * Lg * m * m * m * n
    + 4 * Lg * m * m * m * m
    + 16 * Lg * m * m * m
    + 4 * Lg * m * m
    + 3 * m * m * m
    + 3 * m * m * n 
    + 10 * m * m
    + 2 * n * m 
    + 3 * m" 
  (is "?cost \<le> ?exp Lg")
proof -
  define Log where "Log = nat \<lceil>log (of_rat (4 * \<alpha> / (4 + \<alpha>))) N\<rceil>" 
  have Lg: "Log \<le> Lg" using assms unfolding Log_def .
  have "?cost \<le> ?exp Log" 
    unfolding Log_def
    using reduce_basis_cost(2)[unfolded num_loops_def body_cost_def initial_gso_cost_def base_def]
    by (auto simp: algebra_simps) 
  also have "\<dots> \<le> ?exp Lg"
    by (intro add_mono mult_mono Lg, auto)
  finally show ?thesis .
qed

lemma reduce_basis_cost_0: assumes "m = 0" 
  shows "cost (reduce_basis_cost fs_init) = 0" 
proof -
  from len assms have fs_init: "fs_init = []" by auto
  thus ?thesis unfolding reduce_basis_cost_def by (simp add: cost_simps)
qed

lemma reduce_basis_cost_N:
  assumes "Lg \<ge> nat \<lceil>log (of_rat (4 * \<alpha> / (4 + \<alpha>))) N\<rceil>"   
  and 0: "Lg > 0"  
  shows "cost (reduce_basis_cost fs_init) \<le> 49 * m ^ 3 * n * Lg"
proof (cases "m > 0")
  case True
  with mn 0 have 0: "0 < Lg" "0 < m" "0 < n" by auto
  note reduce_basis_cost_expanded[OF assms(1)]
  also have "4 * Lg * m * m * m * n = 4 * m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "4 * Lg * m * m * m * m \<le> 4 * m ^ 3 * n * Lg"
    using 0 mn by (auto simp add: power3_eq_cube)
  also have "16 * Lg * m * m * m \<le> 16 * m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "4 * Lg * m * m \<le> 4 *  m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "3 * m * m * m \<le> 3 *  m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "3 * m * m * n \<le> 3 * m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "10 * m * m \<le> 10 * m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "2 * n * m  \<le> 2 * m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  also have "3 * m \<le> 3 * m ^ 3 * n * Lg"
    using 0 by (auto simp add: power3_eq_cube)
  finally show ?thesis
    by (auto simp add: algebra_simps)
next
  case False
  with reduce_basis_cost_0 show ?thesis by simp
qed

lemma reduce_basis_cost_M:
  assumes "Lg \<ge> nat \<lceil>log (of_rat (4 * \<alpha> / (4 + \<alpha>))) (M * n)\<rceil>"   
  and 0: "Lg > 0"
  shows "cost (reduce_basis_cost fs_init) \<le> 98 * m ^ 3 * n * Lg"
proof (cases "m > 0")
  case True
  let ?prod = "nat M * nat M * n" 
  let ?p = "nat M * nat M * n * n" 
  let ?lg = "real_of_int (M * n)" 
  from 0 True have m0: "m \<noteq> 0" by simp
  from LLL_inv_N_pos[OF LLL_inv_initial_state g_bound_fs_init m0] have N0: "N > 0" .
  from N_le_MMn[OF m0] have N_prod: "N \<le> ?prod" by auto
  from N0 N_prod have M0: "M > 0" by (cases "M \<le> 0", auto)
  from N0 N_prod have prod0: "0 < ?prod" by linarith
  from prod0 have n0: "n > 0" by auto
  from n0 prod0 M0 have prod_p: "?prod \<le> ?p" by auto
  with N_prod prod0 have N_p: "N \<le> ?p" and p0: "0 < ?p" by linarith+
  let ?base = "real_of_rat (4 * \<alpha> / (4 + \<alpha>))" 
  have base: "1 < ?base" using \<alpha>_gt by auto
  have Lg: "nat \<lceil>log ?base N\<rceil> \<le> nat \<lceil>log ?base ?p\<rceil>"
    by (intro nat_mono ceiling_mono log_mono, subst log_le_cancel_iff[OF base],
      insert M0 N_p N0 p0 n0, auto simp flip: of_int_mult of_nat_mult)
  also have "log ?base ?p = log ?base (?lg^2)" 
    using M0 by (simp add: power2_eq_square ac_simps)
  also have "\<dots> = 2 * log ?base ?lg" 
    by (subst log_nat_power, insert M0 n0, auto)
  finally have "nat \<lceil>log ?base N\<rceil> \<le> nat \<lceil>2 * log ?base ?lg\<rceil>" .
  also have "\<dots> \<le> 2 * Lg" using assms
    by linarith
  finally have Log: "nat \<lceil>log ?base N\<rceil> \<le> 2 * Lg" .
  from 0 have "0 < 2 * Lg" by simp
  from reduce_basis_cost_N[OF Log this]
  show ?thesis by simp
next
  case False
  with reduce_basis_cost_0 show ?thesis by simp
qed
  
  
end (* fixing arith_cost and assume \<alpha> > 4/3 *)
end (* LLL locale *)
end (* theory *)
