(* Title: thys/UF.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Construction of a Universal Function\<close>

theory UF
  imports Rec_Def HOL.GCD Abacus
begin

text \<open>
  This theory file constructs the Universal Function \<open>rec_F\<close>, which is the UTM defined
  in terms of recursive functions. This \<open>rec_F\<close> is essentially an 
  interpreter of Turing Machines. Once the correctness of \<open>rec_F\<close> is established,
  UTM can easil be obtained by compling \<open>rec_F\<close> into the corresponding Turing Machine.
\<close>

section \<open>Universal Function\<close>

subsection \<open>The construction of component functions\<close>

text \<open>
  The recursive function used to do arithmetic addition.
\<close>
definition rec_add :: "recf"
  where
    "rec_add \<equiv>  Pr 1 (id 1 0) (Cn 3 s [id 3 2])"

text \<open>
  The recursive function used to do arithmetic multiplication.
\<close>
definition rec_mult :: "recf"
  where
    "rec_mult = Pr 1 z (Cn 3 rec_add [id 3 0, id 3 2])"

text \<open>
  The recursive function used to do arithmetic precede.
\<close>
definition rec_pred :: "recf"
  where
    "rec_pred = Cn 1 (Pr 1 z (id 3 1)) [id 1 0, id 1 0]"

text \<open>
  The recursive function used to do arithmetic subtraction.
\<close>
definition rec_minus :: "recf" 
  where
    "rec_minus = Pr 1 (id 1 0) (Cn 3 rec_pred [id 3 2])"

text \<open>
  \<open>constn n\<close> is the recursive function which computes 
  nature number \<open>n\<close>.
\<close>
fun constn :: "nat \<Rightarrow> recf"
  where
    "constn 0 = z"  |
    "constn (Suc n) = Cn 1 s [constn n]"


text \<open>
  Sign function, which returns 1 when the input argument is greater than \<open>0\<close>.
\<close>
definition rec_sg :: "recf"
  where
    "rec_sg = Cn 1 rec_minus [constn 1, 
                  Cn 1 rec_minus [constn 1, id 1 0]]"

text \<open>
  \<open>rec_less\<close> compares its two arguments, returns \<open>1\<close> if
  the first is less than the second; otherwise returns \<open>0\<close>.
\<close>
definition rec_less :: "recf"
  where
    "rec_less = Cn 2 rec_sg [Cn 2 rec_minus [id 2 1, id 2 0]]"

text \<open>
  \<open>rec_not\<close> inverse its argument: returns \<open>1\<close> when the
  argument is \<open>0\<close>; returns \<open>0\<close> otherwise.
\<close>
definition rec_not :: "recf"
  where
    "rec_not = Cn 1 rec_minus [constn 1, id 1 0]"

text \<open>
  \<open>rec_eq\<close> compares its two arguments: returns \<open>1\<close>
  if they are equal; return \<open>0\<close> otherwise.
\<close>
definition rec_eq :: "recf"
  where
    "rec_eq = Cn 2 rec_minus [Cn 2 (constn 1) [id 2 0], 
             Cn 2 rec_add [Cn 2 rec_minus [id 2 0, id 2 1], 
               Cn 2 rec_minus [id 2 1, id 2 0]]]"

text \<open>
  \<open>rec_conj\<close> computes the conjunction of its two arguments, 
  returns \<open>1\<close> if both of them are non-zero; returns \<open>0\<close>
  otherwise.
\<close>
definition rec_conj :: "recf"
  where
    "rec_conj = Cn 2 rec_sg [Cn 2 rec_mult [id 2 0, id 2 1]] "

text \<open>
  \<open>rec_disj\<close> computes the disjunction of its two arguments, 
  returns \<open>0\<close> if both of them are zero; returns \<open>0\<close>
  otherwise.
\<close>
definition rec_disj :: "recf"
  where
    "rec_disj = Cn 2 rec_sg [Cn 2 rec_add [id 2 0, id 2 1]]"


text \<open>
  Computes the arity of recursive function.
\<close>

fun arity :: "recf \<Rightarrow> nat"
  where
    "arity z = 1" 
  | "arity s = 1"
  | "arity (id m n) = m"
  | "arity (Cn n f gs) = n"
  | "arity (Pr n f g) = Suc n"
  | "arity (Mn n f) = n"

text \<open>
  \<open>get_fstn_args n (Suc k)\<close> returns
  \<open>[id n 0, id n 1, id n 2, \<dots>, id n k]\<close>, 
  the effect of which is to take out the first \<open>Suc k\<close> 
  arguments out of the \<open>n\<close> input arguments.
\<close>

fun get_fstn_args :: "nat \<Rightarrow>  nat \<Rightarrow> recf list"
  where
    "get_fstn_args n 0 = []"
  | "get_fstn_args n (Suc y) = get_fstn_args n y @ [id n y]"

text \<open>
  \<open>rec_sigma f\<close> returns the recursive functions which 
  sums up the results of \<open>f\<close>:
  \[
  (rec\_sigma f)(x, y) = f(x, 0) + f(x, 1) + \cdots + f(x, y)
  \]
\<close>
fun rec_sigma :: "recf \<Rightarrow> recf"
  where
    "rec_sigma rf = 
       (let vl = arity rf in 
          Pr (vl - 1) (Cn (vl - 1) rf (get_fstn_args (vl - 1) (vl - 1) @ 
                    [Cn (vl - 1) (constn 0) [id (vl - 1) 0]])) 
             (Cn (Suc vl) rec_add [id (Suc vl) vl, 
                    Cn (Suc vl) rf (get_fstn_args (Suc vl) (vl - 1) 
                        @ [Cn (Suc vl) s [id (Suc vl) (vl - 1)]])]))"

text \<open>
  \<open>rec_exec\<close> is the interpreter function for
  reursive functions. The function is defined such that 
  it always returns meaningful results for primitive recursive 
  functions.
\<close>

declare rec_exec.simps[simp del] constn.simps[simp del]

text \<open>
  Correctness of \<open>rec_add\<close>.
\<close>
lemma add_lemma: "\<And> x y. rec_exec rec_add [x, y] =  x + y"
  by(induct_tac y, auto simp: rec_add_def rec_exec.simps)

text \<open>
  Correctness of \<open>rec_mult\<close>.
\<close>
lemma mult_lemma: "\<And> x y. rec_exec rec_mult [x, y] = x * y"
  by(induct_tac y, auto simp: rec_mult_def rec_exec.simps add_lemma)

text \<open>
  Correctness of \<open>rec_pred\<close>.
\<close>
lemma pred_lemma: "\<And> x. rec_exec rec_pred [x] =  x - 1"
  by(induct_tac x, auto simp: rec_pred_def rec_exec.simps)

text \<open>
  Correctness of \<open>rec_minus\<close>.
\<close>
lemma minus_lemma: "\<And> x y. rec_exec rec_minus [x, y] = x - y"
  by(induct_tac y, auto simp: rec_exec.simps rec_minus_def pred_lemma)

text \<open>
  Correctness of \<open>rec_sg\<close>.
\<close>
lemma sg_lemma: "\<And> x. rec_exec rec_sg [x] = (if x = 0 then 0 else 1)"
  by(auto simp: rec_sg_def minus_lemma rec_exec.simps constn.simps)

text \<open>
  Correctness of \<open>constn\<close>.
\<close>
lemma constn_lemma: "rec_exec (constn n) [x] = n"
  by(induct n, auto simp: rec_exec.simps constn.simps)

text \<open>
  Correctness of \<open>rec_less\<close>.
\<close>
lemma less_lemma: "\<And> x y. rec_exec rec_less [x, y] = 
  (if x < y then 1 else 0)"
  by(induct_tac y, auto simp: rec_exec.simps 
      rec_less_def minus_lemma sg_lemma)

text \<open>
  Correctness of \<open>rec_not\<close>.
\<close>
lemma not_lemma: 
  "\<And> x. rec_exec rec_not [x] = (if x = 0 then 1 else 0)"
  by(induct_tac x, auto simp: rec_exec.simps rec_not_def
      constn_lemma minus_lemma)

text \<open>
  Correctness of \<open>rec_eq\<close>.
\<close>
lemma eq_lemma: "\<And> x y. rec_exec rec_eq [x, y] = (if x = y then 1 else 0)"
  by(induct_tac y, auto simp: rec_exec.simps rec_eq_def constn_lemma add_lemma minus_lemma)

text \<open>
  Correctness of \<open>rec_conj\<close>.
\<close>
lemma conj_lemma: "\<And> x y. rec_exec rec_conj [x, y] = (if x = 0 \<or> y = 0 then 0 
                                                       else 1)"
  by(induct_tac y, auto simp: rec_exec.simps sg_lemma rec_conj_def mult_lemma)

text \<open>
  Correctness of \<open>rec_disj\<close>.
\<close>
lemma disj_lemma: "\<And> x y. rec_exec rec_disj [x, y] = (if x = 0 \<and> y = 0 then 0
                                                     else 1)"
  by(induct_tac y, auto simp: rec_disj_def sg_lemma add_lemma rec_exec.simps)


text \<open>
  \<open>primrec recf n\<close> is true iff 
  \<open>recf\<close> is a primitive recursive function 
  with arity \<open>n\<close>.
\<close>
inductive primerec :: "recf \<Rightarrow> nat \<Rightarrow> bool"
  where
    prime_z[intro]:  "primerec z (Suc 0)" |
    prime_s[intro]:  "primerec s (Suc 0)" |
    prime_id[intro!]: "\<lbrakk>n < m\<rbrakk> \<Longrightarrow> primerec (id m n) m" |
    prime_cn[intro!]: "\<lbrakk>primerec f k; length gs = k; 
  \<forall> i < length gs. primerec (gs ! i) m; m = n\<rbrakk> 
  \<Longrightarrow> primerec (Cn n f gs) m" |
    prime_pr[intro!]: "\<lbrakk>primerec f n; 
  primerec g (Suc (Suc n)); m = Suc n\<rbrakk> 
  \<Longrightarrow> primerec (Pr n f g) m" 

inductive_cases prime_cn_reverse'[elim]: "primerec (Cn n f gs) n" 
inductive_cases prime_mn_reverse: "primerec (Mn n f) m" 
inductive_cases prime_z_reverse[elim]: "primerec z n"
inductive_cases prime_s_reverse[elim]: "primerec s n"
inductive_cases prime_id_reverse[elim]: "primerec (id m n) k"
inductive_cases prime_cn_reverse[elim]: "primerec (Cn n f gs) m"
inductive_cases prime_pr_reverse[elim]: "primerec (Pr n f g) m"

declare mult_lemma[simp] add_lemma[simp] pred_lemma[simp] 
  minus_lemma[simp] sg_lemma[simp] constn_lemma[simp] 
  less_lemma[simp] not_lemma[simp] eq_lemma[simp]
  conj_lemma[simp] disj_lemma[simp]

text \<open>
  \<open>Sigma\<close> is the logical specification of 
  the recursive function \<open>rec_sigma\<close>.
\<close>
function Sigma :: "(nat list \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "Sigma g xs = (if last xs = 0 then g xs
                 else (Sigma g (butlast xs @ [last xs - 1]) +
                       g xs)) "
  by pat_completeness auto
termination
proof
  show "wf (measure (\<lambda> (f, xs). last xs))" by auto
next
  fix g xs
  assume "last (xs::nat list) \<noteq> 0"
  thus "((g, butlast xs @ [last xs - 1]), g, xs)  
                   \<in> measure (\<lambda>(f, xs). last xs)"
    by auto
qed

declare rec_exec.simps[simp del] get_fstn_args.simps[simp del]
  arity.simps[simp del] Sigma.simps[simp del]
  rec_sigma.simps[simp del]

lemma rec_pr_Suc_simp_rewrite: 
  "rec_exec (Pr n f g) (xs @ [Suc x]) =
                       rec_exec g (xs @ [x] @ 
                        [rec_exec (Pr n f g) (xs @ [x])])"
  by(simp add: rec_exec.simps)

lemma Sigma_0_simp_rewrite:
  "Sigma f (xs @ [0]) = f (xs @ [0])"
  by(simp add: Sigma.simps)

lemma Sigma_Suc_simp_rewrite: 
  "Sigma f (xs @ [Suc x]) = Sigma f (xs @ [x]) + f (xs @ [Suc x])"
  by(simp add: Sigma.simps)

lemma append_access_1[simp]: "(xs @ ys) ! (Suc (length xs)) = ys ! 1"
  by(simp add: nth_append)

lemma get_fstn_args_take: "\<lbrakk>length xs = m; n \<le> m\<rbrakk> \<Longrightarrow> 
  map (\<lambda> f. rec_exec f xs) (get_fstn_args m n)= take n xs"
proof(induct n)
  case 0 thus "?case"
    by(simp add: get_fstn_args.simps)
next
  case (Suc n) thus "?case"
    by(simp add: get_fstn_args.simps rec_exec.simps 
        take_Suc_conv_app_nth)
qed

lemma arity_primerec[simp]: "primerec f n \<Longrightarrow> arity f = n"
  apply(cases f)
       apply(auto simp: arity.simps )
  apply(erule_tac prime_mn_reverse)
  done

lemma rec_sigma_Suc_simp_rewrite: 
  "primerec f (Suc (length xs))
    \<Longrightarrow> rec_exec (rec_sigma f) (xs @ [Suc x]) = 
    rec_exec (rec_sigma f) (xs @ [x]) + rec_exec f (xs @ [Suc x])"
  apply(induct x)
   apply(auto simp: rec_sigma.simps Let_def rec_pr_Suc_simp_rewrite
      rec_exec.simps get_fstn_args_take)
  done      

text \<open>
  The correctness of \<open>rec_sigma\<close> with respect to its specification.
\<close>
lemma sigma_lemma: 
  "primerec rg (Suc (length xs))
     \<Longrightarrow> rec_exec (rec_sigma rg) (xs @ [x]) = Sigma (rec_exec rg) (xs @ [x])"
  apply(induct x)
   apply(auto simp: rec_exec.simps rec_sigma.simps Let_def 
      get_fstn_args_take Sigma_0_simp_rewrite
      Sigma_Suc_simp_rewrite) 
  done

text \<open>
  \<open>rec_accum f (x1, x2, \<dots>, xn, k) = 
           f(x1, x2, \<dots>, xn, 0) * 
           f(x1, x2, \<dots>, xn, 1) *
               \<dots> 
           f(x1, x2, \<dots>, xn, k)\<close>
\<close>
fun rec_accum :: "recf \<Rightarrow> recf"
  where
    "rec_accum rf = 
       (let vl = arity rf in 
          Pr (vl - 1) (Cn (vl - 1) rf (get_fstn_args (vl - 1) (vl - 1) @ 
                     [Cn (vl - 1) (constn 0) [id (vl - 1) 0]])) 
             (Cn (Suc vl) rec_mult [id (Suc vl) (vl), 
                    Cn (Suc vl) rf (get_fstn_args (Suc vl) (vl - 1) 
                      @ [Cn (Suc vl) s [id (Suc vl) (vl - 1)]])]))"

text \<open>
  \<open>Accum\<close> is the formal specification of \<open>rec_accum\<close>.
\<close>
function Accum :: "(nat list \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "Accum f xs = (if last xs = 0 then f xs 
                     else (Accum f (butlast xs @ [last xs - 1]) *
                       f xs))"
  by pat_completeness auto
termination
proof
  show "wf (measure (\<lambda> (f, xs). last xs))"
    by auto
next
  fix f xs
  assume "last xs \<noteq> (0::nat)"
  thus "((f, butlast xs @ [last xs - 1]), f, xs) \<in> 
            measure (\<lambda>(f, xs). last xs)"
    by auto
qed

lemma rec_accum_Suc_simp_rewrite: 
  "primerec f (Suc (length xs))
    \<Longrightarrow> rec_exec (rec_accum f) (xs @ [Suc x]) = 
    rec_exec (rec_accum f) (xs @ [x]) * rec_exec f (xs @ [Suc x])"
  apply(induct x)
   apply(auto simp: rec_sigma.simps Let_def rec_pr_Suc_simp_rewrite
      rec_exec.simps get_fstn_args_take)
  done  

text \<open>
  The correctness of \<open>rec_accum\<close> with respect to its specification.
\<close>
lemma accum_lemma :
  "primerec rg (Suc (length xs))
     \<Longrightarrow> rec_exec (rec_accum rg) (xs @ [x]) = Accum (rec_exec rg) (xs @ [x])"
  apply(induct x)
   apply(auto simp: rec_exec.simps rec_sigma.simps Let_def 
      get_fstn_args_take)
  done

declare rec_accum.simps [simp del]

text \<open>
  \<open>rec_all t f (x1, x2, \<dots>, xn)\<close> 
  computes the charactrization function of the following FOL formula:
  \<open>(\<forall> x \<le> t(x1, x2, \<dots>, xn). (f(x1, x2, \<dots>, xn, x) > 0))\<close>
\<close>
fun rec_all :: "recf \<Rightarrow> recf \<Rightarrow> recf"
  where
    "rec_all rt rf = 
    (let vl = arity rf in
       Cn (vl - 1) rec_sg [Cn (vl - 1) (rec_accum rf) 
                 (get_fstn_args (vl - 1) (vl - 1) @ [rt])])"

lemma rec_accum_ex:
  assumes "primerec rf (Suc (length xs))"
  shows "(rec_exec (rec_accum rf) (xs @ [x]) = 0) = 
         (\<exists> t \<le> x. rec_exec rf (xs @ [t]) = 0)"
proof(induct x)
  case (Suc x)
  with assms show ?case 
    apply(auto simp add: rec_exec.simps rec_accum.simps get_fstn_args_take)
     apply(rename_tac t ta)
     apply(rule_tac x = ta in exI, simp)
    apply(case_tac "t = Suc x", simp_all)
    apply(rule_tac x = t in exI, simp) done
qed (insert assms,auto simp add: rec_exec.simps rec_accum.simps get_fstn_args_take)


text \<open>
  The correctness of \<open>rec_all\<close>.
\<close>
lemma all_lemma: 
  "\<lbrakk>primerec rf (Suc (length xs));
    primerec rt (length xs)\<rbrakk>
  \<Longrightarrow> rec_exec (rec_all rt rf) xs = (if (\<forall> x \<le> (rec_exec rt xs). 0 < rec_exec rf (xs @ [x])) then 1
                                                                                              else 0)"
  apply(auto simp: rec_all.simps)
   apply(simp add: rec_exec.simps map_append get_fstn_args_take split: if_splits)
   apply(drule_tac x = "rec_exec rt xs" in rec_accum_ex)
   apply(cases "rec_exec (rec_accum rf) (xs @ [rec_exec rt xs]) = 0", simp_all)
   apply force
  apply(simp add: rec_exec.simps map_append get_fstn_args_take)
  apply(drule_tac x = "rec_exec rt xs" in rec_accum_ex)
  apply(cases "rec_exec (rec_accum rf) (xs @ [rec_exec rt xs]) = 0")
   apply force+
  done

text \<open>
  \<open>rec_ex t f (x1, x2, \<dots>, xn)\<close> 
  computes the charactrization function of the following FOL formula:
  \<open>(\<exists> x \<le> t(x1, x2, \<dots>, xn). (f(x1, x2, \<dots>, xn, x) > 0))\<close>
\<close>
fun rec_ex :: "recf \<Rightarrow> recf \<Rightarrow> recf"
  where
    "rec_ex rt rf = 
       (let vl = arity rf in 
         Cn (vl - 1) rec_sg [Cn (vl - 1) (rec_sigma rf) 
                  (get_fstn_args (vl - 1) (vl - 1) @ [rt])])"

lemma rec_sigma_ex: 
  assumes "primerec rf (Suc (length xs))"
  shows "(rec_exec (rec_sigma rf) (xs @ [x]) = 0) = 
                          (\<forall> t \<le> x. rec_exec rf (xs @ [t]) = 0)"
proof(induct x)
  case (Suc x)
  from Suc assms show ?case
    by(auto simp add: rec_exec.simps rec_sigma.simps 
        get_fstn_args_take elim:le_SucE)
qed (insert assms,auto simp: get_fstn_args_take rec_exec.simps rec_sigma.simps)

text \<open>
  The correctness of \<open>ex_lemma\<close>.
\<close>
lemma ex_lemma:"
  \<lbrakk>primerec rf (Suc (length xs));
   primerec rt (length xs)\<rbrakk>
\<Longrightarrow> (rec_exec (rec_ex rt rf) xs =
    (if (\<exists> x \<le> (rec_exec rt xs). 0 <rec_exec rf (xs @ [x])) then 1
     else 0))"
  apply(auto simp: rec_exec.simps get_fstn_args_take split: if_splits)
   apply(drule_tac x = "rec_exec rt xs" in rec_sigma_ex, simp)
  apply(drule_tac x = "rec_exec rt xs" in rec_sigma_ex, simp)
  done

text \<open>
  Definition of \<open>Min[R]\<close> on page 77 of Boolos's book.
\<close>

fun Minr :: "(nat list \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat"
  where "Minr Rr xs w = (let setx = {y | y. (y \<le> w) \<and> Rr (xs @ [y])} in 
                        if (setx = {}) then (Suc w)
                                       else (Min setx))"

declare Minr.simps[simp del] rec_all.simps[simp del]

text \<open>
  The following is a set of auxilliary lemmas about \<open>Minr\<close>.
\<close>
lemma Minr_range: "Minr Rr xs w \<le> w \<or> Minr Rr xs w = Suc w"
  apply(auto simp: Minr.simps)
  apply(subgoal_tac "Min {x. x \<le> w \<and> Rr (xs @ [x])} \<le> x")
   apply(erule_tac order_trans, simp)
  apply(rule_tac Min_le, auto)
  done

lemma expand_conj_in_set: "{x. x \<le> Suc w \<and> Rr (xs @ [x])}
    = (if Rr (xs @ [Suc w]) then insert (Suc w) 
                              {x. x \<le> w \<and> Rr (xs @ [x])}
      else {x. x \<le> w \<and> Rr (xs @ [x])})"
  by (auto elim:le_SucE)

lemma Minr_strip_Suc[simp]: "Minr Rr xs w \<le> w \<Longrightarrow> Minr Rr xs (Suc w) = Minr Rr xs w"
  by(cases "\<forall>x\<le>w. \<not> Rr (xs @ [x])",auto simp add: Minr.simps expand_conj_in_set)

lemma x_empty_set[simp]: "\<forall>x\<le>w. \<not> Rr (xs @ [x]) \<Longrightarrow>  
                           {x. x \<le> w \<and> Rr (xs @ [x])} = {} "
  by auto

lemma Minr_is_Suc[simp]: "\<lbrakk>Minr Rr xs w = Suc w; Rr (xs @ [Suc w])\<rbrakk> \<Longrightarrow> 
                                       Minr Rr xs (Suc w) = Suc w"
  apply(simp add: Minr.simps expand_conj_in_set)
  apply(cases "\<forall>x\<le>w. \<not> Rr (xs @ [x])", auto)
  done

lemma Minr_is_Suc_Suc[simp]: "\<lbrakk>Minr Rr xs w = Suc w; \<not> Rr (xs @ [Suc w])\<rbrakk> \<Longrightarrow> 
                                   Minr Rr xs (Suc w) = Suc (Suc w)"
  apply(simp add: Minr.simps expand_conj_in_set)
  apply(cases "\<forall>x\<le>w. \<not> Rr (xs @ [x])", auto)
  apply(subgoal_tac "Min {x. x \<le> w \<and> Rr (xs @ [x])} \<in> 
                                {x. x \<le> w \<and> Rr (xs @ [x])}", simp)
  apply(rule_tac Min_in, auto)
  done

lemma Minr_Suc_simp: 
  "Minr Rr xs (Suc w) = 
      (if Minr Rr xs w \<le> w then Minr Rr xs w
       else if (Rr (xs @ [Suc w])) then (Suc w)
       else Suc (Suc w))"
  by(insert Minr_range[of Rr xs w], auto)

text \<open>
  \<open>rec_Minr\<close> is the recursive function 
  used to implement \<open>Minr\<close>:
  if \<open>Rr\<close> is implemented by a recursive function \<open>recf\<close>,
  then \<open>rec_Minr recf\<close> is the recursive function used to 
  implement \<open>Minr Rr\<close>
\<close>
fun rec_Minr :: "recf \<Rightarrow> recf"
  where
    "rec_Minr rf = 
     (let vl = arity rf
      in let rq = rec_all (id vl (vl - 1)) (Cn (Suc vl) 
              rec_not [Cn (Suc vl) rf 
                    (get_fstn_args (Suc vl) (vl - 1) @
                                        [id (Suc vl) (vl)])]) 
      in  rec_sigma rq)"

lemma length_getpren_params[simp]: "length (get_fstn_args m n) = n"
  by(induct n, auto simp: get_fstn_args.simps)

lemma length_app:
  "(length (get_fstn_args (arity rf - Suc 0)
                           (arity rf - Suc 0)
   @ [Cn (arity rf - Suc 0) (constn 0)
           [recf.id (arity rf - Suc 0) 0]]))
    = (Suc (arity rf - Suc 0))"
  apply(simp)
  done

lemma primerec_accum: "primerec (rec_accum rf) n \<Longrightarrow> primerec rf n"
  apply(auto simp: rec_accum.simps Let_def)
  apply(erule_tac prime_pr_reverse, simp)
  apply(erule_tac prime_cn_reverse, simp only: length_app)
  done

lemma primerec_all: "primerec (rec_all rt rf) n \<Longrightarrow>
                       primerec rt n \<and> primerec rf (Suc n)"
  apply(simp add: rec_all.simps Let_def)
  apply(erule_tac prime_cn_reverse, simp)
  apply(erule_tac prime_cn_reverse, simp)
  apply(erule_tac x = n in allE, simp add: nth_append primerec_accum)
  done

declare numeral_3_eq_3[simp]

lemma primerec_rec_pred_1[intro]: "primerec rec_pred (Suc 0)"
  apply(simp add: rec_pred_def)
  apply(rule_tac prime_cn, auto dest:less_2_cases[unfolded numeral One_nat_def])
  done

lemma primerec_rec_minus_2[intro]: "primerec rec_minus (Suc (Suc 0))"
  apply(auto simp: rec_minus_def)
  done

lemma primerec_constn_1[intro]: "primerec (constn n) (Suc 0)"
  apply(induct n)
   apply(auto simp: constn.simps)
  done

lemma primerec_rec_sg_1[intro]: "primerec rec_sg (Suc 0)" 
  apply(simp add: rec_sg_def)
  apply(rule_tac k = "Suc (Suc 0)" in prime_cn)
     apply(auto)
  apply(auto dest!:less_2_cases[unfolded numeral One_nat_def])
    apply( auto)
  done

lemma primerec_getpren[elim]: "\<lbrakk>i < n; n \<le> m\<rbrakk> \<Longrightarrow> primerec (get_fstn_args m n ! i) m"
  apply(induct n, auto simp: get_fstn_args.simps)
  apply(cases "i = n", auto simp: nth_append intro: prime_id)
  done

lemma primerec_rec_add_2[intro]: "primerec rec_add (Suc (Suc 0))"
  apply(simp add: rec_add_def)
  apply(rule_tac prime_pr, auto)
  done

lemma primerec_rec_mult_2[intro]:"primerec rec_mult (Suc (Suc 0))"
  apply(simp add: rec_mult_def )
  apply(rule_tac prime_pr, auto)
  using less_2_cases numeral_2_eq_2 by fastforce

lemma primerec_ge_2_elim[elim]: "\<lbrakk>primerec rf n; n \<ge> Suc (Suc 0)\<rbrakk>   \<Longrightarrow> 
                        primerec (rec_accum rf) n"
  apply(auto simp: rec_accum.simps)
   apply(simp add: nth_append, auto dest!:less_2_cases[unfolded numeral One_nat_def])
    apply force
   apply force
  apply(auto simp: nth_append)
  done

lemma primerec_all_iff: 
  "\<lbrakk>primerec rt n; primerec rf (Suc n); n > 0\<rbrakk> \<Longrightarrow> 
                                 primerec (rec_all rt rf) n"
  apply(simp add: rec_all.simps, auto)
    apply(auto, simp add: nth_append, auto)
  done

lemma primerec_rec_not_1[intro]: "primerec rec_not (Suc 0)"
  apply(simp add: rec_not_def)
  apply(rule prime_cn, auto dest!:less_2_cases[unfolded numeral One_nat_def])
  done

lemma Min_false1[simp]: "\<lbrakk>\<not> Min {uu. uu \<le> w \<and> 0 < rec_exec rf (xs @ [uu])} \<le> w;
       x \<le> w; 0 < rec_exec rf (xs @ [x])\<rbrakk>
      \<Longrightarrow>  False"
  apply(subgoal_tac "finite {uu. uu \<le> w \<and> 0 < rec_exec rf (xs @ [uu])}")
   apply(subgoal_tac "{uu. uu \<le> w \<and> 0 < rec_exec rf (xs @ [uu])} \<noteq> {}")
    apply(simp add: Min_le_iff, simp)
   apply(rule_tac x = x in exI, simp)
  apply(simp)
  done

lemma sigma_minr_lemma: 
  assumes prrf:  "primerec rf (Suc (length xs))"
  shows "UF.Sigma (rec_exec (rec_all (recf.id (Suc (length xs)) (length xs))
     (Cn (Suc (Suc (length xs))) rec_not
      [Cn (Suc (Suc (length xs))) rf (get_fstn_args (Suc (Suc (length xs))) 
       (length xs) @ [recf.id (Suc (Suc (length xs))) (Suc (length xs))])])))
      (xs @ [w]) =
       Minr (\<lambda>args. 0 < rec_exec rf args) xs w"
proof(induct w)
  let ?rt = "(recf.id (Suc (length xs)) ((length xs)))"
  let ?rf = "(Cn (Suc (Suc (length xs))) 
    rec_not [Cn (Suc (Suc (length xs))) rf 
    (get_fstn_args (Suc (Suc (length xs))) (length xs) @ 
                [recf.id (Suc (Suc (length xs))) 
    (Suc ((length xs)))])])"
  let ?rq = "(rec_all ?rt ?rf)"
  have prrf: "primerec ?rf (Suc (length (xs @ [0]))) \<and>
        primerec ?rt (length (xs @ [0]))"
    apply(auto simp: prrf nth_append)+
    done
  show "Sigma (rec_exec (rec_all ?rt ?rf)) (xs @ [0])
       = Minr (\<lambda>args. 0 < rec_exec rf args) xs 0"
    apply(simp add: Sigma.simps)
    apply(simp only: prrf all_lemma,  
        auto simp: rec_exec.simps get_fstn_args_take Minr.simps)
    apply(rule_tac Min_eqI, auto)
    done
next
  fix w
  let ?rt = "(recf.id (Suc (length xs)) ((length xs)))"
  let ?rf = "(Cn (Suc (Suc (length xs))) 
    rec_not [Cn (Suc (Suc (length xs))) rf 
    (get_fstn_args (Suc (Suc (length xs))) (length xs) @ 
                [recf.id (Suc (Suc (length xs))) 
    (Suc ((length xs)))])])"
  let ?rq = "(rec_all ?rt ?rf)"
  assume ind:
    "Sigma (rec_exec (rec_all ?rt ?rf)) (xs @ [w]) = Minr (\<lambda>args. 0 < rec_exec rf args) xs w"
  have prrf: "primerec ?rf (Suc (length (xs @ [Suc w]))) \<and>
        primerec ?rt (length (xs @ [Suc w]))"
    apply(auto simp: prrf nth_append)+
    done
  show "UF.Sigma (rec_exec (rec_all ?rt ?rf))
         (xs @ [Suc w]) =
        Minr (\<lambda>args. 0 < rec_exec rf args) xs (Suc w)"
    apply(auto simp: Sigma_Suc_simp_rewrite ind Minr_Suc_simp)
       apply(simp_all only: prrf all_lemma)
       apply(auto simp: rec_exec.simps get_fstn_args_take Let_def Minr.simps split: if_splits)
       apply(drule_tac Min_false1, simp, simp, simp)
      apply (metis le_SucE neq0_conv)
     apply(drule_tac Min_false1, simp, simp, simp)
    apply(drule_tac Min_false1, simp, simp, simp)
    done
qed

text \<open>
  The correctness of \<open>rec_Minr\<close>.
\<close>
lemma Minr_lemma: "
  \<lbrakk>primerec rf (Suc (length xs))\<rbrakk> 
     \<Longrightarrow> rec_exec (rec_Minr rf) (xs @ [w]) = 
            Minr (\<lambda> args. (0 < rec_exec rf args)) xs w"
proof -
  let ?rt = "(recf.id (Suc (length xs)) ((length xs)))"
  let ?rf = "(Cn (Suc (Suc (length xs))) 
    rec_not [Cn (Suc (Suc (length xs))) rf 
    (get_fstn_args (Suc (Suc (length xs))) (length xs) @ 
                [recf.id (Suc (Suc (length xs))) 
    (Suc ((length xs)))])])"
  let ?rq = "(rec_all ?rt ?rf)"
  assume h: "primerec rf (Suc (length xs))"
  have h1: "primerec ?rq (Suc (length xs))"
    apply(rule_tac primerec_all_iff)
      apply(auto simp: h nth_append)+
    done
  moreover have "arity rf = Suc (length xs)"
    using h by auto
  ultimately show "rec_exec (rec_Minr rf) (xs @ [w]) = 
    Minr (\<lambda> args. (0 < rec_exec rf args)) xs w"
    apply(simp add: arity.simps Let_def sigma_lemma all_lemma)
    apply(rule_tac  sigma_minr_lemma)
    apply(simp add: h)
    done
qed

text \<open>
  \<open>rec_le\<close> is the comparasion function 
  which compares its two arguments, testing whether the 
  first is less or equal to the second.
\<close>
definition rec_le :: "recf"
  where
    "rec_le = Cn (Suc (Suc 0)) rec_disj [rec_less, rec_eq]"

text \<open>
  The correctness of \<open>rec_le\<close>.
\<close>
lemma le_lemma: 
  "\<And>x y. rec_exec rec_le [x, y] = (if (x \<le> y) then 1 else 0)"
  by(auto simp: rec_le_def rec_exec.simps)

text \<open>
  Definition of \<open>Max[Rr]\<close> on page 77 of Boolos's book.
\<close>

fun Maxr :: "(nat list \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "Maxr Rr xs w = (let setx = {y. y \<le> w \<and> Rr (xs @[y])} in 
                  if setx = {} then 0
                  else Max setx)"

text \<open>
  \<open>rec_maxr\<close> is the recursive function 
  used to implementation \<open>Maxr\<close>.
\<close>
fun rec_maxr :: "recf \<Rightarrow> recf"
  where
    "rec_maxr rr = (let vl = arity rr in 
                  let rt = id (Suc vl) (vl - 1) in
                  let rf1 = Cn (Suc (Suc vl)) rec_le 
                    [id (Suc (Suc vl)) 
                     ((Suc vl)), id (Suc (Suc vl)) (vl)] in
                  let rf2 = Cn (Suc (Suc vl)) rec_not 
                      [Cn (Suc (Suc vl)) 
                           rr (get_fstn_args (Suc (Suc vl)) 
                            (vl - 1) @ 
                             [id (Suc (Suc vl)) ((Suc vl))])] in
                  let rf = Cn (Suc (Suc vl)) rec_disj [rf1, rf2] in
                  let Qf = Cn (Suc vl) rec_not [rec_all rt rf]
                  in Cn vl (rec_sigma Qf) (get_fstn_args vl vl @
                                                         [id vl (vl - 1)]))"

declare rec_maxr.simps[simp del] Maxr.simps[simp del] 
declare le_lemma[simp]

declare numeral_2_eq_2[simp]

lemma primerec_rec_disj_2[intro]: "primerec rec_disj (Suc (Suc 0))"
  apply(simp add: rec_disj_def, auto)
    apply(auto dest!:less_2_cases[unfolded numeral One_nat_def])
  done

lemma primerec_rec_less_2[intro]: "primerec rec_less (Suc (Suc 0))"
  apply(simp add: rec_less_def, auto)
    apply(auto dest!:less_2_cases[unfolded numeral One_nat_def])
  done

lemma primerec_rec_eq_2[intro]: "primerec rec_eq (Suc (Suc 0))"
  apply(simp add: rec_eq_def)
  apply(rule_tac prime_cn, auto dest!:less_2_cases[unfolded numeral One_nat_def])
       apply force+
  done

lemma primerec_rec_le_2[intro]: "primerec rec_le (Suc (Suc 0))"
  apply(simp add: rec_le_def)
  apply(rule_tac prime_cn, auto dest!:less_2_cases[unfolded numeral One_nat_def])
  done

lemma Sigma_0: "\<forall> i \<le> n. (f (xs @ [i]) = 0) \<Longrightarrow> 
                              Sigma f (xs @ [n]) = 0"
  apply(induct n, simp add: Sigma.simps)
  apply(simp add: Sigma_Suc_simp_rewrite)
  done

lemma Sigma_Suc[elim]: "\<forall>k<Suc w. f (xs @ [k]) = Suc 0
        \<Longrightarrow> Sigma f (xs @ [w]) = Suc w"
  apply(induct w)
   apply(simp add: Sigma.simps, simp)
  apply(simp add: Sigma.simps)
  done

lemma Sigma_max_point: "\<lbrakk>\<forall> k < ma. f (xs @ [k]) = 1;
        \<forall> k \<ge> ma. f (xs @ [k]) = 0; ma \<le> w\<rbrakk>
    \<Longrightarrow> Sigma f (xs @ [w]) = ma"
  apply(induct w, auto)
   apply(rule_tac Sigma_0, simp)
  apply(simp add: Sigma_Suc_simp_rewrite)
  using Sigma_Suc by fastforce

lemma Sigma_Max_lemma: 
  assumes prrf: "primerec rf (Suc (length xs))"
  shows "UF.Sigma (rec_exec (Cn (Suc (Suc (length xs))) rec_not
  [rec_all (recf.id (Suc (Suc (length xs))) (length xs))
  (Cn (Suc (Suc (Suc (length xs)))) rec_disj
  [Cn (Suc (Suc (Suc (length xs)))) rec_le
  [recf.id (Suc (Suc (Suc (length xs)))) (Suc (Suc (length xs))), 
  recf.id (Suc (Suc (Suc (length xs)))) (Suc (length xs))],
  Cn (Suc (Suc (Suc (length xs)))) rec_not
  [Cn (Suc (Suc (Suc (length xs)))) rf
  (get_fstn_args (Suc (Suc (Suc (length xs)))) (length xs) @ 
  [recf.id (Suc (Suc (Suc (length xs)))) (Suc (Suc (length xs)))])]])]))
  ((xs @ [w]) @ [w]) =
       Maxr (\<lambda>args. 0 < rec_exec rf args) xs w"
proof -
  let ?rt = "(recf.id (Suc (Suc (length xs))) ((length xs)))"
  let ?rf1 = "Cn (Suc (Suc (Suc (length xs))))
    rec_le [recf.id (Suc (Suc (Suc (length xs)))) 
    ((Suc (Suc (length xs)))), recf.id 
    (Suc (Suc (Suc (length xs)))) ((Suc (length xs)))]"
  let ?rf2 = "Cn (Suc (Suc (Suc (length xs)))) rf 
               (get_fstn_args (Suc (Suc (Suc (length xs))))
    (length xs) @ 
    [recf.id (Suc (Suc (Suc (length xs))))    
    ((Suc (Suc (length xs))))])"
  let ?rf3 = "Cn (Suc (Suc (Suc (length xs)))) rec_not [?rf2]"
  let ?rf = "Cn (Suc (Suc (Suc (length xs)))) rec_disj [?rf1, ?rf3]"
  let ?rq = "rec_all ?rt ?rf"
  let ?notrq = "Cn (Suc (Suc (length xs))) rec_not [?rq]"
  show "?thesis"
  proof(auto simp: Maxr.simps)
    assume h: "\<forall>x\<le>w. rec_exec rf (xs @ [x]) = 0"
    have "primerec ?rf (Suc (length (xs @ [w, i]))) \<and> 
          primerec ?rt (length (xs @ [w, i]))"
      using prrf
      apply(auto dest!:less_2_cases[unfolded numeral One_nat_def])
            apply force+
      apply(case_tac ia, auto simp: h nth_append primerec_getpren)
      done
    hence "Sigma (rec_exec ?notrq) ((xs@[w])@[w]) = 0"
      apply(rule_tac Sigma_0)
      apply(auto simp: rec_exec.simps all_lemma
          get_fstn_args_take nth_append h)
      done
    thus "UF.Sigma (rec_exec ?notrq)
      (xs @ [w, w]) = 0"
      by simp
  next
    fix x
    assume h: "x \<le> w" "0 < rec_exec rf (xs @ [x])"
    hence "\<exists> ma. Max {y. y \<le> w \<and> 0 < rec_exec rf (xs @ [y])} = ma"
      by auto
    from this obtain ma where k1: 
      "Max {y. y \<le> w \<and> 0 < rec_exec rf (xs @ [y])} = ma" ..
    hence k2: "ma \<le> w \<and> 0 < rec_exec rf (xs @ [ma])"
      using h
      apply(subgoal_tac
          "Max {y. y \<le> w \<and> 0 < rec_exec rf (xs @ [y])} \<in>  {y. y \<le> w \<and> 0 < rec_exec rf (xs @ [y])}")
       apply(erule_tac CollectE, simp)
      apply(rule_tac Max_in, auto)
      done
    hence k3: "\<forall> k < ma. (rec_exec ?notrq (xs @ [w, k]) = 1)"
      apply(auto simp: nth_append)
      apply(subgoal_tac "primerec ?rf (Suc (length (xs @ [w, k]))) \<and> 
        primerec ?rt (length (xs @ [w, k]))")
       apply(auto simp: rec_exec.simps all_lemma get_fstn_args_take nth_append
          dest!:less_2_cases[unfolded numeral One_nat_def])
      using prrf
            apply force+
      done    
    have k4: "\<forall> k \<ge> ma. (rec_exec ?notrq (xs @ [w, k]) = 0)"
      apply(auto)
      apply(subgoal_tac "primerec ?rf (Suc (length (xs @ [w, k]))) \<and> 
        primerec ?rt (length (xs @ [w, k]))")
       apply(auto simp: rec_exec.simps all_lemma get_fstn_args_take nth_append)
       apply(subgoal_tac "x \<le> Max {y. y \<le> w \<and> 0 < rec_exec rf (xs @ [y])}",
          simp add: k1)
       apply(rule_tac Max_ge, auto dest!:less_2_cases[unfolded numeral One_nat_def])
      using prrf apply force+
      apply(auto simp: h nth_append)
      done 
    from k3 k4 k1 have "Sigma (rec_exec ?notrq) ((xs @ [w]) @ [w]) = ma"
      apply(rule_tac Sigma_max_point, simp, simp, simp add: k2)
      done
    from k1 and this show "Sigma (rec_exec ?notrq) (xs @ [w, w]) =
      Max {y. y \<le> w \<and> 0 < rec_exec rf (xs @ [y])}"
      by simp
  qed  
qed

text \<open>
  The correctness of \<open>rec_maxr\<close>.
\<close>
lemma Maxr_lemma:
  assumes h: "primerec rf (Suc (length xs))"
  shows   "rec_exec (rec_maxr rf) (xs @ [w]) = 
            Maxr (\<lambda> args. 0 < rec_exec rf args) xs w"
proof -
  from h have "arity rf = Suc (length xs)"
    by auto
  thus "?thesis"
  proof(simp add: rec_exec.simps rec_maxr.simps nth_append get_fstn_args_take)
    let ?rt = "(recf.id (Suc (Suc (length xs))) ((length xs)))"
    let ?rf1 = "Cn (Suc (Suc (Suc (length xs))))
                     rec_le [recf.id (Suc (Suc (Suc (length xs)))) 
              ((Suc (Suc (length xs)))), recf.id 
             (Suc (Suc (Suc (length xs)))) ((Suc (length xs)))]"
    let ?rf2 = "Cn (Suc (Suc (Suc (length xs)))) rf 
               (get_fstn_args (Suc (Suc (Suc (length xs))))
                (length xs) @ 
                  [recf.id (Suc (Suc (Suc (length xs))))    
                           ((Suc (Suc (length xs))))])"
    let ?rf3 = "Cn (Suc (Suc (Suc (length xs)))) rec_not [?rf2]"
    let ?rf = "Cn (Suc (Suc (Suc (length xs)))) rec_disj [?rf1, ?rf3]"
    let ?rq = "rec_all ?rt ?rf"
    let ?notrq = "Cn (Suc (Suc (length xs))) rec_not [?rq]"
    have prt: "primerec ?rt (Suc (Suc (length xs)))"
      by(auto intro: prime_id)
    have prrf: "primerec ?rf (Suc (Suc (Suc (length xs))))"
      apply(auto dest!:less_2_cases[unfolded numeral One_nat_def])
            apply force+
        apply(auto intro: prime_id)
       apply(simp add: h)
      apply(auto simp add: nth_append)
      done
    from prt and prrf have prrq: "primerec ?rq 
                                       (Suc (Suc (length xs)))"
      by(erule_tac primerec_all_iff, auto)
    hence prnotrp: "primerec ?notrq (Suc (length ((xs @ [w]))))"
      by(rule_tac prime_cn, auto)
    have g1: "rec_exec (rec_sigma ?notrq) ((xs @ [w]) @ [w]) 
      = Maxr (\<lambda>args. 0 < rec_exec rf args) xs w"
      using prnotrp
      using sigma_lemma
      apply(simp only: sigma_lemma)
      apply(rule_tac Sigma_Max_lemma)
      apply(simp add: h)
      done
    thus "rec_exec (rec_sigma ?notrq)
     (xs @ [w, w]) =
    Maxr (\<lambda>args. 0 < rec_exec rf args) xs w"
      apply(simp)
      done
  qed
qed

text \<open>
  \<open>quo\<close> is the formal specification of division.
\<close>
fun quo :: "nat list \<Rightarrow> nat"
  where
    "quo [x, y] = (let Rr = 
                         (\<lambda> zs. ((zs ! (Suc 0) * zs ! (Suc (Suc 0))
                                 \<le> zs ! 0) \<and> zs ! Suc 0 \<noteq> (0::nat)))
                 in Maxr Rr [x, y] x)"

declare quo.simps[simp del]

text \<open>
  The following lemmas shows more directly the menaing of \<open>quo\<close>:
\<close>
lemma quo_is_div: "y > 0 \<Longrightarrow> quo [x, y] = x div y"
proof -
  {
    fix xa ya
    assume h: "y * ya \<le> x"  "y > 0"
    hence "(y * ya) div y \<le> x div y"
      by(insert div_le_mono[of "y * ya" x y], simp)
    from this and h have "ya \<le> x div y" by simp}
  thus ?thesis by(simp add: quo.simps Maxr.simps, auto,
        rule_tac Max_eqI, simp, auto)
qed

lemma quo_zero[intro]: "quo [x, 0] = 0"
  by(simp add: quo.simps Maxr.simps)

lemma quo_div: "quo [x, y] = x div y"  
  by(cases "y=0", auto elim!:quo_is_div)

text \<open>
  \<open>rec_noteq\<close> is the recursive function testing whether its
  two arguments are not equal.
\<close>
definition rec_noteq:: "recf"
  where
    "rec_noteq = Cn (Suc (Suc 0)) rec_not [Cn (Suc (Suc 0)) 
              rec_eq [id (Suc (Suc 0)) (0), id (Suc (Suc 0)) 
                                        ((Suc 0))]]"

text \<open>
  The correctness of \<open>rec_noteq\<close>.
\<close>
lemma noteq_lemma: 
  "\<And> x y. rec_exec rec_noteq [x, y] = 
               (if x \<noteq> y then 1 else 0)"
  by(simp add: rec_exec.simps rec_noteq_def)

declare noteq_lemma[simp]

text \<open>
  \<open>rec_quo\<close> is the recursive function used to implement \<open>quo\<close>
\<close>
definition rec_quo :: "recf"
  where
    "rec_quo = (let rR = Cn (Suc (Suc (Suc 0))) rec_conj
              [Cn (Suc (Suc (Suc 0))) rec_le 
               [Cn (Suc (Suc (Suc 0))) rec_mult 
                  [id (Suc (Suc (Suc 0))) (Suc 0), 
                     id (Suc (Suc (Suc 0))) ((Suc (Suc 0)))],
                id (Suc (Suc (Suc 0))) (0)], 
                Cn (Suc (Suc (Suc 0))) rec_noteq 
                         [id (Suc (Suc (Suc 0))) (Suc (0)),
                Cn (Suc (Suc (Suc 0))) (constn 0) 
                              [id (Suc (Suc (Suc 0))) (0)]]] 
              in Cn (Suc (Suc 0)) (rec_maxr rR)) [id (Suc (Suc 0)) 
                           (0),id (Suc (Suc 0)) (Suc (0)), 
                                   id (Suc (Suc 0)) (0)]"

lemma primerec_rec_conj_2[intro]: "primerec rec_conj (Suc (Suc 0))"
  apply(simp add: rec_conj_def)
  apply(rule_tac prime_cn, auto dest!:less_2_cases[unfolded numeral One_nat_def])
  done

lemma primerec_rec_noteq_2[intro]: "primerec rec_noteq (Suc (Suc 0))"
  apply(simp add: rec_noteq_def)
  apply(rule_tac prime_cn, auto dest!:less_2_cases[unfolded numeral One_nat_def])
  done


lemma quo_lemma1: "rec_exec rec_quo [x, y] = quo [x, y]"
proof(simp add: rec_exec.simps rec_quo_def)
  let ?rR = "(Cn (Suc (Suc (Suc 0))) rec_conj
               [Cn (Suc (Suc (Suc 0))) rec_le
                   [Cn (Suc (Suc (Suc 0))) rec_mult 
               [recf.id (Suc (Suc (Suc 0))) (Suc (0)), 
                recf.id (Suc (Suc (Suc 0))) (Suc (Suc (0)))],
                 recf.id (Suc (Suc (Suc 0))) (0)],  
          Cn (Suc (Suc (Suc 0))) rec_noteq 
                              [recf.id (Suc (Suc (Suc 0))) 
             (Suc (0)), Cn (Suc (Suc (Suc 0))) (constn 0) 
                      [recf.id (Suc (Suc (Suc 0))) (0)]]])"
  have "rec_exec (rec_maxr ?rR) ([x, y]@ [ x]) = Maxr (\<lambda> args. 0 < rec_exec ?rR args) [x, y] x"
  proof(rule_tac Maxr_lemma, simp)
    show "primerec ?rR (Suc (Suc (Suc 0)))"
      apply(auto dest!:less_2_cases[unfolded numeral One_nat_def]) 
             apply force+
      done
  qed
  hence g1: "rec_exec (rec_maxr ?rR) ([x, y,  x]) =
             Maxr (\<lambda> args. if rec_exec ?rR args = 0 then False
                           else True) [x, y] x" 
    by simp
  have g2: "Maxr (\<lambda> args. if rec_exec ?rR args = 0 then False
                           else True) [x, y] x = quo [x, y]"
    apply(simp add: rec_exec.simps)
    apply(simp add: Maxr.simps quo.simps, auto)
    done
  from g1 and g2 show 
    "rec_exec (rec_maxr ?rR) ([x, y,  x]) = quo [x, y]"
    by simp
qed

text \<open>
  The correctness of \<open>quo\<close>.
\<close>
lemma quo_lemma2: "rec_exec rec_quo [x, y] = x div y"
  using quo_lemma1[of x y] quo_div[of x y]
  by simp

text \<open>
  \<open>rec_mod\<close> is the recursive function used to implement 
  the reminder function.
\<close>
definition rec_mod :: "recf"
  where
    "rec_mod = Cn (Suc (Suc 0)) rec_minus [id (Suc (Suc 0)) (0), 
               Cn (Suc (Suc 0)) rec_mult [rec_quo, id (Suc (Suc 0))
                                                     (Suc (0))]]"

text \<open>
  The correctness of \<open>rec_mod\<close>:
\<close>
lemma mod_lemma: "\<And> x y. rec_exec rec_mod [x, y] = (x mod y)"
  by(simp add: rec_exec.simps rec_mod_def quo_lemma2 minus_div_mult_eq_mod)

text\<open>lemmas for embranch function\<close>
type_synonym ftype = "nat list \<Rightarrow> nat"
type_synonym rtype = "nat list \<Rightarrow> bool"

text \<open>
  The specifation of the mutli-way branching statement on
  page 79 of Boolos's book.
\<close>
fun Embranch :: "(ftype * rtype) list \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "Embranch [] xs = 0" |
    "Embranch (gc # gcs) xs = (
                   let (g, c) = gc in 
                   if c xs then g xs else Embranch gcs xs)"

fun rec_embranch' :: "(recf * recf) list \<Rightarrow> nat \<Rightarrow> recf"
  where
    "rec_embranch' [] vl = Cn vl z [id vl (vl - 1)]" |
    "rec_embranch' ((rg, rc) # rgcs) vl = Cn vl rec_add
                   [Cn vl rec_mult [rg, rc], rec_embranch' rgcs vl]"

text \<open>
  \<open>rec_embrach\<close> is the recursive function used to implement
  \<open>Embranch\<close>.
\<close>
fun rec_embranch :: "(recf * recf) list \<Rightarrow> recf"
  where
    "rec_embranch ((rg, rc) # rgcs) = 
         (let vl = arity rg in 
          rec_embranch' ((rg, rc) # rgcs) vl)"

declare Embranch.simps[simp del] rec_embranch.simps[simp del]

lemma embranch_all0: 
  "\<lbrakk>\<forall> j < length rcs. rec_exec (rcs ! j) xs = 0;
    length rgs = length rcs;  
  rcs \<noteq> []; 
  list_all (\<lambda> rf. primerec rf (length xs)) (rgs @ rcs)\<rbrakk>  \<Longrightarrow> 
  rec_exec (rec_embranch (zip rgs rcs)) xs = 0"
proof(induct rcs arbitrary: rgs)
  case (Cons a rcs)
  then show ?case proof(cases rgs, simp)  fix a rcs rgs aa list
    assume ind: 
      "\<And>rgs. \<lbrakk>\<forall>j<length rcs. rec_exec (rcs ! j) xs = 0; 
             length rgs = length rcs; rcs \<noteq> []; 
            list_all (\<lambda>rf. primerec rf (length xs)) (rgs @ rcs)\<rbrakk> \<Longrightarrow> 
                      rec_exec (rec_embranch (zip rgs rcs)) xs = 0"
      and h:  "\<forall>j<length (a # rcs). rec_exec ((a # rcs) ! j) xs = 0"
      "length rgs = length (a # rcs)" 
      "a # rcs \<noteq> []" 
      "list_all (\<lambda>rf. primerec rf (length xs)) (rgs @ a # rcs)"
      "rgs = aa # list"
    have g: "rcs \<noteq> [] \<Longrightarrow> rec_exec (rec_embranch (zip list rcs)) xs = 0"
      using h by(rule_tac ind, auto)
    show "rec_exec (rec_embranch (zip rgs (a # rcs))) xs = 0"
    proof(cases "rcs = []", simp)
      show "rec_exec (rec_embranch (zip rgs [a])) xs = 0"
        using h by (auto simp add: rec_embranch.simps rec_exec.simps)
    next
      assume "rcs \<noteq> []"
      hence "rec_exec (rec_embranch (zip list rcs)) xs = 0"
        using g by simp
      thus "rec_exec (rec_embranch (zip rgs (a # rcs))) xs = 0"
        using h
        by(cases rcs;cases list, auto simp add: rec_embranch.simps rec_exec.simps)
    qed
  qed
qed simp


lemma embranch_exec_0: "\<lbrakk>rec_exec aa xs = 0; zip rgs list \<noteq> []; 
       list_all (\<lambda> rf. primerec rf (length xs)) ([a, aa] @ rgs @ list)\<rbrakk>
       \<Longrightarrow> rec_exec (rec_embranch ((a, aa) # zip rgs list)) xs
         = rec_exec (rec_embranch (zip rgs list)) xs"
  apply(auto simp add: rec_exec.simps rec_embranch.simps)
  apply(cases "zip rgs list", force)
  apply(cases "hd (zip rgs list)", simp add: rec_embranch.simps rec_exec.simps)
  apply(subgoal_tac "arity a = length xs")
   apply(cases rgs;cases list;force)
  by force

lemma zip_null_iff: "\<lbrakk>length xs = k; length ys = k; zip xs ys = []\<rbrakk> \<Longrightarrow> xs = [] \<and> ys = []"
  apply(cases xs, simp, simp)
  apply(cases ys, simp, simp)
  done

lemma zip_null_gr: "\<lbrakk>length xs = k; length ys = k; zip xs ys \<noteq> []\<rbrakk> \<Longrightarrow> 0 < k"
  apply(cases xs, simp, simp)
  done

lemma Embranch_0:  
  "\<lbrakk>length rgs = k; length rcs = k; k > 0; 
  \<forall> j < k. rec_exec (rcs ! j) xs = 0\<rbrakk> \<Longrightarrow>
  Embranch (zip (map rec_exec rgs) (map (\<lambda>r args. 0 < rec_exec r args) rcs)) xs = 0"
proof(induct rgs arbitrary: rcs k)
  case (Cons a rgs rcs k)
  then show ?case
    apply(cases rcs, simp, cases "rgs = []")
     apply(simp add: Embranch.simps)
     apply(erule_tac x = 0 in allE)
     apply (auto simp add: Embranch.simps intro!: Cons(1)).
qed simp

text \<open>
  The correctness of \<open>rec_embranch\<close>.
\<close>
lemma embranch_lemma:
  assumes branch_num:
    "length rgs = n" "length rcs = n" "n > 0"
    and partition: 
    "(\<exists> i < n. (rec_exec (rcs ! i) xs = 1 \<and> (\<forall> j < n. j \<noteq> i \<longrightarrow> 
                                      rec_exec (rcs ! j) xs = 0)))"
    and prime_all: "list_all (\<lambda> rf. primerec rf (length xs)) (rgs @ rcs)"
  shows "rec_exec (rec_embranch (zip rgs rcs)) xs =
                  Embranch (zip (map rec_exec rgs) 
                     (map (\<lambda> r args. 0 < rec_exec r args) rcs)) xs"
  using branch_num partition prime_all
proof(induct rgs arbitrary: rcs n, simp)
  fix a rgs rcs n
  assume ind: 
    "\<And>rcs n. \<lbrakk>length rgs = n; length rcs = n; 0 < n;
    \<exists>i<n. rec_exec (rcs ! i) xs = 1 \<and> (\<forall>j<n. j \<noteq> i \<longrightarrow> rec_exec (rcs ! j) xs = 0);
    list_all (\<lambda>rf. primerec rf (length xs)) (rgs @ rcs)\<rbrakk>
    \<Longrightarrow> rec_exec (rec_embranch (zip rgs rcs)) xs =
    Embranch (zip (map rec_exec rgs) (map (\<lambda>r args. 0 < rec_exec r args) rcs)) xs"
    and h: "length (a # rgs) = n" "length (rcs::recf list) = n" "0 < n"
    " \<exists>i<n. rec_exec (rcs ! i) xs = 1 \<and> 
         (\<forall>j<n. j \<noteq> i \<longrightarrow> rec_exec (rcs ! j) xs = 0)" 
    "list_all (\<lambda>rf. primerec rf (length xs)) ((a # rgs) @ rcs)"
  from h show "rec_exec (rec_embranch (zip (a # rgs) rcs)) xs =
    Embranch (zip (map rec_exec (a # rgs)) (map (\<lambda>r args. 
                0 < rec_exec r args) rcs)) xs"
    apply(cases rcs, simp, simp)
    apply(cases "rec_exec (hd rcs) xs = 0")
     apply(case_tac [!] "zip rgs (tl rcs) = []", simp)
       apply(subgoal_tac "rgs = [] \<and> (tl rcs) = []", simp add: Embranch.simps rec_exec.simps rec_embranch.simps)
       apply(rule_tac  zip_null_iff, simp, simp, simp)
  proof -
    fix aa list
    assume "rcs = aa # list"
    assume g:
      "Suc (length rgs) = n" "Suc (length list) = n" 
      "\<exists>i<n. rec_exec ((aa # list) ! i) xs = Suc 0 \<and> 
          (\<forall>j<n. j \<noteq> i \<longrightarrow> rec_exec ((aa # list) ! j) xs = 0)"
      "primerec a (length xs) \<and> 
      list_all (\<lambda>rf. primerec rf (length xs)) rgs \<and>
      primerec aa (length xs) \<and> 
      list_all (\<lambda>rf. primerec rf (length xs)) list"
      "rec_exec (hd rcs) xs = 0" "rcs = aa # list" "zip rgs (tl rcs) \<noteq> []"
    hence "rec_exec aa xs = 0" "zip rgs list \<noteq> []" by auto
    note g = g(1,2,3,4,6) this
    have "rec_exec (rec_embranch ((a, aa) # zip rgs list)) xs
        = rec_exec (rec_embranch (zip rgs list)) xs"
      apply(rule embranch_exec_0, simp_all add: g)
      done
    from g and this show "rec_exec (rec_embranch ((a, aa) # zip rgs list)) xs =
         Embranch ((rec_exec a, \<lambda>args. 0 < rec_exec aa args) # 
           zip (map rec_exec rgs) (map (\<lambda>r args. 0 < rec_exec r args) list)) xs"
      apply(simp add: Embranch.simps)
      apply(rule_tac n = "n - Suc 0" in ind)
          apply(cases n;force)
         apply(cases n;force)
        apply(cases n;force simp add: zip_null_gr)
       apply(auto)
      apply(rename_tac i)
      apply(case_tac i, force, simp)
      apply(rule_tac x = "i - 1" in exI, simp)
      by auto
  next
    fix aa list
    assume g: "Suc (length rgs) = n" "Suc (length list) = n"
      "\<exists>i<n. rec_exec ((aa # list) ! i) xs = Suc 0 \<and> 
      (\<forall>j<n. j \<noteq> i \<longrightarrow> rec_exec ((aa # list) ! j) xs = 0)"
      "primerec a (length xs) \<and> list_all (\<lambda>rf. primerec rf (length xs)) rgs \<and>
      primerec aa (length xs) \<and> list_all (\<lambda>rf. primerec rf (length xs)) list"
      "rcs = aa # list" "rec_exec (hd rcs) xs \<noteq> 0" "zip rgs (tl rcs) = []"
    thus "rec_exec (rec_embranch ((a, aa) # zip rgs list)) xs = 
        Embranch ((rec_exec a, \<lambda>args. 0 < rec_exec aa args) # 
       zip (map rec_exec rgs) (map (\<lambda>r args. 0 < rec_exec r args) list)) xs"
      apply(subgoal_tac "rgs = [] \<and> list = []", simp)
       prefer 2
       apply(rule_tac zip_null_iff, simp, simp, simp)
      apply(simp add: rec_exec.simps rec_embranch.simps Embranch.simps, auto)
      done
  next
    fix aa list
    assume g: "Suc (length rgs) = n" "Suc (length list) = n"
      "\<exists>i<n. rec_exec ((aa # list) ! i) xs = Suc 0 \<and>  
           (\<forall>j<n. j \<noteq> i \<longrightarrow> rec_exec ((aa # list) ! j) xs = 0)"
      "primerec a (length xs) \<and> list_all (\<lambda>rf. primerec rf (length xs)) rgs
      \<and> primerec aa (length xs) \<and> list_all (\<lambda>rf. primerec rf (length xs)) list"
      "rcs = aa # list" "rec_exec (hd rcs) xs \<noteq> 0" "zip rgs (tl rcs) \<noteq> []"
    have "rec_exec aa xs =  Suc 0"
      using g
      apply(cases "rec_exec aa xs", simp, auto)
      done      
    moreover have "rec_exec (rec_embranch' (zip rgs list) (length xs)) xs = 0"
    proof -
      have "rec_embranch' (zip rgs list) (length xs) = rec_embranch (zip rgs list)"
        using g
        apply(cases "zip rgs list", force)
        apply(cases "hd (zip rgs list)")
        apply(simp add: rec_embranch.simps)
        apply(cases rgs, simp, simp, cases list, simp, auto)
        done
      moreover have "rec_exec (rec_embranch (zip rgs list)) xs = 0"
      proof(rule embranch_all0)
        show " \<forall>j<length list. rec_exec (list ! j) xs = 0"
          using g
          apply(auto)
          apply(rename_tac i j)
          apply(case_tac i, simp)
           apply(erule_tac x = "Suc j" in allE, simp)
          apply(simp)
          apply(erule_tac x = 0 in allE, simp)
          done
      next
        show "length rgs = length list"
          using g by(cases n;force)
      next
        show "list \<noteq> []"
          using g by(cases list; force)
      next
        show "list_all (\<lambda>rf. primerec rf (length xs)) (rgs @ list)"
          using g by auto
      qed
      ultimately show "rec_exec (rec_embranch' (zip rgs list) (length xs)) xs = 0"
        by simp
    qed
    moreover have 
      "Embranch (zip (map rec_exec rgs) 
          (map (\<lambda>r args. 0 < rec_exec r args) list)) xs = 0"
      using g
      apply(rule_tac k = "length rgs" in Embranch_0)
         apply(simp, cases n, simp, simp)
       apply(cases rgs, simp, simp)
      apply(auto)
      apply(rename_tac i j)
      apply(case_tac i, simp)
       apply(erule_tac x = "Suc j" in allE, simp)
      apply(simp)
      apply(rule_tac x = 0 in allE, auto)
      done
    moreover have "arity a = length xs"
      using g
      apply(auto)
      done
    ultimately show "rec_exec (rec_embranch ((a, aa) # zip rgs list)) xs = 
      Embranch ((rec_exec a, \<lambda>args. 0 < rec_exec aa args) #
           zip (map rec_exec rgs) (map (\<lambda>r args. 0 < rec_exec r args) list)) xs"
      apply(simp add: rec_exec.simps rec_embranch.simps Embranch.simps)
      done
  qed
qed

text\<open>
  \<open>prime n\<close> means \<open>n\<close> is a prime number.
\<close>
fun Prime :: "nat \<Rightarrow> bool"
  where
    "Prime x = (1 < x \<and> (\<forall> u < x. (\<forall> v < x. u * v \<noteq> x)))"

declare Prime.simps [simp del]

lemma primerec_all1: 
  "primerec (rec_all rt rf) n \<Longrightarrow> primerec rt n"
  by (simp add: primerec_all)

lemma primerec_all2: "primerec (rec_all rt rf) n \<Longrightarrow> 
  primerec rf (Suc n)"
  by(insert primerec_all[of rt rf n], simp)

text \<open>
  \<open>rec_prime\<close> is the recursive function used to implement
  \<open>Prime\<close>.
\<close>
definition rec_prime :: "recf"
  where
    "rec_prime = Cn (Suc 0) rec_conj 
  [Cn (Suc 0) rec_less [constn 1, id (Suc 0) (0)],
        rec_all (Cn 1 rec_minus [id 1 0, constn 1]) 
       (rec_all (Cn 2 rec_minus [id 2 0, Cn 2 (constn 1) 
  [id 2 0]]) (Cn 3 rec_noteq 
       [Cn 3 rec_mult [id 3 1, id 3 2], id 3 0]))]"

declare numeral_2_eq_2[simp del] numeral_3_eq_3[simp del]

lemma exec_tmp: 
  "rec_exec (rec_all (Cn 2 rec_minus [recf.id 2 0, Cn 2 (constn (Suc 0)) [recf.id 2 0]]) 
  (Cn 3 rec_noteq [Cn 3 rec_mult [recf.id 3 (Suc 0), recf.id 3 2], recf.id 3 0]))  [x, k] = 
  ((if (\<forall>w\<le>rec_exec (Cn 2 rec_minus [recf.id 2 0, Cn 2 (constn (Suc 0)) [recf.id 2 0]]) ([x, k]). 
  0 < rec_exec (Cn 3 rec_noteq [Cn 3 rec_mult [recf.id 3 (Suc 0), recf.id 3 2], recf.id 3 0])
  ([x, k] @ [w])) then 1 else 0))"
  apply(rule_tac all_lemma)
   apply(auto simp:numeral)
   apply (metis (no_types, lifting) Suc_mono length_Cons less_2_cases list.size(3) nth_Cons_0
      nth_Cons_Suc numeral_2_eq_2 prime_cn prime_id primerec_rec_mult_2 zero_less_Suc)
  by (metis (no_types, lifting) One_nat_def length_Cons less_2_cases nth_Cons_0 nth_Cons_Suc 
      prime_cn_reverse primerec_rec_eq_2 rec_eq_def zero_less_Suc)

text \<open>
  The correctness of \<open>Prime\<close>.
\<close>
lemma prime_lemma: "rec_exec rec_prime [x] = (if Prime x then 1 else 0)"
proof(simp add: rec_exec.simps rec_prime_def)
  let ?rt1 = "(Cn 2 rec_minus [recf.id 2 0, 
    Cn 2 (constn (Suc 0)) [recf.id 2 0]])"
  let ?rf1 = "(Cn 3 rec_noteq [Cn 3 rec_mult 
    [recf.id 3 (Suc 0), recf.id 3 2], recf.id 3 (0)])"
  let ?rt2 = "(Cn (Suc 0) rec_minus 
    [recf.id (Suc 0) 0, constn (Suc 0)])"
  let ?rf2 = "rec_all ?rt1 ?rf1"
  have h1: "rec_exec (rec_all ?rt2 ?rf2) ([x]) = 
        (if (\<forall>k\<le>rec_exec ?rt2 ([x]). 0 < rec_exec ?rf2 ([x] @ [k])) then 1 else 0)"
  proof(rule_tac all_lemma, simp_all)
    show "primerec ?rf2 (Suc (Suc 0))"
      apply(rule_tac primerec_all_iff)
        apply(auto simp: numeral)
       apply (metis (no_types, lifting) One_nat_def length_Cons less_2_cases nth_Cons_0 nth_Cons_Suc
          prime_cn_reverse primerec_rec_eq_2 rec_eq_def zero_less_Suc)
      by (metis (no_types, lifting) Suc_mono length_Cons less_2_cases list.size(3) nth_Cons_0 
          nth_Cons_Suc numeral_2_eq_2 prime_cn prime_id primerec_rec_mult_2 zero_less_Suc)
  next
    show "primerec (Cn (Suc 0) rec_minus
             [recf.id (Suc 0) 0, constn (Suc 0)]) (Suc 0)"
      using less_2_cases numeral by fastforce
  qed
  from h1 show 
    "(Suc 0 < x \<longrightarrow>  (rec_exec (rec_all ?rt2 ?rf2) [x] = 0 \<longrightarrow> 
    \<not> Prime x) \<and>
     (0 < rec_exec (rec_all ?rt2 ?rf2) [x] \<longrightarrow> Prime x)) \<and>
    (\<not> Suc 0 < x \<longrightarrow> \<not> Prime x \<and> (rec_exec (rec_all ?rt2 ?rf2) [x] = 0
    \<longrightarrow> \<not> Prime x))"
    apply(auto simp:rec_exec.simps)
       apply(simp add: exec_tmp rec_exec.simps)
  proof -
    assume *:"\<forall>k\<le>x - Suc 0. (0::nat) < (if \<forall>w\<le>x - Suc 0. 
           0 < (if k * w \<noteq> x then 1 else (0 :: nat)) then 1 else 0)" "Suc 0 < x"
    thus "Prime x"
      apply(simp add: rec_exec.simps split: if_splits)
      apply(simp add: Prime.simps, auto)
      apply(rename_tac u v)
      apply(erule_tac x = u in allE, auto)
       apply(case_tac u, simp)
       apply(case_tac "u - 1", simp, simp)
      apply(case_tac v, simp)
      apply(case_tac "v - 1", simp, simp)
      done
  next
    assume "\<not> Suc 0 < x" "Prime x"
    thus "False"
      apply(simp add: Prime.simps)
      done
  next
    fix k
    assume "rec_exec (rec_all ?rt1 ?rf1)
      [x, k] = 0" "k \<le> x - Suc 0" "Prime x"
    thus "False"
      apply(simp add: exec_tmp rec_exec.simps Prime.simps split: if_splits)
      done
  next
    fix k
    assume "rec_exec (rec_all ?rt1 ?rf1)
      [x, k] = 0" "k \<le> x - Suc 0" "Prime x"
    thus "False"
      apply(simp add: exec_tmp rec_exec.simps Prime.simps split: if_splits)
      done
  qed
qed

definition rec_dummyfac :: "recf"
  where
    "rec_dummyfac = Pr 1 (constn 1) 
  (Cn 3 rec_mult [id 3 2, Cn 3 s [id 3 1]])"

text \<open>
  The recursive function used to implment factorization.
\<close>
definition rec_fac :: "recf"
  where
    "rec_fac = Cn 1 rec_dummyfac [id 1 0, id 1 0]"

text \<open>
  Formal specification of factorization.
\<close>
fun fac :: "nat \<Rightarrow> nat"  ("_!" [100] 99)
  where
    "fac 0 = 1" |
    "fac (Suc x) = (Suc x) * fac x"

lemma fac_dummy: "rec_exec rec_dummyfac [x, y] = y !"
  apply(induct y)
   apply(auto simp: rec_dummyfac_def rec_exec.simps)
  done

text \<open>
  The correctness of \<open>rec_fac\<close>.
\<close>
lemma fac_lemma: "rec_exec rec_fac [x] =  x!"
  apply(simp add: rec_fac_def rec_exec.simps fac_dummy)
  done

declare fac.simps[simp del]

text \<open>
  \<open>Np x\<close> returns the first prime number after \<open>x\<close>.
\<close>
fun Np ::"nat \<Rightarrow> nat"
  where
    "Np x = Min {y. y \<le> Suc (x!) \<and> x < y \<and> Prime y}"

declare Np.simps[simp del] rec_Minr.simps[simp del]

text \<open>
  \<open>rec_np\<close> is the recursive function used to implement
  \<open>Np\<close>.
\<close>
definition rec_np :: "recf"
  where
    "rec_np = (let Rr = Cn 2 rec_conj [Cn 2 rec_less [id 2 0, id 2 1], 
  Cn 2 rec_prime [id 2 1]]
             in Cn 1 (rec_Minr Rr) [id 1 0, Cn 1 s [rec_fac]])"

lemma n_le_fact[simp]: "n < Suc (n!)"
proof(induct n)
  case (Suc n)
  then show ?case  apply(simp add: fac.simps)
    apply(cases n, auto simp: fac.simps)
    done
qed simp

lemma divsor_ex: 
  "\<lbrakk>\<not> Prime x; x > Suc 0\<rbrakk> \<Longrightarrow> (\<exists> u > Suc 0. (\<exists> v > Suc 0. u * v = x))"
  by(auto simp: Prime.simps)

lemma divsor_prime_ex: "\<lbrakk>\<not> Prime x; x > Suc 0\<rbrakk> \<Longrightarrow> 
  \<exists> p. Prime p \<and> p dvd x"
  apply(induct x rule: wf_induct[where r = "measure (\<lambda> y. y)"], simp)
  apply(drule_tac divsor_ex, simp, auto)
  apply(rename_tac u v)
  apply(erule_tac x = u in allE, simp)
  apply(case_tac "Prime u", simp)
   apply(rule_tac x = u in exI, simp, auto)
  done

lemma fact_pos[intro]: "0 < n!"
  apply(induct n)
   apply(auto simp: fac.simps)
  done

lemma fac_Suc: "Suc n! =  (Suc n) * (n!)" by(simp add: fac.simps)

lemma fac_dvd: "\<lbrakk>0 < q; q \<le> n\<rbrakk> \<Longrightarrow> q dvd n!"
proof(induct n)
  case (Suc n)
  then show ?case 
    apply(cases "q \<le> n", simp add: fac_Suc)
    apply(subgoal_tac "q = Suc n", simp only: fac_Suc)
     apply(rule_tac dvd_mult2, simp, simp)
    done
qed simp

lemma fac_dvd2: "\<lbrakk>Suc 0 < q; q dvd n!; q \<le> n\<rbrakk> \<Longrightarrow> \<not> q dvd Suc (n!)"
proof(auto simp: dvd_def)
  fix k ka
  assume h1: "Suc 0 < q" "q \<le> n"
    and h2: "Suc (q * k) = q * ka"
  have "k < ka"
  proof - 
    have "q * k < q * ka" 
      using h2 by arith
    thus "k < ka"
      using h1
      by(auto)
  qed
  hence "\<exists>d. d > 0 \<and>  ka = d + k"  
    by(rule_tac x = "ka - k" in exI, simp)
  from this obtain d where "d > 0 \<and> ka = d + k" ..
  from h2 and this and h1 show "False"
    by(simp add: add_mult_distrib2)
qed

lemma prime_ex: "\<exists> p. n < p \<and> p \<le> Suc (n!) \<and> Prime p"
proof(cases "Prime (n! + 1)")
  case True thus "?thesis" 
    by(rule_tac x = "Suc (n!)" in exI, simp)
next
  assume h: "\<not> Prime (n! + 1)"  
  hence "\<exists> p. Prime p \<and> p dvd (n! + 1)"
    by(erule_tac divsor_prime_ex, auto)
  from this obtain q where k: "Prime q \<and> q dvd (n! + 1)" ..
  thus "?thesis"
  proof(cases "q > n")
    case True thus "?thesis"
      using k by(auto intro:dvd_imp_le)
  next
    case False thus "?thesis"
    proof -
      assume g: "\<not> n < q"
      have j: "q > Suc 0"
        using k by(cases q, auto simp: Prime.simps)
      hence "q dvd n!"
        using g 
        apply(rule_tac fac_dvd, auto)
        done
      hence "\<not> q dvd Suc (n!)"
        using g j
        by(rule_tac fac_dvd2, auto)
      thus "?thesis"
        using k by simp
    qed
  qed
qed

lemma Suc_Suc_induct[elim!]: "\<lbrakk>i < Suc (Suc 0); 
  primerec (ys ! 0) n; primerec (ys ! 1) n\<rbrakk> \<Longrightarrow> primerec (ys ! i) n"
  by(cases i, auto)

lemma primerec_rec_prime_1[intro]: "primerec rec_prime (Suc 0)"
  apply(auto simp: rec_prime_def, auto)
  apply(rule_tac primerec_all_iff, auto, auto)
  apply(rule_tac primerec_all_iff, auto, auto simp:  
      numeral_2_eq_2 numeral_3_eq_3)
  done

text \<open>
  The correctness of \<open>rec_np\<close>.
\<close>
lemma np_lemma: "rec_exec rec_np [x] = Np x"
proof(auto simp: rec_np_def rec_exec.simps Let_def fac_lemma)
  let ?rr = "(Cn 2 rec_conj [Cn 2 rec_less [recf.id 2 0,
    recf.id 2 (Suc 0)], Cn 2 rec_prime [recf.id 2 (Suc 0)]])"
  let ?R = "\<lambda> zs. zs ! 0 < zs ! 1 \<and> Prime (zs ! 1)"
  have g1: "rec_exec (rec_Minr ?rr) ([x] @ [Suc (x!)]) = 
    Minr (\<lambda> args. 0 < rec_exec ?rr args) [x] (Suc (x!))"
    by(rule_tac Minr_lemma, auto simp: rec_exec.simps
        prime_lemma, auto simp:  numeral_2_eq_2 numeral_3_eq_3)
  have g2: "Minr (\<lambda> args. 0 < rec_exec ?rr args) [x] (Suc (x!)) = Np x"
    using prime_ex[of x]
    apply(auto simp: Minr.simps Np.simps rec_exec.simps prime_lemma)
    apply(subgoal_tac
        "{uu. (Prime uu \<longrightarrow> (x < uu \<longrightarrow> uu \<le> Suc (x!)) \<and> x < uu) \<and> Prime uu}
    = {y. y \<le> Suc (x!) \<and> x < y \<and> Prime y}", auto)
    done
  from g1 and g2 show "rec_exec (rec_Minr ?rr) ([x, Suc (x!)]) = Np x"
    by simp
qed

text \<open>
  \<open>rec_power\<close> is the recursive function used to implement
  power function.
\<close>
definition rec_power :: "recf"
  where
    "rec_power = Pr 1 (constn 1) (Cn 3 rec_mult [id 3 0, id 3 2])"

text \<open>
  The correctness of \<open>rec_power\<close>.
\<close>
lemma power_lemma: "rec_exec rec_power [x, y] = x^y"
  by(induct y, auto simp: rec_exec.simps rec_power_def)

text\<open>
  \<open>Pi k\<close> returns the \<open>k\<close>-th prime number.
\<close>
fun Pi :: "nat \<Rightarrow> nat"
  where
    "Pi 0 = 2" |
    "Pi (Suc x) = Np (Pi x)"

definition rec_dummy_pi :: "recf"
  where
    "rec_dummy_pi = Pr 1 (constn 2) (Cn 3 rec_np [id 3 2])"

text \<open>
  \<open>rec_pi\<close> is the recursive function used to implement
  \<open>Pi\<close>.
\<close>
definition rec_pi :: "recf"
  where
    "rec_pi = Cn 1 rec_dummy_pi [id 1 0, id 1 0]"

lemma pi_dummy_lemma: "rec_exec rec_dummy_pi [x, y] = Pi y"
  apply(induct y)
  by(auto simp: rec_exec.simps rec_dummy_pi_def Pi.simps np_lemma)

text \<open>
  The correctness of \<open>rec_pi\<close>.
\<close>
lemma pi_lemma: "rec_exec rec_pi [x] = Pi x"
  apply(simp add: rec_pi_def rec_exec.simps pi_dummy_lemma)
  done

fun loR :: "nat list \<Rightarrow> bool"
  where
    "loR [x, y, u] = (x mod (y^u) = 0)"

declare loR.simps[simp del]

text \<open>
  \<open>Lo\<close> specifies the \<open>lo\<close> function given on page 79 of 
  Boolos's book. It is one of the two notions of integeral logarithmetic
  operation on that page. The other is \<open>lg\<close>.
\<close>
fun lo :: " nat \<Rightarrow> nat \<Rightarrow> nat"
  where 
    "lo x y  = (if x > 1 \<and> y > 1 \<and> {u. loR [x, y, u]} \<noteq> {} then Max {u. loR [x, y, u]}
                                                         else 0)"

declare lo.simps[simp del]

lemma primerec_sigma[intro!]:  
  "\<lbrakk>n > Suc 0; primerec rf n\<rbrakk> \<Longrightarrow> 
  primerec (rec_sigma rf) n"
  apply(simp add: rec_sigma.simps)
  apply(auto, auto simp: nth_append)
  done

lemma primerec_rec_maxr[intro!]:  "\<lbrakk>primerec rf n; n > 0\<rbrakk> \<Longrightarrow> primerec (rec_maxr rf) n"
  apply(simp add: rec_maxr.simps)
  apply(rule_tac prime_cn, auto)
   apply(rule_tac primerec_all_iff, auto, auto simp: nth_append)
  done

lemma Suc_Suc_Suc_induct[elim!]: 
  "\<lbrakk>i < Suc (Suc (Suc (0::nat))); primerec (ys ! 0) n;
  primerec (ys ! 1) n;  
  primerec (ys ! 2) n\<rbrakk> \<Longrightarrow> primerec (ys ! i) n"
  apply(cases i, auto)
  apply(cases "i-1", simp, simp add: numeral_2_eq_2)
  done

lemma primerec_2[intro]:
  "primerec rec_quo (Suc (Suc 0))" "primerec rec_mod (Suc (Suc 0))"
  "primerec rec_power (Suc (Suc 0))"
  by(force simp: prime_cn prime_id rec_mod_def rec_quo_def rec_power_def prime_pr numeral)+

text \<open>
  \<open>rec_lo\<close> is the recursive function used to implement \<open>Lo\<close>.
\<close>
definition rec_lo :: "recf"
  where
    "rec_lo = (let rR = Cn 3 rec_eq [Cn 3 rec_mod [id 3 0, 
               Cn 3 rec_power [id 3 1, id 3 2]], 
                     Cn 3 (constn 0) [id 3 1]] in
             let rb =  Cn 2 (rec_maxr rR) [id 2 0, id 2 1, id 2 0] in 
             let rcond = Cn 2 rec_conj [Cn 2 rec_less [Cn 2 (constn 1)
                                             [id 2 0], id 2 0], 
                                        Cn 2 rec_less [Cn 2 (constn 1)
                                                [id 2 0], id 2 1]] in 
             let rcond2 = Cn 2 rec_minus 
                              [Cn 2 (constn 1) [id 2 0], rcond] 
             in Cn 2 rec_add [Cn 2 rec_mult [rb, rcond], 
                  Cn 2 rec_mult [Cn 2 (constn 0) [id 2 0], rcond2]])"

lemma rec_lo_Maxr_lor:
  "\<lbrakk>Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow>  
        rec_exec rec_lo [x, y] = Maxr loR [x, y] x"
proof(auto simp: rec_exec.simps rec_lo_def Let_def 
    numeral_2_eq_2 numeral_3_eq_3)
  let ?rR = "(Cn (Suc (Suc (Suc 0))) rec_eq
     [Cn (Suc (Suc (Suc 0))) rec_mod [recf.id (Suc (Suc (Suc 0))) 0,
     Cn (Suc (Suc (Suc 0))) rec_power [recf.id (Suc (Suc (Suc 0)))
     (Suc 0), recf.id (Suc (Suc (Suc 0))) (Suc (Suc 0))]],
     Cn (Suc (Suc (Suc 0))) (constn 0) [recf.id (Suc (Suc (Suc 0))) (Suc 0)]])"
  have h: "rec_exec (rec_maxr ?rR) ([x, y] @ [x]) =
    Maxr (\<lambda> args. 0 < rec_exec ?rR args) [x, y] x"
    by(rule_tac Maxr_lemma, auto simp: rec_exec.simps
        mod_lemma power_lemma, auto simp: numeral_2_eq_2 numeral_3_eq_3)
  have "Maxr loR [x, y] x =  Maxr (\<lambda> args. 0 < rec_exec ?rR args) [x, y] x"
    apply(simp add: rec_exec.simps mod_lemma power_lemma)
    apply(simp add: Maxr.simps loR.simps)
    done
  from h and this show "rec_exec (rec_maxr ?rR) [x, y, x] = 
    Maxr loR [x, y] x"
    apply(simp)
    done
qed

lemma x_less_exp: "\<lbrakk>y > Suc 0\<rbrakk> \<Longrightarrow> x < y^x"
proof(induct x)
  case (Suc x)
  then show ?case  
    apply(cases x, simp, auto)
    apply(rule_tac y = "y* y^(x-1)" in le_less_trans, auto)
    done
qed simp


lemma uplimit_loR:
  assumes "Suc 0 < x" "Suc 0 < y" "loR [x, y, xa]"
  shows "xa \<le> x"
proof -
  have "Suc 0 < x \<Longrightarrow> Suc 0 < y \<Longrightarrow> y ^ xa dvd x \<Longrightarrow> xa \<le> x" 
    by (meson Suc_lessD le_less_trans nat_dvd_not_less nat_le_linear x_less_exp)
  thus ?thesis using assms by(auto simp: loR.simps)
qed

lemma loR_set_strengthen[simp]: "\<lbrakk>xa \<le> x; loR [x, y, xa]; Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow>
  {u. loR [x, y, u]} = {ya. ya \<le> x \<and> loR [x, y, ya]}"
  apply(rule_tac Collect_cong, auto)
  apply(erule_tac uplimit_loR, simp, simp)
  done

lemma Maxr_lo: "\<lbrakk>Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow>
  Maxr loR [x, y] x = lo x y" 
  apply(simp add: Maxr.simps lo.simps, auto simp: uplimit_loR)
  by (meson uplimit_loR)+

lemma lo_lemma': "\<lbrakk>Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow> 
  rec_exec rec_lo [x, y] = lo x y"
  by(simp add: Maxr_lo  rec_lo_Maxr_lor)

lemma lo_lemma'': "\<lbrakk>\<not> Suc 0 < x\<rbrakk> \<Longrightarrow> rec_exec rec_lo [x, y] = lo x y"
  apply(cases x, auto simp: rec_exec.simps rec_lo_def 
      Let_def lo.simps)
  done

lemma lo_lemma''': "\<lbrakk>\<not> Suc 0 < y\<rbrakk> \<Longrightarrow> rec_exec rec_lo [x, y] = lo x y"
  apply(cases y, auto simp: rec_exec.simps rec_lo_def 
      Let_def lo.simps)
  done

text \<open>
  The correctness of \<open>rec_lo\<close>:
\<close>
lemma lo_lemma: "rec_exec rec_lo [x, y] = lo x y" 
  apply(cases "Suc 0 < x \<and> Suc 0 < y")
   apply(auto simp: lo_lemma' lo_lemma'' lo_lemma''')
  done

fun lgR :: "nat list \<Rightarrow> bool"
  where
    "lgR [x, y, u] = (y^u \<le> x)"

text \<open>
  \<open>lg\<close> specifies the \<open>lg\<close> function given on page 79 of 
  Boolos's book. It is one of the two notions of integeral logarithmetic
  operation on that page. The other is \<open>lo\<close>.
\<close>
fun lg :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "lg x y = (if x > 1 \<and> y > 1 \<and> {u. lgR [x, y, u]} \<noteq> {} then 
                 Max {u. lgR [x, y, u]}
              else 0)"

declare lg.simps[simp del] lgR.simps[simp del]

text \<open>
  \<open>rec_lg\<close> is the recursive function used to implement \<open>lg\<close>.
\<close>
definition rec_lg :: "recf"
  where
    "rec_lg = (let rec_lgR = Cn 3 rec_le
  [Cn 3 rec_power [id 3 1, id 3 2], id 3 0] in
  let conR1 = Cn 2 rec_conj [Cn 2 rec_less 
                     [Cn 2 (constn 1) [id 2 0], id 2 0], 
                            Cn 2 rec_less [Cn 2 (constn 1) 
                                 [id 2 0], id 2 1]] in 
  let conR2 = Cn 2 rec_not [conR1] in 
        Cn 2 rec_add [Cn 2 rec_mult 
              [conR1, Cn 2 (rec_maxr rec_lgR)
                       [id 2 0, id 2 1, id 2 0]], 
                       Cn 2 rec_mult [conR2, Cn 2 (constn 0) 
                                [id 2 0]]])"

lemma lg_maxr: "\<lbrakk>Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow> 
                      rec_exec rec_lg [x, y] = Maxr lgR [x, y] x"
proof(simp add: rec_exec.simps rec_lg_def Let_def)
  assume h: "Suc 0 < x" "Suc 0 < y"
  let ?rR = "(Cn 3 rec_le [Cn 3 rec_power
               [recf.id 3 (Suc 0), recf.id 3 2], recf.id 3 0])"
  have "rec_exec (rec_maxr ?rR) ([x, y] @ [x])
              = Maxr ((\<lambda> args. 0 < rec_exec ?rR args)) [x, y] x" 
  proof(rule Maxr_lemma)
    show "primerec (Cn 3 rec_le [Cn 3 rec_power 
              [recf.id 3 (Suc 0), recf.id 3 2], recf.id 3 0]) (Suc (length [x, y]))"
      apply(auto simp: numeral_3_eq_3)+
      done
  qed
  moreover have "Maxr lgR [x, y] x = Maxr ((\<lambda> args. 0 < rec_exec ?rR args)) [x, y] x"
    apply(simp add: rec_exec.simps power_lemma)
    apply(simp add: Maxr.simps lgR.simps)
    done 
  ultimately show "rec_exec (rec_maxr ?rR) [x, y, x] = Maxr lgR [x, y] x"
    by simp
qed

lemma lgR_ok: "\<lbrakk>Suc 0 < y; lgR [x, y, xa]\<rbrakk> \<Longrightarrow> xa \<le> x"
  apply(auto simp add: lgR.simps)
  apply(subgoal_tac "y^xa > xa", simp)
  apply(erule x_less_exp)
  done

lemma lgR_set_strengthen[simp]: "\<lbrakk>Suc 0 < x; Suc 0 < y; lgR [x, y, xa]\<rbrakk> \<Longrightarrow>
           {u. lgR [x, y, u]} =  {ya. ya \<le> x \<and> lgR [x, y, ya]}"
  apply(rule_tac Collect_cong, auto simp:lgR_ok)
  done

lemma maxr_lg: "\<lbrakk>Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow> Maxr lgR [x, y] x = lg x y"
  apply(auto simp add: lg.simps Maxr.simps)
  using lgR_ok by blast

lemma lg_lemma': "\<lbrakk>Suc 0 < x; Suc 0 < y\<rbrakk> \<Longrightarrow> rec_exec rec_lg [x, y] = lg x y"
  apply(simp add: maxr_lg lg_maxr)
  done

lemma lg_lemma'': "\<not> Suc 0 < x \<Longrightarrow> rec_exec rec_lg [x, y] = lg x y"
  apply(simp add: rec_exec.simps rec_lg_def Let_def lg.simps)
  done

lemma lg_lemma''': "\<not> Suc 0 < y \<Longrightarrow> rec_exec rec_lg [x, y] = lg x y"
  apply(simp add: rec_exec.simps rec_lg_def Let_def lg.simps)
  done

text \<open>
  The correctness of \<open>rec_lg\<close>.
\<close>
lemma lg_lemma: "rec_exec rec_lg [x, y] = lg x y"
  apply(cases "Suc 0 < x \<and> Suc 0 < y", auto simp: 
      lg_lemma' lg_lemma'' lg_lemma''')
  done

text \<open>
  \<open>Entry sr i\<close> returns the \<open>i\<close>-th entry of a list of natural 
  numbers encoded by number \<open>sr\<close> using Godel's coding.
\<close>
fun Entry :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "Entry sr i = lo sr (Pi (Suc i))"

text \<open>
  \<open>rec_entry\<close> is the recursive function used to implement
  \<open>Entry\<close>.
\<close>
definition rec_entry:: "recf"
  where
    "rec_entry = Cn 2 rec_lo [id 2 0, Cn 2 rec_pi [Cn 2 s [id 2 1]]]"

declare Pi.simps[simp del]

text \<open>
  The correctness of \<open>rec_entry\<close>.
\<close>
lemma entry_lemma: "rec_exec rec_entry [str, i] = Entry str i"
  by(simp add: rec_entry_def  rec_exec.simps lo_lemma pi_lemma)


subsection \<open>The construction of F\<close>

text \<open>
  Using the auxilliary functions obtained in last section, 
  we are going to contruct the function \<open>F\<close>, 
  which is an interpreter of Turing Machines.
\<close>

fun listsum2 :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "listsum2 xs 0 = 0"
  | "listsum2 xs (Suc n) = listsum2 xs n + xs ! n"

fun rec_listsum2 :: "nat \<Rightarrow> nat \<Rightarrow> recf"
  where
    "rec_listsum2 vl 0 = Cn vl z [id vl 0]"
  | "rec_listsum2 vl (Suc n) = Cn vl rec_add [rec_listsum2 vl n, id vl n]"

declare listsum2.simps[simp del] rec_listsum2.simps[simp del]

lemma listsum2_lemma: "\<lbrakk>length xs = vl; n \<le> vl\<rbrakk> \<Longrightarrow> 
      rec_exec (rec_listsum2 vl n) xs = listsum2 xs n"
  apply(induct n, simp_all)
   apply(simp_all add: rec_exec.simps rec_listsum2.simps listsum2.simps)
  done

fun strt' :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "strt' xs 0 = 0"
  | "strt' xs (Suc n) = (let dbound = listsum2 xs n + n in 
                       strt' xs n + (2^(xs ! n + dbound) - 2^dbound))"

fun rec_strt' :: "nat \<Rightarrow> nat \<Rightarrow> recf"
  where
    "rec_strt' vl 0 = Cn vl z [id vl 0]"
  | "rec_strt' vl (Suc n) = (let rec_dbound =
  Cn vl rec_add [rec_listsum2 vl n, Cn vl (constn n) [id vl 0]]
  in Cn vl rec_add [rec_strt' vl n, Cn vl rec_minus 
  [Cn vl rec_power [Cn vl (constn 2) [id vl 0], Cn vl rec_add
  [id vl (n), rec_dbound]], 
  Cn vl rec_power [Cn vl (constn 2) [id vl 0], rec_dbound]]])"

declare strt'.simps[simp del] rec_strt'.simps[simp del]

lemma strt'_lemma: "\<lbrakk>length xs = vl; n \<le> vl\<rbrakk> \<Longrightarrow> 
  rec_exec (rec_strt' vl n) xs = strt' xs n"
  apply(induct n)
   apply(simp_all add: rec_exec.simps rec_strt'.simps strt'.simps
      Let_def power_lemma listsum2_lemma)
  done

text \<open>
  \<open>strt\<close> corresponds to the \<open>strt\<close> function on page 90 of B book, but 
  this definition generalises the original one to deal with multiple input arguments.
\<close>
fun strt :: "nat list \<Rightarrow> nat"
  where
    "strt xs = (let ys = map Suc xs in 
              strt' ys (length ys))"

fun rec_map :: "recf \<Rightarrow> nat \<Rightarrow> recf list"
  where
    "rec_map rf vl = map (\<lambda> i. Cn vl rf [id vl i]) [0..<vl]"

text \<open>
  \<open>rec_strt\<close> is the recursive function used to implement \<open>strt\<close>.
\<close>
fun rec_strt :: "nat \<Rightarrow> recf"
  where
    "rec_strt vl = Cn vl (rec_strt' vl vl) (rec_map s vl)"

lemma map_s_lemma: "length xs = vl \<Longrightarrow> 
  map ((\<lambda>a. rec_exec a xs) \<circ> (\<lambda>i. Cn vl s [recf.id vl i]))
  [0..<vl]
        = map Suc xs"
  apply(induct vl arbitrary: xs, simp, auto simp: rec_exec.simps)
  apply(rename_tac vl xs)
  apply(subgoal_tac "\<exists> ys y. xs = ys @ [y]", auto)
proof -
  fix ys y
  assume ind: "\<And>xs. length xs = length (ys::nat list) \<Longrightarrow>
      map ((\<lambda>a. rec_exec a xs) \<circ> (\<lambda>i. Cn (length ys) s 
        [recf.id (length ys) (i)])) [0..<length ys] = map Suc xs"
  show
    "map ((\<lambda>a. rec_exec a (ys @ [y])) \<circ> (\<lambda>i. Cn (Suc (length ys)) s 
  [recf.id (Suc (length ys)) (i)])) [0..<length ys] = map Suc ys"
  proof -
    have "map ((\<lambda>a. rec_exec a ys) \<circ> (\<lambda>i. Cn (length ys) s
        [recf.id (length ys) (i)])) [0..<length ys] = map Suc ys"
      apply(rule_tac ind, simp)
      done
    moreover have
      "map ((\<lambda>a. rec_exec a (ys @ [y])) \<circ> (\<lambda>i. Cn (Suc (length ys)) s
           [recf.id (Suc (length ys)) (i)])) [0..<length ys]
         = map ((\<lambda>a. rec_exec a ys) \<circ> (\<lambda>i. Cn (length ys) s 
                 [recf.id (length ys) (i)])) [0..<length ys]"
      apply(rule_tac map_ext, auto simp: rec_exec.simps nth_append)
      done
    ultimately show "?thesis"
      by simp
  qed
next
  fix vl xs
  assume "length xs = Suc vl"
  thus "\<exists>ys y. xs = ys @ [y]"
    apply(rule_tac x = "butlast xs" in exI, rule_tac x = "last xs" in exI)
    apply(subgoal_tac "xs \<noteq> []", auto)
    done
qed

text \<open>
  The correctness of \<open>rec_strt\<close>.
\<close>
lemma strt_lemma: "length xs = vl \<Longrightarrow> 
  rec_exec (rec_strt vl) xs = strt xs"
  apply(simp add: strt.simps rec_exec.simps strt'_lemma)
  apply(subgoal_tac "(map ((\<lambda>a. rec_exec a xs) \<circ> (\<lambda>i. Cn vl s [recf.id vl (i)])) [0..<vl])
                  = map Suc xs", auto)
  apply(rule map_s_lemma, simp)
  done

text \<open>
  The \<open>scan\<close> function on page 90 of B book.
\<close>
fun scan :: "nat \<Rightarrow> nat"
  where
    "scan r = r mod 2"

text \<open>
  \<open>rec_scan\<close> is the implemention of \<open>scan\<close>.
\<close>
definition rec_scan :: "recf"
  where "rec_scan = Cn 1 rec_mod [id 1 0, constn 2]"

text \<open>
  The correctness of \<open>scan\<close>.
\<close>
lemma scan_lemma: "rec_exec rec_scan [r] = r mod 2"
  by(simp add: rec_exec.simps rec_scan_def mod_lemma)

fun newleft0 :: "nat list \<Rightarrow> nat"
  where
    "newleft0 [p, r] = p"

definition rec_newleft0 :: "recf"
  where
    "rec_newleft0 = id 2 0"

fun newrgt0 :: "nat list \<Rightarrow> nat"
  where
    "newrgt0 [p, r] = r - scan r"

definition rec_newrgt0 :: "recf"
  where
    "rec_newrgt0 = Cn 2 rec_minus [id 2 1, Cn 2 rec_scan [id 2 1]]"

(*newleft1, newrgt1: left rgt number after execute on step*)
fun newleft1 :: "nat list \<Rightarrow> nat"
  where
    "newleft1 [p, r] = p"

definition rec_newleft1 :: "recf"
  where
    "rec_newleft1 = id 2 0"

fun newrgt1 :: "nat list \<Rightarrow> nat"
  where
    "newrgt1 [p, r] = r + 1 - scan r"

definition rec_newrgt1 :: "recf"
  where
    "rec_newrgt1 = 
  Cn 2 rec_minus [Cn 2 rec_add [id 2 1, Cn 2 (constn 1) [id 2 0]], 
                  Cn 2 rec_scan [id 2 1]]"

fun newleft2 :: "nat list \<Rightarrow> nat"
  where
    "newleft2 [p, r] = p div 2"

definition rec_newleft2 :: "recf" 
  where
    "rec_newleft2 = Cn 2 rec_quo [id 2 0, Cn 2 (constn 2) [id 2 0]]"

fun newrgt2 :: "nat list \<Rightarrow> nat"
  where
    "newrgt2 [p, r] = 2 * r + p mod 2"

definition rec_newrgt2 :: "recf"
  where
    "rec_newrgt2 =
    Cn 2 rec_add [Cn 2 rec_mult [Cn 2 (constn 2) [id 2 0], id 2 1],                     
                 Cn 2 rec_mod [id 2 0, Cn 2 (constn 2) [id 2 0]]]"

fun newleft3 :: "nat list \<Rightarrow> nat"
  where
    "newleft3 [p, r] = 2 * p + r mod 2"

definition rec_newleft3 :: "recf"
  where
    "rec_newleft3 = 
  Cn 2 rec_add [Cn 2 rec_mult [Cn 2 (constn 2) [id 2 0], id 2 0], 
                Cn 2 rec_mod [id 2 1, Cn 2 (constn 2) [id 2 0]]]"

fun newrgt3 :: "nat list \<Rightarrow> nat"
  where
    "newrgt3 [p, r] = r div 2"

definition rec_newrgt3 :: "recf"
  where
    "rec_newrgt3 = Cn 2 rec_quo [id 2 1, Cn 2 (constn 2) [id 2 0]]"

text \<open>
  The \<open>new_left\<close> function on page 91 of B book.
\<close>
fun newleft :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "newleft p r a = (if a = 0 \<or> a = 1 then newleft0 [p, r] 
                    else if a = 2 then newleft2 [p, r]
                    else if a = 3 then newleft3 [p, r]
                    else p)"

text \<open>
  \<open>rec_newleft\<close> is the recursive function used to 
  implement \<open>newleft\<close>.
\<close>
definition rec_newleft :: "recf" 
  where
    "rec_newleft =
  (let g0 = 
      Cn 3 rec_newleft0 [id 3 0, id 3 1] in 
  let g1 = Cn 3 rec_newleft2 [id 3 0, id 3 1] in 
  let g2 = Cn 3 rec_newleft3 [id 3 0, id 3 1] in 
  let g3 = id 3 0 in
  let r0 = Cn 3 rec_disj
          [Cn 3 rec_eq [id 3 2, Cn 3 (constn 0) [id 3 0]],
           Cn 3 rec_eq [id 3 2, Cn 3 (constn 1) [id 3 0]]] in 
  let r1 = Cn 3 rec_eq [id 3 2, Cn 3 (constn 2) [id 3 0]] in 
  let r2 = Cn 3 rec_eq [id 3 2, Cn 3 (constn 3) [id 3 0]] in
  let r3 = Cn 3 rec_less [Cn 3 (constn 3) [id 3 0], id 3 2] in 
  let gs = [g0, g1, g2, g3] in 
  let rs = [r0, r1, r2, r3] in 
  rec_embranch (zip gs rs))"

declare newleft.simps[simp del]


lemma Suc_Suc_Suc_Suc_induct: 
  "\<lbrakk>i < Suc (Suc (Suc (Suc 0))); i = 0 \<Longrightarrow>  P i;
    i = 1 \<Longrightarrow> P i; i =2 \<Longrightarrow> P i; 
    i =3 \<Longrightarrow> P i\<rbrakk> \<Longrightarrow> P i"
  apply(cases i, force)
  apply(cases "i - 1", force)
  apply(cases "i - 1 - 1", force)
  by(cases "i - 1 - 1 - 1", auto simp:numeral)

declare quo_lemma2[simp] mod_lemma[simp]

text \<open>
  The correctness of \<open>rec_newleft\<close>.
\<close>
lemma newleft_lemma: 
  "rec_exec rec_newleft [p, r, a] = newleft p r a"
proof(simp only: rec_newleft_def Let_def)
  let ?rgs = "[Cn 3 rec_newleft0 [recf.id 3 0, recf.id 3 1], Cn 3 rec_newleft2 
       [recf.id 3 0, recf.id 3 1], Cn 3 rec_newleft3 [recf.id 3 0, recf.id 3 1], recf.id 3 0]"
  let ?rrs = 
    "[Cn 3 rec_disj [Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 0) 
     [recf.id 3 0]], Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 1) [recf.id 3 0]]], 
     Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 2) [recf.id 3 0]],
     Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 3) [recf.id 3 0]],
     Cn 3 rec_less [Cn 3 (constn 3) [recf.id 3 0], recf.id 3 2]]"
  have k1: "rec_exec (rec_embranch (zip ?rgs ?rrs)) [p, r, a]
                         = Embranch (zip (map rec_exec ?rgs) (map (\<lambda>r args. 0 < rec_exec r args) ?rrs)) [p, r, a]"
    apply(rule_tac embranch_lemma )
        apply(auto simp: numeral_3_eq_3 numeral_2_eq_2 rec_newleft0_def 
        rec_newleft1_def rec_newleft2_def rec_newleft3_def)+
    apply(cases "a = 0 \<or> a = 1", rule_tac x = 0 in exI)
     prefer 2
     apply(cases "a = 2", rule_tac x = "Suc 0" in exI)
      prefer 2
      apply(cases "a = 3", rule_tac x = "2" in exI)
       prefer 2
       apply(cases "a > 3", rule_tac x = "3" in exI, auto)
             apply(auto simp: rec_exec.simps)
        apply(erule_tac [!] Suc_Suc_Suc_Suc_induct, auto simp: rec_exec.simps)
    done
  have k2: "Embranch (zip (map rec_exec ?rgs) (map (\<lambda>r args. 0 < rec_exec r args) ?rrs)) [p, r, a] = newleft p r a"
    apply(simp add: Embranch.simps)
    apply(simp add: rec_exec.simps)
    apply(auto simp: newleft.simps rec_newleft0_def rec_exec.simps
        rec_newleft1_def rec_newleft2_def rec_newleft3_def)
    done
  from k1 and k2 show 
    "rec_exec (rec_embranch (zip ?rgs ?rrs)) [p, r, a] = newleft p r a"
    by simp
qed

text \<open>
  The \<open>newrght\<close> function is one similar to \<open>newleft\<close>, but used to 
  compute the right number.
\<close>
fun newrght :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "newrght p r a  = (if a = 0 then newrgt0 [p, r]
                    else if a = 1 then newrgt1 [p, r]
                    else if a = 2 then newrgt2 [p, r]
                    else if a = 3 then newrgt3 [p, r]
                    else r)"

text \<open>
  \<open>rec_newrght\<close> is the recursive function used to implement 
  \<open>newrgth\<close>.
\<close>
definition rec_newrght :: "recf" 
  where
    "rec_newrght =
  (let g0 = Cn 3 rec_newrgt0 [id 3 0, id 3 1] in 
  let g1 = Cn 3 rec_newrgt1 [id 3 0, id 3 1] in 
  let g2 = Cn 3 rec_newrgt2 [id 3 0, id 3 1] in 
  let g3 = Cn 3 rec_newrgt3 [id 3 0, id 3 1] in
  let g4 = id 3 1 in 
  let r0 = Cn 3 rec_eq [id 3 2, Cn 3 (constn 0) [id 3 0]] in 
  let r1 = Cn 3 rec_eq [id 3 2, Cn 3 (constn 1) [id 3 0]] in 
  let r2 = Cn 3 rec_eq [id 3 2, Cn 3 (constn 2) [id 3 0]] in
  let r3 = Cn 3 rec_eq [id 3 2, Cn 3 (constn 3) [id 3 0]] in
  let r4 = Cn 3 rec_less [Cn 3 (constn 3) [id 3 0], id 3 2] in 
  let gs = [g0, g1, g2, g3, g4] in 
  let rs = [r0, r1, r2, r3, r4] in 
  rec_embranch (zip gs rs))"
declare newrght.simps[simp del]

lemma numeral_4_eq_4: "4 = Suc 3"
  by auto

lemma Suc_5_induct: 
  "\<lbrakk>i < Suc (Suc (Suc (Suc (Suc 0)))); i = 0 \<Longrightarrow> P 0;
  i = 1 \<Longrightarrow> P 1; i = 2 \<Longrightarrow> P 2; i = 3 \<Longrightarrow> P 3; i = 4 \<Longrightarrow> P 4\<rbrakk> \<Longrightarrow> P i"
  apply(cases i, force)
  apply(cases "i-1", force)
  apply(cases "i-1-1")
  using less_2_cases numeral by auto


lemma primerec_rec_scan_1[intro]: "primerec rec_scan (Suc 0)"
  apply(auto simp: rec_scan_def, auto)
  done

text \<open>
  The correctness of \<open>rec_newrght\<close>.
\<close>
lemma newrght_lemma: "rec_exec rec_newrght [p, r, a] = newrght p r a"
proof(simp only: rec_newrght_def Let_def)
  let ?gs' = "[newrgt0, newrgt1, newrgt2, newrgt3, \<lambda> zs. zs ! 1]"
  let ?r0 = "\<lambda> zs. zs ! 2 = 0"
  let ?r1 = "\<lambda> zs. zs ! 2 = 1"
  let ?r2 = "\<lambda> zs. zs ! 2 = 2"
  let ?r3 = "\<lambda> zs. zs ! 2 = 3"
  let ?r4 = "\<lambda> zs. zs ! 2 > 3"
  let ?gs = "map (\<lambda> g. (\<lambda> zs. g [zs ! 0, zs ! 1])) ?gs'"
  let ?rs = "[?r0, ?r1, ?r2, ?r3, ?r4]"
  let ?rgs = 
    "[Cn 3 rec_newrgt0 [recf.id 3 0, recf.id 3 1],
    Cn 3 rec_newrgt1 [recf.id 3 0, recf.id 3 1],
     Cn 3 rec_newrgt2 [recf.id 3 0, recf.id 3 1], 
      Cn 3 rec_newrgt3 [recf.id 3 0, recf.id 3 1], recf.id 3 1]"
  let ?rrs = 
    "[Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 0) [recf.id 3 0]], Cn 3 rec_eq [recf.id 3 2, 
    Cn 3 (constn 1) [recf.id 3 0]], Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 2) [recf.id 3 0]],
     Cn 3 rec_eq [recf.id 3 2, Cn 3 (constn 3) [recf.id 3 0]], 
       Cn 3 rec_less [Cn 3 (constn 3) [recf.id 3 0], recf.id 3 2]]"

  have k1: "rec_exec (rec_embranch (zip ?rgs ?rrs)) [p, r, a]
    = Embranch (zip (map rec_exec ?rgs) (map (\<lambda>r args. 0 < rec_exec r args) ?rrs)) [p, r, a]"
    apply(rule_tac embranch_lemma)
        apply(auto simp: numeral_3_eq_3 numeral_2_eq_2 rec_newrgt0_def 
        rec_newrgt1_def rec_newrgt2_def rec_newrgt3_def)+
    apply(cases "a = 0", rule_tac x = 0 in exI)
     prefer 2
     apply(cases "a = 1", rule_tac x = "Suc 0" in exI)
      prefer 2
      apply(cases "a = 2", rule_tac x = "2" in exI)
       prefer 2
       apply(cases "a = 3", rule_tac x = "3" in exI)
        prefer 2
        apply(cases "a > 3", rule_tac x = "4" in exI, auto simp: rec_exec.simps)
        apply(erule_tac [!] Suc_5_induct, auto simp: rec_exec.simps)
    done
  have k2: "Embranch (zip (map rec_exec ?rgs)
    (map (\<lambda>r args. 0 < rec_exec r args) ?rrs)) [p, r, a] = newrght p r a"
    apply(auto simp:Embranch.simps rec_exec.simps)
        apply(auto simp: newrght.simps rec_newrgt3_def rec_newrgt2_def
        rec_newrgt1_def rec_newrgt0_def rec_exec.simps
        scan_lemma)
    done
  from k1 and k2 show 
    "rec_exec (rec_embranch (zip ?rgs ?rrs)) [p, r, a] =      
                                    newrght p r a" by simp
qed

declare Entry.simps[simp del]

text \<open>
  The \<open>actn\<close> function given on page 92 of B book, which is used to 
  fetch Turing Machine intructions. 
  In \<open>actn m q r\<close>, \<open>m\<close> is the Godel coding of a Turing Machine,
  \<open>q\<close> is the current state of Turing Machine, \<open>r\<close> is the
  right number of Turing Machine tape.
\<close>
fun actn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "actn m q r = (if q \<noteq> 0 then Entry m (4*(q - 1) + 2 * scan r)
                 else 4)"

text \<open>
  \<open>rec_actn\<close> is the recursive function used to implement \<open>actn\<close>
\<close>
definition rec_actn :: "recf"
  where
    "rec_actn = 
  Cn 3 rec_add [Cn 3 rec_mult 
        [Cn 3 rec_entry [id 3 0, Cn 3 rec_add [Cn 3 rec_mult 
                                 [Cn 3 (constn 4) [id 3 0], 
                Cn 3 rec_minus [id 3 1, Cn 3 (constn 1) [id 3 0]]], 
                   Cn 3 rec_mult [Cn 3 (constn 2) [id 3 0],
                      Cn 3 rec_scan [id 3 2]]]], 
            Cn 3 rec_noteq [id 3 1, Cn 3 (constn 0) [id 3 0]]], 
                             Cn 3 rec_mult [Cn 3 (constn 4) [id 3 0], 
             Cn 3 rec_eq [id 3 1, Cn 3 (constn 0) [id 3 0]]]] "

text \<open>
  The correctness of \<open>actn\<close>.
\<close>
lemma actn_lemma: "rec_exec rec_actn [m, q, r] = actn m q r"
  by(auto simp: rec_actn_def rec_exec.simps entry_lemma scan_lemma)

fun newstat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "newstat m q r = (if q \<noteq> 0 then Entry m (4*(q - 1) + 2*scan r + 1)
                    else 0)"

definition rec_newstat :: "recf"
  where
    "rec_newstat = Cn 3 rec_add 
    [Cn 3 rec_mult [Cn 3 rec_entry [id 3 0, 
           Cn 3 rec_add [Cn 3 rec_mult [Cn 3 (constn 4) [id 3 0], 
           Cn 3 rec_minus [id 3 1, Cn 3 (constn 1) [id 3 0]]], 
           Cn 3 rec_add [Cn 3 rec_mult [Cn 3 (constn 2) [id 3 0],
           Cn 3 rec_scan [id 3 2]], Cn 3 (constn 1) [id 3 0]]]], 
           Cn 3 rec_noteq [id 3 1, Cn 3 (constn 0) [id 3 0]]], 
           Cn 3 rec_mult [Cn 3 (constn 0) [id 3 0], 
           Cn 3 rec_eq [id 3 1, Cn 3 (constn 0) [id 3 0]]]] "

lemma newstat_lemma: "rec_exec rec_newstat [m, q, r] = newstat m q r"
  by(auto simp:  rec_exec.simps entry_lemma scan_lemma rec_newstat_def)

declare newstat.simps[simp del] actn.simps[simp del]

text\<open>code the configuration\<close>

fun trpl :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "trpl p q r = (Pi 0)^p * (Pi 1)^q * (Pi 2)^r"

definition rec_trpl :: "recf"
  where
    "rec_trpl = Cn 3 rec_mult [Cn 3 rec_mult 
       [Cn 3 rec_power [Cn 3 (constn (Pi 0)) [id 3 0], id 3 0], 
        Cn 3 rec_power [Cn 3 (constn (Pi 1)) [id 3 0], id 3 1]],
        Cn 3 rec_power [Cn 3 (constn (Pi 2)) [id 3 0], id 3 2]]"
declare trpl.simps[simp del]
lemma trpl_lemma: "rec_exec rec_trpl [p, q, r] = trpl p q r"
  by(auto simp: rec_trpl_def rec_exec.simps power_lemma trpl.simps)

text\<open>left, stat, rght: decode func\<close>
fun left :: "nat \<Rightarrow> nat"
  where
    "left c = lo c (Pi 0)"

fun stat :: "nat \<Rightarrow> nat"
  where
    "stat c = lo c (Pi 1)"

fun rght :: "nat \<Rightarrow> nat"
  where
    "rght c = lo c (Pi 2)"

fun inpt :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "inpt m xs = trpl 0 1 (strt xs)"

fun newconf :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "newconf m c = trpl (newleft (left c) (rght c) 
                        (actn m (stat c) (rght c)))
                        (newstat m (stat c) (rght c)) 
                        (newrght (left c) (rght c) 
                              (actn m (stat c) (rght c)))"

declare left.simps[simp del] stat.simps[simp del] rght.simps[simp del]
  inpt.simps[simp del] newconf.simps[simp del]

definition rec_left :: "recf"
  where
    "rec_left = Cn 1 rec_lo [id 1 0, constn (Pi 0)]"

definition rec_right :: "recf"
  where
    "rec_right = Cn 1 rec_lo [id 1 0, constn (Pi 2)]"

definition rec_stat :: "recf"
  where
    "rec_stat = Cn 1 rec_lo [id 1 0, constn (Pi 1)]"

definition rec_inpt :: "nat \<Rightarrow> recf"
  where
    "rec_inpt vl = Cn vl rec_trpl 
                  [Cn vl (constn 0) [id vl 0], 
                   Cn vl (constn 1) [id vl 0], 
                   Cn vl (rec_strt (vl - 1)) 
                        (map (\<lambda> i. id vl (i)) [1..<vl])]"

lemma left_lemma: "rec_exec rec_left [c] = left c"
  by(simp add: rec_exec.simps rec_left_def left.simps lo_lemma)

lemma right_lemma: "rec_exec rec_right [c] = rght c"
  by(simp add: rec_exec.simps rec_right_def rght.simps lo_lemma)

lemma stat_lemma: "rec_exec rec_stat [c] = stat c"
  by(simp add: rec_exec.simps rec_stat_def stat.simps lo_lemma)

declare rec_strt.simps[simp del] strt.simps[simp del]

lemma map_cons_eq: 
  "(map ((\<lambda>a. rec_exec a (m # xs)) \<circ> 
    (\<lambda>i. recf.id (Suc (length xs)) (i))) 
          [Suc 0..<Suc (length xs)])
        = map (\<lambda> i. xs ! (i - 1)) [Suc 0..<Suc (length xs)]"
  apply(rule map_ext, auto)
   apply(auto simp: rec_exec.simps nth_append nth_Cons split: nat.split)
  done

lemma list_map_eq: 
  "vl = length (xs::nat list) \<Longrightarrow> map (\<lambda> i. xs ! (i - 1))
                                          [Suc 0..<Suc vl] = xs"
proof(induct vl arbitrary: xs)
  case (Suc vl)
  then show ?case 
    apply(subgoal_tac "\<exists> ys y. xs = ys @ [y]", auto)
  proof -
    fix ys y
    assume ind: 
      "\<And>xs. length (ys::nat list) = length (xs::nat list) \<Longrightarrow>
            map (\<lambda>i. xs ! (i - Suc 0)) [Suc 0..<length xs] @
                                [xs ! (length xs - Suc 0)] = xs"
      and h: "Suc 0 \<le> length (ys::nat list)"
    have "map (\<lambda>i. ys ! (i - Suc 0)) [Suc 0..<length ys] @ 
                                   [ys ! (length ys - Suc 0)] = ys"
      apply(rule_tac ind, simp)
      done
    moreover have 
      "map (\<lambda>i. (ys @ [y]) ! (i - Suc 0)) [Suc 0..<length ys]
      = map (\<lambda>i. ys ! (i - Suc 0)) [Suc 0..<length ys]"
      apply(rule map_ext)
      using h
      apply(auto simp: nth_append)
      done
    ultimately show "map (\<lambda>i. (ys @ [y]) ! (i - Suc 0)) 
        [Suc 0..<length ys] @ [(ys @ [y]) ! (length ys - Suc 0)] = ys"
      apply(simp del: map_eq_conv add: nth_append, auto)
      using h
      apply(simp)
      done
  next
    fix vl xs
    assume "Suc vl = length (xs::nat list)"
    thus "\<exists>ys y. xs = ys @ [y]"
      apply(rule_tac x = "butlast xs" in exI, 
          rule_tac x = "last xs" in exI)
      apply(cases "xs \<noteq> []", auto)
      done
  qed
qed simp

lemma nonempty_listE: 
  "Suc 0 \<le> length xs \<Longrightarrow> 
     (map ((\<lambda>a. rec_exec a (m # xs)) \<circ> 
         (\<lambda>i. recf.id (Suc (length xs)) (i))) 
             [Suc 0..<length xs] @ [(m # xs) ! length xs]) = xs"
  using map_cons_eq[of m xs]
  apply(simp del: map_eq_conv add: rec_exec.simps)
  using list_map_eq[of "length xs" xs]
  apply(simp)
  done

lemma inpt_lemma:
  "\<lbrakk>Suc (length xs) = vl\<rbrakk> \<Longrightarrow> 
            rec_exec (rec_inpt vl) (m # xs) = inpt m xs"
  apply(auto simp: rec_exec.simps rec_inpt_def 
      trpl_lemma inpt.simps strt_lemma)
   apply(subgoal_tac
      "(map ((\<lambda>a. rec_exec a (m # xs)) \<circ> 
          (\<lambda>i. recf.id (Suc (length xs)) (i))) 
            [Suc 0..<length xs] @ [(m # xs) ! length xs]) = xs", simp)
   apply(auto elim:nonempty_listE, cases xs, auto)
  done

definition rec_newconf:: "recf"
  where
    "rec_newconf = 
    Cn 2 rec_trpl 
        [Cn 2 rec_newleft [Cn 2 rec_left [id 2 1], 
                           Cn 2 rec_right [id 2 1], 
                           Cn 2 rec_actn [id 2 0, 
                                          Cn 2 rec_stat [id 2 1], 
                           Cn 2 rec_right [id 2 1]]],
          Cn 2 rec_newstat [id 2 0, 
                            Cn 2 rec_stat [id 2 1], 
                            Cn 2 rec_right [id 2 1]],
           Cn 2 rec_newrght [Cn 2 rec_left [id 2 1], 
                             Cn 2 rec_right [id 2 1], 
                             Cn 2 rec_actn [id 2 0, 
                                   Cn 2 rec_stat [id 2 1], 
                             Cn 2 rec_right [id 2 1]]]]"

lemma newconf_lemma: "rec_exec rec_newconf [m ,c] = newconf m c"
  by(auto simp: rec_newconf_def rec_exec.simps 
      trpl_lemma newleft_lemma left_lemma
      right_lemma stat_lemma newrght_lemma actn_lemma 
      newstat_lemma newconf.simps)

declare newconf_lemma[simp]

text \<open>
  \<open>conf m r k\<close> computes the TM configuration after \<open>k\<close> steps of execution
  of TM coded as \<open>m\<close> starting from the initial configuration where the left number equals \<open>0\<close>, 
  right number equals \<open>r\<close>. 
\<close>
fun conf :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "conf m r 0 = trpl 0 (Suc 0) r"
  | "conf m r (Suc t) = newconf m (conf m r t)"

declare conf.simps[simp del]

text \<open>
  \<open>conf\<close> is implemented by the following recursive function \<open>rec_conf\<close>.
\<close>
definition rec_conf :: "recf"
  where
    "rec_conf = Pr 2 (Cn 2 rec_trpl [Cn 2 (constn 0) [id 2 0], Cn 2 (constn (Suc 0)) [id 2 0], id 2 1])
                  (Cn 4 rec_newconf [id 4 0, id 4 3])"

lemma conf_step: 
  "rec_exec rec_conf [m, r, Suc t] =
         rec_exec rec_newconf [m, rec_exec rec_conf [m, r, t]]"
proof -
  have "rec_exec rec_conf ([m, r] @ [Suc t]) = 
          rec_exec rec_newconf [m, rec_exec rec_conf [m, r, t]]"
    by(simp only: rec_conf_def rec_pr_Suc_simp_rewrite,
        simp add: rec_exec.simps)
  thus "rec_exec rec_conf [m, r, Suc t] =
                rec_exec rec_newconf [m, rec_exec rec_conf [m, r, t]]"
    by simp
qed

text \<open>
  The correctness of \<open>rec_conf\<close>.
\<close>
lemma conf_lemma: 
  "rec_exec rec_conf [m, r, t] = conf m r t"
  by (induct t)
    (auto simp add: rec_conf_def rec_exec.simps conf.simps inpt_lemma trpl_lemma)

text \<open>
  \<open>NSTD c\<close> returns true if the configureation coded by \<open>c\<close> is no a stardard
  final configuration.
\<close>
fun NSTD :: "nat \<Rightarrow> bool"
  where
    "NSTD c = (stat c \<noteq> 0 \<or> left c \<noteq> 0 \<or> 
             rght c \<noteq> 2^(lg (rght c + 1) 2) - 1 \<or> rght c = 0)"

text \<open>
  \<open>rec_NSTD\<close> is the recursive function implementing \<open>NSTD\<close>.
\<close>
definition rec_NSTD :: "recf"
  where
    "rec_NSTD =
     Cn 1 rec_disj [
          Cn 1 rec_disj [
             Cn 1 rec_disj 
                [Cn 1 rec_noteq [rec_stat, constn 0], 
                 Cn 1 rec_noteq [rec_left, constn 0]] , 
              Cn 1 rec_noteq [rec_right,  
                              Cn 1 rec_minus [Cn 1 rec_power 
                                 [constn 2, Cn 1 rec_lg 
                                    [Cn 1 rec_add        
                                     [rec_right, constn 1], 
                                            constn 2]], constn 1]]],
               Cn 1 rec_eq [rec_right, constn 0]]"

lemma NSTD_lemma1: "rec_exec rec_NSTD [c] = Suc 0 \<or>
                   rec_exec rec_NSTD [c] = 0"
  by(simp add: rec_exec.simps rec_NSTD_def)

declare NSTD.simps[simp del]
lemma NSTD_lemma2': "(rec_exec rec_NSTD [c] = Suc 0) \<Longrightarrow> NSTD c"
  apply(simp add: rec_exec.simps rec_NSTD_def stat_lemma left_lemma 
      lg_lemma right_lemma power_lemma NSTD.simps)
  apply(auto)
  apply(cases "0 < left c", simp, simp)
  done

lemma NSTD_lemma2'': 
  "NSTD c \<Longrightarrow> (rec_exec rec_NSTD [c] = Suc 0)"
  apply(simp add: rec_exec.simps rec_NSTD_def stat_lemma 
      left_lemma lg_lemma right_lemma power_lemma NSTD.simps)
  apply(auto split: if_splits)
  done

text \<open>
  The correctness of \<open>NSTD\<close>.
\<close>
lemma NSTD_lemma2: "(rec_exec rec_NSTD [c] = Suc 0) = NSTD c"
  using NSTD_lemma1
  apply(auto intro: NSTD_lemma2' NSTD_lemma2'')
  done

fun nstd :: "nat \<Rightarrow> nat"
  where
    "nstd c = (if NSTD c then 1 else 0)"

lemma nstd_lemma: "rec_exec rec_NSTD [c] = nstd c"
  using NSTD_lemma1
  apply(simp add: NSTD_lemma2, auto)
  done

text\<open>
  \<open>nonstep m r t\<close> means afer \<open>t\<close> steps of execution, the TM coded by \<open>m\<close>
  is not at a stardard final configuration.
\<close>
fun nonstop :: "nat \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat"
  where
    "nonstop m r t = nstd (conf m r t)"

text \<open>
  \<open>rec_nonstop\<close> is the recursive function implementing \<open>nonstop\<close>.
\<close>
definition rec_nonstop :: "recf"
  where
    "rec_nonstop = Cn 3 rec_NSTD [rec_conf]"

text \<open>
  The correctness of \<open>rec_nonstop\<close>.
\<close>
lemma nonstop_lemma: 
  "rec_exec rec_nonstop [m, r, t] = nonstop m r t"
  apply(simp add: rec_exec.simps rec_nonstop_def nstd_lemma conf_lemma)
  done

text\<open>
  \<open>rec_halt\<close> is the recursive function calculating the steps a TM needs to execute before
  to reach a stardard final configuration. This recursive function is the only one
  using \<open>Mn\<close> combinator. So it is the only non-primitive recursive function 
  needs to be used in the construction of the universal function \<open>F\<close>.
\<close>

definition rec_halt :: "recf"
  where
    "rec_halt = Mn (Suc (Suc 0)) (rec_nonstop)"

declare nonstop.simps[simp del]

text \<open>
  The lemma relates the interpreter of primitive functions with
  the calculation relation of general recursive functions. 
\<close>

declare numeral_2_eq_2[simp] numeral_3_eq_3[simp]

lemma primerec_rec_right_1[intro]: "primerec rec_right (Suc 0)"
  by(auto simp: rec_right_def rec_lo_def Let_def;force)

lemma primerec_rec_pi_helper:
  "\<forall>i<Suc (Suc 0). primerec ([recf.id (Suc 0) 0, recf.id (Suc 0) 0] ! i) (Suc 0)"
  by fastforce

lemmas primerec_rec_pi_helpers =
  primerec_rec_pi_helper primerec_constn_1 primerec_rec_sg_1 primerec_rec_not_1 primerec_rec_conj_2

lemma primrec_dummyfac:
  "\<forall>i<Suc (Suc 0).
       primerec
        ([recf.id (Suc 0) 0,
          Cn (Suc 0) s
           [Cn (Suc 0) rec_dummyfac
             [recf.id (Suc 0) 0, recf.id (Suc 0) 0]]] !
         i)
        (Suc 0)"
  by(auto simp: rec_dummyfac_def;force)

lemma primerec_rec_pi_1[intro]:  "primerec rec_pi (Suc 0)"
  apply(simp add: rec_pi_def rec_dummy_pi_def 
      rec_np_def rec_fac_def rec_prime_def
      rec_Minr.simps Let_def get_fstn_args.simps
      arity.simps
      rec_all.simps rec_sigma.simps rec_accum.simps)
  apply(tactic \<open>resolve_tac @{context} [@{thm prime_cn},  @{thm prime_pr}] 1\<close>
      ;(simp add:primerec_rec_pi_helpers primrec_dummyfac)?)+
  by fastforce+

lemma primerec_recs[intro]:
  "primerec rec_trpl (Suc (Suc (Suc 0)))"
  "primerec rec_newleft0 (Suc (Suc 0))"
  "primerec rec_newleft1 (Suc (Suc 0))"
  "primerec rec_newleft2 (Suc (Suc 0))"
  "primerec rec_newleft3 (Suc (Suc 0))"
  "primerec rec_newleft (Suc (Suc (Suc 0)))"
  "primerec rec_left (Suc 0)"
  "primerec rec_actn (Suc (Suc (Suc 0)))"
  "primerec rec_stat (Suc 0)"
  "primerec rec_newstat (Suc (Suc (Suc 0)))"
           apply(simp_all add: rec_newleft_def rec_embranch.simps rec_left_def rec_lo_def rec_entry_def
      rec_actn_def Let_def arity.simps rec_newleft0_def rec_stat_def rec_newstat_def
      rec_newleft1_def rec_newleft2_def rec_newleft3_def rec_trpl_def)
           apply(tactic \<open>resolve_tac @{context} [@{thm prime_cn}, 
    @{thm prime_id}, @{thm prime_pr}] 1\<close>;force)+
  done

lemma primerec_rec_newrght[intro]: "primerec rec_newrght (Suc (Suc (Suc 0)))"
  apply(simp add: rec_newrght_def rec_embranch.simps
      Let_def arity.simps rec_newrgt0_def 
      rec_newrgt1_def rec_newrgt2_def rec_newrgt3_def)
  apply(tactic \<open>resolve_tac @{context} [@{thm prime_cn}, 
    @{thm prime_id}, @{thm prime_pr}] 1\<close>;force)+
  done

lemma primerec_rec_newconf[intro]: "primerec rec_newconf (Suc (Suc 0))"
  apply(simp add: rec_newconf_def)
  by(tactic \<open>resolve_tac @{context} [@{thm prime_cn}, 
    @{thm prime_id}, @{thm prime_pr}] 1\<close>;force)

lemma primerec_rec_conf[intro]: "primerec rec_conf (Suc (Suc (Suc 0)))"
  apply(simp add: rec_conf_def)
  by(tactic \<open>resolve_tac @{context} [@{thm prime_cn}, 
    @{thm prime_id}, @{thm prime_pr}] 1\<close>;force simp: numeral)

lemma primerec_recs2[intro]:
  "primerec rec_lg (Suc (Suc 0))"
  "primerec rec_nonstop (Suc (Suc (Suc 0)))"
   apply(simp_all add: rec_lg_def rec_nonstop_def rec_NSTD_def rec_stat_def
      rec_lo_def Let_def rec_left_def rec_right_def rec_newconf_def
      rec_newstat_def)
  by(tactic \<open>resolve_tac @{context} [@{thm prime_cn}, 
    @{thm prime_id}, @{thm prime_pr}] 1\<close>;fastforce)+

lemma primerec_terminate: 
  "\<lbrakk>primerec f x; length xs = x\<rbrakk> \<Longrightarrow> terminate f xs"
proof(induct arbitrary: xs rule: primerec.induct)
  fix xs
  assume "length (xs::nat list) = Suc 0"  thus "terminate z xs"
    by(cases xs, auto intro: termi_z)
next
  fix xs
  assume "length (xs::nat list) = Suc 0" thus "terminate s xs"
    by(cases xs, auto intro: termi_s)
next
  fix n m xs
  assume "n < m" "length (xs::nat list) = m"  thus "terminate (id m n) xs"
    by(erule_tac termi_id, simp)
next
  fix f k gs m n xs
  assume ind: "\<forall>i<length gs. primerec (gs ! i) m \<and> (\<forall>x. length x = m \<longrightarrow> terminate (gs ! i) x)"
    and ind2: "\<And> xs. length xs = k \<Longrightarrow> terminate f xs"
    and h: "primerec f k"  "length gs = k" "m = n" "length (xs::nat list) = m"
  have "terminate f (map (\<lambda>g. rec_exec g xs) gs)"
    using ind2[of "(map (\<lambda>g. rec_exec g xs) gs)"] h
    by simp
  moreover have "\<forall>g\<in>set gs. terminate g xs"
    using ind h
    by(auto simp: set_conv_nth)
  ultimately show "terminate (Cn n f gs) xs"
    using h
    by(rule_tac termi_cn, auto)
next
  fix f n g m xs
  assume ind1: "\<And>xs. length xs = n \<Longrightarrow> terminate f xs"
    and ind2: "\<And>xs. length xs = Suc (Suc n) \<Longrightarrow> terminate g xs"
    and h: "primerec f n" " primerec g (Suc (Suc n))" " m = Suc n" "length (xs::nat list) = m"
  have "\<forall>y<last xs. terminate g (butlast xs @ [y, rec_exec (Pr n f g) (butlast xs @ [y])])"
    using h ind2 by(auto)
  moreover have "terminate f (butlast xs)"
    using ind1[of "butlast xs"] h
    by simp
  moreover have "length (butlast xs) = n"
    using h by simp
  ultimately have "terminate (Pr n f g) (butlast xs @ [last xs])"
    by(rule_tac termi_pr, simp_all)
  thus "terminate (Pr n f g) xs"
    using h
    by(cases "xs = []", auto)
qed

text \<open>
  The following lemma gives the correctness of \<open>rec_halt\<close>.
  It says: if \<open>rec_halt\<close> calculates that the TM coded by \<open>m\<close>
  will reach a standard final configuration after \<open>t\<close> steps of execution, then it is indeed so.
\<close>

text \<open>F: universal machine\<close>

text \<open>
  \<open>valu r\<close> extracts computing result out of the right number \<open>r\<close>.
\<close>
fun valu :: "nat \<Rightarrow> nat"
  where
    "valu r = (lg (r + 1) 2) - 1"

text \<open>
  \<open>rec_valu\<close> is the recursive function implementing \<open>valu\<close>.
\<close>
definition rec_valu :: "recf"
  where
    "rec_valu = Cn 1 rec_minus [Cn 1 rec_lg [s, constn 2], constn 1]"

text \<open>
  The correctness of \<open>rec_valu\<close>.
\<close>
lemma value_lemma: "rec_exec rec_valu [r] = valu r"
  by(simp add: rec_exec.simps rec_valu_def lg_lemma)

lemma primerec_rec_valu_1[intro]: "primerec rec_valu (Suc 0)"
  unfolding rec_valu_def
  apply(rule prime_cn[of _ "Suc (Suc 0)"])
  by auto auto

declare valu.simps[simp del]

text \<open>
  The definition of the universal function \<open>rec_F\<close>.
\<close>
definition rec_F :: "recf"
  where
    "rec_F = Cn (Suc (Suc 0)) rec_valu [Cn (Suc (Suc 0)) rec_right [Cn (Suc (Suc 0))
 rec_conf ([id (Suc (Suc 0)) 0, id (Suc (Suc 0)) (Suc 0), rec_halt])]]"

lemma terminate_halt_lemma: 
  "\<lbrakk>rec_exec rec_nonstop ([m, r] @ [t]) = 0; 
     \<forall>i<t. 0 < rec_exec rec_nonstop ([m, r] @ [i])\<rbrakk> \<Longrightarrow> terminate rec_halt [m, r]"
  apply(simp add: rec_halt_def)
  apply(rule termi_mn, auto)
  by(rule primerec_terminate; auto)+


text \<open>
  The correctness of \<open>rec_F\<close>, halt case.
\<close>

lemma F_lemma: "rec_exec rec_halt [m, r] = t \<Longrightarrow> rec_exec rec_F [m, r] = (valu (rght (conf m r t)))"
  by(simp add: rec_F_def rec_exec.simps value_lemma right_lemma conf_lemma halt_lemma)

lemma terminate_F_lemma: "terminate rec_halt [m, r] \<Longrightarrow> terminate rec_F [m, r]"
  apply(simp add: rec_F_def)
  apply(rule termi_cn, auto)
   apply(rule primerec_terminate, auto)
  apply(rule termi_cn, auto)
   apply(rule primerec_terminate, auto)
  apply(rule termi_cn, auto)
    apply(rule primerec_terminate, auto)
   apply(rule termi_id;force)
  apply(rule termi_id;force)
  done

text \<open>
  The correctness of \<open>rec_F\<close>, nonhalt case.
\<close>

subsection \<open>Coding function of TMs\<close>

text \<open>
  The purpose of this section is to get the coding function of Turing Machine, which is 
  going to be named \<open>code\<close>.
\<close>

fun bl2nat :: "cell list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "bl2nat [] n = 0"
  | "bl2nat (Bk#bl) n = bl2nat bl (Suc n)"
  | "bl2nat (Oc#bl) n = 2^n + bl2nat bl (Suc n)"

fun bl2wc :: "cell list \<Rightarrow> nat"
  where
    "bl2wc xs = bl2nat xs 0"

fun trpl_code :: "config \<Rightarrow> nat"
  where
    "trpl_code (st, l, r) = trpl (bl2wc l) st (bl2wc r)"

declare bl2nat.simps[simp del] bl2wc.simps[simp del]
  trpl_code.simps[simp del]

fun action_map :: "action \<Rightarrow> nat"
  where
    "action_map W0 = 0"
  | "action_map W1 = 1"
  | "action_map L = 2"
  | "action_map R = 3"
  | "action_map Nop = 4"

fun action_map_iff :: "nat \<Rightarrow> action"
  where
    "action_map_iff (0::nat) = W0"
  | "action_map_iff (Suc 0) = W1"
  | "action_map_iff (Suc (Suc 0)) = L"
  | "action_map_iff (Suc (Suc (Suc 0))) = R"
  | "action_map_iff n = Nop"

fun block_map :: "cell \<Rightarrow> nat"
  where
    "block_map Bk = 0"
  | "block_map Oc = 1"

fun godel_code' :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "godel_code' [] n = 1"
  | "godel_code' (x#xs) n = (Pi n)^x * godel_code' xs (Suc n) "

fun godel_code :: "nat list \<Rightarrow> nat"
  where
    "godel_code xs = (let lh = length xs in 
                   2^lh * (godel_code' xs (Suc 0)))"

fun modify_tprog :: "instr list \<Rightarrow> nat list"
  where
    "modify_tprog [] =  []"
  | "modify_tprog ((ac, ns)#nl) = action_map ac # ns # modify_tprog nl"

text \<open>
  \<open>code tp\<close> gives the Godel coding of TM program \<open>tp\<close>.
\<close>
fun code :: "instr list \<Rightarrow> nat"
  where 
    "code tp = (let nl = modify_tprog tp in 
              godel_code nl)"

subsection \<open>Relating interperter functions to the execution of TMs\<close>

lemma bl2wc_0[simp]: "bl2wc [] = 0" by(simp add: bl2wc.simps bl2nat.simps)

lemma fetch_action_map_4[simp]: "\<lbrakk>fetch tp 0 b = (nact, ns)\<rbrakk> \<Longrightarrow> action_map nact = 4"
  apply(simp add: fetch.simps)
  done

lemma Pi_gr_1[simp]: "Pi n > Suc 0"
proof(induct n, auto simp: Pi.simps Np.simps)
  fix n
  let ?setx = "{y. y \<le> Suc (Pi n!) \<and> Pi n < y \<and> Prime y}"
  have "finite ?setx" by auto
  moreover have "?setx \<noteq> {}"
    using prime_ex[of "Pi n"]
    apply(auto)
    done
  ultimately show "Suc 0 < Min ?setx"
    apply(simp add: Min_gr_iff)
    apply(auto simp: Prime.simps)
    done
qed

lemma Pi_not_0[simp]: "Pi n > 0"
  using Pi_gr_1[of n]
  by arith

declare godel_code.simps[simp del]

lemma godel_code'_nonzero[simp]: "0 < godel_code' nl n"
  apply(induct nl arbitrary: n)
   apply(auto simp: godel_code'.simps)
  done

lemma godel_code_great: "godel_code nl > 0"
  apply(simp add: godel_code.simps)
  done

lemma godel_code_eq_1: "(godel_code nl = 1) = (nl = [])"
  apply(auto simp: godel_code.simps)
  done

lemma godel_code_1_iff[elim]: 
  "\<lbrakk>i < length nl; \<not> Suc 0 < godel_code nl\<rbrakk> \<Longrightarrow> nl ! i = 0"
  using godel_code_great[of nl] godel_code_eq_1[of nl]
  apply(simp)
  done

lemma prime_coprime: "\<lbrakk>Prime x; Prime y; x\<noteq>y\<rbrakk> \<Longrightarrow> coprime x y"
proof (simp only: Prime.simps coprime_def, auto simp: dvd_def,
    rule_tac classical, simp)
  fix d k ka
  assume case_ka: "\<forall>u<d * ka. \<forall>v<d * ka. u * v \<noteq> d * ka" 
    and case_k: "\<forall>u<d * k. \<forall>v<d * k. u * v \<noteq> d * k"
    and h: "(0::nat) < d" "d \<noteq> Suc 0" "Suc 0 < d * ka" 
    "ka \<noteq> k" "Suc 0 < d * k"
  from h have "k > Suc 0 \<or> ka >Suc 0"
    by (cases ka;cases k;force+)
  from this show "False"
  proof(erule_tac disjE)
    assume  "(Suc 0::nat) < k"
    hence "k < d*k \<and> d < d*k"
      using h
      by(auto)
    thus "?thesis"
      using case_k
      apply(erule_tac x = d in allE)
      apply(simp)
      apply(erule_tac x = k in allE)
      apply(simp)
      done
  next
    assume "(Suc 0::nat) < ka"
    hence "ka < d * ka \<and> d < d*ka"
      using h by auto
    thus "?thesis"
      using case_ka
      apply(erule_tac x = d in allE)
      apply(simp)
      apply(erule_tac x = ka in allE)
      apply(simp)
      done
  qed
qed

lemma Pi_inc: "Pi (Suc i) > Pi i"
proof(simp add: Pi.simps Np.simps)
  let ?setx = "{y. y \<le> Suc (Pi i!) \<and> Pi i < y \<and> Prime y}"
  have "finite ?setx" by simp
  moreover have "?setx \<noteq> {}"
    using prime_ex[of "Pi i"]
    apply(auto)
    done
  ultimately show "Pi i < Min ?setx"
    apply(simp)
    done
qed    

lemma Pi_inc_gr: "i < j \<Longrightarrow> Pi i < Pi j"
proof(induct j, simp)
  fix j
  assume ind: "i < j \<Longrightarrow> Pi i < Pi j"
    and h: "i < Suc j"
  from h show "Pi i < Pi (Suc j)"
  proof(cases "i < j")
    case True thus "?thesis"
    proof -
      assume "i < j"
      hence "Pi i < Pi j" by(erule_tac ind)
      moreover have "Pi j < Pi (Suc j)"
        apply(simp add: Pi_inc)
        done
      ultimately show "?thesis"
        by simp
    qed
  next
    assume "i < Suc j" "\<not> i < j"
    hence "i = j"
      by arith
    thus "Pi i < Pi (Suc j)"
      apply(simp add: Pi_inc)
      done
  qed
qed      

lemma Pi_notEq: "i \<noteq> j \<Longrightarrow> Pi i \<noteq> Pi j"
  apply(cases "i < j")
  using Pi_inc_gr[of i j]
   apply(simp)
  using Pi_inc_gr[of j i]
  apply(simp)
  done

lemma prime_2[intro]: "Prime (Suc (Suc 0))"
  apply(auto simp: Prime.simps)
  using less_2_cases by fastforce

lemma Prime_Pi[intro]: "Prime (Pi n)"
proof(induct n, auto simp: Pi.simps Np.simps)
  fix n
  let ?setx = "{y. y \<le> Suc (Pi n!) \<and> Pi n < y \<and> Prime y}"
  show "Prime (Min ?setx)"
  proof -
    have "finite ?setx" by simp
    moreover have "?setx \<noteq> {}" 
      using prime_ex[of "Pi n"]
      apply(simp)
      done
    ultimately show "?thesis"
      apply(drule_tac Min_in, simp, simp)
      done
  qed
qed

lemma Pi_coprime: "i \<noteq> j \<Longrightarrow> coprime (Pi i) (Pi j)"
  using Prime_Pi[of i]
  using Prime_Pi[of j]
  apply(rule_tac prime_coprime, simp_all add: Pi_notEq)
  done

lemma Pi_power_coprime: "i \<noteq> j \<Longrightarrow> coprime ((Pi i)^m) ((Pi j)^n)"
  unfolding coprime_power_right_iff coprime_power_left_iff using Pi_coprime by auto

lemma coprime_dvd_mult_nat2: "\<lbrakk>coprime (k::nat) n; k dvd n * m\<rbrakk> \<Longrightarrow> k dvd m"
  unfolding coprime_dvd_mult_right_iff.

declare godel_code'.simps[simp del]

lemma godel_code'_butlast_last_id' :
  "godel_code' (ys @ [y]) (Suc j) = godel_code' ys (Suc j) * 
                                Pi (Suc (length ys + j)) ^ y"
proof(induct ys arbitrary: j, simp_all add: godel_code'.simps)
qed  

lemma godel_code'_butlast_last_id: 
  "xs \<noteq> [] \<Longrightarrow> godel_code' xs (Suc j) = 
  godel_code' (butlast xs) (Suc j) * Pi (length xs + j)^(last xs)"
  apply(subgoal_tac "\<exists> ys y. xs = ys @ [y]")
   apply(erule_tac exE, erule_tac exE, simp add: 
      godel_code'_butlast_last_id')
  apply(rule_tac x = "butlast xs" in exI)
  apply(rule_tac x = "last xs" in exI, auto)
  done

lemma godel_code'_not0: "godel_code' xs n \<noteq> 0"
  apply(induct xs, auto simp: godel_code'.simps)
  done

lemma godel_code_append_cons: 
  "length xs = i \<Longrightarrow> godel_code' (xs@y#ys) (Suc 0)
    = godel_code' xs (Suc 0) * Pi (Suc i)^y * godel_code' ys (i + 2)"
proof(induct "length xs" arbitrary: i y ys xs, simp add: godel_code'.simps,simp)
  fix x xs i y ys
  assume ind: 
    "\<And>xs i y ys. \<lbrakk>x = i; length xs = i\<rbrakk> \<Longrightarrow> 
       godel_code' (xs @ y # ys) (Suc 0) 
     = godel_code' xs (Suc 0) * Pi (Suc i) ^ y * 
                             godel_code' ys (Suc (Suc i))"
    and h: "Suc x = i" 
    "length (xs::nat list) = i"
  have 
    "godel_code' (butlast xs @ last xs # ((y::nat)#ys)) (Suc 0) = 
        godel_code' (butlast xs) (Suc 0) * Pi (Suc (i - 1))^(last xs) 
              * godel_code' (y#ys) (Suc (Suc (i - 1)))"
    apply(rule_tac ind)
    using h
    by(auto)
  moreover have 
    "godel_code' xs (Suc 0)= godel_code' (butlast xs) (Suc 0) *
                                                  Pi (i)^(last xs)"
    using godel_code'_butlast_last_id[of xs] h
    apply(cases "xs = []", simp, simp)
    done 
  moreover have "butlast xs @ last xs # y # ys = xs @ y # ys"
    using h
    apply(cases xs, auto)
    done
  ultimately show 
    "godel_code' (xs @ y # ys) (Suc 0) =
               godel_code' xs (Suc 0) * Pi (Suc i) ^ y *
                    godel_code' ys (Suc (Suc i))"
    using h
    apply(simp add: godel_code'_not0 Pi_not_0)
    apply(simp add: godel_code'.simps)
    done
qed

lemma Pi_coprime_pre: 
  "length ps \<le> i \<Longrightarrow> coprime (Pi (Suc i)) (godel_code' ps (Suc 0))"
proof(induct "length ps" arbitrary: ps)
  fix x ps
  assume ind: 
    "\<And>ps. \<lbrakk>x = length ps; length ps \<le> i\<rbrakk> \<Longrightarrow>
                  coprime (Pi (Suc i)) (godel_code' ps (Suc 0))"
    and h: "Suc x = length ps"
    "length (ps::nat list) \<le> i"
  have g: "coprime (Pi (Suc i)) (godel_code' (butlast ps) (Suc 0))"
    apply(rule_tac ind)
    using h by auto
  have k: "godel_code' ps (Suc 0) = 
         godel_code' (butlast ps) (Suc 0) * Pi (length ps)^(last ps)"
    using godel_code'_butlast_last_id[of ps 0] h 
    by(cases ps, simp, simp)
  from g have "coprime (Pi (Suc i)) (Pi (length ps) ^ last ps)"
    unfolding coprime_power_right_iff using Pi_coprime h(2) by auto
  with g have 
    "coprime (Pi (Suc i)) (godel_code' (butlast ps) (Suc 0) *
                                        Pi (length ps)^(last ps)) "
    unfolding coprime_mult_right_iff coprime_power_right_iff by auto

  from this and k show "coprime (Pi (Suc i)) (godel_code' ps (Suc 0))"
    by simp
qed (auto simp add: godel_code'.simps)

lemma Pi_coprime_suf: "i < j \<Longrightarrow> coprime (Pi i) (godel_code' ps j)"
proof(induct "length ps" arbitrary: ps)
  fix x ps
  assume ind: 
    "\<And>ps. \<lbrakk>x = length ps; i < j\<rbrakk> \<Longrightarrow> 
                    coprime (Pi i) (godel_code' ps j)"
    and h: "Suc x = length (ps::nat list)" "i < j"
  have g: "coprime (Pi i) (godel_code' (butlast ps) j)"
    apply(rule ind) using h by auto
  have k: "(godel_code' ps j) = godel_code' (butlast ps) j *
                                 Pi (length ps + j - 1)^last ps"
    using h godel_code'_butlast_last_id[of ps "j - 1"]
    apply(cases "ps = []", simp, simp)
    done
  from g have
    "coprime (Pi i) (godel_code' (butlast ps) j * 
                          Pi (length ps + j - 1)^last ps)"
    using Pi_power_coprime[of i "length ps + j - 1" 1 "last ps"] h
    by(auto)
  from k and this show "coprime (Pi i) (godel_code' ps j)"
    by auto
qed (simp add: godel_code'.simps)

lemma godel_finite: 
  "finite {u. Pi (Suc i) ^ u dvd godel_code' nl (Suc 0)}"
proof(rule bounded_nat_set_is_finite[of _ "godel_code' nl (Suc 0)",rule_format],goal_cases)
  case (1 ia)
  then show ?case proof(cases "ia < godel_code' nl (Suc 0)")
    case False
    hence g1: "Pi (Suc i) ^ ia dvd godel_code' nl (Suc 0)"
      and g2: "\<not> ia < godel_code' nl (Suc 0)"
      and "Pi (Suc i)^ia \<le> godel_code' nl (Suc 0)"
      using godel_code'_not0[of nl "Suc 0"] using 1 by (auto elim:dvd_imp_le)
    moreover have "ia < Pi (Suc i)^ia"
      by(rule x_less_exp[OF Pi_gr_1])
    ultimately show ?thesis
      using g2 by(auto)
  qed auto
qed

lemma godel_code_in: 
  "i < length nl \<Longrightarrow>  nl ! i  \<in> {u. Pi (Suc i) ^ u dvd
                                     godel_code' nl (Suc 0)}"
proof -
  assume h: "i<length nl"
  hence "godel_code' (take i nl@(nl!i)#drop (Suc i) nl) (Suc 0)
           = godel_code' (take i nl) (Suc 0) *  Pi (Suc i)^(nl!i) *
                               godel_code' (drop (Suc i) nl) (i + 2)"
    by(rule_tac godel_code_append_cons, simp)
  moreover from h have "take i nl @ (nl ! i) # drop (Suc i) nl = nl"
    using upd_conv_take_nth_drop[of i nl "nl ! i"]
    by simp
  ultimately  show 
    "nl ! i \<in> {u. Pi (Suc i) ^ u dvd godel_code' nl (Suc 0)}"
    by(simp)
qed

lemma godel_code'_get_nth:
  "i < length nl \<Longrightarrow> Max {u. Pi (Suc i) ^ u dvd 
                          godel_code' nl (Suc 0)} = nl ! i"
proof(rule_tac Max_eqI)
  let ?gc = "godel_code' nl (Suc 0)"
  assume h: "i < length nl" thus "finite {u. Pi (Suc i) ^ u dvd ?gc}"
    by (simp add: godel_finite)  
next
  fix y
  let ?suf ="godel_code' (drop (Suc i) nl) (i + 2)"
  let ?pref = "godel_code' (take i nl) (Suc 0)"
  assume h: "i < length nl" 
    "y \<in> {u. Pi (Suc i) ^ u dvd godel_code' nl (Suc 0)}"
  moreover hence
    "godel_code' (take i nl@(nl!i)#drop (Suc i) nl) (Suc 0)
    = ?pref * Pi (Suc i)^(nl!i) * ?suf"
    by(rule_tac godel_code_append_cons, simp)
  moreover from h have "take i nl @ (nl!i) # drop (Suc i) nl = nl"
    using upd_conv_take_nth_drop[of i nl "nl!i"]
    by simp
  ultimately show "y\<le>nl!i"
  proof(simp)
    let ?suf' = "godel_code' (drop (Suc i) nl) (Suc (Suc i))"
    assume mult_dvd: 
      "Pi (Suc i) ^ y dvd ?pref *  Pi (Suc i) ^ nl ! i * ?suf'"
    hence "Pi (Suc i) ^ y dvd ?pref * Pi (Suc i) ^ nl ! i"
    proof -
      have "coprime (Pi (Suc i)^y) ?suf'" by (simp add: Pi_coprime_suf)
      thus ?thesis using coprime_dvd_mult_left_iff mult_dvd by blast
    qed
    hence "Pi (Suc i) ^ y dvd Pi (Suc i) ^ nl ! i"
    proof(rule_tac coprime_dvd_mult_nat2)
      have "coprime (Pi (Suc i)^y) (?pref^Suc 0)" using Pi_coprime_pre by simp
      thus "coprime (Pi (Suc i) ^ y) ?pref" by simp
    qed
    hence "Pi (Suc i) ^ y \<le>  Pi (Suc i) ^ nl ! i "
      apply(rule_tac dvd_imp_le, auto)
      done
    thus "y \<le> nl ! i"
      apply(rule_tac power_le_imp_le_exp, auto)
      done
  qed
next
  assume h: "i<length nl"

  thus "nl ! i \<in> {u. Pi (Suc i) ^ u dvd godel_code' nl (Suc 0)}"
    by(rule_tac godel_code_in, simp)
qed

lemma godel_code'_set[simp]: 
  "{u. Pi (Suc i) ^ u dvd (Suc (Suc 0)) ^ length nl * 
                                     godel_code' nl (Suc 0)} = 
    {u. Pi (Suc i) ^ u dvd  godel_code' nl (Suc 0)}"
  apply(rule_tac Collect_cong, auto)
  apply(rule_tac n = " (Suc (Suc 0)) ^ length nl" in 
      coprime_dvd_mult_nat2)
proof -
  have "Pi 0 = (2::nat)" by(simp add: Pi.simps)
  show "coprime (Pi (Suc i) ^ u) ((Suc (Suc 0)) ^ length nl)" for u
    using Pi_coprime Pi.simps(1) by force
qed

lemma godel_code_get_nth: 
  "i < length nl \<Longrightarrow> 
           Max {u. Pi (Suc i) ^ u dvd godel_code nl} = nl ! i"
  by(simp add: godel_code.simps godel_code'_get_nth)

lemma mod_dvd_simp: "(x mod y = (0::nat)) = (y dvd x)"
  by(simp add: dvd_def, auto)

lemma dvd_power_le: "\<lbrakk>a > Suc 0; a ^ y dvd a ^ l\<rbrakk> \<Longrightarrow> y \<le> l"
  apply(cases "y \<le> l", simp, simp)
  apply(subgoal_tac "\<exists> d. y = l + d", auto simp: power_add)
  apply(rule_tac x = "y - l" in exI, simp)
  done


lemma Pi_nonzeroE[elim]: "Pi n = 0 \<Longrightarrow> RR"
  using Pi_not_0[of n] by simp

lemma Pi_not_oneE[elim]: "Pi n = Suc 0 \<Longrightarrow> RR"
  using Pi_gr_1[of n] by simp

lemma finite_power_dvd:
  "\<lbrakk>(a::nat) > Suc 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> finite {u. a^u dvd y}"
  apply(auto simp: dvd_def simp:gr0_conv_Suc intro!:bounded_nat_set_is_finite[of _ y])
  by (metis le_less_trans mod_less mod_mult_self1_is_0 not_le Suc_lessD less_trans_Suc
      mult.right_neutral n_less_n_mult_m x_less_exp
      zero_less_Suc zero_less_mult_pos)

lemma conf_decode1: "\<lbrakk>m \<noteq> n; m \<noteq> k; k \<noteq> n\<rbrakk> \<Longrightarrow> 
  Max {u. Pi m ^ u dvd Pi m ^ l * Pi n ^ st * Pi k ^ r} = l"
proof -
  let ?setx = "{u. Pi m ^ u dvd Pi m ^ l * Pi n ^ st * Pi k ^ r}"
  assume g: "m \<noteq> n" "m \<noteq> k" "k \<noteq> n"
  show "Max ?setx = l"
  proof(rule_tac Max_eqI)
    show "finite ?setx"
      apply(rule_tac finite_power_dvd, auto)
      done
  next
    fix y
    assume h: "y \<in> ?setx"
    have "Pi m ^ y dvd Pi m ^ l"
    proof -
      have "Pi m ^ y dvd Pi m ^ l * Pi n ^ st"
        using h g Pi_power_coprime
        by (simp add: coprime_dvd_mult_left_iff)
      thus "Pi m^y dvd Pi m^l" using g Pi_power_coprime coprime_dvd_mult_left_iff by blast
    qed
    thus "y \<le> (l::nat)"
      apply(rule_tac a = "Pi m" in power_le_imp_le_exp)
       apply(simp_all)
      apply(rule_tac dvd_power_le, auto)
      done
  next
    show "l \<in> ?setx" by simp
  qed
qed

lemma left_trpl_fst[simp]: "left (trpl l st r) = l"
  apply(simp add: left.simps trpl.simps lo.simps loR.simps mod_dvd_simp)
  apply(auto simp: conf_decode1)
   apply(cases "Pi 0 ^ l * Pi (Suc 0) ^ st * Pi (Suc (Suc 0)) ^ r")
    apply(auto)
  apply(erule_tac x = l in allE, auto)
  done   

lemma stat_trpl_snd[simp]: "stat (trpl l st r) = st"
  apply(simp add: stat.simps trpl.simps lo.simps 
      loR.simps mod_dvd_simp, auto)
    apply(subgoal_tac "Pi 0 ^ l * Pi (Suc 0) ^ st * Pi (Suc (Suc 0)) ^ r
               = Pi (Suc 0)^st * Pi 0 ^ l *  Pi (Suc (Suc 0)) ^ r")
     apply(simp (no_asm_simp) add: conf_decode1, simp)
   apply(cases "Pi 0 ^ l * Pi (Suc 0) ^ st * 
                                  Pi (Suc (Suc 0)) ^ r", auto)
  apply(erule_tac x = st in allE, auto)
  done

lemma rght_trpl_trd[simp]: "rght (trpl l st r) = r"
  apply(simp add: rght.simps trpl.simps lo.simps 
      loR.simps mod_dvd_simp, auto)
    apply(subgoal_tac "Pi 0 ^ l * Pi (Suc 0) ^ st * Pi (Suc (Suc 0)) ^ r
               = Pi (Suc (Suc 0))^r * Pi 0 ^ l *  Pi (Suc 0) ^ st")
     apply(simp (no_asm_simp) add: conf_decode1, simp)
   apply(cases "Pi 0 ^ l * Pi (Suc 0) ^ st * Pi (Suc (Suc 0)) ^ r",
      auto)
  apply(erule_tac x = r in allE, auto)
  done

lemma max_lor:
  "i < length nl \<Longrightarrow> Max {u. loR [godel_code nl, Pi (Suc i), u]} 
                   = nl ! i"
  apply(simp add: loR.simps godel_code_get_nth mod_dvd_simp)
  done

lemma godel_decode: 
  "i < length nl \<Longrightarrow> Entry (godel_code nl) i = nl ! i"
  apply(auto simp: Entry.simps lo.simps max_lor)
  apply(erule_tac x = "nl!i" in allE)
  using max_lor[of i nl] godel_finite[of i nl]
  apply(simp)
  apply(drule_tac Max_in, auto simp: loR.simps 
      godel_code.simps mod_dvd_simp)
  using godel_code_in[of i nl]
  apply(simp)
  done

lemma Four_Suc: "4 = Suc (Suc (Suc (Suc 0)))"
  by auto

declare numeral_2_eq_2[simp del]

lemma modify_tprog_fetch_even: 
  "\<lbrakk>st \<le> length tp div 2; st > 0\<rbrakk> \<Longrightarrow>
  modify_tprog tp ! (4 * (st - Suc 0) ) = 
  action_map (fst (tp ! (2 * (st - Suc 0))))"
proof(induct st arbitrary: tp, simp)
  fix tp st
  assume ind: 
    "\<And>tp. \<lbrakk>st \<le> length tp div 2; 0 < st\<rbrakk> \<Longrightarrow> 
     modify_tprog tp ! (4 * (st - Suc 0)) =
               action_map (fst ((tp::instr list) ! (2 * (st - Suc 0))))"
    and h: "Suc st \<le> length (tp::instr list) div 2" "0 < Suc st"
  thus "modify_tprog tp ! (4 * (Suc st - Suc 0)) = 
          action_map (fst (tp ! (2 * (Suc st - Suc 0))))"
  proof(cases "st = 0")
    case True thus "?thesis"
      using h by(cases tp, auto)
  next
    case False
    assume g: "st \<noteq> 0"
    hence "\<exists> aa ab ba bb tp'. tp = (aa, ab) # (ba, bb) # tp'"
      using h by(cases tp; cases "tl tp", auto)
    from this obtain aa ab ba bb tp' where g1: 
      "tp = (aa, ab) # (ba, bb) # tp'" by blast
    hence g2: 
      "modify_tprog tp' ! (4 * (st - Suc 0)) = 
      action_map (fst ((tp'::instr list) ! (2 * (st - Suc 0))))"
      using h g by (auto intro:ind)
    thus "?thesis"
      using g1 g
      by(cases st, auto simp add: Four_Suc)
  qed
qed

lemma modify_tprog_fetch_odd: 
  "\<lbrakk>st \<le> length tp div 2; st > 0\<rbrakk> \<Longrightarrow> 
       modify_tprog tp ! (Suc (Suc (4 * (st - Suc 0)))) = 
       action_map (fst (tp ! (Suc (2 * (st - Suc 0)))))"
proof(induct st arbitrary: tp, simp)
  fix tp st
  assume ind: 
    "\<And>tp. \<lbrakk>st \<le> length tp div 2; 0 < st\<rbrakk> \<Longrightarrow>  
       modify_tprog tp ! Suc (Suc (4 * (st - Suc 0))) = 
          action_map (fst (tp ! Suc (2 * (st - Suc 0))))"
    and h: "Suc st \<le> length (tp::instr list) div 2" "0 < Suc st"
  thus "modify_tprog tp ! Suc (Suc (4 * (Suc st - Suc 0))) 
     = action_map (fst (tp ! Suc (2 * (Suc st - Suc 0))))"
  proof(cases "st = 0")
    case True thus "?thesis"
      using h
      apply(cases tp, force)
      by(cases "tl tp", auto)
  next
    case False
    assume g: "st \<noteq> 0"
    hence "\<exists> aa ab ba bb tp'. tp = (aa, ab) # (ba, bb) # tp'"
      using h
      apply(cases tp, simp, cases "tl tp", simp, simp)
      done
    from this obtain aa ab ba bb tp' where g1: 
      "tp = (aa, ab) # (ba, bb) # tp'" by blast
    hence g2: "modify_tprog tp' ! Suc (Suc (4 * (st  - Suc 0))) = 
          action_map (fst (tp' ! Suc (2 * (st - Suc 0))))"
      apply(rule_tac ind)
      using h g by auto
    thus "?thesis"
      using g1 g
      apply(cases st, simp, simp add: Four_Suc)
      done
  qed
qed    

lemma modify_tprog_fetch_action:
  "\<lbrakk>st \<le> length tp div 2; st > 0; b = 1 \<or> b = 0\<rbrakk> \<Longrightarrow> 
      modify_tprog tp ! (4 * (st - Suc 0) + 2* b) =
      action_map (fst (tp ! ((2 * (st - Suc 0)) + b)))"
  apply(erule_tac disjE, auto elim: modify_tprog_fetch_odd
      modify_tprog_fetch_even)
  done 

lemma length_modify: "length (modify_tprog tp) = 2 * length tp"
  apply(induct tp, auto)
  done

declare fetch.simps[simp del]

lemma fetch_action_eq: 
  "\<lbrakk>block_map b = scan r; fetch tp st b = (nact, ns);
   st \<le> length tp div 2\<rbrakk> \<Longrightarrow> actn (code tp) st r = action_map nact"
proof(simp add: actn.simps, auto)
  let ?i = "4 * (st - Suc 0) + 2 * (r mod 2)"
  assume h: "block_map b = r mod 2" "fetch tp st b = (nact, ns)" 
    "st \<le> length tp div 2" "0 < st"
  have "?i < length (modify_tprog tp)"
  proof -
    have "length (modify_tprog tp) = 2 * length tp"
      by(simp add: length_modify)
    thus "?thesis"
      using h
      by(auto)
  qed
  hence 
    "Entry (godel_code (modify_tprog tp))?i = 
                                   (modify_tprog tp) ! ?i"
    by(erule_tac godel_decode)
  moreover have 
    "modify_tprog tp ! ?i = 
            action_map (fst (tp ! (2 * (st - Suc 0) + r mod 2)))"
    apply(rule_tac  modify_tprog_fetch_action)
    using h
    by(auto)    
  moreover have "(fst (tp ! (2 * (st - Suc 0) + r mod 2))) = nact"
    using h
    apply(cases st, simp_all add: fetch.simps nth_of.simps)
    apply(cases b, auto simp: block_map.simps nth_of.simps fetch.simps 
        split: if_splits)
    apply(cases "r mod 2", simp, simp)
    done
  ultimately show 
    "Entry (godel_code (modify_tprog tp))
                      (4 * (st - Suc 0) + 2 * (r mod 2))
           = action_map nact" 
    by simp
qed

lemma fetch_zero_zero[simp]: "fetch tp 0 b = (nact, ns) \<Longrightarrow> ns = 0"
  by(simp add: fetch.simps)

lemma modify_tprog_fetch_state:
  "\<lbrakk>st \<le> length tp div 2; st > 0; b = 1 \<or> b = 0\<rbrakk> \<Longrightarrow> 
     modify_tprog tp ! Suc (4 * (st - Suc 0) + 2 * b) =
  (snd (tp ! (2 * (st - Suc 0) + b)))"
proof(induct st arbitrary: tp, simp)
  fix st tp
  assume ind: 
    "\<And>tp. \<lbrakk>st \<le> length tp div 2; 0 < st; b = 1 \<or> b = 0\<rbrakk> \<Longrightarrow> 
    modify_tprog tp ! Suc (4 * (st - Suc 0) + 2 * b) =
                             snd (tp ! (2 * (st - Suc 0) + b))"
    and h:
    "Suc st \<le> length (tp::instr list) div 2" 
    "0 < Suc st" 
    "b = 1 \<or> b = 0"
  show "modify_tprog tp ! Suc (4 * (Suc st - Suc 0) + 2 * b) =
                             snd (tp ! (2 * (Suc st - Suc 0) + b))"
  proof(cases "st = 0")
    case True
    thus "?thesis"
      using h
      apply(cases tp, force)
      apply(cases "tl tp", auto)
      done
  next
    case False
    assume g: "st \<noteq> 0"
    hence "\<exists> aa ab ba bb tp'. tp = (aa, ab) # (ba, bb) # tp'"
      using h
      by(cases tp, force, cases "tl tp", auto)
    from this obtain aa ab ba bb tp' where g1:
      "tp = (aa, ab) # (ba, bb) # tp'" by blast
    hence g2: 
      "modify_tprog tp' ! Suc (4 * (st - Suc 0) + 2 * b) =
                              snd (tp' ! (2 * (st - Suc 0) + b))"
      apply(intro ind)
      using h g by auto
    thus "?thesis"
      using g1 g
      by(cases st;force)
  qed
qed

lemma fetch_state_eq:
  "\<lbrakk>block_map b = scan r; 
  fetch tp st b = (nact, ns);
  st \<le> length tp div 2\<rbrakk> \<Longrightarrow> newstat (code tp) st r = ns"
proof(simp add: newstat.simps, auto)
  let ?i = "Suc (4 * (st - Suc 0) + 2 * (r mod 2))"
  assume h: "block_map b = r mod 2" "fetch tp st b =
             (nact, ns)" "st \<le> length tp div 2" "0 < st"
  have "?i < length (modify_tprog tp)"
  proof -
    have "length (modify_tprog tp) = 2 * length tp"
      by(simp add: length_modify)
    thus "?thesis"
      using h
      by(auto)
  qed
  hence "Entry (godel_code (modify_tprog tp)) (?i) = 
                                  (modify_tprog tp) ! ?i"
    by(erule_tac godel_decode)
  moreover have 
    "modify_tprog tp ! ?i =  
               (snd (tp ! (2 * (st - Suc 0) + r mod 2)))"
    apply(rule_tac  modify_tprog_fetch_state)
    using h
    by(auto)
  moreover have "(snd (tp ! (2 * (st - Suc 0) + r mod 2))) = ns"
    using h
    apply(cases st, simp)
    apply(cases b, auto simp: fetch.simps split: if_splits)
    apply(cases "(2 * (st - r mod 2) + r mod 2) = 
                       (2 * (st - 1) + r mod 2)";auto)
    by (metis diff_Suc_Suc diff_zero prod.sel(2))
  ultimately show "Entry (godel_code (modify_tprog tp)) (?i)
           = ns" 
    by simp
qed


lemma tpl_eqI[intro!]: 
  "\<lbrakk>a = a'; b = b'; c = c'\<rbrakk> \<Longrightarrow> trpl a b c = trpl a' b' c'"
  by simp

lemma bl2nat_double: "bl2nat xs (Suc n) = 2 * bl2nat xs n"
proof(induct xs arbitrary: n)
  case Nil thus "?case"
    by(simp add: bl2nat.simps)
next
  case (Cons x xs) thus "?case"
  proof -
    assume ind: "\<And>n. bl2nat xs (Suc n) = 2 * bl2nat xs n "
    show "bl2nat (x # xs) (Suc n) = 2 * bl2nat (x # xs) n"
    proof(cases x)
      case Bk thus "?thesis"
        apply(simp add: bl2nat.simps)
        using ind[of "Suc n"] by simp
    next
      case Oc thus "?thesis"
        apply(simp add: bl2nat.simps)
        using ind[of "Suc n"] by simp
    qed
  qed
qed


lemma bl2wc_simps[simp]:
  "bl2wc (Oc # tl c) = Suc (bl2wc c) - bl2wc c mod 2 "
  "bl2wc (Bk # c) = 2*bl2wc (c)"
  "2 * bl2wc (tl c) = bl2wc c - bl2wc c mod 2 "
  "bl2wc [Oc] = Suc 0"
  "c \<noteq> [] \<Longrightarrow> bl2wc (tl c) = bl2wc c div 2"
  "c \<noteq> [] \<Longrightarrow> bl2wc [hd c] = bl2wc c mod 2"
  "c \<noteq> [] \<Longrightarrow> bl2wc (hd c # d) = 2 * bl2wc d + bl2wc c mod 2"
  "2 * (bl2wc c div 2) = bl2wc c - bl2wc c mod 2"
  "bl2wc (Oc # list) mod 2 = Suc 0" 
  by(cases c;cases "hd c";force simp: bl2wc.simps bl2nat.simps bl2nat_double)+

declare code.simps[simp del]
declare nth_of.simps[simp del]

text \<open>
  The lemma relates the one step execution of TMs with the interpreter function \<open>rec_newconf\<close>.
\<close>
lemma rec_t_eq_step: 
  "(\<lambda> (s, l, r). s \<le> length tp div 2) c \<Longrightarrow>
  trpl_code (step0 c tp) = 
  rec_exec rec_newconf [code tp, trpl_code c]"
proof(cases c)
  case (fields s l r) assume "case c of (s, l, r) \<Rightarrow> s \<le> length tp div 2"
  with fields have "s \<le> length tp div 2" by auto
  thus ?thesis unfolding fields 
  proof(cases "fetch tp s (read r)",
      simp add: newconf.simps trpl_code.simps step.simps)
    fix a b ca aa ba
    assume h: "(a::nat) \<le> length tp div 2" 
      "fetch tp a (read ca) = (aa, ba)"
    moreover hence "actn (code tp) a (bl2wc ca) = action_map aa"
      apply(rule_tac b = "read ca" 
          in fetch_action_eq, auto)
      apply(cases "hd ca";cases ca;force)
      done
    moreover from h have "(newstat (code tp) a (bl2wc ca)) = ba"
      apply(rule_tac b = "read ca" 
          in fetch_state_eq, auto split: list.splits)
      apply(cases "hd ca";cases ca;force)
      done
    ultimately show 
      "trpl_code (ba, update aa (b, ca)) =
          trpl (newleft (bl2wc b) (bl2wc ca) (actn (code tp) a (bl2wc ca))) 
    (newstat (code tp) a (bl2wc ca)) (newrght (bl2wc b) (bl2wc ca) (actn (code tp) a (bl2wc ca)))"
      apply(cases aa)
          apply(auto simp: trpl_code.simps 
          newleft.simps newrght.simps split: action.splits)
      done
  qed
qed

lemma bl2nat_simps[simp]: "bl2nat (Oc # Oc\<up>x) 0 = (2 * 2 ^ x - Suc 0)"
  "bl2nat (Bk\<up>x) n = 0"
  by(induct x;force simp: bl2nat.simps bl2nat_double exp_ind)+

lemma bl2nat_exp_zero[simp]: "bl2nat (Oc\<up>y) 0 = 2^y - Suc 0"
proof(induct y)
  case (Suc y)
  then show ?case by(cases "(2::nat)^y", auto)
qed (auto simp: bl2nat.simps bl2nat_double)

lemma bl2nat_cons_bk: "bl2nat (ks @ [Bk]) 0 = bl2nat ks 0"
proof(induct ks)
  case (Cons a ks)
  then show ?case by (cases a, auto simp: bl2nat.simps bl2nat_double)
qed (auto simp: bl2nat.simps)

lemma bl2nat_cons_oc:
  "bl2nat (ks @ [Oc]) 0 =  bl2nat ks 0 + 2 ^ length ks"
proof(induct ks)
  case (Cons a ks)
  then show ?case 
    by(cases a, auto simp: bl2nat.simps bl2nat_double)
qed (auto simp: bl2nat.simps)

lemma bl2nat_append: 
  "bl2nat (xs @ ys) 0 = bl2nat xs 0 + bl2nat ys (length xs) "
proof(induct "length xs" arbitrary: xs ys, simp add: bl2nat.simps)
  fix x xs ys
  assume ind: 
    "\<And>xs ys. x = length xs \<Longrightarrow> 
             bl2nat (xs @ ys) 0 = bl2nat xs 0 + bl2nat ys (length xs)"
    and h: "Suc x = length (xs::cell list)"
  have "\<exists> ks k. xs = ks @ [k]" 
    apply(rule_tac x = "butlast xs" in exI,
        rule_tac x = "last xs" in exI)
    using h
    apply(cases xs, auto)
    done
  from this obtain ks k where "xs = ks @ [k]" by blast
  moreover hence 
    "bl2nat (ks @ (k # ys)) 0 = bl2nat ks 0 +
                               bl2nat (k # ys) (length ks)"
    apply(rule_tac ind) using h by simp
  ultimately show "bl2nat (xs @ ys) 0 = 
                  bl2nat xs 0 + bl2nat ys (length xs)"
    apply(cases k, simp_all add: bl2nat.simps)
     apply(simp_all only: bl2nat_cons_bk bl2nat_cons_oc)
    done
qed

lemma trpl_code_simp[simp]:
  "trpl_code (steps0 (Suc 0, Bk\<up>l, <lm>) tp 0) = 
    rec_exec rec_conf [code tp, bl2wc (<lm>), 0]"
  apply(simp add: steps.simps rec_exec.simps conf_lemma  conf.simps 
      inpt.simps trpl_code.simps bl2wc.simps)
  done

text \<open>
  The following lemma relates the multi-step interpreter function \<open>rec_conf\<close>
  with the multi-step execution of TMs.
\<close>
lemma state_in_range_step
  : "\<lbrakk>a \<le> length A div 2; step0 (a, b, c) A = (st, l, r); tm_wf (A,0)\<rbrakk>
  \<Longrightarrow> st \<le> length A div 2"
  apply(simp add: step.simps fetch.simps tm_wf.simps 
      split: if_splits list.splits)
   apply(case_tac [!] a, auto simp: list_all_length 
      fetch.simps nth_of.simps)
   apply(erule_tac x = "A ! (2*nat) " in ballE, auto)
  apply(cases "hd c", auto simp: fetch.simps nth_of.simps)
   apply(erule_tac x = "A !(2 * nat)" in ballE, auto)
  apply(erule_tac x = "A !Suc (2 * nat)" in ballE, auto)
  done

lemma state_in_range: "\<lbrakk>steps0 (Suc 0, tp) A stp = (st, l, r); tm_wf (A, 0)\<rbrakk>
  \<Longrightarrow> st \<le> length A div 2"
proof(induct stp arbitrary: st l r)
  case (Suc stp st l r)
  from Suc.prems show ?case
  proof(simp add: step_red, cases "(steps0 (Suc 0, tp) A stp)", simp)
    fix a b c 
    assume h3: "step0 (a, b, c) A = (st, l, r)"
      and h4: "steps0 (Suc 0, tp) A stp = (a, b, c)"
    have "a \<le> length A div 2" using Suc.prems h4 by (auto intro: Suc.hyps)
    thus "?thesis" using h3 Suc.prems by (auto elim: state_in_range_step)
  qed
qed(auto simp: tm_wf.simps steps.simps)

lemma rec_t_eq_steps:
  "tm_wf (tp,0) \<Longrightarrow>
  trpl_code (steps0 (Suc 0, Bk\<up>l, <lm>) tp stp) = 
  rec_exec rec_conf [code tp, bl2wc (<lm>), stp]"
proof(induct stp)
  case 0 thus "?case" by(simp)
next
  case (Suc n) thus "?case"
  proof -
    assume ind: 
      "tm_wf (tp,0) \<Longrightarrow> trpl_code (steps0 (Suc 0, Bk\<up> l, <lm>) tp n) 
      = rec_exec rec_conf [code tp, bl2wc (<lm>), n]"
      and h: "tm_wf (tp, 0)"
    show 
      "trpl_code (steps0 (Suc 0, Bk\<up> l, <lm>) tp (Suc n)) =
      rec_exec rec_conf [code tp, bl2wc (<lm>), Suc n]"
    proof(cases "steps0 (Suc 0, Bk\<up> l, <lm>) tp  n", 
        simp only: step_red conf_lemma conf.simps)
      fix a b c
      assume g: "steps0 (Suc 0, Bk\<up> l, <lm>) tp n = (a, b, c) "
      hence "conf (code tp) (bl2wc (<lm>)) n= trpl_code (a, b, c)"
        using ind h
        apply(simp add: conf_lemma)
        done
      moreover hence 
        "trpl_code (step0 (a, b, c) tp) = 
        rec_exec rec_newconf [code tp, trpl_code (a, b, c)]"
        apply(rule_tac rec_t_eq_step)
        using h g
        apply(simp add: state_in_range)
        done
      ultimately show 
        "trpl_code (step0 (a, b, c) tp) =
            newconf (code tp) (conf (code tp) (bl2wc (<lm>)) n)"
        by(simp)
    qed
  qed
qed

lemma bl2wc_Bk_0[simp]: "bl2wc (Bk\<up> m) = 0"
  apply(induct m)
   apply(simp, simp)
  done

lemma bl2wc_Oc_then_Bk[simp]: "bl2wc (Oc\<up> rs@Bk\<up> n) = bl2wc (Oc\<up> rs)"
  apply(induct rs, simp, 
      simp add: bl2wc.simps bl2nat.simps bl2nat_double)
  done

lemma lg_power: "x > Suc 0 \<Longrightarrow> lg (x ^ rs) x = rs"
proof(simp add: lg.simps, auto)
  fix xa
  assume h: "Suc 0 < x"
  show "Max {ya. ya \<le> x ^ rs \<and> lgR [x ^ rs, x, ya]} = rs"
    apply(rule_tac Max_eqI, simp_all add: lgR.simps)
     apply(simp add: h)
    using x_less_exp[of x rs] h
    apply(simp)
    done
next
  assume "\<not> Suc 0 < x ^ rs" "Suc 0 < x" 
  thus "rs = 0"
    apply(cases "x ^ rs", simp, simp)
    done
next
  assume "Suc 0 < x" "\<forall>xa. \<not> lgR [x ^ rs, x, xa]"
  thus "rs = 0"
    apply(simp only:lgR.simps)
    apply(erule_tac x = rs in allE, simp)
    done
qed    

text \<open>
  The following lemma relates execution of TMs with 
  the multi-step interpreter function \<open>rec_nonstop\<close>. Note,
  \<open>rec_nonstop\<close> is constructed using \<open>rec_conf\<close>.
\<close>

declare tm_wf.simps[simp del]

lemma nonstop_t_eq: 
  "\<lbrakk>steps0 (Suc 0, Bk\<up>l, <lm>) tp stp = (0, Bk\<up> m, Oc\<up> rs @ Bk\<up> n); 
   tm_wf (tp, 0); 
  rs > 0\<rbrakk> 
  \<Longrightarrow> rec_exec rec_nonstop [code tp, bl2wc (<lm>), stp] = 0"
proof(simp add: nonstop_lemma nonstop.simps )
  assume h: "steps0 (Suc 0, Bk\<up>l, <lm>) tp stp = (0, Bk\<up> m, Oc\<up> rs @ Bk\<up> n)"
    and tc_t: "tm_wf (tp, 0)" "rs > 0"
  have g: "rec_exec rec_conf [code tp,  bl2wc (<lm>), stp] =
                                        trpl_code (0, Bk\<up> m, Oc\<up> rs@Bk\<up> n)"
    using rec_t_eq_steps[of tp l lm stp] tc_t h
    by(simp)
  thus "\<not> NSTD (conf (code tp) (bl2wc (<lm>)) stp)" 
  proof(auto simp: NSTD.simps)
    show "stat (conf (code tp) (bl2wc (<lm>)) stp) = 0"
      using g
      by(auto simp: conf_lemma trpl_code.simps)
  next
    show "left (conf (code tp) (bl2wc (<lm>)) stp) = 0"
      using g
      by(simp add: conf_lemma trpl_code.simps)
  next
    show "rght (conf (code tp) (bl2wc (<lm>)) stp) = 
           2 ^ lg (Suc (rght (conf (code tp) (bl2wc (<lm>)) stp))) 2 - Suc 0"
      using g h
    proof(simp add: conf_lemma trpl_code.simps)
      have "2 ^ lg (Suc (bl2wc (Oc\<up> rs))) 2 = Suc (bl2wc (Oc\<up> rs))"
        apply(simp add: bl2wc.simps lg_power)
        done
      thus "bl2wc (Oc\<up> rs) = 2 ^ lg (Suc (bl2wc (Oc\<up> rs))) 2 - Suc 0"
        apply(simp)
        done
    qed
  next
    show "0 < rght (conf (code tp) (bl2wc (<lm>)) stp)"
      using g h tc_t
      apply(simp add: conf_lemma trpl_code.simps bl2wc.simps
          bl2nat.simps)
      apply(cases rs, simp, simp add: bl2nat.simps)
      done
  qed
qed

lemma actn_0_is_4[simp]: "actn m 0 r = 4"
  by(simp add: actn.simps)

lemma newstat_0_0[simp]: "newstat m 0 r = 0"
  by(simp add: newstat.simps)

declare step_red[simp del]

lemma halt_least_step: 
  "\<lbrakk>steps0 (Suc 0, Bk\<up>l, <lm>) tp stp = 
       (0, Bk\<up> m, Oc\<up>rs @ Bk\<up>n); 
    tm_wf (tp, 0); 
    0<rs\<rbrakk> \<Longrightarrow>
    \<exists> stp. (nonstop (code tp) (bl2wc (<lm>)) stp = 0 \<and>
       (\<forall> stp'. nonstop (code tp) (bl2wc (<lm>)) stp' = 0 \<longrightarrow> stp \<le> stp'))"
proof(induct stp)
  case 0
  then show ?case by (simp add: steps.simps(1))
next
  case (Suc stp)
  hence ind: 
    "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp = (0, Bk\<up> m, Oc\<up> rs @ Bk\<up> n) \<Longrightarrow> 
    \<exists>stp. nonstop (code tp) (bl2wc (<lm>)) stp = 0 \<and> 
          (\<forall>stp'. nonstop (code tp) (bl2wc (<lm>)) stp' = 0 \<longrightarrow> stp \<le> stp')"
    and h: 
    "steps0 (Suc 0, Bk\<up> l, <lm>) tp (Suc stp) = (0, Bk\<up> m, Oc\<up> rs @ Bk\<up> n)"
    "tm_wf (tp, 0::nat)" 
    "0 < rs" by simp+
  {
    fix a b c nat
    assume "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp = (a, b, c)"
      "a = Suc nat"
    hence "\<exists>stp. nonstop (code tp) (bl2wc (<lm>)) stp = 0 \<and> 
      (\<forall>stp'. nonstop (code tp) (bl2wc (<lm>)) stp' = 0 \<longrightarrow> stp \<le> stp')"
      using h
      apply(rule_tac x = "Suc stp" in exI, auto)
       apply(drule_tac  nonstop_t_eq, simp_all add: nonstop_lemma)
    proof -
      fix stp'
      assume g:"steps0 (Suc 0, Bk\<up> l, <lm>) tp stp = (Suc nat, b, c)" 
        "nonstop (code tp) (bl2wc (<lm>)) stp' = 0"
      thus  "Suc stp \<le> stp'"
      proof(cases "Suc stp \<le> stp'", simp, simp)
        assume "\<not> Suc stp \<le> stp'"
        hence "stp' \<le> stp" by simp
        hence "\<not> is_final (steps0 (Suc 0, Bk\<up> l, <lm>) tp stp')"
          using g
          apply(cases "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp'",auto, simp)
          apply(subgoal_tac "\<exists> n. stp = stp' + n", auto)
           apply(cases "fst (steps0 (Suc 0, Bk \<up> l, <lm>) tp stp')", simp_all add: steps.simps)
          apply(rule_tac x = "stp - stp'"  in exI, simp)
          done         
        hence "nonstop (code tp) (bl2wc (<lm>)) stp' = 1"
        proof(cases "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp'",
            simp add: nonstop.simps)
          fix a b c
          assume k: 
            "0 < a" "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp' = (a, b, c)"
          thus " NSTD (conf (code tp) (bl2wc (<lm>)) stp')"
            using rec_t_eq_steps[of tp l lm stp'] h
          proof(simp add: conf_lemma) 
            assume "trpl_code (a, b, c) = conf (code tp) (bl2wc (<lm>)) stp'"
            moreover have "NSTD (trpl_code (a, b, c))"
              using k
              apply(auto simp: trpl_code.simps NSTD.simps)
              done
            ultimately show "NSTD (conf (code tp) (bl2wc (<lm>)) stp')" by simp
          qed
        qed
        thus "False" using g by simp
      qed qed
    }
    note [intro] = this
    from h show 
      "\<exists>stp. nonstop (code tp) (bl2wc (<lm>)) stp = 0 
    \<and> (\<forall>stp'. nonstop (code tp) (bl2wc (<lm>)) stp' = 0 \<longrightarrow> stp \<le> stp')"
      by(simp add: step_red, 
          cases "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp", simp, 
          cases "fst (steps0 (Suc 0, Bk\<up> l, <lm>) tp stp)",
          auto simp add: nonstop_t_eq intro:ind dest:nonstop_t_eq)
  qed    

lemma conf_trpl_ex: "\<exists> p q r. conf m (bl2wc (<lm>)) stp = trpl p q r"
  apply(induct stp, auto simp: conf.simps inpt.simps trpl.simps 
      newconf.simps)
  apply(rule_tac x = 0 in exI, rule_tac x = 1 in exI, 
      rule_tac x = "bl2wc (<lm>)" in exI)
  apply(simp)
  done

lemma nonstop_rgt_ex: 
  "nonstop m (bl2wc (<lm>)) stpa = 0 \<Longrightarrow> \<exists> r. conf m (bl2wc (<lm>)) stpa = trpl 0 0 r"
  apply(auto simp: nonstop.simps NSTD.simps split: if_splits)
  using conf_trpl_ex[of m lm stpa]
  apply(auto)
  done

lemma max_divisors: "x > Suc 0 \<Longrightarrow> Max {u. x ^ u dvd x ^ r} = r"
proof(rule_tac Max_eqI)
  assume "x > Suc 0"
  thus "finite {u. x ^ u dvd x ^ r}"
    apply(rule_tac finite_power_dvd, auto)
    done
next
  fix y 
  assume "Suc 0 < x" "y \<in> {u. x ^ u dvd x ^ r}"
  thus "y \<le> r"
    apply(cases "y\<le> r", simp)
    apply(subgoal_tac "\<exists> d. y = r + d")
     apply(auto simp: power_add)
    apply(rule_tac x = "y - r" in exI, simp)
    done
next
  show "r \<in> {u. x ^ u dvd x ^ r}" by simp
qed  

lemma lo_power:
  assumes "x > Suc 0" shows "lo (x ^ r) x = r"
proof -
  have "\<not> Suc 0 < x ^ r \<Longrightarrow> r = 0" using assms
    by (metis Suc_lessD Suc_lessI nat_power_eq_Suc_0_iff zero_less_power)
  moreover have "\<forall>xa. \<not> x ^ xa dvd x ^ r \<Longrightarrow> r = 0"
    using dvd_refl assms by(cases "x^r";blast)
  ultimately show ?thesis using assms
    by(auto simp: lo.simps loR.simps mod_dvd_simp elim:max_divisors)
qed

lemma lo_rgt: "lo (trpl 0 0 r) (Pi 2) = r"
  apply(simp add: trpl.simps lo_power)
  done

lemma conf_keep: 
  "conf m lm stp = trpl 0 0 r  \<Longrightarrow>
  conf m lm (stp + n) = trpl 0 0 r"
  apply(induct n)
   apply(auto simp: conf.simps  newconf.simps newleft.simps 
      newrght.simps rght.simps lo_rgt)
  done

lemma halt_state_keep_steps_add:
  "\<lbrakk>nonstop m (bl2wc (<lm>)) stpa = 0\<rbrakk> \<Longrightarrow> 
  conf m (bl2wc (<lm>)) stpa = conf m (bl2wc (<lm>)) (stpa + n)"
  apply(drule_tac nonstop_rgt_ex, auto simp: conf_keep)
  done

lemma halt_state_keep: 
  "\<lbrakk>nonstop m (bl2wc (<lm>)) stpa = 0; nonstop m (bl2wc (<lm>)) stpb = 0\<rbrakk> \<Longrightarrow>
  conf m (bl2wc (<lm>)) stpa = conf m (bl2wc (<lm>)) stpb"
  apply(cases "stpa > stpb")
  using halt_state_keep_steps_add[of m lm stpb "stpa - stpb"] 
   apply simp
  using halt_state_keep_steps_add[of m lm stpa "stpb - stpa"]
  apply(simp)
  done

text \<open>
  The correntess of \<open>rec_F\<close> which relates the interpreter function \<open>rec_F\<close> with the
  execution of of TMs.
\<close>

lemma terminate_halt: 
  "\<lbrakk>steps0 (Suc 0, Bk\<up>l, <lm>) tp stp = (0, Bk\<up>m, Oc\<up>rs@Bk\<up>n); 
    tm_wf (tp,0); 0<rs\<rbrakk> \<Longrightarrow> terminate rec_halt [code tp, (bl2wc (<lm>))]"
  by(frule_tac halt_least_step;force simp:nonstop_lemma intro:terminate_halt_lemma)

lemma terminate_F: 
  "\<lbrakk>steps0 (Suc 0, Bk\<up>l, <lm>) tp stp = (0, Bk\<up>m, Oc\<up>rs@Bk\<up>n); 
    tm_wf (tp,0); 0<rs\<rbrakk> \<Longrightarrow> terminate rec_F [code tp, (bl2wc (<lm>))]"
  apply(drule_tac terminate_halt, simp_all)
  apply(erule_tac terminate_F_lemma)
  done

lemma F_correct: 
  "\<lbrakk>steps0 (Suc 0, Bk\<up>l, <lm>) tp stp = (0, Bk\<up>m, Oc\<up>rs@Bk\<up>n); 
    tm_wf (tp,0); 0<rs\<rbrakk>
   \<Longrightarrow> rec_exec rec_F [code tp, (bl2wc (<lm>))] = (rs - Suc 0)"
  apply(frule_tac halt_least_step, auto)
  apply(frule_tac  nonstop_t_eq, auto simp: nonstop_lemma)
  using rec_t_eq_steps[of tp l lm stp]
  apply(simp add: conf_lemma)
proof -
  fix stpa
  assume h: 
    "nonstop (code tp) (bl2wc (<lm>)) stpa = 0" 
    "\<forall>stp'. nonstop (code tp) (bl2wc (<lm>)) stp' = 0 \<longrightarrow> stpa \<le> stp'" 
    "nonstop (code tp) (bl2wc (<lm>)) stp = 0" 
    "trpl_code (0, Bk\<up> m, Oc\<up> rs @ Bk\<up> n) = conf (code tp) (bl2wc (<lm>)) stp"
    "steps0 (Suc 0, Bk\<up> l, <lm>) tp stp = (0, Bk\<up> m, Oc\<up> rs @ Bk\<up> n)"
  hence g1: "conf (code tp) (bl2wc (<lm>)) stpa = trpl_code (0, Bk\<up> m, Oc\<up> rs @ Bk\<up>n)"
    using halt_state_keep[of "code tp" lm stpa stp]
    by(simp)
  moreover have g2:
    "rec_exec rec_halt [code tp, (bl2wc (<lm>))] = stpa"
    using h
    by(auto simp: rec_exec.simps rec_halt_def nonstop_lemma intro!: Least_equality)
  show  
    "rec_exec rec_F [code tp, (bl2wc (<lm>))] = (rs - Suc 0)"
  proof -
    have 
      "valu (rght (conf (code tp) (bl2wc (<lm>)) stpa)) = rs - Suc 0" 
      using g1 
      apply(simp add: valu.simps trpl_code.simps 
          bl2wc.simps  bl2nat_append lg_power)
      done
    thus "?thesis" 
      by(simp add: rec_exec.simps F_lemma g2)
  qed
qed

end