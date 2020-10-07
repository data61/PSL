(*  Title:      AF_Stream_Exec.thy
    Date:       Dec 2006
    Author:     David Trachtenherz
*)

section \<open>Processing of message streams\<close>

theory AF_Stream_Exec
imports AF_Stream "List-Infinite.ListInf_Prefix" "List-Infinite.SetIntervalStep"
begin

subsection \<open>Executing components with state transition functions\<close>

subsubsection \<open>Basic definitions\<close>

text \<open>
  Function type for functions converting
  an input value to an input port message for a component\<close>
type_synonym ('a, 'in) Port_Input_Value = "'a \<Rightarrow> 'in message_af"

text \<open>
  Function type for functions extracting
  the output value of a single output port from
  a component value\<close>
type_synonym ('comp, 'out) Port_Output_Value = "'comp \<Rightarrow> 'out message_af"

text \<open>
  Function type for functions extracting
  the local state of a component from
  a component value\<close>
type_synonym ('comp, 'state) Comp_Local_State = "'comp \<Rightarrow> 'state"

text \<open>
  Function type for transition functions
  computing the component's value after processing
  an input for a single time unit\<close>
type_synonym ('comp, 'input) Comp_Trans_Fun = "'input \<Rightarrow> 'comp \<Rightarrow> 'comp"


\<comment> \<open>Execute a component for all inputs in the input stream @{typ "'input list"}\<close>
primrec f_Exec_Comp :: "('comp, 'input) Comp_Trans_Fun \<Rightarrow> 'input list \<Rightarrow> 'comp \<Rightarrow> 'comp"
where
  f_Exec_Nil:  "f_Exec_Comp trans_fun [] c = c"
| f_Exec_Cons: "f_Exec_Comp trans_fun (x#xs) c = f_Exec_Comp trans_fun xs (trans_fun x c)"

\<comment> \<open>Execute the component for at most n steps\<close>
definition f_Exec_Comp_N :: "('comp, 'input) Comp_Trans_Fun \<Rightarrow> nat \<Rightarrow> 'input list \<Rightarrow> 'comp \<Rightarrow> 'comp"
  where "f_Exec_Comp_N trans_fun n xs c \<equiv> f_Exec_Comp trans_fun (xs \<down> n) c"

\<comment> \<open>Produce the component stream for all inputs in the input stream\<close>
primrec f_Exec_Comp_Stream :: "('comp, 'input) Comp_Trans_Fun \<Rightarrow> 'input list \<Rightarrow> 'comp \<Rightarrow> 'comp list"
where
  f_Exec_Stream_Nil:  "f_Exec_Comp_Stream trans_fun [] c = []"
| f_Exec_Stream_Cons: "f_Exec_Comp_Stream trans_fun (x # xs) c =
    (trans_fun x c) # ( f_Exec_Comp_Stream trans_fun xs (trans_fun x c) )"

primrec f_Exec_Comp_Stream_Init ::
  "('comp, 'input) Comp_Trans_Fun \<Rightarrow> 'input list \<Rightarrow> 'comp \<Rightarrow> 'comp list"
where
  f_Exec_Stream_Init_Nil:  "f_Exec_Comp_Stream_Init trans_fun [] c = [c]"
| f_Exec_Stream_Init_Cons: "f_Exec_Comp_Stream_Init trans_fun (x # xs) c =
    c # ( f_Exec_Comp_Stream_Init trans_fun xs (trans_fun x c) )"

definition i_Exec_Comp_Stream ::
    "('comp, 'input) Comp_Trans_Fun \<Rightarrow> 'input ilist \<Rightarrow> 'comp \<Rightarrow> 'comp ilist"
  where "i_Exec_Comp_Stream \<equiv> \<lambda>trans_fun input c n. f_Exec_Comp trans_fun (input \<Down> Suc n) c"

definition i_Exec_Comp_Stream_Init ::
    "('comp, 'input) Comp_Trans_Fun \<Rightarrow> 'input ilist \<Rightarrow> 'comp \<Rightarrow> 'comp ilist"
  where "i_Exec_Comp_Stream_Init \<equiv> \<lambda>trans_fun input c n. f_Exec_Comp trans_fun (input \<Down> n) c"


subsubsection \<open>Basic results\<close>

lemma f_Exec_one: "f_Exec_Comp trans_fun [m] c = trans_fun m c"
by simp

lemma f_Exec_Stream_length[rule_format, simp]:"
  \<forall>c. length (f_Exec_Comp_Stream trans_fun xs c) = length xs"
by (induct xs, simp_all)

lemma f_Exec_Stream_empty_conv:"
  (f_Exec_Comp_Stream trans_fun xs c = []) = (xs = [])"
by (simp add: length_0_conv[symmetric] del: length_0_conv)

lemma f_Exec_Stream_not_empty_conv:"
  (f_Exec_Comp_Stream trans_fun xs c \<noteq> []) = (xs \<noteq> [])"
by (simp add: f_Exec_Stream_empty_conv)

lemma f_Exec_eq_f_Exec_Stream_last[rule_format]:"
  \<forall>c. f_Exec_Comp trans_fun xs c = last (c # (f_Exec_Comp_Stream trans_fun xs c))"
by (induct xs, simp_all)

corollary f_Exec_eq_f_Exec_Stream_last2[rule_format]: "
  xs \<noteq> [] \<Longrightarrow>
  f_Exec_Comp trans_fun xs c = last (f_Exec_Comp_Stream trans_fun xs c)"
by (simp add: f_Exec_eq_f_Exec_Stream_last f_Exec_Stream_empty_conv[symmetric, of xs trans_fun c])

corollary f_Exec_eq_f_Exec_Stream_last_if: "
  f_Exec_Comp trans_fun xs c = (if xs = [] then c else last (f_Exec_Comp_Stream trans_fun xs c))"
by (simp add: f_Exec_eq_f_Exec_Stream_last2)

corollary f_Exec_take_eq_last_f_Exec_Stream_take:"
  \<lbrakk> xs \<noteq> []; 0 < n \<rbrakk> \<Longrightarrow>
  f_Exec_Comp trans_fun (xs \<down> n) c =
  last (f_Exec_Comp_Stream trans_fun (xs \<down> n) c)"
by (simp add: f_Exec_eq_f_Exec_Stream_last2 take_not_empty_conv)

corollary f_Exec_N_eq_last_f_Exec_Stream_take:"
  \<lbrakk> xs \<noteq> []; 0 < n \<rbrakk> \<Longrightarrow>
    f_Exec_Comp_N trans_fun n xs c =
    last (f_Exec_Comp_Stream trans_fun (xs \<down> n) c)"
by (simp add: f_Exec_Comp_N_def f_Exec_take_eq_last_f_Exec_Stream_take)

lemma f_Exec_Stream_nth: "
  \<And>n c. n < length xs \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c ! n = f_Exec_Comp trans_fun (xs \<down> Suc n) c"
apply (induct xs, simp)
apply (simp add: nth_Cons')
done

lemma f_Exec_Stream_nth2: "
  n \<le> length xs \<Longrightarrow>
  (c # f_Exec_Comp_Stream trans_fun xs c) ! n = f_Exec_Comp trans_fun (xs \<down> n) c"
by (simp add: nth_Cons' f_Exec_Stream_nth)

lemma f_Exec_N_all:"
  length xs \<le> n \<Longrightarrow>
    f_Exec_Comp_N trans_fun n xs c = f_Exec_Comp trans_fun xs c"
by (simp add: f_Exec_Comp_N_def)

lemma f_Exec_Stream_append[rule_format]:"\<forall>c.
  f_Exec_Comp_Stream trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream trans_fun xs c) @
    (f_Exec_Comp_Stream trans_fun ys (f_Exec_Comp trans_fun xs c))"
by (induct xs, simp_all)

corollary f_Exec_Stream_append_last_Cons[rule_format]:"
  f_Exec_Comp_Stream trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream trans_fun xs c) @
    (f_Exec_Comp_Stream trans_fun ys (last (c # (f_Exec_Comp_Stream  trans_fun xs c))))"
by (simp add: f_Exec_Stream_append f_Exec_eq_f_Exec_Stream_last)

corollary f_Exec_Stream_append_last[rule_format]:"
  xs \<noteq> [] \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream trans_fun xs c) @
    (f_Exec_Comp_Stream trans_fun ys (last (f_Exec_Comp_Stream  trans_fun xs c)))"
by (simp add: f_Exec_Stream_append_last_Cons f_Exec_Stream_empty_conv)

corollary f_Exec_Stream_append_if:"
  f_Exec_Comp_Stream trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream trans_fun xs c) @
    (f_Exec_Comp_Stream trans_fun ys (
      if xs = [] then c else last (f_Exec_Comp_Stream trans_fun xs c)))"
by (simp add: f_Exec_Stream_append f_Exec_eq_f_Exec_Stream_last_if)
corollary f_Exec_append:"
  f_Exec_Comp trans_fun (xs @ ys) c =
  f_Exec_Comp trans_fun ys (f_Exec_Comp trans_fun xs c)"
by (simp add: f_Exec_eq_f_Exec_Stream_last f_Exec_Stream_append_if f_Exec_Stream_empty_conv)

corollary f_Exec_Stream_Cons_rev: "
  xs \<noteq> [] \<Longrightarrow>
  (trans_fun (hd xs) c) #
  f_Exec_Comp_Stream trans_fun (tl xs) (trans_fun (hd xs) c) =
  f_Exec_Comp_Stream trans_fun xs c"
by (subst f_Exec_Stream_Cons[symmetric], simp)

lemma f_Exec_Stream_snoc: "
  f_Exec_Comp_Stream trans_fun (xs @ [x]) c =
    f_Exec_Comp_Stream trans_fun xs c @
    [trans_fun x (f_Exec_Comp trans_fun xs c)]"
by (simp add: f_Exec_Stream_append)

lemma f_Exec_snoc: "
  f_Exec_Comp trans_fun (xs @ [x]) c =
  trans_fun x (f_Exec_Comp trans_fun xs c)"
by (simp add: f_Exec_append)


lemma f_Exec_N_append[rule_format]:"
  f_Exec_Comp_N trans_fun (a + b) xs c =
  f_Exec_Comp_N trans_fun b (xs \<up> a) (f_Exec_Comp_N trans_fun a xs c)"
apply (simp add: f_Exec_Comp_N_def f_Exec_append[symmetric])
apply (simp add: take_drop add.commute[of b])
apply (rule subst[of "xs \<down> (a + b) \<down> a" "xs \<down> a" ], simp add: min_eqL)
apply (subst append_take_drop_id, simp)
done

corollary f_Exec_N_Suc[rule_format]:"
  f_Exec_Comp_N trans_fun (Suc n) xs c =
  f_Exec_Comp_N trans_fun (Suc 0) (xs \<up> n) (f_Exec_Comp_N trans_fun n xs c)"
by (simp add: f_Exec_N_append[symmetric])

corollary f_Exec_N_Suc2[rule_format]:"
  n < length xs \<Longrightarrow>
  f_Exec_Comp_N trans_fun (Suc n) xs c =
  trans_fun (xs ! n) (f_Exec_Comp_N trans_fun n xs c)"
by (simp add: f_Exec_Comp_N_def take_Suc_conv_app_nth f_Exec_append)

theorem f_Exec_Stream_take:"
  (f_Exec_Comp_Stream trans_fun xs c) \<down> n =
  f_Exec_Comp_Stream trans_fun (xs \<down> n) c"
apply (case_tac "length xs \<le> n", simp)
apply (rule subst[OF append_take_drop_id, of _ n xs])
apply (simp add: f_Exec_Stream_append del: append_take_drop_id)
done

theorem f_Exec_Stream_drop:"
  (f_Exec_Comp_Stream trans_fun xs c) \<up> n =
  f_Exec_Comp_Stream trans_fun (xs \<up> n)
    (f_Exec_Comp trans_fun (xs \<down> n) c)"
apply (case_tac "length xs \<le> n", simp)
apply (rule subst[OF append_take_drop_id, of _ n xs])
apply (simp add: f_Exec_Stream_append del: append_take_drop_id)
done

lemma i_Exec_Stream_nth: "
  i_Exec_Comp_Stream trans_fun input c n = f_Exec_Comp trans_fun (input \<Down> Suc n) c"
by (simp add: i_Exec_Comp_Stream_def)

lemma i_Exec_Stream_nth_Suc: "
  i_Exec_Comp_Stream trans_fun input c (Suc n) =
  trans_fun (input (Suc n)) (i_Exec_Comp_Stream trans_fun input c n)"
by (simp add: i_Exec_Stream_nth i_take_Suc_conv_app_nth f_Exec_append)

lemma i_Exec_Stream_nth_Suc_first: "
  i_Exec_Comp_Stream trans_fun input c (Suc n) =
  (i_Exec_Comp_Stream trans_fun (input \<Up> Suc 0) (trans_fun (input 0) c) n)"
by (simp add: i_Exec_Stream_nth i_take_Suc)

lemma f_Exec_Stream_nth_eq_i_Exec_Stream_nth: "
  n < n' \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun (input \<Down> n') c ! n =
  i_Exec_Comp_Stream trans_fun input c n"
by (simp add: f_Exec_Stream_nth i_Exec_Stream_nth min_eqR)


lemma i_Exec_Stream_append: "
  i_Exec_Comp_Stream trans_fun (xs \<frown> input) c =
  f_Exec_Comp_Stream trans_fun xs c \<frown>
  i_Exec_Comp_Stream trans_fun input (f_Exec_Comp trans_fun xs c)"
by (simp add: ilist_eq_iff i_Exec_Stream_nth f_Exec_Stream_nth f_Exec_append i_append_nth Suc_diff_le)

lemma i_Exec_Stream_append_last_Cons: "
  i_Exec_Comp_Stream trans_fun (xs \<frown> input) c =
  f_Exec_Comp_Stream trans_fun xs c \<frown>
  i_Exec_Comp_Stream trans_fun input (
    last (c # f_Exec_Comp_Stream trans_fun xs c))"
by (simp add: f_Exec_eq_f_Exec_Stream_last i_Exec_Stream_append)

lemma i_Exec_Stream_append_last: "
  xs \<noteq> [] \<Longrightarrow>
  i_Exec_Comp_Stream trans_fun (xs \<frown> input) c =
  f_Exec_Comp_Stream trans_fun xs c \<frown>
  i_Exec_Comp_Stream trans_fun input (
    last (f_Exec_Comp_Stream trans_fun xs c))"
by (simp add: f_Exec_Stream_empty_conv i_Exec_Stream_append_last_Cons)

lemma i_Exec_Stream_append_if: "
  i_Exec_Comp_Stream trans_fun (xs \<frown> input) c =
  f_Exec_Comp_Stream trans_fun xs c \<frown>
  i_Exec_Comp_Stream trans_fun input (
    if xs = [] then c
    else last (f_Exec_Comp_Stream trans_fun xs c))"
by (simp add: i_Exec_Stream_append_last)

corollary i_Exec_Stream_Cons: "
  i_Exec_Comp_Stream trans_fun ([x] \<frown> input) c =
  [trans_fun x c] \<frown> i_Exec_Comp_Stream trans_fun input (trans_fun x c)"
by (simp add: i_Exec_Stream_append)

corollary i_Exec_Stream_Cons_rev: "
  [trans_fun (input 0) c] \<frown>
  i_Exec_Comp_Stream trans_fun (input \<Up> Suc 0) (trans_fun (input 0) c) =
  i_Exec_Comp_Stream trans_fun input c"
apply (insert i_Exec_Stream_append[of trans_fun "[input 0]" "input \<Up> Suc 0" c])
apply (simp add: i_drop_Suc_conv_tl)
done

theorem i_Exec_Stream_take:"
  (i_Exec_Comp_Stream trans_fun input c) \<Down> n =
  f_Exec_Comp_Stream trans_fun (input \<Down> n) c"
by (simp add: list_eq_iff f_Exec_Stream_nth i_Exec_Stream_nth min_eqR)

theorem i_Exec_Stream_drop:"
  (i_Exec_Comp_Stream trans_fun input c) \<Up> n =
  i_Exec_Comp_Stream trans_fun (input \<Up> n) (f_Exec_Comp trans_fun (input \<Down> n) c)"
apply (rule subst[OF i_append_i_take_i_drop_id, of _ n input])
apply (simp add: i_Exec_Stream_append  i_drop_def del: i_append_i_take_i_drop_id)
done

lemma f_Exec_Stream_expand_aggregate_map_take: "
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) k ag \<down> n =
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun ((xs \<down> n) \<odot>\<^sub>f k) c)) k ag"
by (simp add: f_aggregate_take_mult[symmetric] take_map f_Exec_Stream_take f_expand_take_mult)

corollary f_Exec_Stream_expand_aggregate_take: "
  f_aggregate (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c) k ag \<down> n =
  f_aggregate (f_Exec_Comp_Stream trans_fun ((xs \<down> n) \<odot>\<^sub>f k) c) k ag"
by (insert f_Exec_Stream_expand_aggregate_map_take[of n id trans_fun xs k c ag], simp add: map_id)

lemma i_Exec_Stream_expand_aggregate_map_take: "
  0 < k \<Longrightarrow>
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) k ag \<Down> n =
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun ((input \<Down> n) \<odot>\<^sub>f k) c)) k ag"
by (simp add: i_aggregate_i_take_mult[symmetric] i_Exec_Stream_take i_expand_i_take_mult)

corollary i_Exec_Stream_expand_aggregate_take: "
  0 < k \<Longrightarrow>
  i_aggregate (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) k ag \<Down> n =
  f_aggregate (f_Exec_Comp_Stream trans_fun ((input \<Down> n) \<odot>\<^sub>f k) c) k ag"
by (drule i_Exec_Stream_expand_aggregate_map_take[of k n id trans_fun input c ag], simp add: map_id)

lemma f_Exec_Stream_expand_aggregate_map_drop: "
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) k ag \<up> n =
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun ((xs \<up> n) \<odot>\<^sub>f k) (
    f_Exec_Comp trans_fun ((xs \<down> n) \<odot>\<^sub>f k) c))) k ag"
by (simp add: f_aggregate_drop_mult[symmetric] drop_map f_Exec_Stream_drop f_expand_take_mult f_expand_drop_mult)

corollary f_Exec_Stream_expand_aggregate_drop: "
  f_aggregate (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c) k ag \<up> n =
  f_aggregate (f_Exec_Comp_Stream trans_fun ((xs \<up> n) \<odot>\<^sub>f k) (
    f_Exec_Comp trans_fun ((xs \<down> n) \<odot>\<^sub>f k) c)) k ag"
by (insert f_Exec_Stream_expand_aggregate_map_drop[of n id trans_fun xs k c ag], simp add: map_id)

lemma i_Exec_Stream_expand_aggregate_map_drop: "
  0 < k \<Longrightarrow>
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) k ag \<Up> n =
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun ((input \<Up> n) \<odot>\<^sub>i k) (
    f_Exec_Comp trans_fun ((input \<Down> n) \<odot>\<^sub>f k) c))) k ag"
by (simp add: i_aggregate_i_drop_mult[symmetric] i_Exec_Stream_drop i_expand_i_take_mult i_expand_i_drop_mult)

corollary i_Exec_Stream_expand_aggregate_drop: "
  0 < k \<Longrightarrow>
  i_aggregate (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) k ag \<Up> n =
  i_aggregate (i_Exec_Comp_Stream trans_fun ((input \<Up> n) \<odot>\<^sub>i k) (
    f_Exec_Comp trans_fun ((input \<Down> n) \<odot>\<^sub>f k) c)) k ag"
by (drule i_Exec_Stream_expand_aggregate_map_drop[of k n id trans_fun input c ag], simp)


lemma f_Exec_Stream_expand_aggregate_map_nth_eq_i_nth: "
  \<lbrakk> 0 < k; n < n' \<rbrakk> \<Longrightarrow>
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (input \<Down> n' \<odot>\<^sub>f k) c)) k ag ! n =
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) k ag n"
apply (simp add: f_aggregate_nth i_aggregate_nth f_Exec_Stream_take f_Exec_Stream_drop i_Exec_Stream_take i_Exec_Stream_drop drop_map take_map)
apply (simp add: f_expand_take_mod i_expand_i_take_mod f_expand_drop_mod i_expand_i_drop_mod i_drop_i_take_1 drop_take_1 min_eqR)
done

corollary f_Exec_Stream_expand_aggregate_map_nth_eq_i_nth': "
  0 < k \<Longrightarrow>
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (input \<Down> Suc n \<odot>\<^sub>f k) c)) k ag ! n =
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) k ag n"
by (simp add: f_Exec_Stream_expand_aggregate_map_nth_eq_i_nth)

corollary f_Exec_Stream_expand_aggregate_nth_eq_i_nth: "
  \<lbrakk> 0 < k; n < n' \<rbrakk> \<Longrightarrow>
  f_aggregate (f_Exec_Comp_Stream trans_fun (input \<Down> n' \<odot>\<^sub>f k) c) k ag ! n =
  i_aggregate (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) k ag n"
by (drule f_Exec_Stream_expand_aggregate_map_nth_eq_i_nth[where f=id], simp_all add: map_id)

corollary f_Exec_Stream_expand_aggregate_nth_eq_i_nth': "
  0 < k \<Longrightarrow>
  f_aggregate (f_Exec_Comp_Stream trans_fun (input \<Down> Suc n \<odot>\<^sub>f k) c) k ag ! n =
  i_aggregate (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) k ag n"
by (simp add: f_Exec_Stream_expand_aggregate_nth_eq_i_nth)


lemma f_Exec_Stream_expand_shrink_last_map_nth_eq_f_Exec_Comp: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c) \<div>\<^bsub>fl\<^esub> k ! n =
  f (f_Exec_Comp trans_fun ((xs \<down> Suc n) \<odot>\<^sub>f k) c)"
apply (simp add: f_shrink_last_map f_shrink_last_length f_shrink_last_nth)
apply (subgoal_tac "n * k + k - Suc 0 < length xs * k")
 prefer 2
 apply (drule Suc_leI[of n])
 apply (drule mult_le_mono1[of _ _ k], simp)
apply (simp add: f_Exec_Stream_nth add.commute[of k] f_expand_take_mult[symmetric])
done

corollary f_Exec_Stream_expand_shrink_last_nth_eq_f_Exec_Comp: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c \<div>\<^bsub>fl\<^esub> k ! n =
  f_Exec_Comp trans_fun ((xs \<down> Suc n) \<odot>\<^sub>f k) c"
by (drule f_Exec_Stream_expand_shrink_last_map_nth_eq_f_Exec_Comp[where f=id], simp_all add: map_id)

lemma f_Exec_Stream_expand_aggregate_map_nth: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) k ag ! n =
  ag (map f (f_Exec_Comp_Stream trans_fun (xs ! n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun (xs \<down> n \<odot>\<^sub>f k) c)))"
apply (simp add: f_aggregate_nth take_map drop_map)
apply (simp add: take_map drop_map f_Exec_Stream_drop f_Exec_Stream_take f_expand_take_mod f_expand_drop_mod drop_take_1)
done

corollary f_Exec_Stream_expand_aggregate_nth: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_aggregate (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c) k ag ! n =
  ag (f_Exec_Comp_Stream trans_fun (xs ! n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun (xs \<down> n \<odot>\<^sub>f k) c))"
by (drule f_Exec_Stream_expand_aggregate_map_nth[where f=id], simp_all add: map_id)

corollary f_Exec_Stream_expand_shrink_map_nth: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) \<div>\<^sub>f k ! n =
  last_message (map f (f_Exec_Comp_Stream trans_fun (xs ! n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun (xs \<down> n \<odot>\<^sub>f k) c)))"
by (simp add: f_shrink_def f_Exec_Stream_expand_aggregate_map_nth)

lemma i_Exec_Stream_expand_aggregate_map_nth: "
  0 < k \<Longrightarrow>
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) k ag n =
  ag (map f (f_Exec_Comp_Stream trans_fun (input n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun ((input \<Down> n) \<odot>\<^sub>f k) c)))"
by (simp add: i_aggregate_nth i_Exec_Stream_drop i_Exec_Stream_take i_expand_i_take_mod i_expand_i_drop_mod i_drop_i_take_1)

corollary i_Exec_Stream_expand_aggregate_nth: "
  0 < k \<Longrightarrow>
  i_aggregate (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) k ag n =
  ag (f_Exec_Comp_Stream trans_fun (input n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun ((input \<Down> n) \<odot>\<^sub>f k) c))"
by (drule i_Exec_Stream_expand_aggregate_map_nth[where f=id], simp add: map_id)

corollary i_Exec_Stream_expand_shrink_map_nth: "
  0 < k \<Longrightarrow>
  ((f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) \<div>\<^sub>i k) n =
  last_message (map f (f_Exec_Comp_Stream trans_fun (input n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun (input \<Down> n \<odot>\<^sub>f k) c)))"
by (simp add: i_shrink_def i_Exec_Stream_expand_aggregate_map_nth)

lemma f_Exec_Stream_expand_snoc: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c \<up> (n * k) \<down> k =
  f_Exec_Comp_Stream trans_fun (xs ! n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>)
    (f_Exec_Comp trans_fun (xs \<down> n \<odot>\<^sub>f k) c)"
by (simp add: f_Exec_Stream_drop f_Exec_Stream_take f_expand_take_mod f_expand_drop_mod drop_take_1)

lemma f_Exec_Stream_expand_map_aggregate_append: "
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun ((xs @ ys) \<odot>\<^sub>f k) c)) k ag =
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) k ag @
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (ys \<odot>\<^sub>f k) (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c))) k ag"
by (simp add: f_Exec_Stream_append f_aggregate_append_mod)

lemma i_Exec_Stream_expand_map_aggregate_append: "
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun ((xs \<frown> input) \<odot>\<^sub>i k) c)) k ag =
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) k ag \<frown>
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c))) k ag"
by (simp add: i_expand_i_append i_Exec_Stream_append i_aggregate_i_append_mod)

lemma f_Exec_Stream_expand_map_aggregate_Cons: "
  0 < k \<Longrightarrow>
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun ((x # xs) \<odot>\<^sub>f k) c)) k ag =
  ag (map f (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)) #
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) (
    f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c))) k ag"
apply (subst append_eq_Cons[of x xs, symmetric])
apply (subst f_Exec_Stream_expand_map_aggregate_append)
apply (simp add: f_aggregate_one)
done

lemma f_Exec_Stream_expand_map_aggregate_snoc: "
  0 < k \<Longrightarrow>
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun ((xs @ [x]) \<odot>\<^sub>f k) c)) k ag =
  f_aggregate (map f (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) k ag @
  [ag (map f (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c)))]"
apply (subst f_Exec_Stream_expand_map_aggregate_append)
apply (simp add: f_aggregate_one)
done

lemma i_Exec_Stream_expand_map_aggregate_Cons: "
  0 < k \<Longrightarrow>
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (([x] \<frown> input) \<odot>\<^sub>i k) c)) k ag =
  [ag (map f (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c))] \<frown>
  i_aggregate (f \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) (
    f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c))) k ag"
apply (subst i_Exec_Stream_expand_map_aggregate_append)
apply (simp add: f_aggregate_one)
done

lemma f_Exec_N_eq_f_Exec_Stream_nth:"
  n \<le> length xs \<Longrightarrow>
  f_Exec_Comp_N trans_fun n xs c = (c # f_Exec_Comp_Stream trans_fun xs c) ! n"
by (simp add: f_Exec_Comp_N_def f_Exec_Stream_nth2)

theorem f_Exec_Stream_causal: "
  xs \<down> n = ys \<down> n \<Longrightarrow>
  (f_Exec_Comp_Stream trans_fun xs c) \<down> n = (f_Exec_Comp_Stream trans_fun ys c) \<down> n"
by (simp add: f_Exec_Stream_take)
theorem i_Exec_Stream_causal: "
  input1 \<Down> n = input2 \<Down> n \<Longrightarrow>
  (i_Exec_Comp_Stream trans_fun input1 c) \<Down> n = (i_Exec_Comp_Stream trans_fun input2 c) \<Down> n"
by (simp add: i_Exec_Stream_take)


text \<open>Results for \<open>f_Exec_Comp_Stream_Init\<close>\<close>

text \<open>
  \<open>f_Exec_Comp_Stream_Init\<close> computes the execution stream of a component
  with the initial value of the component
  at the beginning of the result stream.\<close>

lemma f_Exec_Stream_Init_length[rule_format, simp]:"
  \<forall>c. length (f_Exec_Comp_Stream_Init trans_fun xs c) = Suc (length xs)"
by (induct xs, simp_all)

lemma f_Exec_Stream_Init_not_empty:"
  (f_Exec_Comp_Stream_Init trans_fun xs c \<noteq> [])"
by (simp add: length_0_conv[symmetric] del: length_0_conv)

lemma f_Exec_eq_f_Exec_Stream_Init_last[rule_format]:"
  \<forall>c. f_Exec_Comp trans_fun xs c = last (f_Exec_Comp_Stream_Init trans_fun xs c)"
by (induct xs, simp_all add: f_Exec_Stream_Init_not_empty)

lemma f_Exec_Stream_Init_eq_f_Exec_Stream_Cons[rule_format]: "
  \<forall>c. f_Exec_Comp_Stream_Init trans_fun xs c = c # f_Exec_Comp_Stream trans_fun xs c"
by (induct xs, simp_all)

corollary f_Exec_Stream_Init_eq_f_Exec_Stream_Cons_output: "
  output_fun c = \<NoMsg> \<Longrightarrow>
  map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c) =
  \<NoMsg> # map output_fun (f_Exec_Comp_Stream trans_fun xs c)"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)

corollary f_Exec_Stream_Init_tl_eq_f_Exec_Stream: "
  tl (f_Exec_Comp_Stream_Init trans_fun xs c) = f_Exec_Comp_Stream trans_fun xs c"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)

lemma f_Exec_N_eq_last_f_Exec_Stream_Init_take:"
  f_Exec_Comp_N trans_fun n xs c =
  last (f_Exec_Comp_Stream_Init trans_fun (xs \<down> n) c)"
by (simp add: f_Exec_Comp_N_def f_Exec_eq_f_Exec_Stream_Init_last)

lemma f_Exec_Stream_Init_nth: "
  n \<le> length xs \<Longrightarrow>
  f_Exec_Comp_Stream_Init trans_fun xs c ! n = f_Exec_Comp trans_fun (xs \<down> n) c"
apply (subst f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)
apply (case_tac n, simp)
apply (simp add: f_Exec_Stream_nth)
done

lemma f_Exec_Stream_Init_nth_0: "f_Exec_Comp_Stream_Init trans_fun xs c ! 0 = c"
by (simp add: f_Exec_Stream_Init_nth)

lemma f_Exec_Stream_Init_hd: "hd (f_Exec_Comp_Stream_Init trans_fun xs c) = c"
by (simp add: hd_conv_nth f_Exec_Stream_Init_not_empty f_Exec_Stream_Init_nth_0)

lemma f_Exec_Stream_Init_nth_Suc_eq_f_Exec_Stream_nth: "
  f_Exec_Comp_Stream_Init trans_fun xs c ! (Suc n) = f_Exec_Comp_Stream trans_fun xs c ! n"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)

lemma f_Exec_Stream_Init_append:"
  f_Exec_Comp_Stream_Init trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream_Init trans_fun xs c) @
    tl (f_Exec_Comp_Stream_Init trans_fun ys (f_Exec_Comp trans_fun xs c))"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons f_Exec_Stream_append)

corollary f_Exec_Stream_Init_append_last:"
  f_Exec_Comp_Stream_Init trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream_Init trans_fun xs c) @
    tl (f_Exec_Comp_Stream_Init trans_fun ys (last (f_Exec_Comp_Stream_Init trans_fun xs c)))"
by (simp add: f_Exec_Stream_Init_append f_Exec_eq_f_Exec_Stream_Init_last)

lemma f_Exec_Stream_Init_f_Exec_Stream_append:"
  f_Exec_Comp_Stream_Init trans_fun (xs @ ys) c =
    (f_Exec_Comp_Stream_Init trans_fun xs c) @
    (f_Exec_Comp_Stream trans_fun ys (f_Exec_Comp trans_fun xs c))"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons f_Exec_Stream_append)

lemma f_Exec_Stream_Init_take:"
  (f_Exec_Comp_Stream_Init trans_fun xs c) \<down> Suc n =
  f_Exec_Comp_Stream_Init trans_fun (xs \<down> n) c"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons f_Exec_Stream_take)

lemma f_Exec_Stream_Init_drop:"
  n \<le> length xs \<Longrightarrow>
  (f_Exec_Comp_Stream_Init trans_fun xs c) \<up> n =
  f_Exec_Comp_Stream_Init trans_fun (xs \<up> n)
    (f_Exec_Comp trans_fun (xs \<down> n) c)"
apply (case_tac n, simp)
apply (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons f_Exec_Stream_drop)
apply (simp add: take_Suc_conv_app_nth f_Exec_append Cons_nth_drop_Suc[symmetric])
done

lemma f_Exec_Stream_Init_drop_geq_not_valid:"
  length xs \<le> n \<Longrightarrow>
  (f_Exec_Comp_Stream_Init trans_fun xs c) \<up> Suc n \<noteq>
  f_Exec_Comp_Stream_Init trans_fun arbitrary_input arbitrary_comp"
by (simp add: f_Exec_Stream_Init_not_empty[symmetric])

lemma i_Exec_Stream_Init_nth: "
  i_Exec_Comp_Stream_Init trans_fun input c n = f_Exec_Comp trans_fun (input \<Down> n) c"
by (simp add: i_Exec_Comp_Stream_Init_def)

lemma i_Exec_Stream_Init_nth_0: "
  i_Exec_Comp_Stream_Init trans_fun input c 0 = c"
by (simp add: i_Exec_Stream_Init_nth)

lemma i_Exec_Stream_Init_nth_Suc_eq_i_Exec_Stream_nth: "
  i_Exec_Comp_Stream_Init trans_fun input c (Suc n) = i_Exec_Comp_Stream trans_fun input c n"
by (simp add: i_Exec_Stream_Init_nth i_Exec_Stream_nth)

lemma i_Exec_Stream_Init_eq_i_Exec_Stream_Cons: "
  i_Exec_Comp_Stream_Init trans_fun input c = [c] \<frown> i_Exec_Comp_Stream trans_fun input c"
by (simp add: ilist_eq_iff i_Exec_Stream_Init_nth i_append_nth i_Exec_Stream_nth)

corollary i_Exec_Stream_Init_eq_i_Exec_Stream_Cons_output: "
  output_fun c = \<NoMsg> \<Longrightarrow>
  output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun input c =
  [\<NoMsg>] \<frown> (output_fun \<circ> i_Exec_Comp_Stream trans_fun input c)"
by (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)

lemma i_Exec_Stream_Init_append:"
  i_Exec_Comp_Stream_Init trans_fun (input1 \<frown> input2) c =
    (f_Exec_Comp_Stream_Init trans_fun input1 c) \<frown>
    ((i_Exec_Comp_Stream_Init trans_fun input2 (f_Exec_Comp trans_fun input1 c)) \<Up> Suc 0)"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons i_Exec_Stream_Init_eq_i_Exec_Stream_Cons i_Exec_Stream_append)

corollary i_Exec_Stream_Init_append_last:"
  i_Exec_Comp_Stream_Init trans_fun (input1 \<frown> input2) c =
    (f_Exec_Comp_Stream_Init trans_fun input1 c) \<frown>
    ((i_Exec_Comp_Stream_Init trans_fun input2 (last (f_Exec_Comp_Stream_Init trans_fun input1 c))) \<Up> Suc 0)"
by (simp add: i_Exec_Stream_Init_append f_Exec_eq_f_Exec_Stream_Init_last)

lemma i_Exec_Stream_Init_i_Exec_Stream_append:"
  i_Exec_Comp_Stream_Init trans_fun (input1 \<frown> input2) c =
    (f_Exec_Comp_Stream_Init trans_fun input1 c) \<frown>
    (i_Exec_Comp_Stream trans_fun input2 (f_Exec_Comp trans_fun input1 c))"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons i_Exec_Stream_Init_eq_i_Exec_Stream_Cons i_Exec_Stream_append)

lemma i_Exec_Stream_Init_take:"
  (i_Exec_Comp_Stream_Init trans_fun input c) \<Down> Suc n =
  f_Exec_Comp_Stream_Init trans_fun (input \<Down> n) c"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons i_Exec_Stream_Init_eq_i_Exec_Stream_Cons i_Exec_Stream_take)
lemma i_Exec_Stream_Init_drop:"
  (i_Exec_Comp_Stream_Init trans_fun input c) \<Up> n =
  i_Exec_Comp_Stream_Init trans_fun (input \<Up> n)
    (f_Exec_Comp trans_fun (input \<Down> n) c)"
apply (case_tac n, simp)
apply (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons i_Exec_Stream_drop)
apply (simp add: ilist_eq_iff i_take_Suc_conv_app_nth f_Exec_append i_Exec_Stream_nth i_append_nth i_take_first i_take_drop_eq_map)
apply (simp add: upt_conv_Cons)
done

theorem f_Exec_Stream_Init_strictly_causal: "
  xs \<down> n = ys \<down> n \<Longrightarrow>
  (f_Exec_Comp_Stream_Init trans_fun xs c) \<down> Suc n = (f_Exec_Comp_Stream_Init trans_fun ys c) \<down> Suc n"
by (simp add: f_Exec_Stream_Init_take)

theorem i_Exec_Stream_Init_strictly_causal: "
  input1 \<Down> n = input2 \<Down> n \<Longrightarrow>
  (i_Exec_Comp_Stream_Init trans_fun input1 c) \<Down> Suc n = (i_Exec_Comp_Stream_Init trans_fun input2 c) \<Down> Suc n"
by (simp add: i_Exec_Stream_Init_take)

theorem f_Exec_N_eq_f_Exec_Stream_Init_nth:"
  n \<le> length xs \<Longrightarrow>
  f_Exec_Comp_N trans_fun n xs c = f_Exec_Comp_Stream_Init trans_fun xs c ! n"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons f_Exec_N_eq_f_Exec_Stream_nth)


text \<open>Basic results for previous element functions\<close>

text \<open>
  The functions \<open>list_Previous\<close> and \<open>ilist_Previous\<close>
  return the previous element of the list relatively to the specified position @{term n}
  or the initial element if @{term n} is 0,\<close>

definition list_Previous :: "'value list \<Rightarrow> 'value \<Rightarrow> nat \<Rightarrow> 'value"
  where "list_Previous xs init n \<equiv>
    case n of
      0 \<Rightarrow> init
    | Suc n' \<Rightarrow> xs ! n'"

definition ilist_Previous :: "'value ilist \<Rightarrow> 'value \<Rightarrow> nat \<Rightarrow> 'value"
  where "ilist_Previous f init n \<equiv>
    case n of
      0 \<Rightarrow> init
    | Suc n' \<Rightarrow> f n'"

abbreviation "list_Previous'" :: "'value list \<Rightarrow> 'value \<Rightarrow> nat \<Rightarrow> 'value"
    ( "_\<^bsup>\<leftarrow>' _\<^esup> _" [1000, 10, 100] 100)
  where "xs\<^bsup>\<leftarrow>' init\<^esup> n \<equiv> list_Previous xs init n"

abbreviation "ilist_Previous'" :: "'value ilist \<Rightarrow> 'value \<Rightarrow> nat \<Rightarrow> 'value"
    ( "_\<^bsup>\<leftarrow> _\<^esup> _" [1000, 10, 100] 100)
  where "f\<^bsup>\<leftarrow> init\<^esup> n \<equiv> ilist_Previous f init n"

lemma list_Previous_nth: "xs\<^bsup>\<leftarrow>' init\<^esup> n = (case n of 0 \<Rightarrow> init | Suc n' \<Rightarrow> xs ! n')"
by (simp add: list_Previous_def)

lemma ilist_Previous_nth: "f\<^bsup>\<leftarrow> init\<^esup> n = (case n of 0 \<Rightarrow> init | Suc n' \<Rightarrow> f n')"
by (simp add: ilist_Previous_def)

lemma list_Previous_nth_if: "xs\<^bsup>\<leftarrow>' init\<^esup> n = (if n = 0 then init else xs ! (n - Suc 0))"
by (case_tac n, simp_all add: list_Previous_nth)

lemma ilist_Previous_nth_if: "f\<^bsup>\<leftarrow> init\<^esup> n = (if n = 0 then init else f (n - Suc 0))"
by (case_tac n, simp_all add: ilist_Previous_nth)

lemma list_Previous_Cons: "xs\<^bsup>\<leftarrow>' init\<^esup> n = (init # xs) ! n"
by (case_tac n, simp_all add: list_Previous_nth)

lemma ilist_Previous_Cons: "f\<^bsup>\<leftarrow> init\<^esup> n = ([init] \<frown> f) n"
by (case_tac n, simp_all add: ilist_Previous_nth)

lemma list_Previous_0: "xs\<^bsup>\<leftarrow>' init\<^esup> 0 = init"
by (simp add: list_Previous_def)

lemma ilist_Previous_0: "f\<^bsup>\<leftarrow> init\<^esup> 0 = init"
by (simp add: ilist_Previous_def)

lemma list_Previous_gr0: "0 < n \<Longrightarrow> xs\<^bsup>\<leftarrow>' init\<^esup> n = xs ! (n - Suc 0)"
by (case_tac n, simp_all add: list_Previous_nth)

lemma ilist_Previous_gr0: "0 < n \<Longrightarrow> f\<^bsup>\<leftarrow> init\<^esup> n = f (n - Suc 0)"
by (case_tac n, simp_all add: ilist_Previous_nth)

lemma list_Previous_Suc: "xs\<^bsup>\<leftarrow>' init\<^esup> (Suc n) = xs ! n"
by (simp add: list_Previous_def)

lemma ilist_Previous_Suc: "f\<^bsup>\<leftarrow> init\<^esup> (Suc n) = f n"
by (simp add: ilist_Previous_def)


lemma f_Exec_Stream_Previous_f_Exec_Stream_Init: "
  f_Exec_Comp_Stream_Init trans_fun xs c ! n =
  (f_Exec_Comp_Stream trans_fun xs c)\<^bsup>\<leftarrow>' c\<^esup> n"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons list_Previous_Cons)

lemma i_Exec_Stream_Previous_i_Exec_Stream_Init: "
  i_Exec_Comp_Stream_Init trans_fun input c n =
  (i_Exec_Comp_Stream trans_fun input c)\<^bsup>\<leftarrow> c\<^esup> n"
by (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons ilist_Previous_Cons)


lemma f_Exec_Stream_hd: "
  0 < length xs \<Longrightarrow> hd (f_Exec_Comp_Stream trans_fun xs c) = trans_fun (hd xs) c"
by (case_tac xs, simp+)

lemma f_Exec_Stream_nth_0: "
  0 < length xs \<Longrightarrow> (f_Exec_Comp_Stream trans_fun xs c) ! 0= trans_fun (xs ! 0) c"
by (case_tac xs, simp+)

text \<open>
  The calculation of the n-th result stream element
  from the previous result stream element and the current input stream element.\<close>
lemma f_Exec_Stream_nth_gr0_calc: "
  \<lbrakk> n < length xs; 0 < n \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c ! n =
  trans_fun (xs ! n) (f_Exec_Comp_Stream trans_fun xs c ! (n - 1))"
by (simp add: f_Exec_Stream_nth take_Suc_conv_app_nth f_Exec_append)

lemma f_Exec_Stream_nth_calc_Previous: "
  n < length xs \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c ! n =
  trans_fun (xs ! n) ((f_Exec_Comp_Stream trans_fun xs c)\<^bsup>\<leftarrow>' c\<^esup> n)"
apply (case_tac n)
 apply (simp add: list_Previous_0 f_Exec_Stream_nth_0)
apply (simp add: list_Previous_def f_Exec_Stream_nth_gr0_calc)
done


lemma i_Exec_Stream_nth_0: "
  (i_Exec_Comp_Stream trans_fun input c) 0 = trans_fun (input 0) c"
by (simp add: i_Exec_Stream_nth i_take_first)

lemma i_Exec_Stream_nth_gr0_calc: "
  0 < n \<Longrightarrow>
  (i_Exec_Comp_Stream trans_fun input c) n =
  trans_fun (input n) ((i_Exec_Comp_Stream trans_fun input c) (n - 1))"
by (simp add: i_Exec_Stream_nth i_take_Suc_conv_app_nth f_Exec_append)

text \<open>
  The component state (and thus its output) at time point @{term "n"}
  is computed from the previous state
  (the state at time @{term "n-1"} for @{term "n > 0"}
  or the initial state for @{term "n = 0"})
  and the input at time @{term "n"}.\<close>
lemma i_Exec_Stream_nth_calc_Previous: "
  i_Exec_Comp_Stream trans_fun input c n =
  trans_fun (input n) ((i_Exec_Comp_Stream trans_fun input c)\<^bsup>\<leftarrow> c\<^esup> n)"
by (simp add: i_Exec_Stream_nth ilist_Previous_nth_if i_take_first i_take_Suc_conv_app_nth f_Exec_append)

lemma f_Exec_Stream_Init_nth_Suc_calc: "
  n < length xs \<Longrightarrow>
  f_Exec_Comp_Stream_Init trans_fun xs c ! Suc n =
  trans_fun (xs ! n) (f_Exec_Comp_Stream_Init trans_fun xs c ! n)"
by (simp add: f_Exec_Stream_Init_eq_f_Exec_Stream_Cons f_Exec_Stream_nth nth_Cons' length_greater_0_conv[THEN iffD1, OF gr_implies_gr0] take_Suc_conv_app_nth f_Exec_append)

lemma f_Exec_Stream_Init_nth_Plus1_calc: "
  n < length xs \<Longrightarrow>
  f_Exec_Comp_Stream_Init trans_fun xs c ! (n + 1)=
  trans_fun (xs ! n) (f_Exec_Comp_Stream_Init trans_fun xs c ! n)"
by (simp add: f_Exec_Stream_Init_nth_Suc_calc)

lemma f_Exec_Stream_Init_nth_gr0_calc: "
  \<lbrakk> n \<le> length xs; 0 < n \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Init trans_fun xs c ! n =
  trans_fun (xs ! (n - 1)) (f_Exec_Comp_Stream_Init trans_fun xs c ! (n - 1))"
by (clarsimp simp: gr0_conv_Suc f_Exec_Stream_Init_nth_Suc_calc)

text \<open>
  At the beginning,
  the component state (and thus its output)
  for the execution stream with initial state
  is represented by the initial state,
  contrary to the @{term "i_Exec_Comp_Stream"}
  that does not contain the initial state.\<close>

text \<open>
  The component state (and thus its output) at time point @{term "n + 1"}
  for the execution stream with initial state
  is computed from the previous state
  (the state at time @{term "n"})
  and the previous input
  (input at time @{term "n"}),
  contrary to the @{term "i_Exec_Comp_Stream"},
  where each state at time @{term "n"}
  represents the resulting state after processing the input at time @{term "n"}.\<close>

lemma i_Exec_Stream_Init_nth_Suc_calc: "
  i_Exec_Comp_Stream_Init trans_fun input c (Suc n) =
  trans_fun (input n) (i_Exec_Comp_Stream_Init trans_fun input c n)"
by (simp add: i_Exec_Stream_Init_nth i_take_Suc_conv_app_nth f_Exec_append)

lemma i_Exec_Stream_Init_nth_Plus1_calc: "
  i_Exec_Comp_Stream_Init trans_fun input c (n + 1) =
  trans_fun (input n) (i_Exec_Comp_Stream_Init trans_fun input c n)"
by (simp add: i_Exec_Stream_Init_nth_Suc_calc)

lemma i_Exec_Stream_Init_nth_gr0_calc: "
  0 < n \<Longrightarrow>
  i_Exec_Comp_Stream_Init trans_fun input c n =
  trans_fun (input (n - 1)) (i_Exec_Comp_Stream_Init trans_fun input c (n - 1))"
by (clarsimp simp: gr0_conv_Suc i_Exec_Stream_Init_nth_Suc_calc)


text \<open>Correlation between Pre/Post-Conditions for
  \<open>f_Exec_Comp_Stream\<close> and \<open>f_Exec_Comp_Stream_Init\<close>\<close>

lemma f_Exec_Stream_Pre_Post1: "
  \<lbrakk> n < length xs;
    c_n = (f_Exec_Comp_Stream trans_fun xs c)\<^bsup>\<leftarrow>' c\<^esup> n; x_n = xs ! n \<rbrakk> \<Longrightarrow>
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (f_Exec_Comp_Stream trans_fun xs c ! n)) =
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (trans_fun x_n c_n))"
by (simp add: f_Exec_Stream_nth_calc_Previous)

text \<open>Direct relation between input and result after transition\<close>
lemma f_Exec_Stream_Pre_Post2: "
  \<lbrakk> n < length xs;
    c_n = (f_Exec_Comp_Stream trans_fun xs c)\<^bsup>\<leftarrow>' c\<^esup> n; x_n = xs ! n \<rbrakk> \<Longrightarrow>
  (P c_n \<longrightarrow> Q (xs ! n) (f_Exec_Comp_Stream trans_fun xs c ! n)) =
  (P c_n \<longrightarrow> Q x_n (trans_fun x_n c_n))"
by (simp add: f_Exec_Stream_nth_calc_Previous)

lemma f_Exec_Stream_Pre_Post2_Suc: "
  \<lbrakk> Suc n < length xs;
    c_n = f_Exec_Comp_Stream trans_fun xs c ! n; x_n1 = xs ! Suc n \<rbrakk> \<Longrightarrow>
  (P c_n \<longrightarrow> Q (xs ! Suc n) (f_Exec_Comp_Stream trans_fun xs c ! Suc n)) =
  (P c_n \<longrightarrow> Q x_n1 (trans_fun x_n1 c_n))"
by (simp add: f_Exec_Stream_nth_gr0_calc)

lemma f_Exec_Stream_Init_Pre_Post1: "
  \<lbrakk> n < length xs;
    c_n = f_Exec_Comp_Stream_Init trans_fun xs c ! n; x_n = xs ! n \<rbrakk> \<Longrightarrow>
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (f_Exec_Comp_Stream_Init trans_fun xs c ! Suc n)) =
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (trans_fun x_n c_n))"
by (simp add: f_Exec_Stream_Init_nth_Suc_calc)

text \<open>Direct relation between input and state before transition\<close>
lemma f_Exec_Stream_Init_Pre_Post2: "
  \<lbrakk> n < length xs;
    c_n = f_Exec_Comp_Stream_Init trans_fun xs c ! n; x_n = xs ! n \<rbrakk> \<Longrightarrow>
  (P (xs ! n) (f_Exec_Comp_Stream_Init trans_fun xs c ! n) \<longrightarrow>
     Q (f_Exec_Comp_Stream_Init trans_fun xs c ! Suc n)) =
  (P x_n c_n \<longrightarrow> Q (trans_fun x_n c_n))"
by (simp add: f_Exec_Stream_Init_nth_Suc_calc)


lemma i_Exec_Stream_Pre_Post1: "
  \<lbrakk> c_n = (i_Exec_Comp_Stream trans_fun input c)\<^bsup>\<leftarrow> c\<^esup> n; x_n = input n \<rbrakk> \<Longrightarrow>
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (i_Exec_Comp_Stream trans_fun input c n)) =
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (trans_fun x_n c_n))"
by (simp add: i_Exec_Stream_nth_calc_Previous)

text \<open>Direct relation between input and result after transition\<close>
lemma i_Exec_Stream_Pre_Post2: "
  \<lbrakk> c_n = (i_Exec_Comp_Stream trans_fun input c)\<^bsup>\<leftarrow> c\<^esup> n; x_n = input n \<rbrakk> \<Longrightarrow>
  (P c_n \<longrightarrow> Q (input n) (i_Exec_Comp_Stream trans_fun input c n)) =
  (P c_n \<longrightarrow> Q x_n (trans_fun x_n c_n))"
by (simp add: i_Exec_Stream_nth_calc_Previous)

lemma i_Exec_Stream_Pre_Post2_Suc: "
  \<lbrakk> c_n = i_Exec_Comp_Stream trans_fun input c n; x_n1 = input (Suc n) \<rbrakk> \<Longrightarrow>
  (P c_n \<longrightarrow> Q (input (Suc n)) (i_Exec_Comp_Stream trans_fun input c (Suc n))) =
  (P c_n \<longrightarrow> Q x_n1 (trans_fun x_n1 c_n))"
by (simp add: i_Exec_Stream_nth_gr0_calc)

lemma i_Exec_Stream_Init_Pre_Post1: "
  \<lbrakk> c_n = i_Exec_Comp_Stream_Init trans_fun input c n; x_n = input n \<rbrakk> \<Longrightarrow>
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (i_Exec_Comp_Stream_Init trans_fun input c (Suc n))) =
  (P1 x_n \<and> P2 c_n \<longrightarrow> Q (trans_fun x_n c_n))"
by (simp add: i_Exec_Stream_Init_nth_Suc_calc)

text \<open>Direct relation between input and state before transition\<close>
lemma i_Exec_Stream_Init_Pre_Post2: "
  \<lbrakk> c_n = i_Exec_Comp_Stream_Init trans_fun input c n; x_n = input n \<rbrakk> \<Longrightarrow>
  (P (input n) (i_Exec_Comp_Stream_Init trans_fun input c n) \<longrightarrow>
     Q (i_Exec_Comp_Stream_Init trans_fun input c (Suc n))) =
  (P x_n c_n \<longrightarrow> Q (trans_fun x_n c_n))"
by (simp add: i_Exec_Stream_Init_nth_Suc_calc)


text \<open>Basic results for stream prefices\<close>

lemma f_Exec_Stream_prefix: "
  prefix xs ys \<Longrightarrow>
  prefix (f_Exec_Comp_Stream trans_fun xs c)
         (f_Exec_Comp_Stream trans_fun ys c)"
by (clarsimp simp: prefix_def f_Exec_Stream_append)

lemma i_Exec_Stream_prefix: "
 xs \<sqsubseteq> input \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c \<sqsubseteq>
  i_Exec_Comp_Stream trans_fun input c"
by (simp add: iprefix_eq_iprefix_take i_Exec_Stream_take)

lemma f_Exec_N_prefix: "
  \<lbrakk> n \<le> length xs; prefix xs ys \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_N trans_fun n xs c =
  f_Exec_Comp_N trans_fun n ys c"
by (simp add: f_Exec_Comp_N_def prefix_imp_take_eq)

theorem f_Exec_Stream_prefix_causal[rule_format]:"
  n \<le> length (xs \<sqinter> ys) \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c \<down> n =
  f_Exec_Comp_Stream trans_fun ys c \<down> n"
by (rule f_Exec_Stream_causal, rule inf_prefix_take_correct)

lemma f_Exec_Stream_Init_prefix:"
  prefix xs ys \<Longrightarrow>
  prefix (f_Exec_Comp_Stream_Init trans_fun xs c)
         (f_Exec_Comp_Stream_Init trans_fun ys c)"
by (clarsimp simp: prefix_def f_Exec_Stream_Init_append)

lemma i_Exec_Stream_Init_prefix: "
 xs \<sqsubseteq> input \<Longrightarrow>
  f_Exec_Comp_Stream_Init trans_fun xs c \<sqsubseteq>
  i_Exec_Comp_Stream_Init trans_fun input c"
by (simp add: iprefix_eq_iprefix_take i_Exec_Stream_Init_take)

theorem f_Exec_Stream_Init_prefix_strictly_causal[rule_format]:"
  n \<le> length (xs \<sqinter> ys) \<Longrightarrow>
  f_Exec_Comp_Stream_Init trans_fun xs c \<down> Suc n =
  f_Exec_Comp_Stream_Init trans_fun ys c \<down> Suc n"
by (rule f_Exec_Stream_Init_strictly_causal, rule inf_prefix_take_correct)

text \<open>
  A predicate indicating
  whether a component is deterministically dependent
  on the local state extracted by the the given local state function.\<close>
definition Deterministic_Trans_Fun ::
    "('comp, 'input) Comp_Trans_Fun \<Rightarrow> ('comp, 'state) Comp_Local_State \<Rightarrow> bool"
  where "Deterministic_Trans_Fun trans_fun localState \<equiv>
    \<forall>c1 c2 x. localState c1 = localState c2 \<longrightarrow> trans_fun x c1 = trans_fun x c2"

lemma Deterministic_f_Exec: "
  \<lbrakk> Deterministic_Trans_Fun trans_fun localState; localState c1 = localState c2; xs \<noteq> [] \<rbrakk> \<Longrightarrow>
  f_Exec_Comp trans_fun xs c1 = f_Exec_Comp trans_fun xs c2"
apply (unfold Deterministic_Trans_Fun_def)
apply (case_tac xs, simp)
apply (rename_tac y ys)
apply (drule_tac x=c1 in spec)
apply (drule_tac x=c2 in spec)
apply simp
done

lemma Deterministic_f_Exec_Stream: "
  \<lbrakk> Deterministic_Trans_Fun trans_fun localState; localState c1 = localState c2 \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c1 = f_Exec_Comp_Stream trans_fun xs c2"
apply (clarsimp simp: list_eq_iff f_Exec_Stream_nth)
apply (rule Deterministic_f_Exec)
apply (simp add: length_greater_0_conv[THEN iffD1, OF gr_implies_gr0])+
done

lemma Deterministic_i_Exec_Stream: "
  \<lbrakk> Deterministic_Trans_Fun trans_fun localState; localState c1 = localState c2 \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream trans_fun input c1 = i_Exec_Comp_Stream trans_fun input c2"
apply (clarsimp simp: ilist_eq_iff i_Exec_Stream_nth)
apply (rule Deterministic_f_Exec)
apply simp+
done


subsubsection \<open>Connected streams\<close>

text \<open>
  A predicate indicating for two message streams,
  that the ports, they correspond to, are connected.
  The predicate implies strict causality.\<close>

definition f_Streams_Connected :: "'a fstream_af \<Rightarrow> 'a fstream_af \<Rightarrow> bool"
  where "f_Streams_Connected outS inS \<equiv> inS = \<NoMsg> # outS"

definition i_Streams_Connected :: "'a istream_af \<Rightarrow> 'a istream_af \<Rightarrow> bool"
  where "i_Streams_Connected outS inS \<equiv> inS = [\<NoMsg>] \<frown> outS"

lemmas Streams_Connected_defs =
  f_Streams_Connected_def
  i_Streams_Connected_def

lemma f_Streams_Connected_imp_not_empty: "f_Streams_Connected outS inS \<Longrightarrow> inS \<noteq> []"
by (simp add: f_Streams_Connected_def)

lemma f_Streams_Connected_nth_conv: "
  f_Streams_Connected outS inS =
  (length inS = Suc (length outS) \<and>
  (\<forall>i<length inS. inS ! i = (case i of 0 \<Rightarrow> \<NoMsg> | Suc k \<Rightarrow> outS ! k)))"
by (simp add: f_Streams_Connected_def list_eq_iff nth_Cons)

lemma f_Streams_Connected_nth_conv_if: "
  f_Streams_Connected outS inS =
  (length inS = Suc (length outS) \<and>
  (\<forall>i<length inS. inS ! i = (if i = 0 then \<NoMsg> else outS ! (i - Suc 0))))"
apply (subst f_Streams_Connected_nth_conv)
apply (rule conj_cong, simp)
apply (rule all_imp_eqI, simp)
apply (rename_tac i, case_tac i, simp+)
done

lemma i_Streams_Connected_nth_conv: "
  i_Streams_Connected outS inS =
  (\<forall>i. inS i = (case i of 0 \<Rightarrow> \<NoMsg> | Suc k \<Rightarrow> outS k))"
by (simp add: i_Streams_Connected_def ilist_eq_iff i_append_nth_Cons)

lemma i_Streams_Connected_nth_conv_if: "
  i_Streams_Connected outS inS =
  (\<forall>i. inS i = (if i = 0 then \<NoMsg> else outS (i - Suc 0)))"
apply (subst i_Streams_Connected_nth_conv)
apply (rule all_eqI)
apply (rename_tac i, case_tac i, simp+)
done


lemma f_Exec_Stream_Init_eq_output_channel: "
  \<lbrakk> output_fun c = \<NoMsg>;
    f_Streams_Connected
      (map output_fun (f_Exec_Comp_Stream trans_fun xs c))
      channel \<rbrakk> \<Longrightarrow>
  map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c) = channel"
by (simp add: f_Streams_Connected_def f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)

lemma i_Exec_Stream_Init_eq_output_channel: "
  \<lbrakk> output_fun c = \<NoMsg>;
    i_Streams_Connected
      (output_fun \<circ> (i_Exec_Comp_Stream trans_fun input c))
      channel \<rbrakk> \<Longrightarrow>
  output_fun \<circ> (i_Exec_Comp_Stream_Init trans_fun input c) = channel"
by (simp add: i_Streams_Connected_def i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)


lemma f_Exec_Stream_output_causal: "
  \<lbrakk> xs \<down> n = ys \<down> n;
    output1 = map output_fun (f_Exec_Comp_Stream trans_fun xs c);
    output2 = map output_fun (f_Exec_Comp_Stream trans_fun ys c) \<rbrakk> \<Longrightarrow>
  output1 \<down> n = output2 \<down> n"
by (simp add: take_map f_Exec_Stream_causal[of n xs])

lemma f_Exec_Stream_Init_output_strictly_causal: "
  \<lbrakk> xs \<down> n = ys \<down> n;
    output1 = map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c);
    output2 = map output_fun (f_Exec_Comp_Stream_Init trans_fun ys c) \<rbrakk> \<Longrightarrow>
  output1 \<down> Suc n = output2 \<down> Suc n"
by (simp add: take_map f_Exec_Stream_Init_strictly_causal[of n xs])

lemma i_Exec_Stream_output_causal: "
  \<lbrakk> input1 \<Down> n = input2 \<Down> n;
    output1 = output_fun \<circ> i_Exec_Comp_Stream trans_fun input1 c;
    output2 = output_fun \<circ> i_Exec_Comp_Stream trans_fun input2 c \<rbrakk> \<Longrightarrow>
  output1 \<Down> n = output2 \<Down> n"
by (simp add: i_Exec_Stream_causal[of n input1])

lemma i_Exec_Stream_Init_output_strictly_causal: "
  \<lbrakk> input1 \<Down> n = input2 \<Down> n;
    output1 = output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun input1 c;
    output2 = output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun input2 c \<rbrakk> \<Longrightarrow>
  output1 \<Down> Suc n = output2 \<Down> Suc n"
by (simp add: i_Exec_Stream_Init_strictly_causal[of n input1])

lemma f_Exec_Stream_Connected_strictly_causal: "
  \<lbrakk> xs \<down> n = ys \<down> n;
    f_Streams_Connected
      (map output_fun (f_Exec_Comp_Stream trans_fun xs c))
      channel1;
    f_Streams_Connected
      (map output_fun (f_Exec_Comp_Stream trans_fun ys c))
      channel2 \<rbrakk> \<Longrightarrow>
  channel1 \<down> Suc n = channel2 \<down> Suc n"
by (simp add: f_Streams_Connected_def take_map f_Exec_Stream_take)

lemma i_Exec_Stream_Connected_strictly_causal: "
  \<lbrakk> input1 \<Down> n = input2 \<Down> n;
    i_Streams_Connected
      (portOutput \<circ> (i_Exec_Comp_Stream trans_fun input1 c))
      channel1;
    i_Streams_Connected
      (portOutput \<circ> (i_Exec_Comp_Stream trans_fun input2 c))
      channel2 \<rbrakk> \<Longrightarrow>
  channel1 \<Down> Suc n = channel2 \<Down> Suc n"
by (simp add: i_Streams_Connected_def i_take_Suc_Cons i_Exec_Stream_take)


text \<open>
  A predicate for the semantics with initial state in result stream
  indicating for two message streams that the ports, they correspond to, are connected.\<close>
definition f_Streams_Connected_Init :: "'a fstream_af \<Rightarrow> 'a fstream_af \<Rightarrow> bool"
  where "f_Streams_Connected_Init outS inS \<equiv> inS = outS"

definition i_Streams_Connected_Init :: "'a istream_af \<Rightarrow> 'a istream_af \<Rightarrow> bool"
  where "i_Streams_Connected_Init outS inS \<equiv> inS = outS"

lemmas Streams_Connected_Init_defs =
  f_Streams_Connected_Init_def
  i_Streams_Connected_Init_def

lemma f_Streams_Connected_Init_nth_conv: "
  f_Streams_Connected_Init outS inS =
  (length inS = length outS \<and> (\<forall>i<length inS. inS ! i = outS ! i))"
by (simp add: f_Streams_Connected_Init_def list_eq_iff)

lemma i_Streams_Connected_Init_nth_conv: "
  i_Streams_Connected_Init outS inS =
  (\<forall>i. inS i = outS i)"
by (simp add: i_Streams_Connected_Init_def ilist_eq_iff)


lemma f_Exec_Stream_Init_eq_output_channel2: "
  \<lbrakk> output_fun c = \<NoMsg>;
    f_Streams_Connected_Init
      (map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c))
      channel \<rbrakk> \<Longrightarrow>
  map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c) = channel"
by (simp add: f_Streams_Connected_Init_def f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)
lemma i_Exec_Stream_Init_eq_output_channel2: "
  \<lbrakk> output_fun c = \<NoMsg>;
    i_Streams_Connected_Init
      (output_fun \<circ> (i_Exec_Comp_Stream_Init trans_fun input c))
      channel \<rbrakk> \<Longrightarrow>
  output_fun \<circ> (i_Exec_Comp_Stream_Init trans_fun input c) = channel"
by (simp add: i_Streams_Connected_Init_def i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)

lemma f_Exec_Stream_Connected_Init_strictly_causal: "
  \<lbrakk> xs \<down> n = ys \<down> n;
    f_Streams_Connected_Init
      (map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c))
      channel1;
    f_Streams_Connected_Init
      (map output_fun (f_Exec_Comp_Stream_Init trans_fun ys c))
      channel2 \<rbrakk> \<Longrightarrow>
  channel1 \<down> Suc n = channel2 \<down> Suc n"
by (simp add: f_Streams_Connected_Init_def f_Exec_Stream_Init_eq_f_Exec_Stream_Cons take_map f_Exec_Stream_take)

lemma i_Exec_Stream_Connected_Init_strictly_causal: "
  \<lbrakk> input1 \<Down> n = input2 \<Down> n;
    i_Streams_Connected_Init
      (portOutput \<circ> (i_Exec_Comp_Stream_Init trans_fun input1 c))
      channel1;
    i_Streams_Connected_Init
      (portOutput \<circ> (i_Exec_Comp_Stream_Init trans_fun input2 c))
      channel2 \<rbrakk> \<Longrightarrow>
  channel1 \<Down> Suc n = channel2 \<Down> Suc n"
by (simp add: i_Streams_Connected_Init_def i_Exec_Stream_Init_eq_i_Exec_Stream_Cons i_Exec_Stream_take)


subsubsection \<open>Additional auxiliary results\<close>

text \<open>The following lemma shows that,
  if the system state is different at some time points
  with respect to a certain predicate @{term P},
  then there exists a defined time point between these two,
  where the state change has taken place\<close>

lemma f_State_Change_exists_set: "
  \<lbrakk> n1 \<le> n2; n1 \<in> I; n2 \<in> I;
    \<not> P (f_Exec_Comp trans_fun (input \<down> n1) c);
    P (f_Exec_Comp trans_fun (input \<down> n2) c) \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. n1 \<le> n \<and> n < n2 \<and>
    \<not> P (f_Exec_Comp trans_fun (input \<down> n) c) \<and>
    P (f_Exec_Comp trans_fun (input \<down> (inext n I)) c)"
by (rule inext_predicate_change_exists)

lemma f_State_Change_exists: "
  \<lbrakk> n1 \<le> n2;
    \<not> P (f_Exec_Comp trans_fun (input \<down> n1) c);
    P (f_Exec_Comp trans_fun (input \<down> n2) c) \<rbrakk> \<Longrightarrow>
  \<exists>n\<ge>n1. n < n2 \<and>
    \<not> P (f_Exec_Comp trans_fun (input \<down> n) c) \<and>
    P (f_Exec_Comp trans_fun (input \<down> (Suc n)) c)"
by (rule nat_Suc_predicate_change_exists)

lemma i_State_Change_exists_set: "
  \<lbrakk> n1 \<le> n2; n1 \<in> I; n2 \<in> I;
    \<not> P (i_Exec_Comp_Stream trans_fun input c n1);
    P (i_Exec_Comp_Stream trans_fun input c n2) \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. n1 \<le> n \<and> n < n2 \<and>
    \<not> P (i_Exec_Comp_Stream trans_fun input c n) \<and>
    P (i_Exec_Comp_Stream trans_fun input c (inext n I))"
by (rule inext_predicate_change_exists)

lemma i_State_Change_exists: "
  \<lbrakk> n1 \<le> n2;
    \<not> P (i_Exec_Comp_Stream trans_fun input c n1);
    P (i_Exec_Comp_Stream trans_fun input c n2) \<rbrakk> \<Longrightarrow>
  \<exists>n\<ge>n1. n < n2 \<and>
    \<not> P (i_Exec_Comp_Stream trans_fun input c n) \<and>
    P (i_Exec_Comp_Stream trans_fun input c (Suc n))"
by (rule nat_Suc_predicate_change_exists)

lemma i_State_Change_Init_exists_set: "
  \<lbrakk> n1 \<le> n2; n1 \<in> I; n2 \<in> I;
    \<not> P (i_Exec_Comp_Stream_Init trans_fun input c n1);
    P (i_Exec_Comp_Stream_Init trans_fun input c n2) \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. n1 \<le> n \<and> n < n2 \<and>
    \<not> P (i_Exec_Comp_Stream_Init trans_fun input c n) \<and>
    P (i_Exec_Comp_Stream_Init trans_fun input c (inext n I))"
by (rule inext_predicate_change_exists)

lemma i_State_Change_Init_exists: "
  \<lbrakk> n1 \<le> n2;
    \<not> P (i_Exec_Comp_Stream_Init trans_fun input c n1);
    P (i_Exec_Comp_Stream_Init trans_fun input c n2) \<rbrakk> \<Longrightarrow>
  \<exists>n\<ge>n1. n < n2 \<and>
    \<not> P (i_Exec_Comp_Stream_Init trans_fun input c n) \<and>
    P (i_Exec_Comp_Stream_Init trans_fun input c (Suc n))"
by (rule nat_Suc_predicate_change_exists)


subsection \<open>Components with accelerated execution\<close>

text \<open>
  This section deals with variable execution speed components.
  A component accelerated by a (clocking) factor @{term k}
  processes streams expanded by factor @{term k}
  and its output streams are compressed by factor @{term k}.\<close>


subsubsection \<open>Equivalence relation for executions\<close>

text \<open>
  A predicate indicating for
  two components together with transition functions
  and a given equivalence predicate for their local states,
  that the components exhibit equivalent observable behaviour
  after expanding input streams and shrinking output streams
  by a constant factor,
  given that their local states are equivalent
  with respect to the specified equivalence relations.\<close>

definition
  Equiv_Exec :: "
    'input \<Rightarrow>
    ('state1 \<Rightarrow> 'state2 \<Rightarrow> bool) \<Rightarrow> \<comment> \<open>Equivalence predicate for local states\<close>
    ('comp1, 'state1) Comp_Local_State \<Rightarrow>
    ('comp2, 'state2) Comp_Local_State \<Rightarrow>
    ('input, 'input1) Port_Input_Value \<Rightarrow> \<comment> \<open>Input adaptor for first component\<close>
    ('input, 'input2) Port_Input_Value \<Rightarrow> \<comment> \<open>Input adaptor for second component\<close>
    ('comp1, 'output) Port_Output_Value \<Rightarrow>
    ('comp2, 'output) Port_Output_Value \<Rightarrow>
    ('comp1, 'input1 message_af) Comp_Trans_Fun \<Rightarrow>
    ('comp2, 'input2 message_af) Comp_Trans_Fun \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> 'comp1 \<Rightarrow> 'comp2 \<Rightarrow> bool"
where
  "Equiv_Exec
    m equiv_states
      localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2 \<equiv>
    equiv_states (localState1 c1) (localState2 c2) \<longrightarrow> (
      last_message (map output_fun1 (
        f_Exec_Comp_Stream trans_fun1 (input_fun1 m # \<NoMsg>\<^bsup>k1 - Suc 0\<^esup>) c1)) =
      last_message (map output_fun2 (
        f_Exec_Comp_Stream trans_fun2 (input_fun2 m # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2)) \<and>
      equiv_states
        (localState1 (f_Exec_Comp trans_fun1 (input_fun1 m # \<NoMsg>\<^bsup>k1 - Suc 0\<^esup>) c1))
        (localState2 (f_Exec_Comp trans_fun2 (input_fun2 m # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2)))"

text \<open>
  Predicate indicating for
  two components together with transition functions
  and a given equivalence predicate for their local states,
  that the equivalence predicate is stable
  with respect to component execution,
  i.e., it determines the equivalence
  of components' local states
  both for the initial states and after the components
  have processed an arbitrary input.
  The restricting version @{term "Equiv_Exec_stable_set"}
  guarantees stability only for inputs from a given restriction set,
  the not-restricting version guarantees stability for all inputs.\<close>
definition
  Equiv_Exec_stable_set :: "
    'input set \<Rightarrow>
    ('state1 \<Rightarrow> 'state2 \<Rightarrow> bool) \<Rightarrow> \<comment> \<open>Equivalence predicate for local states\<close>
    ('comp1, 'state1) Comp_Local_State \<Rightarrow>
    ('comp2, 'state2) Comp_Local_State \<Rightarrow>
    ('input, 'input1) Port_Input_Value \<Rightarrow> \<comment> \<open>Input adaptor for first component\<close>
    ('input, 'input2) Port_Input_Value \<Rightarrow> \<comment> \<open>Input adaptor for second component\<close>
    ('comp1, 'output) Port_Output_Value \<Rightarrow>
    ('comp2, 'output) Port_Output_Value \<Rightarrow>
    ('comp1, 'input1 message_af) Comp_Trans_Fun \<Rightarrow>
    ('comp2, 'input2 message_af) Comp_Trans_Fun \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> 'comp1 \<Rightarrow> 'comp2 \<Rightarrow> bool"
where
  "Equiv_Exec_stable_set A
    equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2 \<equiv>
   \<forall>input m. set input \<subseteq> A \<and> m \<in> A \<longrightarrow>
     Equiv_Exec m
       equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
       trans_fun1 trans_fun2 k1 k2
       (f_Exec_Comp trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1)
       (f_Exec_Comp trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2)"

definition
  Equiv_Exec_stable :: "
    ('state1 \<Rightarrow> 'state2 \<Rightarrow> bool) \<Rightarrow> \<comment> \<open>Equivalence predicate for local states\<close>
    ('comp1, 'state1) Comp_Local_State \<Rightarrow>
    ('comp2, 'state2) Comp_Local_State \<Rightarrow>
    ('input, 'input1) Port_Input_Value \<Rightarrow> \<comment> \<open>Input adaptor for first component\<close>
    ('input, 'input2) Port_Input_Value \<Rightarrow> \<comment> \<open>Input adaptor for second component\<close>
    ('comp1, 'output) Port_Output_Value \<Rightarrow>
    ('comp2, 'output) Port_Output_Value \<Rightarrow>
    ('comp1, 'input1 message_af) Comp_Trans_Fun \<Rightarrow>
    ('comp2, 'input2 message_af) Comp_Trans_Fun \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> 'comp1 \<Rightarrow> 'comp2 \<Rightarrow> bool"
where
  "Equiv_Exec_stable
    equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2 \<equiv>
   \<forall>input m.
     Equiv_Exec m
       equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
       trans_fun1 trans_fun2 k1 k2
       (f_Exec_Comp trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1)
       (f_Exec_Comp trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2)"

lemma Equiv_Exec_equiv_statesI: "
  \<lbrakk> equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec
      m equiv_states
        localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
        trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  equiv_states
    (localState1 (f_Exec_Comp trans_fun1 (input_fun1 m # \<NoMsg>\<^bsup>k1 - Suc 0\<^esup>) c1))
    (localState2 (f_Exec_Comp trans_fun2 (input_fun2 m # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2))"
by (simp add: Equiv_Exec_def)

lemma Equiv_Exec_output_eqI: "
  \<lbrakk> equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec
      m equiv_states
      localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
        trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  last_message (map output_fun1 (
    f_Exec_Comp_Stream trans_fun1 (input_fun1 m # \<NoMsg>\<^bsup>k1 - Suc 0\<^esup>) c1)) =
  last_message (map output_fun2 (
    f_Exec_Comp_Stream trans_fun2 (input_fun2 m # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2))"
by (simp add: Equiv_Exec_def)

lemma Equiv_Exec_equiv_statesI': "
  \<lbrakk> equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec
      m equiv_states
        localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
        trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  equiv_states
   (localState1 (f_Exec_Comp trans_fun1 NoMsg\<^bsup>k1 - Suc 0\<^esup> (trans_fun1 (input_fun1 m) c1)))
   (localState2 (f_Exec_Comp trans_fun2 NoMsg\<^bsup>k2 - Suc 0\<^esup> (trans_fun2 (input_fun2 m) c2)))"
by (simp add: Equiv_Exec_def)

lemma Equiv_Exec_le1: "
  \<lbrakk> k1 \<le> Suc 0; k2 \<le> Suc 0;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec m
      equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  output_fun1 (trans_fun1 (input_fun1 m) c1) =
  output_fun2 (trans_fun2 (input_fun2 m) c2) \<and>
  equiv_states
    (localState1 (trans_fun1 (input_fun1 m) c1))
    (localState2 (trans_fun2 (input_fun2 m) c2))"
by (simp add: Equiv_Exec_def)


lemma Equiv_Exec_stable_set_UNIV: "
  Equiv_Exec_stable_set
    UNIV equiv_states
    localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2 =
  Equiv_Exec_stable
    equiv_states
    localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2"
by (simp add: Equiv_Exec_stable_set_def Equiv_Exec_stable_def)

lemma Equiv_Exec_stable_setI: "
  \<lbrakk> Equiv_Exec_stable_set A
    equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2;
    set input \<subseteq> A; m \<in> A \<rbrakk> \<Longrightarrow>
  Equiv_Exec
        m equiv_states
        localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
        trans_fun1 trans_fun2 k1 k2
        (f_Exec_Comp trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1)
        (f_Exec_Comp trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2)"
by (simp add: Equiv_Exec_stable_set_def)

lemma Equiv_Exec_stableI: "
  Equiv_Exec_stable
    equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2 \<Longrightarrow>
  Equiv_Exec m
    equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2
    (f_Exec_Comp trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1)
    (f_Exec_Comp trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2)"
by (simp add: Equiv_Exec_stable_def)


text \<open>Reflexitity, symmetry and transitivity results for @{term "Equiv_Exec"}\<close>

lemma Equiv_Exec_refl: "
  \<lbrakk> \<And>c. equiv_states (localState c) (localState c) \<rbrakk> \<Longrightarrow>
  Equiv_Exec
    m equiv_states
    localState localState input_fun input_fun output_fun output_fun
    trans_fun trans_fun k k c c"
by (simp add: Equiv_Exec_def)

lemma Equiv_Exec_sym[rule_format]: "
  \<lbrakk> \<forall>c1 c2.
      equiv_states (localState1 c1) (localState2 c2) =
      equiv_states (localState2 c2) (localState1 c1) \<rbrakk> \<Longrightarrow>
  Equiv_Exec
    m equiv_states
    localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2 =
  Equiv_Exec
    m equiv_states
    localState2 localState1 input_fun2 input_fun1 output_fun2 output_fun1
    trans_fun2 trans_fun1 k2 k1 c2 c1"
by (fastforce simp: Equiv_Exec_def)

lemma Equiv_Exec_sym2: "
  \<lbrakk> equiv_states_sym = (\<lambda>s1 s2. equiv_states s2 s1) \<rbrakk> \<Longrightarrow>
  Equiv_Exec
    m equiv_states
    localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
    trans_fun1 trans_fun2 k1 k2 c1 c2 =
  Equiv_Exec
    m equiv_states_sym
    localState2 localState1 input_fun2 input_fun1 output_fun2 output_fun1
    trans_fun2 trans_fun1 k2 k1 c2 c1"
by (fastforce simp: Equiv_Exec_def)

lemma Equiv_Exec_sym2_ex: "
  \<exists>equiv_states_sym.
    Equiv_Exec
      m equiv_states
      localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2 =
    Equiv_Exec
      m equiv_states_sym
      localState2 localState1 input_fun2 input_fun1 output_fun2 output_fun1
      trans_fun2 trans_fun1 k2 k1 c2 c1"
by (rule exI, rule Equiv_Exec_sym2, simp)

lemma Equiv_Exec_trans: "
  \<lbrakk> Equiv_Exec
      m equiv_states12
      localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2;
    Equiv_Exec
      m equiv_states23
      localState2 localState3 input_fun2 input_fun3 output_fun2 output_fun3
      trans_fun2 trans_fun3 k2 k3 c2 c3;
    equiv_states13 = (\<lambda>s1 s3. (
      if s1 = localState1 c1 \<and> s3 = localState3 c3 then
        equiv_states12 s1 (localState2 c2) \<and>
        equiv_states23 (localState2 c2) s3
      else
        equiv_states12 s1 (
          localState2 (f_Exec_Comp trans_fun2 (input_fun2 m # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2))) \<and>
        equiv_states23 (
          localState2 (f_Exec_Comp trans_fun2 (input_fun2 m # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2)) s3) \<rbrakk> \<Longrightarrow>
    Equiv_Exec
      m equiv_states13
      localState1 localState3 input_fun1 input_fun3 output_fun1 output_fun3
      trans_fun1 trans_fun3 k1 k3 c1 c3"
by (fastforce simp: Equiv_Exec_def)

lemma Equiv_Exec_trans_ex: "
  \<lbrakk> Equiv_Exec
      m equiv_states12
      localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2;
    Equiv_Exec
      m equiv_states23
      localState2 localState3 input_fun2 input_fun3 output_fun2 output_fun3
      trans_fun2 trans_fun3 k2 k3 c2 c3 \<rbrakk> \<Longrightarrow>
    \<exists>equiv_states13. Equiv_Exec
      m equiv_states13
      localState1 localState3 input_fun1 input_fun3 output_fun1 output_fun3
      trans_fun1 trans_fun3 k1 k3 c1 c3"
by (blast intro: Equiv_Exec_trans)


text \<open>A predicate indicating for
  a given local state extraction function and
  a given transition function,
  that components, whose states are equal with regard to the
  local state extraction function,
  are transformed into equal componenents,
  when the transition function is applied with the same input.\<close>
definition Exec_Equal_State ::
    "('comp, 'state) Comp_Local_State \<Rightarrow> ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow> bool"
  where "Exec_Equal_State localState trans_fun \<equiv>
    \<forall>c1 c2 m. localState c1 = localState c2 \<longrightarrow> trans_fun m c1 = trans_fun m c2"

lemma Exec_Equal_StateD: "
  \<lbrakk> Exec_Equal_State localState trans_fun;
    localState c1 = localState c2 \<rbrakk> \<Longrightarrow>
  trans_fun m c1 = trans_fun m c2"
by (unfold Exec_Equal_State_def, blast)

lemma Exec_Equal_StateD': "
  Exec_Equal_State localState trans_fun \<Longrightarrow>
  \<forall>c1 c2 m. localState c1 = localState c2 \<longrightarrow> trans_fun m c1 = trans_fun m c2"
by (unfold Exec_Equal_State_def, blast)

lemma Exec_Equal_StateI: "
  (\<And>c1 c2 m. localState c1 = localState c2 \<Longrightarrow> trans_fun m c1 = trans_fun m c2)
  \<Longrightarrow> Exec_Equal_State localState trans_fun"
by (unfold Exec_Equal_State_def, blast)

lemma f_Exec_Equal_State: "\<And>c1 c2.
  \<lbrakk> Exec_Equal_State localState trans_fun;
    localState c1 = localState c2; xs \<noteq> [] \<rbrakk> \<Longrightarrow>
  f_Exec_Comp trans_fun xs c1 = f_Exec_Comp trans_fun xs c2"
apply (induct xs, simp)
apply (case_tac "xs = []")
 apply simp
 apply (rule Exec_Equal_StateD, assumption+)
apply (drule_tac x="trans_fun a c1" in meta_spec)
apply (drule_tac x="trans_fun a c2" in meta_spec)
apply (drule_tac ?c1.0=c1 and ?c2.0=c2 and m=a in Exec_Equal_StateD, assumption)
apply simp
done

lemma f_Exec_Stream_Equal_State: "
  \<lbrakk> Exec_Equal_State localState trans_fun;
    localState c1 = localState c2 \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream trans_fun xs c1 =
  f_Exec_Comp_Stream trans_fun xs c2"
apply (clarsimp simp: list_eq_iff f_Exec_Stream_nth)
apply (drule gr_implies_gr0)
apply (rule f_Exec_Equal_State)
apply simp+
done

lemma i_Exec_Stream_Equal_State: "
  \<lbrakk> Exec_Equal_State localState trans_fun;
    localState c1 = localState c2 \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream trans_fun input c1 =
  i_Exec_Comp_Stream trans_fun input c2"
apply (clarsimp simp: ilist_eq_iff i_Exec_Stream_nth)
apply (rule f_Exec_Equal_State)
apply simp+
done


subsubsection \<open>Idle states\<close>

definition State_Idle ::
  "('comp, 'state) Comp_Local_State \<Rightarrow> ('comp \<Rightarrow> 'output message_af) \<Rightarrow>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow> 'state \<Rightarrow> bool"
  where "State_Idle localState output_fun trans_fun state \<equiv>
    \<forall>c. localState c = state \<longrightarrow>
      localState (trans_fun \<NoMsg> c) = state \<and>
      output_fun (trans_fun \<NoMsg> c) = \<NoMsg>"

lemma State_IdleD: "
  \<lbrakk> State_Idle localState output_fun trans_fun state;
    localState c = state \<rbrakk> \<Longrightarrow>
  localState (trans_fun \<NoMsg> c) = state \<and>
  output_fun (trans_fun \<NoMsg> c) = \<NoMsg>"
by (unfold State_Idle_def, blast)

lemma State_IdleD': "
  State_Idle localState output_fun trans_fun state \<Longrightarrow>
  \<forall>c. localState c = state \<longrightarrow>
  localState (trans_fun \<NoMsg> c) = state \<and>
  output_fun (trans_fun \<NoMsg> c) = \<NoMsg>"
by (unfold State_Idle_def, blast)

lemma State_IdleI: "
  \<lbrakk> \<And>c. localState c = state \<Longrightarrow>
    localState (trans_fun \<NoMsg> c) = state \<and>
    output_fun (trans_fun \<NoMsg> c) = \<NoMsg> \<rbrakk> \<Longrightarrow>
  State_Idle localState output_fun trans_fun state"
by (unfold State_Idle_def, blast)

lemma State_Idle_step[rule_format]: "
  \<lbrakk> State_Idle localState output_fun trans_fun (localState c) \<rbrakk> \<Longrightarrow>
  State_Idle localState output_fun trans_fun (localState (trans_fun \<NoMsg> c))"
apply (frule State_IdleD[OF _ refl], erule conjE)
apply (rule State_IdleI, rename_tac c0)
apply (drule_tac c=c0 in State_IdleD)
apply simp+
done

lemma f_Exec_State_Idle_replicate_NoMsg_state[rule_format]: "
  \<And>c. State_Idle localState output_fun trans_fun (localState c) \<Longrightarrow>
  localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c) = localState c"
apply (induct n, simp)
apply (frule State_Idle_step)
apply (drule_tac c=c in State_IdleD, rule refl)
apply simp
done


lemma f_Exec_State_Idle_replicate_NoMsg_gr0_output[rule_format]: "\<And>c.
  \<lbrakk> State_Idle localState output_fun trans_fun (localState c); 0 < n \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c) = \<NoMsg>"
apply (induct n, simp)
apply (case_tac "n = 0")
 apply simp
 apply (rule State_IdleD[THEN conjunct2], assumption, simp)
apply (drule State_Idle_step)
apply simp
done

lemma f_Exec_State_Idle_replicate_NoMsg_output[rule_format]: "
  \<lbrakk> State_Idle localState output_fun trans_fun (localState c);
    output_fun c = \<NoMsg> \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c) = \<NoMsg>"
apply (case_tac "n = 0", simp)
apply (simp add: f_Exec_State_Idle_replicate_NoMsg_gr0_output)
done

lemma f_Exec_Stream_State_Idle_replicate_NoMsg_output[rule_format]: "
  \<lbrakk> State_Idle localState output_fun trans_fun (localState c) \<rbrakk> \<Longrightarrow>
  map output_fun (f_Exec_Comp_Stream trans_fun \<NoMsg>\<^bsup>n\<^esup> c) = \<NoMsg>\<^bsup>n\<^esup>"
by (simp add: list_eq_iff f_Exec_Stream_nth min_eqL f_Exec_State_Idle_replicate_NoMsg_gr0_output del: replicate.simps)

corollary f_Exec_State_Idle_append_replicate_NoMsg_state: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun xs c)) \<rbrakk> \<Longrightarrow>
  localState (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c) =
  localState (f_Exec_Comp trans_fun xs c)"
by (simp add: f_Exec_append f_Exec_State_Idle_replicate_NoMsg_state)

corollary f_Exec_State_Idle_append_replicate_NoMsg_ge_state: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>m\<^esup>) c));
    m \<le> n \<rbrakk> \<Longrightarrow>
  localState (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c) =
  localState (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>m\<^esup>) c)"
apply (rule_tac t=n and s="m + (n - m)" in subst, simp)
apply (simp only: replicate_add append_assoc[symmetric])
apply (rule f_Exec_State_Idle_append_replicate_NoMsg_state, simp)
done

corollary f_Exec_State_Idle_replicate_NoMsg_ge_state: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>m\<^esup> c));
    m \<le> n \<rbrakk> \<Longrightarrow>
  localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c) =
  localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>m\<^esup> c)"
by (cut_tac f_Exec_State_Idle_append_replicate_NoMsg_ge_state[where xs="[]"], simp+)

corollary f_Exec_State_Idle_append_replicate_NoMsg_gr0_output: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun xs c));
    0 < n \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c) = \<NoMsg>"
by (simp add: f_Exec_append f_Exec_State_Idle_replicate_NoMsg_gr0_output)

corollary f_Exec_Stream_State_Idle_append_replicate_NoMsg_gr0_output: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun xs c)) \<rbrakk> \<Longrightarrow>
  map output_fun (f_Exec_Comp_Stream trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c) =
  map output_fun (f_Exec_Comp_Stream trans_fun xs c) @ \<NoMsg>\<^bsup>n\<^esup>"
by (simp add: f_Exec_Stream_append f_Exec_Stream_State_Idle_replicate_NoMsg_output)

corollary f_Exec_State_Idle_append_replicate_NoMsg_gr_output: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>m\<^esup>) c));
    m < n \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c) = \<NoMsg>"
apply (rule_tac t=n and s="m + (n - m)" in subst, simp)
apply (simp only: replicate_add append_assoc[symmetric])
apply (rule f_Exec_State_Idle_append_replicate_NoMsg_gr0_output, simp+)
done

corollary f_Exec_State_Idle_append_replicate_NoMsg_ge_output: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>m\<^esup>) c));
    output_fun (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>m\<^esup>) c) = \<NoMsg>; m \<le> n \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c) = \<NoMsg>"
by (fastforce simp: order_le_less f_Exec_State_Idle_append_replicate_NoMsg_gr_output)

corollary f_Exec_State_Idle_replicate_NoMsg_gr_output: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>m\<^esup> c));
    m < n \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c) = \<NoMsg>"
by (cut_tac xs="[]" in f_Exec_State_Idle_append_replicate_NoMsg_gr_output, simp+)

corollary f_Exec_State_Idle_replicate_NoMsg_ge_output: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>m\<^esup> c));
    output_fun (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>m\<^esup> c) = \<NoMsg>; m \<le> n \<rbrakk> \<Longrightarrow>
  output_fun (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c) = \<NoMsg>"
by (fastforce simp: order_le_less f_Exec_State_Idle_replicate_NoMsg_gr_output)


lemma State_Idle_append_replicate_NoMsg_output_last_message: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun xs c)) \<rbrakk> \<Longrightarrow>
  last_message (map output_fun (f_Exec_Comp_Stream trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c)) =
  last_message (map output_fun (f_Exec_Comp_Stream trans_fun xs c))"
by (simp add: f_Exec_Stream_State_Idle_append_replicate_NoMsg_gr0_output last_message_append_replicate_NoMsg)

lemma State_Idle_append_replicate_NoMsg_output_Msg_eq_last_message: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun xs c));
    output_fun (f_Exec_Comp trans_fun xs c) \<noteq> \<NoMsg>;
    xs \<noteq> [] \<rbrakk> \<Longrightarrow>
  last_message (map output_fun (f_Exec_Comp_Stream trans_fun (xs @ \<NoMsg>\<^bsup>n\<^esup>) c)) =
  output_fun (f_Exec_Comp trans_fun xs c)"
apply (simp add: State_Idle_append_replicate_NoMsg_output_last_message f_Exec_eq_f_Exec_Stream_last2 )
apply (subst last_message_Msg_eq_last)
apply (simp add: map_last f_Exec_Stream_not_empty_conv)+
done

corollary State_Idle_output_Msg_eq_last_message: "
  \<lbrakk> State_Idle localState output_fun trans_fun (
      localState (f_Exec_Comp trans_fun xs c));
    output_fun (f_Exec_Comp trans_fun xs c) \<noteq> \<NoMsg>;
    xs \<noteq> [] \<rbrakk> \<Longrightarrow>
  last_message (map output_fun (f_Exec_Comp_Stream trans_fun xs c)) =
  output_fun (f_Exec_Comp trans_fun xs c)"
by (rule_tac n=0 in subst[OF State_Idle_append_replicate_NoMsg_output_Msg_eq_last_message, rule_format], simp+)

lemma State_Idle_imp_exists_state_change: "
  \<lbrakk> \<not> State_Idle localState output_fun trans_fun (localState c);
    State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c)) \<rbrakk> \<Longrightarrow>
  \<exists>i<n. (
    \<not> State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>i\<^esup> c)) \<and> (
    \<forall>j\<le>n. i < j \<longrightarrow> State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>j\<^esup> c))))"
apply (cut_tac
  a=0 and b=n and
  P="\<lambda>x. State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun NoMsg\<^bsup>x\<^esup> c))"
  in nat_Suc_predicate_change_exists, simp+)
apply (clarify, rename_tac n1)
apply (rule_tac x=n1 in exI)
apply clarsimp
apply (rule_tac t="j" and s="Suc n1 + (j - Suc n1)" in subst, simp)
apply (subst replicate_add)
apply (simp add: replicate_add f_Exec_State_Idle_append_replicate_NoMsg_state)
done

lemma State_Idle_imp_exists_state_change2: "
  \<lbrakk> \<not> State_Idle localState output_fun trans_fun (localState c);
    State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>n\<^esup> c)) \<rbrakk> \<Longrightarrow>
  \<exists>i<n. (
    (\<forall>j\<le>i. \<not> State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>i\<^esup> c))) \<and>
    (\<forall>j\<le>n. i < j \<longrightarrow> State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun \<NoMsg>\<^bsup>j\<^esup> c))))"
apply (frule State_Idle_imp_exists_state_change, assumption)
apply (clarify, rename_tac i)
apply (rule_tac x=i in exI)
apply simp
done


subsubsection \<open>Basic definitions for accelerated execution\<close>

text \<open>Stream processing with accelerated components\<close>

definition f_Exec_Comp_Stream_Acc_Output ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'output message_af) \<Rightarrow> \<comment> \<open>Output extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input fstream_af \<Rightarrow> 'comp \<Rightarrow>
    'output fstream_af"
  where "f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<equiv>
    (map output_fun (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) \<div>\<^sub>f k"

definition f_Exec_Comp_Stream_Acc_LocalState ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'state) \<Rightarrow> \<comment> \<open>Local state extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input fstream_af \<Rightarrow> 'comp \<Rightarrow>
    'state list"
  where "f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c \<equiv>
    (map localState (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) \<div>\<^bsub>fl\<^esub> k"

definition i_Exec_Comp_Stream_Acc_Output ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'output message_af) \<Rightarrow> \<comment> \<open>Output extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input istream_af \<Rightarrow> 'comp \<Rightarrow>
    'output istream_af"
  where "i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c \<equiv>
    (output_fun \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) \<div>\<^sub>i k"

definition i_Exec_Comp_Stream_Acc_LocalState ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'state) \<Rightarrow> \<comment> \<open>Local state extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input istream_af \<Rightarrow> 'comp \<Rightarrow>
    'state ilist"
  where "i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c \<equiv>
    (localState \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) \<div>\<^bsub>il\<^esub> k"

definition f_Exec_Comp_Stream_Acc_Output_Init ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'output message_af) \<Rightarrow> \<comment> \<open>Output extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input fstream_af \<Rightarrow> 'comp \<Rightarrow>
    'output fstream_af"
  where "f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c \<equiv>
    (output_fun c) # f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c"

definition f_Exec_Comp_Stream_Acc_LocalState_Init ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'state) \<Rightarrow> \<comment> \<open>Local state extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow> 'input fstream_af \<Rightarrow> 'comp \<Rightarrow>
    'state list"
  where "f_Exec_Comp_Stream_Acc_LocalState_Init k localState trans_fun xs c \<equiv>
    (localState c) # f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c"

definition i_Exec_Comp_Stream_Acc_Output_Init ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'output message_af) \<Rightarrow> \<comment> \<open>Output extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input istream_af \<Rightarrow> 'comp \<Rightarrow>
    'output istream_af"
  where "i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input c \<equiv>
    [output_fun c] \<frown> (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c)"

definition i_Exec_Comp_Stream_Acc_LocalState_Init ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp \<Rightarrow> 'state) \<Rightarrow> \<comment> \<open>Local state extraction function\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    'input istream_af \<Rightarrow> 'comp \<Rightarrow>
    'state ilist"
  where "i_Exec_Comp_Stream_Acc_LocalState_Init k localState trans_fun input c \<equiv>
    [localState c] \<frown> (i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c)"

lemma f_Exec_Stream_Acc_Output_length[simp]: "
  0 < k \<Longrightarrow>
  length (f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c) = length xs"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def f_shrink_length)

lemma f_Exec_Stream_Acc_LocalState_length[simp]: "
  0 < k \<Longrightarrow>
  length (f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c) = length xs"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_def f_shrink_last_length)

lemmas f_Exec_Stream_Acc_length =
  f_Exec_Stream_Acc_LocalState_length
  f_Exec_Stream_Acc_Output_length


subsubsection \<open>Basic results for accelerated execution\<close>

lemma f_Exec_Stream_Acc_Output_Nil[simp]: "
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun [] c = []"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def)

lemma f_Exec_Stream_Acc_LocalState_Nil[simp]: "
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun [] c = []"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_def)

lemmas f_Exec_Stream_Acc_Nil =
  f_Exec_Stream_Acc_LocalState_Nil
  f_Exec_Stream_Acc_Output_Nil

lemma f_Exec_Stream_Acc_Output_0[simp]: "
  f_Exec_Comp_Stream_Acc_Output 0 output_fun trans_fun xs c = []"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def)

lemma f_Exec_Stream_Acc_LocalState_0[simp]: "
  f_Exec_Comp_Stream_Acc_LocalState 0 localState trans_fun xs c = []"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_def)

lemmas f_Exec_Stream_Acc_0 =
  f_Exec_Stream_Acc_LocalState_0
  f_Exec_Stream_Acc_Output_0

lemma f_Exec_Stream_Acc_Output_1[simp]: "
  f_Exec_Comp_Stream_Acc_Output (Suc 0) output_fun trans_fun xs c =
  map output_fun (f_Exec_Comp_Stream trans_fun xs c)"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def)

lemma f_Exec_Stream_Acc_LocalState_1[simp]: "
  f_Exec_Comp_Stream_Acc_LocalState (Suc 0) localState trans_fun xs c =
  map localState (f_Exec_Comp_Stream trans_fun xs c)"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_def)

lemma i_Exec_Stream_Acc_Output_1[simp]: "
  i_Exec_Comp_Stream_Acc_Output (Suc 0) output_fun trans_fun input c =
  output_fun \<circ> (i_Exec_Comp_Stream trans_fun input c)"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def)

lemma i_Exec_Stream_Acc_LocalState_1[simp]: "
  i_Exec_Comp_Stream_Acc_LocalState (Suc 0) localState trans_fun input c =
  localState \<circ> (i_Exec_Comp_Stream trans_fun input c)"
by (simp add: i_Exec_Comp_Stream_Acc_LocalState_def)

lemma f_Exec_Stream_Acc_Output_eq_last_message_hold: "
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c =
  (map output_fun (f_Exec_Comp_Stream trans_fun (xs \<odot>\<^sub>f k) c)) \<longmapsto>\<^sub>f k \<div>\<^bsub>fl\<^esub> k"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def f_shrink_eq_f_last_message_hold_shrink_last)

lemma i_Exec_Stream_Acc_Output_eq_last_message_hold: "0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c =
  (output_fun \<circ> (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c)) \<longmapsto>\<^sub>i k \<div>\<^bsub>il\<^esub> k"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_i_last_message_hold_shrink_last)

lemma f_Exec_Stream_Acc_Output_take: "
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<down> n =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (xs \<down> n) c"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def f_shrink_def f_Exec_Stream_expand_aggregate_map_take)

lemma f_Exec_Stream_Acc_Output_drop: "
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<up> n =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (xs \<up> n) (
    f_Exec_Comp trans_fun (xs \<down> n \<odot>\<^sub>f k) c)"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def f_shrink_def f_Exec_Stream_expand_aggregate_map_drop)

lemma i_Exec_Stream_Acc_Output_take: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c \<Down> n =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (input \<Down> n) c"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def i_Exec_Comp_Stream_Acc_Output_def
  f_shrink_def i_shrink_def i_Exec_Stream_expand_aggregate_map_take)

lemma i_Exec_Stream_Acc_Output_drop: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c \<Up> n =
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (input \<Up> n) (
    f_Exec_Comp trans_fun (input \<Down> n \<odot>\<^sub>f k) c)"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_def i_Exec_Stream_expand_aggregate_map_drop)

lemma i_Exec_Stream_Acc_LocalState_take: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c \<Down> n =
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (input \<Down> n) c"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_def i_Exec_Comp_Stream_Acc_LocalState_def
  f_shrink_last_def i_shrink_last_def i_Exec_Stream_expand_aggregate_map_take)

lemma i_Exec_Stream_Acc_LocalState_drop: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c \<Up> n =
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (input \<Up> n) (
    f_Exec_Comp trans_fun (input \<Down> n \<odot>\<^sub>f k) c)"
by (simp add: i_Exec_Comp_Stream_Acc_LocalState_def i_shrink_last_def i_Exec_Stream_expand_aggregate_map_drop)

lemma f_Exec_Stream_Acc_Output_append: "
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (xs @ ys) c =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c @
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun ys (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c)"
by (simp only: f_Exec_Comp_Stream_Acc_Output_def f_shrink_def f_Exec_Stream_expand_map_aggregate_append)

lemma f_Exec_Stream_Acc_Output_Cons: "
  0 < k \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (x # xs) c =
  last_message (map output_fun (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)) #
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs (
    f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)"
by (simp only: f_Exec_Comp_Stream_Acc_Output_def f_shrink_def f_Exec_Stream_expand_map_aggregate_Cons)

lemma f_Exec_Stream_Acc_Output_one: "
  0 < k \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun [x] c =
  [last_message (map output_fun (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c))]"
by (simp add: f_Exec_Stream_Acc_Output_Cons)

lemma f_Exec_Stream_Acc_Output_snoc: "
  0 < k \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (xs @ [x]) c =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c @
  [last_message (map output_fun (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c)))]"
by (simp add: f_Exec_Stream_Acc_Output_append f_Exec_Stream_Acc_Output_one)

lemma i_Exec_Stream_Acc_Output_append: "
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (xs \<frown> input) c =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<frown>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c)"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def i_Exec_Comp_Stream_Acc_Output_def f_shrink_def i_shrink_def i_Exec_Stream_expand_map_aggregate_append)

lemma i_Exec_Stream_Acc_Output_Cons: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun ([x] \<frown> input) c =
  [last_message (map output_fun (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c))] \<frown>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input (
    f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)"
by (simp add: i_Exec_Stream_Acc_Output_append f_Exec_Stream_Acc_Output_one)

lemma f_Exec_Stream_Acc_LocalState_append: "
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (xs @ ys) c =
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c @
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun ys (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c)"
by (simp only: f_Exec_Comp_Stream_Acc_LocalState_def f_shrink_last_def f_Exec_Stream_expand_map_aggregate_append)

lemma f_Exec_Stream_Acc_LocalState_Cons: "
  0 < k \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (x # xs) c =
  localState (f_Exec_Comp trans_fun (x #  \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c) #
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs (
    f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)"
apply (unfold f_Exec_Comp_Stream_Acc_LocalState_def)
apply (simp only: f_shrink_last_map f_expand_Cons append_Cons[symmetric])
apply (simp add: f_Exec_Stream_append replicate_pred_Cons_length f_shrink_last_Cons del: f_Exec_Stream_Cons append_Cons)
apply (simp add: f_Exec_eq_f_Exec_Stream_last2[symmetric] f_Exec_Stream_empty_conv)
done

lemma f_Exec_Stream_Acc_LocalState_one: "
  0 < k \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun [x] c =
  [localState (f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)]"
by (simp add: f_Exec_Stream_Acc_LocalState_Cons)

lemma f_Exec_Stream_Acc_LocalState_snoc: "
  0 < k \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (xs @ [x]) c =
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c @
  [localState (f_Exec_Comp trans_fun ((xs @ [x]) \<odot>\<^sub>f k) c)]"
by (simp add: f_Exec_Stream_Acc_LocalState_append f_Exec_Stream_Acc_LocalState_Cons f_Exec_append)

lemma i_Exec_Stream_Acc_LocalState_append: "
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (xs \<frown> input) c =
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c \<frown>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input (
    f_Exec_Comp trans_fun (xs \<odot>\<^sub>f k) c)"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_def i_Exec_Comp_Stream_Acc_LocalState_def f_shrink_last_def i_shrink_last_def i_Exec_Stream_expand_map_aggregate_append)

lemma i_Exec_Stream_Acc_LocalState_Cons: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun ([x] \<frown> input) c =
  [localState (f_Exec_Comp trans_fun (x #  \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)] \<frown>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input (
    f_Exec_Comp trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)"
by (simp add: i_Exec_Stream_Acc_LocalState_append f_Exec_Stream_Acc_LocalState_one f_expand_one)

lemma f_Exec_Stream_Acc_Output_nth: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c ! n =
  last_message (map output_fun (
    f_Exec_Comp_Stream trans_fun (xs ! n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) (
      f_Exec_Comp trans_fun (xs \<down> n \<odot>\<^sub>f k) c)))"
by (unfold f_Exec_Comp_Stream_Acc_Output_def f_shrink_def, rule f_Exec_Stream_expand_aggregate_map_nth)

lemma f_Exec_Stream_Acc_Output_nth_eq_i_nth: "
  \<lbrakk> 0 < k; n < n' \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (input \<Down> n') c ! n =
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c n"
by (unfold f_Exec_Comp_Stream_Acc_Output_def i_Exec_Comp_Stream_Acc_Output_def f_shrink_def i_shrink_def, rule f_Exec_Stream_expand_aggregate_map_nth_eq_i_nth)

lemma i_Exec_Stream_Acc_Output_nth: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c n =
  last_message (map output_fun (
    f_Exec_Comp_Stream trans_fun (input n # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) (
      f_Exec_Comp trans_fun (input \<Down> n \<odot>\<^sub>f k) c)))"
by (unfold i_Exec_Comp_Stream_Acc_Output_def i_shrink_def, rule i_Exec_Stream_expand_aggregate_map_nth)

corollary i_Exec_Stream_Acc_Output_nth_f_nth: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c n =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (input \<Down> Suc n) c ! n"
by (simp add: f_Exec_Stream_Acc_Output_nth_eq_i_nth)

corollary i_Exec_Stream_Acc_Output_nth_f_last: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c n =
  last (f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun (input \<Down> Suc n) c)"
by (simp add: i_Exec_Stream_Acc_Output_nth_f_nth last_nth length_greater_0_conv[THEN iffD1])

lemma f_Exec_Stream_Acc_LocalState_nth: "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c ! n =
  localState (f_Exec_Comp trans_fun (xs \<down> Suc n \<odot>\<^sub>f k) c)"
apply (simp add: f_Exec_Comp_Stream_Acc_LocalState_def f_shrink_last_map)
apply (simp add: f_shrink_last_nth' f_shrink_last_length del: mult_Suc)
apply (simp add: f_Exec_Stream_nth less_imp_Suc_mult_pred_less f_expand_take_mod del: mult_Suc)
done

lemma f_Exec_Stream_Acc_LocalState_nth_eq_i_nth: "
  \<lbrakk> 0 < k; n < n' \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (input \<Down> n') c ! n =
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c n"
by (unfold f_Exec_Comp_Stream_Acc_LocalState_def i_Exec_Comp_Stream_Acc_LocalState_def f_shrink_last_def i_shrink_last_def, rule f_Exec_Stream_expand_aggregate_map_nth_eq_i_nth)

corollary i_Exec_Stream_Acc_LocalState_nth_f_nth: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k output_fun trans_fun input c n =
  f_Exec_Comp_Stream_Acc_LocalState k output_fun trans_fun (input \<Down> Suc n) c ! n"
by (simp add: f_Exec_Stream_Acc_LocalState_nth_eq_i_nth)

corollary i_Exec_Stream_Acc_LocalState_nth_f_last: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c n =
  last (f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun (input \<Down> Suc n) c)"
by (simp add: i_Exec_Stream_Acc_LocalState_nth_f_nth last_nth length_greater_0_conv[THEN iffD1])

lemma i_Exec_Stream_Acc_LocalState_nth: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c n =
  localState (f_Exec_Comp trans_fun (input \<Down> Suc n \<odot>\<^sub>f k) c)"
by (simp add: i_Exec_Stream_Acc_LocalState_nth_f_nth f_Exec_Stream_Acc_LocalState_nth)

lemma f_Exec_Stream_Acc_Output_causal: "
  xs \<down> n = ys \<down> n \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<down> n =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun ys c \<down> n"
by (simp add: f_Exec_Stream_Acc_Output_take)

lemma i_Exec_Stream_Acc_Output_causal: "
  input1 \<Down> n = input2 \<Down> n \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input1 c \<Down> n =
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input2 c \<Down> n"
apply (case_tac "k = 0")
 apply (simp add: i_Exec_Comp_Stream_Acc_Output_def)
apply (simp add: i_Exec_Stream_Acc_Output_take)
done

lemma f_Exec_Stream_Acc_Output_Connected_strictly_causal: "
  \<lbrakk> xs \<down> n = ys \<down> n;
    f_Streams_Connected
      (f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c)
      channel1;
    f_Streams_Connected
      (f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun ys c)
      channel2 \<rbrakk> \<Longrightarrow>
  channel1 \<down> Suc n = channel2 \<down> Suc n"
by (simp add: f_Streams_Connected_def f_Exec_Stream_Acc_Output_take)

lemma i_Exec_Stream_Acc_Output_Connected_strictly_causal: "
  \<lbrakk> input1 \<Down> n = input2 \<Down> n;
    i_Streams_Connected
      (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input1 c)
      channel1;
    i_Streams_Connected
      (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input2 c)
      channel2 \<rbrakk> \<Longrightarrow>
  channel1 \<Down> Suc n = channel2 \<Down> Suc n"
apply (unfold i_Streams_Connected_def)
apply (case_tac "k = 0")
 apply (simp add: i_Exec_Comp_Stream_Acc_Output_def)
apply (simp add: i_Exec_Stream_Acc_Output_take)
done


text \<open>Complete execution cycles/steps of accelrated execution\<close>

definition Acc_Trans_Fun_Step ::
  "nat \<Rightarrow> \<comment> \<open>Acceleration factor\<close>
    ('comp, 'input message_af) Comp_Trans_Fun \<Rightarrow>
    ('comp list \<Rightarrow> 'comp) \<Rightarrow> \<comment> \<open>Pointwise output shrink function\<close>
    'input message_af \<Rightarrow> 'comp \<Rightarrow>
    'comp"
  where "Acc_Trans_Fun_Step k trans_fun pointwise_shrink x c \<equiv>
    pointwise_shrink (f_Exec_Comp_Stream trans_fun (x # \<NoMsg>\<^bsup>k - Suc 0\<^esup>) c)"

definition is_Pointwise_Output_Shrink ::
  "('comp list \<Rightarrow> 'comp) \<Rightarrow> \<comment> \<open>Pointwise output shrink function\<close>
    ('comp \<Rightarrow> 'output message_af) \<Rightarrow> \<comment> \<open>Output extraction function for consideration\<close>
    bool"
  where "is_Pointwise_Output_Shrink pointwise_shrink output_fun \<equiv>
    \<forall>cs. output_fun (pointwise_shrink cs) = last_message (map output_fun cs)"

primrec is_Pointwise_Output_Shrink_list ::
  "('comp list \<Rightarrow> 'comp) \<Rightarrow> \<comment> \<open>Pointwise output shrink function\<close>
    ('comp \<Rightarrow> 'output message_af) list \<Rightarrow> \<comment> \<open>List of output extraction functions for consideration\<close>
    bool"
where
  "is_Pointwise_Output_Shrink_list pointwise_shrink [] = True"
| "is_Pointwise_Output_Shrink_list pointwise_shrink (f # fs) =
    (is_Pointwise_Output_Shrink pointwise_shrink f \<and>
     is_Pointwise_Output_Shrink_list pointwise_shrink fs)"

definition is_correct_localState_Pointwise_Output_Shrink ::
  "('comp list \<Rightarrow> 'comp) \<Rightarrow> \<comment> \<open>Pointwise output shrink function\<close>
    ('comp \<Rightarrow> 'state) \<Rightarrow> \<comment> \<open>Local state extraction function\<close>
    bool"
  where "is_correct_localState_Pointwise_Output_Shrink pointwise_shrink localState \<equiv>
    \<forall>cs. cs \<noteq> [] \<longrightarrow> localState (pointwise_shrink cs) = localState (last cs)"

lemma Deterministic_trans_fun_imp_acc_trans_fun:
  "Deterministic_Trans_Fun trans_fun localState \<Longrightarrow>
    Deterministic_Trans_Fun (Acc_Trans_Fun_Step k trans_fun pointwise_shrink) localState"
apply (simp (no_asm) only: Deterministic_Trans_Fun_def Acc_Trans_Fun_Step_def)
apply clarify
apply (subst Deterministic_f_Exec_Stream, simp+)
done

lemma is_Pointwise_Output_Shrink_list_imp_is_Pointwise_Output_Shrink:
  "\<lbrakk> is_Pointwise_Output_Shrink_list pointwise_shrink fs; output_fun \<in> set fs \<rbrakk> \<Longrightarrow>
    is_Pointwise_Output_Shrink pointwise_shrink output_fun"
apply (induct fs, simp)
apply fastforce
done

lemma is_Pointwise_Output_Shrink_list_eq_is_Pointwise_Output_Shrink_all:
  "(is_Pointwise_Output_Shrink_list pointwise_shrink fs) =
    (\<forall>output_fun \<in> set fs. is_Pointwise_Output_Shrink pointwise_shrink output_fun)"
apply (rule iffI)
 apply (rule ballI)
 apply (rule is_Pointwise_Output_Shrink_list_imp_is_Pointwise_Output_Shrink)
 apply (simp add: member_def)+
apply (induct fs, simp)
apply simp
done

lemma is_Pointwise_Output_Shrink_subset:
  "\<lbrakk> is_Pointwise_Output_Shrink_list pointwise_shrink fs; set fs' \<subseteq> set fs \<rbrakk> \<Longrightarrow>
    is_Pointwise_Output_Shrink_list pointwise_shrink fs'"
by (fastforce simp: is_Pointwise_Output_Shrink_list_eq_is_Pointwise_Output_Shrink_all)

lemma f_Exec_Stream_Acc_LocalState_eq_Acc_Trans_Fun_Step_LocalState: "\<And>c.
  \<lbrakk> 0 < k;
    Deterministic_Trans_Fun trans_fun localState;
    is_correct_localState_Pointwise_Output_Shrink pointwise_shrink localState \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c =
  map localState (f_Exec_Comp_Stream (Acc_Trans_Fun_Step k trans_fun pointwise_shrink) xs c)"
apply (drule Deterministic_trans_fun_imp_acc_trans_fun[of trans_fun localState k pointwise_shrink])
apply (clarsimp simp: list_eq_iff)
apply (simp add: f_Exec_Stream_Acc_LocalState_nth f_Exec_Stream_nth)
apply (induct xs, simp)
apply (rename_tac x xs c i)
apply (simp add: Acc_Trans_Fun_Step_def f_expand_Cons f_Exec_append)
apply (case_tac i)
 apply simp
 apply (simp only: is_correct_localState_Pointwise_Output_Shrink_def)
 apply (drule_tac x="f_Exec_Comp_Stream trans_fun (x # NoMsg\<^bsup>k - Suc 0\<^esup>) c" in spec)
 apply (simp add: f_Exec_Stream_not_empty_conv f_Exec_eq_f_Exec_Stream_last)
apply (rename_tac i2)
apply (drule_tac x="f_Exec_Comp trans_fun \<NoMsg>\<^bsup>k - Suc 0\<^esup> (trans_fun x c)" in meta_spec)
apply (drule_tac x=i2 in meta_spec)
apply (simp add: is_correct_localState_Pointwise_Output_Shrink_def)
apply (drule_tac x="f_Exec_Comp_Stream trans_fun (x # NoMsg\<^bsup>k - Suc 0\<^esup>) c" in spec)
apply (simp add: f_Exec_Stream_not_empty_conv)
apply (rule arg_cong[where f=localState])
apply (rule Deterministic_f_Exec)
  apply assumption
 apply (simp add: f_Exec_eq_f_Exec_Stream_last)
apply (simp add: length_greater_0_conv[symmetric] del: length_greater_0_conv)
done

lemma f_Exec_Stream_Acc_Output_eq_Acc_Trans_Fun_Step_Output: "\<And>c.
  \<lbrakk> 0 < k;
    Deterministic_Trans_Fun trans_fun localState;
    is_correct_localState_Pointwise_Output_Shrink pointwise_shrink localState;
    is_Pointwise_Output_Shrink pointwise_shrink output_fun \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c =
  map output_fun (f_Exec_Comp_Stream (Acc_Trans_Fun_Step k trans_fun pointwise_shrink) xs c)"
apply (drule Deterministic_trans_fun_imp_acc_trans_fun[of trans_fun localState k pointwise_shrink])
apply (clarsimp simp: list_eq_iff)
apply (simp add: f_Exec_Stream_Acc_Output_nth f_Exec_Stream_nth del: f_Exec_Stream_Cons)
apply (induct xs, simp)
apply (rename_tac x xs c i)
apply (simp add: Acc_Trans_Fun_Step_def del: f_Exec_Stream_Cons)
apply (case_tac i)
 apply (simp add: is_Pointwise_Output_Shrink_def)
apply (rename_tac i2)
apply (simp add: f_Exec_append)
apply (drule_tac x="f_Exec_Comp trans_fun \<NoMsg>\<^bsup>k - Suc 0\<^esup> (trans_fun x c)" in meta_spec)
apply (drule_tac x=i2 in meta_spec)
apply (simp add: is_correct_localState_Pointwise_Output_Shrink_def)
apply (drule_tac x="f_Exec_Comp_Stream trans_fun (x # NoMsg\<^bsup>k - Suc 0\<^esup>) c" in spec)
apply (simp add: f_Exec_Stream_not_empty_conv)
apply (rule arg_cong[where f=output_fun])
apply (rule Deterministic_f_Exec)
  apply assumption
 apply (simp add: f_Exec_eq_f_Exec_Stream_last)
apply (simp add: length_greater_0_conv[symmetric] del: length_greater_0_conv)
done

lemma i_Exec_Stream_Acc_LocalState_eq_Acc_Trans_Fun_Step_LocalState: "\<And>c.
  \<lbrakk> 0 < k;
    Deterministic_Trans_Fun trans_fun localState;
    is_correct_localState_Pointwise_Output_Shrink pointwise_shrink localState \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c =
  localState \<circ> (i_Exec_Comp_Stream (Acc_Trans_Fun_Step k trans_fun pointwise_shrink) input c)"
apply (rule ilist_i_take_eq_conv[THEN iffD2], rule allI)
apply (simp add: i_Exec_Stream_Acc_LocalState_take i_Exec_Stream_take f_Exec_Stream_Acc_LocalState_eq_Acc_Trans_Fun_Step_LocalState)
done

lemma i_Exec_Stream_Acc_Output_eq_Acc_Trans_Fun_Step_Output: "\<And>c.
  \<lbrakk> 0 < k;
    Deterministic_Trans_Fun trans_fun localState;
    is_correct_localState_Pointwise_Output_Shrink pointwise_shrink localState;
    is_Pointwise_Output_Shrink pointwise_shrink output_fun \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c =
  output_fun \<circ> (i_Exec_Comp_Stream (Acc_Trans_Fun_Step k trans_fun pointwise_shrink) input c)"
apply (rule ilist_i_take_eq_conv[THEN iffD2], rule allI)
apply (simp add: i_Exec_Stream_Acc_Output_take i_Exec_Stream_take f_Exec_Stream_Acc_Output_eq_Acc_Trans_Fun_Step_Output)
done


subsubsection \<open>Basic results for accelerated execution with initial state in the resulting stream\<close>

lemma f_Exec_Stream_Acc_Output_Init_length: "
  0 < k \<Longrightarrow>
  length (f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c) = Suc (length xs)"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def)

lemma f_Exec_Stream_Acc_LocalState_Init_length: "
  0 < k \<Longrightarrow>
  length (f_Exec_Comp_Stream_Acc_LocalState_Init k localState trans_fun xs c) = Suc (length xs)"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_Init_def)

lemma f_Exec_Stream_Acc_Output_Init_Nil: "
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun [] c = [output_fun c]"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def)

lemma f_Exec_Stream_Acc_LocalState_Init_Nil: "
  f_Exec_Comp_Stream_Acc_LocalState_Init k localState trans_fun [] c = [localState c]"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_Init_def)

lemma f_Exec_Stream_Acc_Output_Init_1: "
  f_Exec_Comp_Stream_Acc_Output_Init (Suc 0) output_fun trans_fun xs c =
  map output_fun (f_Exec_Comp_Stream_Init trans_fun xs c)"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)

lemma f_Exec_Stream_Acc_LocalState_Init_1: "
  f_Exec_Comp_Stream_Acc_LocalState_Init (Suc 0) localState trans_fun xs c =
  map localState (f_Exec_Comp_Stream_Init trans_fun xs c)"
by (simp add: f_Exec_Comp_Stream_Acc_LocalState_Init_def f_Exec_Stream_Init_eq_f_Exec_Stream_Cons)

lemma i_Exec_Stream_Acc_Output_Init_1: "
  i_Exec_Comp_Stream_Acc_Output_Init (Suc 0) output_fun trans_fun input c =
  output_fun \<circ> (i_Exec_Comp_Stream_Init trans_fun input c)"
by (simp add: i_Exec_Comp_Stream_Acc_Output_Init_def i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)

lemma i_Exec_Stream_Acc_LocalState_Init_1: "
  i_Exec_Comp_Stream_Acc_LocalState_Init (Suc 0) localState trans_fun input c =
  localState \<circ> (i_Exec_Comp_Stream_Init trans_fun input c)"
by (simp add: i_Exec_Comp_Stream_Acc_LocalState_Init_def i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)

lemma f_Exec_Stream_Acc_Output_Init_take: "
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c \<down> (Suc n) =
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun (xs \<down> n) c"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def f_Exec_Stream_Acc_Output_take)

lemma f_Exec_Stream_Acc_Output_Init_drop': "
  \<lbrakk> 0 < k; n < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c \<up> Suc n =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<up> n"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def)


lemma i_Exec_Stream_Acc_Output_Init_take: "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input c \<Down> (Suc n) =
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun (input \<Down> n) c"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def i_Exec_Comp_Stream_Acc_Output_Init_def i_Exec_Stream_Acc_Output_take)

lemma i_Exec_Stream_Acc_Output_Init_drop': "
  0 < k \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c \<Up> Suc n =
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c \<Up> n"
by (simp add: i_Exec_Comp_Stream_Acc_Output_Init_def)

lemma f_Exec_Stream_Acc_Output_Init_strictly_causal: "
  xs \<down> n = ys \<down> n \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c \<down> Suc n =
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun ys c \<down> Suc n"
by (simp add: f_Exec_Comp_Stream_Acc_Output_Init_def, rule f_Exec_Stream_Acc_Output_causal)

lemma i_Exec_Stream_Acc_Output_Init_strictly_causal: "
  input1 \<Down> n = input2 \<Down> n \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input1 c \<Down> Suc n =
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input2 c \<Down> Suc n"
by (simp add: i_Exec_Comp_Stream_Acc_Output_Init_def, rule i_Exec_Stream_Acc_Output_causal)

lemma f_Exec_Stream_Acc_Output_Init_eq_f_Exec_Stream_Acc_Output_Cons: "
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c =
  output_fun c # f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c"
by (simp add: f_Exec_Comp_Stream_Acc_Output_def f_Exec_Comp_Stream_Acc_Output_Init_def)

lemma f_Exec_Stream_Acc_Output_Init_eq_f_Exec_Stream_Acc_Output_Cons_output: "
  output_fun c = \<NoMsg> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c =
  \<NoMsg> # f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c"
by (simp add: f_Exec_Stream_Acc_Output_Init_eq_f_Exec_Stream_Acc_Output_Cons)

lemma f_Exec_Stream__Acc_OutputInit_tl_eq_f_Exec_Stream_Acc_Output: "
  tl (f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c) =
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c"
by (simp add: f_Exec_Stream_Acc_Output_Init_eq_f_Exec_Stream_Acc_Output_Cons)

lemma f_Exec_Stream_Previous_f_Exec_Stream_Acc_Output_Init: "
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c ! n =
  (f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c)\<^bsup>\<leftarrow>' output_fun c\<^esup> n"
by (simp add: f_Exec_Stream_Acc_Output_Init_eq_f_Exec_Stream_Acc_Output_Cons list_Previous_nth_if nth_Cons')

lemma f_Exec_Stream_Acc_Output_Init_eq_output_channel: "
  \<lbrakk> output_fun c = \<NoMsg>;
    f_Streams_Connected
      (f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c)
      channel \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun xs c = channel"
by (simp add: f_Streams_Connected_def f_Exec_Stream_Acc_Output_Init_eq_f_Exec_Stream_Acc_Output_Cons_output)


lemma i_Exec_Stream_Acc_Output_Init_eq_i_Exec_Stream_Acc_Output_Cons: "
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input c =
  [output_fun c] \<frown> i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_Exec_Comp_Stream_Acc_Output_Init_def)

lemma i_Exec_Stream_Acc_Output_Init_eq_i_Exec_Stream_Acc_Output_Cons_output: "
  output_fun c = \<NoMsg> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input c =
  [\<NoMsg> ] \<frown> i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c"
by (simp add: i_Exec_Stream_Acc_Output_Init_eq_i_Exec_Stream_Acc_Output_Cons)

lemma i_Exec_Stream_Previous_i_Exec_Stream_Acc_Output_Init: "
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input c n =
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c)\<^bsup>\<leftarrow> output_fun c\<^esup> n"
by (simp add: i_Exec_Stream_Acc_Output_Init_eq_i_Exec_Stream_Acc_Output_Cons ilist_Previous_nth_if)

lemma i_Exec_Stream_Acc_Output_Init_eq_output_channel: "
  \<lbrakk> output_fun c = \<NoMsg>;
    i_Streams_Connected
      (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c)
      channel \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output_Init k output_fun trans_fun input c = channel"
by (simp add: i_Streams_Connected_def i_Exec_Stream_Acc_Output_Init_eq_i_Exec_Stream_Acc_Output_Cons_output)


subsubsection \<open>Rules for proving execution equivalence\<close>

text \<open>
  A required precondition is that the @{term equiv_states} relation,
  which indicates whether the local states of @{term c1} and @{term c2}
  are equivalent with respect to observable behaviour,
  is preserved also after executing an input stream,
  because the @{term equiv_states} relation
  should deliver valid results not only at the time point @{term 0}
  but at every time point.\<close>

lemma f_Equiv_Exec_Stream_expand_shrink_equiv_state_set[rule_format]: "
  \<And>c1 c2 i. \<lbrakk>
   0 < k1; 0 < k2;
   equiv_states (localState1 c1) (localState2 c2);
   \<forall>input0. set input0 \<subseteq> A \<longrightarrow> (\<forall>m\<in>A.
      Equiv_Exec m equiv_states
      localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2
      (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
      (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2));
      \<comment> \<open>\<open>equiv_states\<close> relation implies equivalent executions\<close>
      \<comment> \<open>not only at the beginning but also after processing an input\<close>
   set input \<subseteq> A; i < length input \<rbrakk> \<Longrightarrow>
   equiv_states
     (localState1 ((f_Exec_Comp_Stream trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1) \<div>\<^bsub>fl\<^esub> k1 ! i))
     (localState2 ((f_Exec_Comp_Stream trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2) \<div>\<^bsub>fl\<^esub> k2 ! i))"
apply (induct input, simp)
apply (clarsimp simp: append_Cons[symmetric] f_Exec_Stream_append_if f_shrink_last_Cons nth_Cons simp del: last.simps f_Exec_Stream_Cons append_Cons)
apply (case_tac i)
 apply (drule_tac x="[]" in spec)
 apply (drule mp, simp)
 apply (drule_tac x=a in bspec, assumption)
 apply (simp del: last.simps f_Exec_Stream_Cons)
 apply (subst f_Exec_eq_f_Exec_Stream_last2[symmetric], simp)+
 apply (rule Equiv_Exec_equiv_statesI[of equiv_states localState1 _ localState2 _ _ input_fun1], assumption+)
apply (rename_tac i')
apply (subst f_Exec_eq_f_Exec_Stream_last2[symmetric], simp)+
apply (drule_tac x="f_Exec_Comp trans_fun1 (input_fun1 a # \<NoMsg>\<^bsup>k1 - Suc 0\<^esup>) c1" in meta_spec)
apply (drule_tac x="f_Exec_Comp trans_fun2 (input_fun2 a # \<NoMsg>\<^bsup>k2 - Suc 0\<^esup>) c2" in meta_spec)
apply (drule_tac x=i' in meta_spec)
apply (drule meta_mp, simp)+
 apply (drule_tac x="[]" in spec, simp)
 apply (drule_tac x=a in bspec, assumption)
 apply (rule Equiv_Exec_equiv_statesI'[of equiv_states localState1 _ localState2 _ _ input_fun1], simp+)
apply clarsimp
apply (drule meta_mp)
 apply clarify
 apply (drule_tac x="a # input0" in spec)
 apply (simp add: f_Exec_append)
apply simp
done

corollary f_Equiv_Exec_Stream_expand_shrink_equiv_state: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m. Equiv_Exec m
       equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
       trans_fun1 trans_fun2 k1 k2
       (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
       (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2);
    i<length input \<rbrakk> \<Longrightarrow>
  equiv_states
    (localState1 ((f_Exec_Comp_Stream trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1) \<div>\<^bsub>fl\<^esub> k1 ! i))
    (localState2 ((f_Exec_Comp_Stream trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2) \<div>\<^bsub>fl\<^esub> k2 ! i))"
by (rule f_Equiv_Exec_Stream_expand_shrink_equiv_state_set[of k1 k2 equiv_states localState1 c1 localState2 c2 UNIV input_fun1 input_fun2 output_fun1 output_fun2], simp+)

lemma f_Equiv_Exec_expand_shrink_equiv_state_set:"
  \<lbrakk> 0 < k1; 0 < k2; equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m. \<lbrakk>set input0 \<subseteq> A; m \<in> A\<rbrakk> \<Longrightarrow>
       Equiv_Exec
         m equiv_states localState1 localState2
         input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2
         (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
         (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2);
    set input \<subseteq> A \<rbrakk> \<Longrightarrow>
  equiv_states
    (localState1 (f_Exec_Comp trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1))
    (localState2 (f_Exec_Comp trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2))"
apply (case_tac "input = []", simp)
apply (subgoal_tac "map input_fun1 input \<odot>\<^sub>f k1 \<noteq> [] \<and> map input_fun2 input \<odot>\<^sub>f k2 \<noteq> []")
 prefer 2
 apply (simp add: length_greater_0_conv[symmetric] del: length_greater_0_conv)
apply (simp add: f_Exec_eq_f_Exec_Stream_last2 last_nth f_Exec_Stream_not_empty_conv)
apply (insert f_shrink_last_nth[of "length input - Suc 0" "f_Exec_Comp_Stream trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1" k1, symmetric])
apply (insert f_shrink_last_nth[of "length input - Suc 0" "f_Exec_Comp_Stream trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2" k2, symmetric])
apply (simp add: diff_mult_distrib gr0_imp_self_le_mult2)
apply (rule f_Equiv_Exec_Stream_expand_shrink_equiv_state_set[of k1 k2 equiv_states localState1 _ localState2 _ A input_fun1 input_fun2 output_fun1 output_fun2])
apply simp+
done

lemma f_Equiv_Exec_expand_shrink_equiv_state:"
  \<lbrakk> 0 < k1; 0 < k2; equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m.
       Equiv_Exec
         m equiv_states localState1 localState2
         input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2
         (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
         (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2) \<rbrakk> \<Longrightarrow>
  equiv_states
    (localState1 (f_Exec_Comp trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1))
    (localState2 (f_Exec_Comp trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2))"
by (rule f_Equiv_Exec_expand_shrink_equiv_state_set[of k1 k2 equiv_states localState1 _ localState2 _ UNIV input_fun1 input_fun2 output_fun1 output_fun2], simp+)

lemma i_Equiv_Exec_Stream_expand_shrink_equiv_state_set[rule_format]: "
  \<lbrakk> 0 < k1; 0 < k2; equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m. \<lbrakk>set input0 \<subseteq> A; m \<in> A\<rbrakk> \<Longrightarrow>
       Equiv_Exec
        m equiv_states localState1 localState2
        input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2
       (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
       (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2);
    range input \<subseteq> A \<rbrakk> \<Longrightarrow>
  equiv_states
    (localState1 ((i_Exec_Comp_Stream trans_fun1 ((input_fun1 \<circ> input) \<odot>\<^sub>i k1) c1 \<div>\<^bsub>il\<^esub> k1) i))
    (localState2 ((i_Exec_Comp_Stream trans_fun2 ((input_fun2 \<circ> input) \<odot>\<^sub>i k2) c2 \<div>\<^bsub>il\<^esub> k2) i))"
apply (simp add: i_shrink_last_nth i_Exec_Stream_nth i_expand_i_take_mod)
apply (rule f_Equiv_Exec_expand_shrink_equiv_state_set[of
  k1 k2 equiv_states localState1 c1 localState2 c2 A input_fun1 input_fun2 output_fun1 output_fun2])
apply (simp add: subset_trans[OF set_i_take_subset])+
done

lemma i_Equiv_Exec_Stream_expand_shrink_equiv_state: "
  \<lbrakk> 0 < k1; 0 < k2; equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m.
       Equiv_Exec
        m equiv_states localState1 localState2
        input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2
       (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
       (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2) \<rbrakk> \<Longrightarrow>
  equiv_states
    (localState1 ((i_Exec_Comp_Stream trans_fun1 ((input_fun1 \<circ> input) \<odot>\<^sub>i k1) c1 \<div>\<^bsub>il\<^esub> k1) i))
    (localState2 ((i_Exec_Comp_Stream trans_fun2 ((input_fun2 \<circ> input) \<odot>\<^sub>i k2) c2 \<div>\<^bsub>il\<^esub> k2) i))"
by (rule i_Equiv_Exec_Stream_expand_shrink_equiv_state_set[of k1 k2 equiv_states localState1 c1 localState2 c2 UNIV input_fun1 input_fun2 output_fun1 output_fun2], simp+)

lemma f_Equiv_Exec_Stream_expand_shrink_output_set_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m. \<lbrakk> set input0 \<subseteq> A; m \<in> A \<rbrakk> \<Longrightarrow>
       Equiv_Exec
         m equiv_states localState1 localState2
         input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2
         (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
         (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2);
    set input \<subseteq> A \<rbrakk> \<Longrightarrow>
  (map output_fun1 (
    f_Exec_Comp_Stream trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1)) \<div>\<^sub>f k1 =
  (map output_fun2 (
    f_Exec_Comp_Stream trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2)) \<div>\<^sub>f k2"
apply (subst list_eq_iff)
apply (clarsimp simp: f_shrink_length)
apply (simp del: last.simps f_Exec_Stream_Cons add: f_shrink_nth take_map drop_map f_Exec_Stream_take f_Exec_Stream_drop f_expand_take_mod f_expand_drop_mod take_first)
apply (frule_tac n=i in subset_trans[OF set_take_subset, rule_format])
apply (unfold atomize_all atomize_imp, intro allI impI)
apply (frule_tac x="take i input" in spec)
apply (drule_tac x="input ! i" in spec)
apply (erule impE, assumption)
apply (erule impE)
 apply (blast intro: nth_mem)
apply (simp del: last.simps f_Exec_Stream_Cons)
apply (rule Equiv_Exec_output_eqI[of equiv_states localState1 _ localState2 _ _ input_fun1 input_fun2])
 apply (case_tac i, simp)
 apply (simp add: take_map[symmetric] f_Exec_Stream_expand_shrink_last_nth_eq_f_Exec_Comp[symmetric])
 apply (frule Suc_lessD)
 apply (simp add: f_Equiv_Exec_Stream_expand_shrink_equiv_state_set[of k1 k2 equiv_states localState1 _ localState2 _ A input_fun1 input_fun2 output_fun1 output_fun2])
apply simp
done

lemma f_Equiv_Exec_Stream_expand_shrink_output_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m.
       Equiv_Exec
         m equiv_states localState1 localState2
         input_fun1 input_fun2 output_fun1 output_fun2
         trans_fun1 trans_fun2 k1 k2
         (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
         (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2) \<rbrakk> \<Longrightarrow>
  (map output_fun1 (
    f_Exec_Comp_Stream trans_fun1 (map input_fun1 input \<odot>\<^sub>f k1) c1)) \<div>\<^sub>f k1 =
  (map output_fun2 (
    f_Exec_Comp_Stream trans_fun2 (map input_fun2 input \<odot>\<^sub>f k2) c2)) \<div>\<^sub>f k2"
by (rule f_Equiv_Exec_Stream_expand_shrink_output_set_eq[of k1 k2 equiv_states localState1 _ localState2 _ UNIV], simp+)

lemma i_Equiv_Exec_Stream_expand_shrink_output_set_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m. \<lbrakk> set input0 \<subseteq> A; m \<in> A \<rbrakk> \<Longrightarrow>
       Equiv_Exec
         m equiv_states localState1 localState2
         input_fun1 input_fun2 output_fun1 output_fun2
         trans_fun1 trans_fun2 k1 k2
         (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
         (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2);
    range input \<subseteq> A \<rbrakk> \<Longrightarrow>
  (output_fun1 \<circ>
    i_Exec_Comp_Stream trans_fun1 ((input_fun1 \<circ> input) \<odot>\<^sub>i k1) c1) \<div>\<^sub>i k1 =
  (output_fun2 \<circ>
    i_Exec_Comp_Stream trans_fun2 ((input_fun2 \<circ> input) \<odot>\<^sub>i k2) c2) \<div>\<^sub>i k2"
apply (clarsimp simp: ilist_eq_iff, rename_tac i)
apply (simp del: last.simps f_Exec_Stream_Cons add: i_shrink_nth i_Exec_Stream_take i_Exec_Stream_drop i_expand_i_take_mod i_expand_i_drop_mod i_take_first map_one f_expand_one)
apply (rule Equiv_Exec_output_eqI[of
  equiv_states localState1 _ localState2 _ _
  input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2])
apply (rule f_Equiv_Exec_expand_shrink_equiv_state_set[of
  k1 k2 equiv_states localState1 _ localState2 _ A
  input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2])
apply (simp add: subset_trans[OF set_i_take_subset] subsetD[OF _ rangeI])+
done

lemma i_Equiv_Exec_Stream_expand_shrink_output_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    \<And>input0 m.
       Equiv_Exec
         m equiv_states localState1 localState2
         input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2
         (f_Exec_Comp trans_fun1 (map input_fun1 input0 \<odot>\<^sub>f k1) c1)
         (f_Exec_Comp trans_fun2 (map input_fun2 input0 \<odot>\<^sub>f k2) c2) \<rbrakk> \<Longrightarrow>
  (output_fun1 \<circ>
    i_Exec_Comp_Stream trans_fun1 ((input_fun1 \<circ> input) \<odot>\<^sub>i k1) c1) \<div>\<^sub>i k1 =
  (output_fun2 \<circ>
    i_Exec_Comp_Stream trans_fun2 ((input_fun2 \<circ> input) \<odot>\<^sub>i k2) c2) \<div>\<^sub>i k2"
apply (rule i_Equiv_Exec_Stream_expand_shrink_output_set_eq[of
  k1 k2 equiv_states localState1 c1 localState2 c2 UNIV
  input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2])
apply simp+
done


lemma f_Equiv_Exec_Stream_Acc_LocalState_set: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable_set A
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2;
      \<comment> \<open>\<open>equiv_states\<close> relation implies equivalent executions\<close>
      \<comment> \<open>not only at the beginning but also after processing an input\<close>
    set input \<subseteq> A;
    i < length input \<rbrakk> \<Longrightarrow>
  equiv_states
    (f_Exec_Comp_Stream_Acc_LocalState k1 localState1 trans_fun1 (map input_fun1 input) c1 ! i)
    (f_Exec_Comp_Stream_Acc_LocalState k2 localState2 trans_fun2 (map input_fun2 input) c2 ! i)"
apply (unfold f_Exec_Comp_Stream_Acc_LocalState_def Equiv_Exec_stable_set_def)
apply (simp add: f_shrink_last_map f_shrink_last_length)
apply (rule f_Equiv_Exec_Stream_expand_shrink_equiv_state_set[of
  k1 k2 equiv_states localState1 c1 localState2 c2 A
  input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 input, rule_format])
apply simp+
done

lemma f_Equiv_Exec_Stream_Acc_LocalState: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2;
      \<comment> \<open>\<open>equiv_states\<close> relation implies equivalent executions\<close>
      \<comment> \<open>not only at the beginning but also after processing an input\<close>
    i < length input \<rbrakk> \<Longrightarrow>
  equiv_states
    (f_Exec_Comp_Stream_Acc_LocalState k1 localState1 trans_fun1 (map input_fun1 input) c1 ! i)
    (f_Exec_Comp_Stream_Acc_LocalState k2 localState2 trans_fun2 (map input_fun2 input) c2 ! i)"
apply (rule f_Equiv_Exec_Stream_Acc_LocalState_set[where A=UNIV])
apply (simp add: Equiv_Exec_stable_set_UNIV)+
done

lemma f_Equiv_Exec_Stream_Acc_Output_set_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable_set A
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2 c1 c2;
    set input \<subseteq> A \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k1 output_fun1 trans_fun1 (map input_fun1 input) c1 =
  f_Exec_Comp_Stream_Acc_Output k2 output_fun2 trans_fun2 (map input_fun2 input) c2"
apply (unfold f_Exec_Comp_Stream_Acc_Output_def Equiv_Exec_stable_set_def)
apply (rule f_Equiv_Exec_Stream_expand_shrink_output_set_eq[of
  k1 k2 equiv_states localState1 c1 localState2 c2
  A input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 input])
apply simp+
done

lemma f_Equiv_Exec_Stream_Acc_Output_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k1 output_fun1 trans_fun1 (map input_fun1 input) c1 =
  f_Exec_Comp_Stream_Acc_Output k2 output_fun2 trans_fun2 (map input_fun2 input) c2"
apply (rule f_Equiv_Exec_Stream_Acc_Output_set_eq[of k1 k2 equiv_states localState1 c1 localState2 c2 UNIV])
apply (simp add: Equiv_Exec_stable_set_UNIV)+
done


lemma i_Equiv_Exec_Stream_Acc_LocalState_set: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable_set A
      equiv_states localState1 localState2 input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2;
    range input \<subseteq> A \<rbrakk> \<Longrightarrow>
  equiv_states
    (i_Exec_Comp_Stream_Acc_LocalState k1 localState1 trans_fun1 (input_fun1 \<circ> input) c1 i)
    (i_Exec_Comp_Stream_Acc_LocalState k2 localState2 trans_fun2 (input_fun2 \<circ> input) c2 i)"
apply (simp add: i_Exec_Stream_Acc_LocalState_nth_f_nth)
apply (rule f_Equiv_Exec_Stream_Acc_LocalState_set)
apply (simp add:  subset_trans[OF set_i_take_subset])+
done

lemma i_Equiv_Exec_Stream_Acc_LocalState: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2
      trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  equiv_states
    (i_Exec_Comp_Stream_Acc_LocalState k1 localState1 trans_fun1 (input_fun1 \<circ> input) c1 i)
    (i_Exec_Comp_Stream_Acc_LocalState k2 localState2 trans_fun2 (input_fun2 \<circ> input) c2 i)"
apply (rule i_Equiv_Exec_Stream_Acc_LocalState_set[where A=UNIV])
apply (simp add: Equiv_Exec_stable_set_UNIV)+
done

lemma i_Equiv_Exec_Stream_Acc_Output_set_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable_set A
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2 c1 c2;
    range input \<subseteq> A \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k1 output_fun1 trans_fun1 (input_fun1 \<circ> input) c1 =
  i_Exec_Comp_Stream_Acc_Output k2 output_fun2 trans_fun2 (input_fun2 \<circ> input) c2"
apply (clarsimp simp: ilist_eq_iff i_Exec_Stream_Acc_Output_nth_f_nth, rename_tac i)
apply (drule_tac n="Suc i" in subset_trans[OF set_i_take_subset, rule_format])
apply (simp add: f_Equiv_Exec_Stream_Acc_Output_set_eq[where equiv_states=equiv_states])
done

lemma i_Equiv_Exec_Stream_Acc_Output_eq: "
  \<lbrakk> 0 < k1; 0 < k2;
    equiv_states (localState1 c1) (localState2 c2);
    Equiv_Exec_stable
      equiv_states localState1 localState2
      input_fun1 input_fun2 output_fun1 output_fun2 trans_fun1 trans_fun2 k1 k2 c1 c2 \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k1 output_fun1 trans_fun1 (input_fun1 \<circ> input) c1 =
  i_Exec_Comp_Stream_Acc_Output k2 output_fun2 trans_fun2 (input_fun2 \<circ> input) c2"
apply (rule i_Equiv_Exec_Stream_Acc_Output_set_eq[of k1 k2 equiv_states localState1 c1 localState2 c2 UNIV])
apply (simp add: Equiv_Exec_stable_set_UNIV)+
done


subsubsection \<open>Idle states and accelerated execution\<close>

lemma f_Exec_Stream_Acc_LocalState__State_Idle_nth[rule_format]: "
  \<And>c i.
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n\<le>i. State_Idle localState output_fun trans_fun (
      f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c ! n);
    i < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c ! i =
  f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c ! i"
apply (frule length_greater_0_conv[THEN iffD1, OF gr_implies_gr0])
apply (simp only: f_Exec_Stream_Acc_LocalState_nth take_Suc_conv_app_nth)
apply (simp only: f_expand_snoc f_Exec_append)
apply (rule_tac s="\<NoMsg>\<^bsup>l - Suc 0\<^esup> @ \<NoMsg>\<^bsup>k-l\<^esup>" and t="\<NoMsg>\<^bsup>k - Suc 0\<^esup>" in subst)
 apply (simp add: replicate_le_diff2)
apply (subst append_Cons[symmetric])
apply (induct xs, simp)
apply (case_tac i)
 apply (simp add: f_Exec_Stream_Acc_LocalState_Cons f_Exec_State_Idle_append_replicate_NoMsg_state)
apply (rename_tac n)
apply (drule_tac x="f_Exec_Comp trans_fun (a # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c" in meta_spec)
apply (drule_tac x=n in meta_spec)
apply (simp del: f_Exec_Cons)
apply (frule length_greater_imp_not_empty)
apply (drule meta_mp)
 apply (simp add: f_Exec_Stream_Acc_LocalState_nth f_Exec_append)
apply (simp add: append_Cons[symmetric] f_expand_Cons f_Exec_append del: append_Cons)
apply (subgoal_tac "
  localState (f_Exec_Comp trans_fun (a # NoMsg\<^bsup>k - Suc 0\<^esup>) c) =
  localState (f_Exec_Comp trans_fun (a # NoMsg\<^bsup>l - Suc 0\<^esup>) c)")
 prefer 2
 apply (drule_tac x=0 in spec)
 apply (simp add: f_Exec_Stream_Acc_LocalState_Cons)
 apply (subst replicate_le_diff2[OF Suc_leI, symmetric], assumption+)
 apply (simp add: append_Cons[symmetric] f_Exec_append del: append_Cons)
 apply (rule f_Exec_State_Idle_replicate_NoMsg_state, assumption)
apply (case_tac "n = 0")
 apply (frule_tac
   ?c1.0="f_Exec_Comp trans_fun (a # NoMsg\<^bsup>k - Suc 0\<^esup>) c" and
   xs = "xs ! 0 # NoMsg\<^bsup>l - Suc 0\<^esup>" in f_Exec_Equal_State)
 apply simp+
apply (frule_tac
  ?c1.0="f_Exec_Comp trans_fun (a # NoMsg\<^bsup>k - Suc 0\<^esup>) c" and
  xs = "xs \<down> n \<odot>\<^sub>f k" in f_Exec_Equal_State)
apply (simp add: f_expand_not_empty_conv)+
done

corollary f_Exec_Stream_Acc_LocalState__State_Idle_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n<length xs. State_Idle localState output_fun trans_fun (
      f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c ! n) \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c =
  f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c"
apply (clarsimp simp: list_eq_iff)
apply (rule f_Exec_Stream_Acc_LocalState__State_Idle_nth)
apply simp_all
apply (drule_tac x=n in spec)
apply simp
done

lemma i_Exec_Stream_Acc_LocalState__State_Idle_nth[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n\<le>i. State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun input c n) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c i =
  i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun input c i"
apply (simp only: f_Exec_Stream_Acc_LocalState_nth_eq_i_nth[of _ _ "Suc i", symmetric])
apply (rule f_Exec_Stream_Acc_LocalState__State_Idle_nth)
apply simp_all
apply (drule_tac x=n in spec)
apply (simp add: f_Exec_Stream_Acc_LocalState_nth_eq_i_nth)
done

corollary i_Exec_Stream_Acc_LocalState__State_Idle_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n. State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun input c n) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c =
  i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun input c"
apply (clarsimp simp: ilist_eq_iff)
apply (rule i_Exec_Stream_Acc_LocalState__State_Idle_nth)
apply simp_all
apply (drule_tac x=n in spec)
apply simp
done

lemma f_Exec_Stream_Acc_Output__State_Idle_nth[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n\<le>i. State_Idle localState output_fun trans_fun (
      f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c ! n);
    i < length xs \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c ! i =
  f_Exec_Comp_Stream_Acc_Output l output_fun trans_fun xs c ! i"
apply (drule order_le_less[THEN iffD1], erule disjE)
 prefer 2
 apply simp
apply (frule zero_less_diff[of k l, THEN iffD2])
apply (frule length_greater_imp_not_empty)
apply (simp add: f_Exec_Stream_Acc_Output_nth del: f_Exec_Stream_Cons)
apply (subst replicate_le_diff2[OF Suc_leI, symmetric])
 apply (simp del: f_Exec_Stream_Cons)+
apply (subst append_Cons[symmetric])
apply (case_tac i)
 apply (drule_tac x=0 in spec)
 apply (simp add: f_Exec_Stream_Acc_LocalState_nth take_first f_expand_one del: last.simps f_Exec_Cons f_Exec_Stream_Cons append_Cons replicate.simps)
 apply (simp only: f_Exec_Stream_append map_append last_message_append)
 apply (rule if_P')
  apply (clarsimp simp: last_message_NoMsg_conv f_Exec_Stream_nth min_eqL simp del: last.simps f_Exec_Comp.simps append_Cons replicate.simps)
  apply (rule f_Exec_State_Idle_replicate_NoMsg_gr0_output)
  apply (simp del: last.simps f_Exec_Comp_Stream.simps append_Cons)+
apply (rename_tac n)
apply (simp only: f_Exec_Stream_append map_append last_message_append)
apply (subgoal_tac "
  localState (f_Exec_Comp trans_fun (xs \<down> Suc n \<odot>\<^sub>f k) c) =
  localState (f_Exec_Comp trans_fun (xs \<down> Suc n \<odot>\<^sub>f l) c)")
 prefer 2
 apply (simp add: f_Exec_Stream_Acc_LocalState_nth[symmetric])
 apply (rule f_Exec_Stream_Acc_LocalState__State_Idle_nth)
 apply simp+
 apply (rename_tac n, drule_tac x=n in spec, simp)
 apply simp
apply (rule if_P')
 apply (simp add: last_message_NoMsg_conv f_Exec_Stream_nth min_eqL del: f_Exec_Comp.simps replicate.simps)
 apply (clarify, rename_tac j)
 apply (frule_tac x="Suc n" in spec)
 apply (simp only: f_Exec_Stream_Acc_LocalState_nth)
 apply (rule_tac
   ?c1.0="f_Exec_Comp trans_fun (xs \<down> Suc n \<odot>\<^sub>f l) c"
   and ?c2.0="f_Exec_Comp trans_fun (xs \<down> Suc n \<odot>\<^sub>f k) c"
   in subst[OF f_Exec_Equal_State, rule_format])
  apply (simp del: f_Exec_Comp.simps replicate.simps)+
 apply (simp only: take_Suc_conv_app_nth f_expand_snoc f_Exec_append)
 apply (rule f_Exec_State_Idle_replicate_NoMsg_gr0_output, assumption)
 apply simp
apply (rule arg_cong[where f="\<lambda>x. last_message (map output_fun x)"])
apply (rule f_Exec_Stream_Equal_State, assumption+)
done

lemma f_Exec_Stream_Acc_Output__State_Idle_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n<length xs. State_Idle localState output_fun trans_fun (
      f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c ! n) \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c =
  f_Exec_Comp_Stream_Acc_Output l output_fun trans_fun xs c"
apply (clarsimp simp: list_eq_iff)
apply (rule f_Exec_Stream_Acc_Output__State_Idle_nth)
apply simp_all
apply (drule_tac x=n in spec)
apply simp
done

lemma i_Exec_Stream_Acc_Output__State_Idle_nth[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n\<le>i. State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun input c n) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c i =
  i_Exec_Comp_Stream_Acc_Output l output_fun trans_fun input c i"
apply (simp only: i_Exec_Stream_Acc_Output_nth_f_nth)
apply (rule f_Exec_Stream_Acc_Output__State_Idle_nth)
apply simp_all
apply (drule_tac x=n in spec)
apply (simp add: f_Exec_Stream_Acc_LocalState_nth_eq_i_nth)
done

lemma i_Exec_Stream_Acc_Output__State_Idle_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    \<forall>n. State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun input c n) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c =
  i_Exec_Comp_Stream_Acc_Output l output_fun trans_fun input c"
apply (clarsimp simp: ilist_eq_iff)
apply (rule i_Exec_Stream_Acc_Output__State_Idle_nth)
apply simp_all
apply (drule_tac x=n in spec)
apply simp
done


text \<open>
  When a certain number @{term l} of steps suffices to reach
  an idle state from any other idle state,
  than for any acceleration factor @{term "k \<ge> l"}
  the accelerated processing of every input message
  will be finished in an idle state.\<close>
lemma f_Exec_Stream_Acc_LocalState__State_Idle_all[rule_format]: "
  \<And>c xs. \<lbrakk> 0 < l; l \<le> k;
    State_Idle localState output_fun trans_fun (localState c);
    \<forall>c m. State_Idle localState output_fun trans_fun (localState c) \<longrightarrow>
      State_Idle localState output_fun trans_fun (
        localState (f_Exec_Comp trans_fun (m # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c));
    i < length xs \<rbrakk> \<Longrightarrow>
  State_Idle localState output_fun trans_fun (
    f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c ! i)"
apply (frule length_greater_imp_not_empty)
apply (subgoal_tac "
  State_Idle localState output_fun trans_fun (
    localState (f_Exec_Comp trans_fun (hd xs # NoMsg\<^bsup>k - Suc 0\<^esup>) c))")
 prefer 2
 apply (drule_tac x=c in spec, drule_tac x="hd xs" in spec)
 apply (rule subst[OF replicate_le_diff2[OF Suc_leI], of 0 l k], assumption+)
 apply (simp add: f_Exec_append f_Exec_State_Idle_replicate_NoMsg_state)
apply (induct i)
 apply (simp add: f_Exec_Stream_Acc_LocalState_nth take_first hd_eq_first)
apply (drule_tac x="f_Exec_Comp trans_fun (hd xs # NoMsg\<^bsup>k - Suc 0\<^esup>) c" in meta_spec)
apply (drule_tac x="tl xs" in meta_spec)
apply (subgoal_tac "i < length (tl xs) \<and> tl xs \<noteq> []", elim conjE)
 prefer 2
 apply (simp add: length_greater_0_conv[symmetric] del: length_greater_0_conv)
apply (simp add: f_Exec_Stream_Acc_LocalState_nth)
apply (rule_tac n="Suc i" in ssubst[OF take_Suc, rule_format], assumption)
apply (simp add: append_Cons[symmetric] f_Exec_append del: append_Cons)
apply (drule meta_mp)
 apply (drule_tac x="f_Exec_Comp trans_fun (hd xs # NoMsg\<^bsup>k - Suc 0\<^esup>) c" in spec)
 apply (drule mp, simp)
 apply (drule_tac x="hd (tl xs)" in spec)
 apply (subst replicate_le_diff2[OF Suc_leI, of 0 l k, symmetric], simp+)
 apply (simp add: f_Exec_append f_Exec_State_Idle_replicate_NoMsg_state)
apply (simp add: f_Exec_Stream_Acc_LocalState_nth)
done

lemma i_Exec_Stream_Acc_LocalState__State_Idle_all[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k;
    State_Idle localState output_fun trans_fun (localState c);
    \<forall>c m. State_Idle localState output_fun trans_fun (localState c) \<longrightarrow>
      State_Idle localState output_fun trans_fun (
        localState (f_Exec_Comp trans_fun (m # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c)) \<rbrakk> \<Longrightarrow>
  State_Idle localState output_fun trans_fun (
    i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c i)"
apply (simp only: i_Exec_Stream_Acc_LocalState_nth_f_nth)
apply (rule f_Exec_Stream_Acc_LocalState__State_Idle_all)
apply simp_all
apply (rename_tac c' m, drule_tac x=c' in spec)
apply simp
done

lemma f_Exec_Stream_Acc_Output__State_Idle_all_imp_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    State_Idle localState output_fun trans_fun (localState c);
    \<forall>c m. State_Idle localState output_fun trans_fun (localState c) \<longrightarrow>
      State_Idle localState output_fun trans_fun (
        localState (f_Exec_Comp trans_fun (m # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c)) \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_Output k output_fun trans_fun xs c =
  f_Exec_Comp_Stream_Acc_Output l output_fun trans_fun xs c"
apply (rule f_Exec_Stream_Acc_Output__State_Idle_eq, assumption+)
apply (simp add: f_Exec_Stream_Acc_LocalState__State_Idle_all)
done

lemma i_Exec_Stream_Acc_Output__State_Idle_all_imp_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    State_Idle localState output_fun trans_fun (localState c);
    \<forall>c m. State_Idle localState output_fun trans_fun (localState c) \<longrightarrow>
      State_Idle localState output_fun trans_fun (
        localState (f_Exec_Comp trans_fun (m # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c)) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c =
  i_Exec_Comp_Stream_Acc_Output l output_fun trans_fun input c"
apply (rule i_Exec_Stream_Acc_Output__State_Idle_eq, assumption+)
apply (simp add: i_Exec_Stream_Acc_LocalState__State_Idle_all)
done

lemma f_Exec_Stream_Acc_LocalState__State_Idle_all_imp_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    State_Idle localState output_fun trans_fun (localState c);
    \<forall>c m. State_Idle localState output_fun trans_fun (localState c) \<longrightarrow>
      State_Idle localState output_fun trans_fun (
        localState (f_Exec_Comp trans_fun (m # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c)) \<rbrakk> \<Longrightarrow>
  f_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c =
  f_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c"
apply (rule f_Exec_Stream_Acc_LocalState__State_Idle_eq, assumption+)
apply (rule f_Exec_Stream_Acc_LocalState__State_Idle_all)
apply simp+
done

lemma i_Exec_Stream_Acc_LocalState__State_Idle_all_imp_eq[rule_format]: "
  \<lbrakk> 0 < l; l \<le> k; Exec_Equal_State localState trans_fun;
    State_Idle localState output_fun trans_fun (localState c);
    \<forall>c m. State_Idle localState output_fun trans_fun (localState c) \<longrightarrow>
      State_Idle localState output_fun trans_fun (
        localState (f_Exec_Comp trans_fun (m # \<NoMsg>\<^bsup>l - Suc 0\<^esup>) c)) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun xs c =
  i_Exec_Comp_Stream_Acc_LocalState l localState trans_fun xs c"
apply (rule i_Exec_Stream_Acc_LocalState__State_Idle_eq, assumption+)
apply (rule i_Exec_Stream_Acc_LocalState__State_Idle_all)
apply simp+
done


text \<open>Converting inputs\<close>

lemma f_Exec_input_map: "\<And>c.
  f_Exec_Comp trans_fun (map f xs) c = f_Exec_Comp (trans_fun \<circ> f) xs c"
by (induct xs, simp+)
lemma f_Exec_Stream_input_map: "
  f_Exec_Comp_Stream trans_fun (map f xs) c =
  f_Exec_Comp_Stream (trans_fun \<circ> f) xs c"
by (simp add: list_eq_iff f_Exec_Stream_nth take_map f_Exec_input_map)
lemma i_Exec_Stream_input_map: "
  i_Exec_Comp_Stream trans_fun (f \<circ> input) c =
  i_Exec_Comp_Stream (trans_fun \<circ> f) input c"
by (simp add: ilist_eq_iff i_Exec_Stream_nth f_Exec_input_map)

end
