(* Author: Tobias Nipkow *)

section "Interval Analysis"

theory Abs_Int2_ivl
imports Abs_Int2 "HOL-IMP.Abs_Int_Tests"
begin

datatype ivl = I "int option" "int option"

definition "\<gamma>_ivl i = (case i of
  I (Some l) (Some h) \<Rightarrow> {l..h} |
  I (Some l) None \<Rightarrow> {l..} |
  I None (Some h) \<Rightarrow> {..h} |
  I None None \<Rightarrow> UNIV)"

abbreviation I_Some_Some :: "int \<Rightarrow> int \<Rightarrow> ivl"  ("{_\<dots>_}") where
"{lo\<dots>hi} == I (Some lo) (Some hi)"
abbreviation I_Some_None :: "int \<Rightarrow> ivl"  ("{_\<dots>}") where
"{lo\<dots>} == I (Some lo) None"
abbreviation I_None_Some :: "int \<Rightarrow> ivl"  ("{\<dots>_}") where
"{\<dots>hi} == I None (Some hi)"
abbreviation I_None_None :: "ivl"  ("{\<dots>}") where
"{\<dots>} == I None None"

definition "num_ivl n = {n\<dots>n}"

fun in_ivl :: "int \<Rightarrow> ivl \<Rightarrow> bool" where
"in_ivl k (I (Some l) (Some h)) \<longleftrightarrow> l \<le> k \<and> k \<le> h" |
"in_ivl k (I (Some l) None) \<longleftrightarrow> l \<le> k" |
"in_ivl k (I None (Some h)) \<longleftrightarrow> k \<le> h" |
"in_ivl k (I None None) \<longleftrightarrow> True"

instantiation option :: (plus)plus
begin

fun plus_option where
"Some x + Some y = Some(x+y)" |
"_ + _ = None"

instance ..

end

definition empty where "empty = {1\<dots>0}"

fun is_empty where
"is_empty {l\<dots>h} = (h<l)" |
"is_empty _ = False"

lemma [simp]: "is_empty(I l h) =
  (case l of Some l \<Rightarrow> (case h of Some h \<Rightarrow> h<l | None \<Rightarrow> False) | None \<Rightarrow> False)"
by(auto split:option.split)

lemma [simp]: "is_empty i \<Longrightarrow> \<gamma>_ivl i = {}"
by(auto simp add: \<gamma>_ivl_def split: ivl.split option.split)

definition "plus_ivl i1 i2 = (if is_empty i1 | is_empty i2 then empty else
  case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow> I (l1+l2) (h1+h2))"

instantiation ivl :: SL_top
begin

definition le_option :: "bool \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> bool" where
"le_option pos x y =
 (case x of (Some i) \<Rightarrow> (case y of Some j \<Rightarrow> i\<le>j | None \<Rightarrow> pos)
  | None \<Rightarrow> (case y of Some j \<Rightarrow> \<not>pos | None \<Rightarrow> True))"

fun le_aux where
"le_aux (I l1 h1) (I l2 h2) = (le_option False l2 l1 & le_option True h1 h2)"

definition le_ivl where
"i1 \<sqsubseteq> i2 =
 (if is_empty i1 then True else
  if is_empty i2 then False else le_aux i1 i2)"

definition min_option :: "bool \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> int option" where
"min_option pos o1 o2 = (if le_option pos o1 o2 then o1 else o2)"

definition max_option :: "bool \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> int option" where
"max_option pos o1 o2 = (if le_option pos o1 o2 then o2 else o1)"

definition "i1 \<squnion> i2 =
 (if is_empty i1 then i2 else if is_empty i2 then i1
  else case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow>
          I (min_option False l1 l2) (max_option True h1 h2))"

definition "\<top> = {\<dots>}"

instance
proof (standard, goal_cases)
  case (1 x) thus ?case
    by(cases x, simp add: le_ivl_def le_option_def split: option.split)
next
  case (2 x y z) thus ?case
    by(cases x, cases y, cases z, auto simp: le_ivl_def le_option_def split: option.splits if_splits)
next
  case (3 x y) thus ?case
    by(cases x, cases y, simp add: le_ivl_def join_ivl_def le_option_def min_option_def max_option_def split: option.splits)
next
  case (4 x y) thus ?case
    by(cases x, cases y, simp add: le_ivl_def join_ivl_def le_option_def min_option_def max_option_def split: option.splits)
next
  case (5 x y z) thus ?case
    by(cases x, cases y, cases z, auto simp add: le_ivl_def join_ivl_def le_option_def min_option_def max_option_def split: option.splits if_splits)
next
  case (6 x) thus ?case
    by(cases x, simp add: Top_ivl_def le_ivl_def le_option_def split: option.split)
qed

end


instantiation ivl :: L_top_bot
begin

definition "i1 \<sqinter> i2 = (if is_empty i1 \<or> is_empty i2 then empty else
  case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow>
    I (max_option False l1 l2) (min_option True h1 h2))"

definition "\<bottom> = empty"

instance
proof (standard, goal_cases)
  case 1 thus ?case
    by (simp add:meet_ivl_def empty_def le_ivl_def le_option_def max_option_def min_option_def split: ivl.splits option.splits)
next
  case 2 thus ?case
    by (simp add: empty_def meet_ivl_def le_ivl_def le_option_def max_option_def min_option_def split: ivl.splits option.splits)
next
  case (3 x y z) thus ?case
    by (cases x, cases y, cases z, auto simp add: le_ivl_def meet_ivl_def empty_def le_option_def max_option_def min_option_def split: option.splits if_splits)
next
  case (4 x) show ?case by(cases x, simp add: bot_ivl_def empty_def le_ivl_def)
qed

end

instantiation option :: (minus)minus
begin

fun minus_option where
"Some x - Some y = Some(x-y)" |
"_ - _ = None"

instance ..

end

definition "minus_ivl i1 i2 = (if is_empty i1 | is_empty i2 then empty else
  case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow> I (l1-h2) (h1-l2))"

lemma gamma_minus_ivl:
  "n1 : \<gamma>_ivl i1 \<Longrightarrow> n2 : \<gamma>_ivl i2 \<Longrightarrow> n1-n2 : \<gamma>_ivl(minus_ivl i1 i2)"
by(auto simp add: minus_ivl_def \<gamma>_ivl_def split: ivl.splits option.splits)

definition "filter_plus_ivl i i1 i2 = (\<^cancel>\<open>if is_empty i then empty else\<close>
  i1 \<sqinter> minus_ivl i i2, i2 \<sqinter> minus_ivl i i1)"

fun filter_less_ivl :: "bool \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl * ivl" where
"filter_less_ivl res (I l1 h1) (I l2 h2) =
  (if is_empty(I l1 h1) \<or> is_empty(I l2 h2) then (empty, empty) else
   if res
   then (I l1 (min_option True h1 (h2 - Some 1)),
         I (max_option False (l1 + Some 1) l2) h2)
   else (I (max_option False l1 l2) h1, I l2 (min_option True h1 h2)))"

global_interpretation Val_abs
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
proof (standard, goal_cases)
  case 1 thus ?case
    by(auto simp: \<gamma>_ivl_def le_ivl_def le_option_def split: ivl.split option.split if_splits)
next
  case 2 show ?case by(simp add: \<gamma>_ivl_def Top_ivl_def)
next
  case 3 thus ?case by(simp add: \<gamma>_ivl_def num_ivl_def)
next
  case 4 thus ?case
    by(auto simp add: \<gamma>_ivl_def plus_ivl_def split: ivl.split option.splits)
qed

global_interpretation Val_abs1_gamma
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
defines aval_ivl = aval'
proof (standard, goal_cases)
  case 1 thus ?case
    by(auto simp add: \<gamma>_ivl_def meet_ivl_def empty_def min_option_def max_option_def split: ivl.split option.split)
next
  case 2 show ?case by(auto simp add: bot_ivl_def \<gamma>_ivl_def empty_def)
qed

lemma mono_minus_ivl:
  "i1 \<sqsubseteq> i1' \<Longrightarrow> i2 \<sqsubseteq> i2' \<Longrightarrow> minus_ivl i1 i2 \<sqsubseteq> minus_ivl i1' i2'"
apply(auto simp add: minus_ivl_def empty_def le_ivl_def le_option_def split: ivl.splits)
  apply(simp split: option.splits)
 apply(simp split: option.splits)
apply(simp split: option.splits)
done


global_interpretation Val_abs1
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
proof (standard, goal_cases)
  case 1 thus ?case
    by (simp add: \<gamma>_ivl_def split: ivl.split option.split)
next
  case 2 thus ?case
    by(auto simp add: filter_plus_ivl_def)
      (metis gamma_minus_ivl add_diff_cancel add.commute)+
next
  case (3 _ _ a1 a2) thus ?case
    by(cases a1, cases a2,
      auto simp: \<gamma>_ivl_def min_option_def max_option_def le_option_def split: if_splits option.splits)
qed

global_interpretation Abs_Int1
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
defines afilter_ivl = afilter
and bfilter_ivl = bfilter
and step_ivl = step'
and AI_ivl = AI
and aval_ivl' = aval''
..


text\<open>Monotonicity:\<close>

global_interpretation Abs_Int1_mono
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
proof (standard, goal_cases)
  case 1 thus ?case
    by(auto simp: plus_ivl_def le_ivl_def le_option_def empty_def split: if_splits ivl.splits option.splits)
next
  case 2 thus ?case
    by(auto simp: filter_plus_ivl_def le_prod_def mono_meet mono_minus_ivl)
next
  case (3 a1 b1 a2 b2) thus ?case
    apply(cases a1, cases b1, cases a2, cases b2, auto simp: le_prod_def)
    by(auto simp add: empty_def le_ivl_def le_option_def min_option_def max_option_def split: option.splits)
qed


subsection "Tests"

value "show_acom_opt (AI_ivl test1_ivl)"

text\<open>Better than \<open>AI_const\<close>:\<close>
value "show_acom_opt (AI_ivl test3_const)"
value "show_acom_opt (AI_ivl test4_const)"
value "show_acom_opt (AI_ivl test6_const)"

value "show_acom_opt (AI_ivl test2_ivl)"
value "show_acom (((step_ivl \<top>)^^0) (\<bottom>\<^sub>c test2_ivl))"
value "show_acom (((step_ivl \<top>)^^1) (\<bottom>\<^sub>c test2_ivl))"
value "show_acom (((step_ivl \<top>)^^2) (\<bottom>\<^sub>c test2_ivl))"

text\<open>Fixed point reached in 2 steps. Not so if the start value of x is known:\<close>

value "show_acom_opt (AI_ivl test3_ivl)"
value "show_acom (((step_ivl \<top>)^^0) (\<bottom>\<^sub>c test3_ivl))"
value "show_acom (((step_ivl \<top>)^^1) (\<bottom>\<^sub>c test3_ivl))"
value "show_acom (((step_ivl \<top>)^^2) (\<bottom>\<^sub>c test3_ivl))"
value "show_acom (((step_ivl \<top>)^^3) (\<bottom>\<^sub>c test3_ivl))"
value "show_acom (((step_ivl \<top>)^^4) (\<bottom>\<^sub>c test3_ivl))"

text\<open>Takes as many iterations as the actual execution. Would diverge if
loop did not terminate. Worse still, as the following example shows: even if
the actual execution terminates, the analysis may not. The value of y keeps
decreasing as the analysis is iterated, no matter how long:\<close>

value "show_acom (((step_ivl \<top>)^^50) (\<bottom>\<^sub>c test4_ivl))"

text\<open>Relationships between variables are NOT captured:\<close>
value "show_acom_opt (AI_ivl test5_ivl)"

text\<open>Again, the analysis would not terminate:\<close>
value "show_acom (((step_ivl \<top>)^^50) (\<bottom>\<^sub>c test6_ivl))"

end
