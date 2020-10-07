(*  Title:      JinjaThreads/Compiler/ListIndex.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Indexing variables in variable lists\<close>

theory ListIndex imports Main begin

text\<open>In order to support local variables and arbitrarily nested
blocks, the local variables are arranged as an indexed list. The
outermost local variable (``this'') is the first element in the list,
the most recently created local variable the last element. When
descending into a block structure, a corresponding list @{term Vs} of
variable names is maintained. To find the index of some variable
@{term V}, we have to find the index of the \emph{last} occurrence of
@{term V} in @{term Vs}. This is what @{term index} does:\<close>

primrec index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
where
  "index [] y = 0"
| "index (x#xs) y =
  (if x=y then if x \<in> set xs then index xs y + 1 else 0 else index xs y + 1)"

definition hidden :: "'a list \<Rightarrow> nat \<Rightarrow> bool"
where "hidden xs i  \<equiv>  i < size xs \<and> xs!i \<in> set(drop (i+1) xs)"

subsection \<open>@{term index}\<close>

lemma [simp]: "index (xs @ [x]) x = size xs"
(*<*)by(induct xs) simp_all(*>*)


lemma [simp]: "(index (xs @ [x]) y = size xs) = (x = y)"
(*<*)by(induct xs) auto(*>*)


lemma [simp]: "x \<in> set xs \<Longrightarrow> xs ! index xs x = x"
(*<*)by(induct xs) auto(*>*)


lemma [simp]: "x \<notin> set xs \<Longrightarrow> index xs x = size xs"
(*<*)by(induct xs) auto(*>*)


lemma index_size_conv[simp]: "(index xs x = size xs) = (x \<notin> set xs)"
(*<*)by(induct xs) auto(*>*)


lemma size_index_conv[simp]: "(size xs = index xs x) = (x \<notin> set xs)"
(*<*)by(induct xs) auto(*>*)


lemma "(index xs x < size xs) = (x \<in> set xs)"
(*<*)by(induct xs) auto(*>*)


lemma [simp]: "\<lbrakk> y \<in> set xs; x \<noteq> y \<rbrakk> \<Longrightarrow> index (xs @ [x]) y = index xs y"
(*<*)by(induct xs) auto(*>*)


lemma index_less_size[simp]: "x \<in> set xs \<Longrightarrow> index xs x < size xs"
(*<*)
apply(induct xs)
 apply simp
apply(fastforce)
done
(*>*)

lemma index_less_aux: "\<lbrakk>x \<in> set xs; size xs \<le> n\<rbrakk> \<Longrightarrow> index xs x < n"
(*<*)
apply(subgoal_tac "index xs x < size xs")
apply(simp (no_asm_simp))
apply simp
done
(*>*)


lemma [simp]: "x \<in> set xs \<or> y \<in> set xs \<Longrightarrow> (index xs x = index xs y) = (x = y)"
(*<*)by (induct xs) auto(*>*)


lemma inj_on_index: "inj_on (index xs) (set xs)"
(*<*)by(simp add:inj_on_def)(*>*)


lemma index_drop: "\<And>x i. \<lbrakk> x \<in> set xs; index xs x < i \<rbrakk> \<Longrightarrow> x \<notin> set(drop i xs)"
(*<*)
apply(induct xs)
apply (auto simp:drop_Cons split:if_split_asm nat.splits dest:in_set_dropD)
done
(*>*)


subsection \<open>@{term hidden}\<close>

lemma hidden_index: "x \<in> set xs \<Longrightarrow> hidden (xs @ [x]) (index xs x)"
(*<*)
apply(auto simp add:hidden_def index_less_aux nth_append)
 apply(drule index_less_size)
 apply(simp del:index_less_size)
done
(*>*)


lemma hidden_inacc: "hidden xs i \<Longrightarrow> index xs x \<noteq> i"
(*<*)
apply(case_tac "x \<in> set xs")
apply(auto simp add:hidden_def index_less_aux nth_append index_drop)
done
(*>*)


lemma [simp]: "hidden xs i \<Longrightarrow> hidden (xs@[x]) i"
(*<*)by(auto simp add:hidden_def nth_append)(*>*)


lemma fun_upds_apply: "\<And>m ys.
  (m(xs[\<mapsto>]ys)) x =
  (let xs' = take (size ys) xs
   in if x \<in> set xs' then Some(ys ! index xs' x) else m x)"
(*<*)
apply(induct xs)
 apply (simp add:Let_def)
apply(case_tac ys)
 apply (simp add:Let_def)
apply (simp add:Let_def)
done
(*>*)


lemma map_upds_apply_eq_Some:
  "((m(xs[\<mapsto>]ys)) x = Some y) =
  (let xs' = take (size ys) xs
   in if x \<in> set xs' then ys ! index xs' x = y else m x = Some y)"
(*<*)by(simp add:fun_upds_apply Let_def)(*>*)


lemma map_upds_upd_conv_index:
  "\<lbrakk>x \<in> set xs; size xs \<le> size ys \<rbrakk>
  \<Longrightarrow> m(xs[\<mapsto>]ys)(x\<mapsto>y) = m(xs[\<mapsto>]ys[index xs x := y])"
(*<*)
apply(rule ext)
apply(simp add:fun_upds_apply index_less_aux eq_sym_conv Let_def)
done
(*>*)

lemma image_index:
  "A \<subseteq> set(xs@[x]) \<Longrightarrow> index (xs @ [x]) ` A =
  (if x \<in> A then insert (size xs) (index xs ` (A-{x})) else index xs ` A)"
(*<*)
apply(auto simp:image_def)
   apply(rule bexI)
    prefer 2 apply blast
   apply simp
  apply(rule ccontr)
  apply(erule_tac x=xa in ballE)
   prefer 2 apply blast
  apply(fastforce simp add:neq_commute)
 apply(subgoal_tac "x \<noteq> xa")
  prefer 2 apply blast
 apply(fastforce simp add:neq_commute)
apply(subgoal_tac "x \<noteq> xa")
 prefer 2 apply blast
apply(force)
done
(*>*)

lemma index_le_lengthD: "index xs x < length xs \<Longrightarrow> x \<in> set xs"
by(erule contrapos_pp)(simp)

lemma not_hidden_index_nth: "\<lbrakk> i < length Vs; \<not> hidden Vs i \<rbrakk> \<Longrightarrow> index Vs (Vs ! i) = i"
by(induct Vs arbitrary: i)(auto split: if_split_asm nat.split_asm simp add: nth_Cons hidden_def)

lemma hidden_snoc_nth:
  assumes len: "i < length Vs"
  shows "hidden (Vs @ [Vs ! i]) i"
proof(cases "hidden Vs i")
  case True thus ?thesis by simp
next
  case False
  with len have "index Vs (Vs ! i) = i" by(rule not_hidden_index_nth)
  moreover from len have "hidden (Vs @ [Vs ! i]) (index Vs (Vs ! i))"
    by(auto intro: hidden_index)
  ultimately show ?thesis by simp
qed

lemma map_upds_Some_eq_nth_index:
  assumes "[Vs [\<mapsto>] vs] V = Some v" "length Vs \<le> length vs"
  shows "vs ! index Vs V = v"
proof -
  from \<open>[Vs [\<mapsto>] vs] V = Some v\<close> have "V \<in> set Vs"
    by -(rule classical, auto)
  with \<open>[Vs [\<mapsto>] vs] V = Some v\<close> \<open>length Vs \<le> length vs\<close> show ?thesis
  proof(induct Vs arbitrary: vs)
    case Nil thus ?case by simp
  next
    case (Cons x xs ys)
    note IH = \<open>\<And>vs. \<lbrakk> [xs [\<mapsto>] vs] V = Some v; length xs \<le> length vs; V \<in> set xs \<rbrakk> \<Longrightarrow> vs ! index xs V = v\<close>
    from \<open>[x # xs [\<mapsto>] ys] V = Some v\<close> obtain y Ys where "ys = y # Ys" by(cases ys, auto)
    with \<open>length (x # xs) \<le> length ys\<close> have "length xs \<le> length Ys" by simp
    show ?case
    proof(cases "V \<in> set xs")
      case True
      with \<open>[x # xs [\<mapsto>] ys] V = Some v\<close> \<open>length xs \<le> length Ys\<close> \<open>ys = y # Ys\<close>
      have "[xs [\<mapsto>] Ys] V = Some v"
        apply(auto simp add: map_upds_def map_of_eq_None_iff set_zip image_Collect split: if_split_asm)
        apply(clarsimp simp add: in_set_conv_decomp)
        apply(hypsubst_thin)
        apply(erule_tac x="length ys" in allE)
        by(simp)
      with IH[OF this \<open>length xs \<le> length Ys\<close> True] \<open>ys = y # Ys\<close> True
      show ?thesis by(simp)
    next
      case False with \<open>V \<in> set (x # xs)\<close> have "x = V" by auto
      with False \<open>[x # xs [\<mapsto>] ys] V = Some v\<close> \<open>ys = y # Ys\<close> have "y = v"
        by(auto)
      with False \<open>x = V\<close> \<open>ys = y # Ys\<close> 
      show ?thesis by(simp)
    qed
  qed
qed

end
