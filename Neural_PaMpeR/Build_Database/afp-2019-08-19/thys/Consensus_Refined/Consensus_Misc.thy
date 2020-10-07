(*<*)
theory Consensus_Misc
imports Main
begin
(*>*)

subsection \<open>Miscellaneous lemmas\<close>

method_setup clarsimp_all =
  \<open>Method.sections clasimp_modifiers >>
    K (SIMPLE_METHOD o CHANGED_PROP o PARALLEL_ALLGOALS o clarsimp_tac)\<close>
  "clarify simplified, all goals"

lemma div_Suc:
  "Suc m div n = (if Suc m mod n = 0 then Suc (m div n) else m div n)" (is "_ = ?rhs")
proof (cases "Suc m mod n = 0")
  case True
  then show ?thesis
    by simp (metis Zero_not_Suc diff_Suc_Suc div_geq minus_mod_eq_mult_div mod_Suc mod_less neq0_conv nonzero_mult_div_cancel_left)
next
  case False
  then show ?thesis
    by simp (metis diff_Suc_Suc div_eq_0_iff minus_mod_eq_mult_div mod_Suc neq0_conv nonzero_mult_div_cancel_left)
qed

definition flip where
  flip_def: "flip f \<equiv> \<lambda>x y. f y x"

lemma option_expand':
  "\<lbrakk>(option = None) = (option' = None); \<And>x y. \<lbrakk>option = Some x; option' = Some y\<rbrakk> \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> 
    option = option'"
  by(rule option.expand, auto)

(*********************************)
subsection \<open>Argmax\<close>
definition Max_by :: "('a \<Rightarrow> 'b :: linorder) \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "Max_by f S = (SOME x. x \<in> S \<and> f x = Max (f ` S))"

lemma Max_by_dest:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max_by f A \<in> A \<and> f (Max_by f A) = Max (f ` A)" (is "?P (Max_by f A)")
proof(simp only: Max_by_def some_eq_ex[where P="?P"])
  from assms have "finite (f ` A)" "f ` A \<noteq> {}" by auto
  from Max_in[OF this] show "\<exists>x. x \<in> A \<and> f x = Max (f ` A)"
    by (metis image_iff)
qed

lemma Max_by_in:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max_by f A \<in> A" using assms
  by(rule Max_by_dest[THEN conjunct1])

lemma Max_by_ge:
  assumes "finite A" "x \<in> A"
  shows "f x \<le> f (Max_by f A)"
proof-
  from assms(1) have fin_image: "finite (f ` A)" by simp
  from assms(2) have non_empty: "A \<noteq> {}" by auto
  have "f x \<in> f ` A" using assms(2) by simp
  from Max_ge[OF fin_image this] and Max_by_dest[OF assms(1) non_empty, of f] show ?thesis
    by(simp)
qed

lemma finite_UN_D:
  "finite (\<Union>S) \<Longrightarrow> \<forall>A \<in> S. finite A"
  by (metis Union_upper finite_subset)

lemma Max_by_eqI:
  assumes
    fin: "finite A"
    and "\<And>y. y \<in> A \<Longrightarrow> cmp_f y \<le> cmp_f x" 
    and in_X: "x \<in> A"
    and inj: "inj_on cmp_f A"
  shows "Max_by cmp_f A = x"
proof-
  have in_M: "Max_by cmp_f A \<in> A" using assms
    by(auto intro!: Max_by_in)
  hence "cmp_f (Max_by cmp_f A) \<le> cmp_f x" using assms 
    by auto
  also have "cmp_f x \<le> cmp_f (Max_by cmp_f A)"
    by (intro Max_by_ge assms)
  finally show ?thesis  using inj in_M in_X
    by(auto simp add: inj_on_def)
qed
    
lemma Max_by_Union_distrib:
  "\<lbrakk> finite A; A = \<Union>S; S \<noteq> {}; {} \<notin> S; inj_on cmp_f A \<rbrakk> \<Longrightarrow> 
    Max_by cmp_f A = Max_by cmp_f (Max_by cmp_f ` S)"
proof(rule Max_by_eqI, assumption)
  fix y
  assume assms: "finite A" "A = \<Union>S" "{} \<notin> S" "y \<in> A"
  then obtain B where B_def: "B \<in> S" "y \<in> B" by auto
  hence "cmp_f y \<le> cmp_f (Max_by cmp_f B)" using assms
    by (metis Max_by_ge finite_UN_D)
  also have "... \<le> cmp_f (Max_by cmp_f (Max_by cmp_f ` S))" using B_def(1) assms
    by (metis Max_by_ge finite_UnionD finite_imageI imageI)
  finally show "cmp_f y \<le> cmp_f (Max_by cmp_f (Max_by cmp_f ` S))" .
next
  assume assms: "finite A" "A = \<Union>S" "{} \<notin> S" "S \<noteq> {}"
  hence "Max_by cmp_f ` S \<noteq> {}" "finite (Max_by cmp_f ` S)"
    apply (metis image_is_empty)
    by (metis assms(1) assms(2) finite_UnionD finite_imageI)
  hence "Max_by cmp_f (Max_by cmp_f ` S) \<in> (Max_by cmp_f ` S)"
    by(blast intro!: Max_by_in)
  also have "(Max_by cmp_f ` S) \<subseteq> A"
  proof -
    have f1: "\<forall>v0 v1. (\<not> finite v0 \<or> v0 = {}) \<or> Max_by (v1::'a \<Rightarrow> 'b) v0 \<in> v0" using Max_by_in by blast
    have "\<forall>v1. v1 \<notin> S \<or> finite v1" using assms(1) assms(2) finite_UN_D by blast
    then obtain v2_13 :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where "Max_by cmp_f ` S \<subseteq> \<Union>S" using f1 assms(3) by blast
    thus "Max_by cmp_f ` S \<subseteq> A" using assms(2) by presburger
  qed
  finally show "Max_by cmp_f (Max_by cmp_f ` S) \<in> A" .
qed

lemma Max_by_UNION_distrib:
  "\<lbrakk>finite A; A = (\<Union>x\<in>S. f x); S \<noteq> {}; {} \<notin> f ` S; inj_on cmp_f A\<rbrakk> \<Longrightarrow> 
    Max_by cmp_f A = Max_by cmp_f (Max_by cmp_f ` (f ` S))"
  by(force intro!: Max_by_Union_distrib)

lemma Max_by_eta:
  "Max_by f = (\<lambda>S. (SOME x. x \<in> S \<and> f x = Max (f ` S)))"
  by(auto simp add: Max_by_def)

lemma Max_is_Max_by_id:
  "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> Max S = Max_by id S "
  apply(clarsimp simp add: Max_by_def)
  by (metis (mono_tags, lifting) Max_in someI_ex)

definition option_Max_by :: "('a \<Rightarrow> 'b :: linorder) \<Rightarrow> 'a set \<Rightarrow> 'a option" where
  "option_Max_by cmp_f A \<equiv> if A = {} then None else Some (Max_by cmp_f A)"

(*********************************)

subsection \<open>Function and map graphs\<close>

definition fun_graph where
  "fun_graph f = {(x, f x)|x. True}"

definition map_graph :: "('a, 'b)map \<Rightarrow> ('a \<times> 'b) set" where
  "map_graph f = {(x, y)|x y. (x, Some y) \<in> fun_graph f}"

lemma map_graph_mem[simp]:
  "((x, y) \<in> map_graph f) = (f x = Some y)"
  by(auto simp add: dom_def map_graph_def fun_graph_def)

lemma finite_fun_graph:
  "finite A \<Longrightarrow> finite (fun_graph f \<inter> (A \<times> UNIV))"
  apply(rule bij_betw_finite[where A=A and f="\<lambda>x. (x, f x)", THEN iffD1])
  by(auto simp add: fun_graph_def bij_betw_def inj_on_def)

lemma finite_map_graph:
  "finite A \<Longrightarrow> finite (map_graph f \<inter> (A \<times> UNIV))"
  by(force simp add: map_graph_def
    dest!: finite_fun_graph[where f=f]
    intro!: finite_surj[where A="fun_graph f \<inter> (A \<times> UNIV)" and f="apsnd the"] 
  )

lemma finite_dom_finite_map_graph:
  "finite (dom f) \<Longrightarrow> finite (map_graph f)"
  apply(simp add: dom_def map_graph_def fun_graph_def)
  apply(erule finite_surj[where f="\<lambda>x. (x, the (f x))"])
  apply(clarsimp simp add: image_def)
  by (metis option.sel)

(*******************************************************************)
lemma ran_map_addD:
  "x \<in> ran (m ++ f) \<Longrightarrow> x \<in> ran m \<or> x \<in> ran f"
  by(auto simp add: ran_def)

subsection \<open>Constant maps\<close>

definition const_map :: "'v \<Rightarrow> 'k set \<Rightarrow> ('k, 'v)map" where
  "const_map v S \<equiv> (\<lambda>_. Some v) |` S"

lemma const_map_empty[simp]:
  "const_map v {} = Map.empty"
  by(auto simp add: const_map_def)

lemma const_map_ran[simp]: "x \<in> ran (const_map v S) = (S \<noteq> {} \<and> x = v)"
  by(auto simp add: const_map_def ran_def restrict_map_def)

lemma const_map_is_None:
  "(const_map y A  x = None) = (x \<notin> A)"
  by(auto simp add: const_map_def restrict_map_def)

lemma const_map_is_Some:
  "(const_map y A x = Some z) = (z = y \<and> x \<in> A)"
  by(auto simp add: const_map_def restrict_map_def)

lemma const_map_in_set:
  "x \<in> A \<Longrightarrow> const_map v A x = Some v"
  by(auto simp add: const_map_def)

lemma const_map_notin_set:
  "x \<notin> A \<Longrightarrow> const_map v A x = None"
  by(auto simp add: const_map_def)

lemma dom_const_map:
  "dom (const_map v S) = S"
  by(auto simp add: const_map_def)

(*******************************************************************)
subsection \<open>Votes with maximum timestamps.\<close>
(*******************************************************************)

definition vote_set :: "('round \<Rightarrow> ('process, 'val)map) \<Rightarrow> 'process set \<Rightarrow> ('round \<times> 'val)set" where
  "vote_set vs Q \<equiv> {(r, v)|a r v. ((r, a), v) \<in> map_graph (case_prod vs) \<and> a \<in> Q}"

lemma inj_on_fst_vote_set:
  "inj_on fst (vote_set v_hist {p})"
  by(clarsimp simp add: inj_on_def vote_set_def)

lemma finite_vote_set:
  assumes "\<forall>r'\<ge>(r :: nat). v_hist r' = Map.empty"
    "finite S"
  shows "finite (vote_set v_hist S)"
proof-
  define vs where "vs = {((r, a), v)|r a v. ((r, a), v) \<in> map_graph (case_prod v_hist) \<and> a \<in> S}"
  have "vs
      = (\<Union>p\<in>S. ((\<lambda>(r, v). ((r, p), v)) ` (map_graph (\<lambda>r. v_hist r p))))"
      by(auto simp add: map_graph_def fun_graph_def vs_def)
  also have "... \<le> (\<Union>p\<in>S. (\<lambda>r. ((r, p), the (v_hist r p))) ` {0..<r})" 
    using assms(1)
    apply auto
    apply (auto simp add: map_graph_def fun_graph_def image_def)
    apply (metis le_less_linear option.distinct(1))
    done
  also note I=finite_subset[OF calculation] 
  have "finite vs"
    by(auto intro: I assms(2) nat_seg_image_imp_finite[where n=r])    
    
  thus ?thesis
    apply(clarsimp simp add: map_graph_def fun_graph_def vote_set_def vs_def)
    apply(erule finite_surj[where f="\<lambda>((r, a), v). (r, v)"])
    by(force simp add: image_def)
qed

definition mru_of_set 
  :: "('round :: linorder \<Rightarrow> ('process, 'val)map) \<Rightarrow> ('process set, 'round \<times> 'val)map" where
  "mru_of_set vs \<equiv> \<lambda>Q. option_Max_by fst (vote_set vs Q)"

definition process_mru 
  :: "('round :: linorder \<Rightarrow> ('process, 'val)map) \<Rightarrow> ('process, 'round \<times> 'val)map" where
  "process_mru vs \<equiv> \<lambda>a. mru_of_set vs {a}"

lemma process_mru_is_None:
  "(process_mru v_f a = None) = (vote_set v_f {a} = {})"
  by(auto simp add: process_mru_def mru_of_set_def option_Max_by_def)

lemma process_mru_is_Some:
  "(process_mru v_f a = Some rv) = (vote_set v_f {a} \<noteq> {} \<and> rv = Max_by fst (vote_set v_f {a}))"
  by(auto simp add: process_mru_def mru_of_set_def option_Max_by_def)

lemma vote_set_upd:
  "vote_set (v_hist(r := v_f)) {p} = 
      (if p \<in> dom v_f 
        then insert (r, the (v_f p))
        else id
      )
      (if v_hist r p = None
        then vote_set v_hist {p}
        else vote_set v_hist {p} - {(r, the (v_hist r p))}
      )
  "
  by(auto simp add: vote_set_def const_map_is_Some split: if_split_asm)

lemma finite_vote_set_upd:
  " finite (vote_set v_hist {a}) \<Longrightarrow> 
    finite (vote_set (v_hist(r := v_f)) {a})"
  by(simp add: vote_set_upd)

lemma vote_setD:
  "rv \<in> vote_set v_f {a} \<Longrightarrow> v_f (fst rv) a = Some (snd rv)"
  by(auto simp add: vote_set_def)

lemma process_mru_new_votes:
  assumes
    "\<forall>r' \<ge> (r :: nat). v_hist r' = Map.empty"
  shows 
    "process_mru (v_hist(r := v_f)) = 
    (process_mru v_hist ++ (\<lambda>p. map_option (Pair r) (v_f p)))"
proof(rule ext, rule option_expand')
  fix p
  show  
    "(process_mru (v_hist(r := v_f)) p = None) =
    ((process_mru v_hist ++ (\<lambda>p. map_option (Pair r) (v_f p))) p = None)" using assms
    by(force simp add: vote_set_def restrict_map_def  const_map_is_None process_mru_is_None)
next
  fix p rv rv'
  assume eqs:
    "process_mru (v_hist(r := v_f)) p = Some rv"
    "(process_mru v_hist ++ (\<lambda>p. map_option (Pair r) (v_f p))) p = Some rv'"
  moreover have "v_hist (r) p = None" using assms(1)
    by(auto)

  ultimately show "rv = rv'"  using eqs assms 
    by(auto simp add: map_add_Some_iff const_map_is_Some const_map_is_None 
      process_mru_is_Some vote_set_upd dest!: vote_setD intro!: Max_by_eqI
      finite_vote_set[OF assms]
      intro: ccontr inj_on_fst_vote_set)
qed


end
