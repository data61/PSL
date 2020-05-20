theory SestoftConf
imports Launchbury.Terms Launchbury.Substitution
begin

datatype stack_elem = Alts exp exp | Arg var | Upd var | Dummy var

instantiation stack_elem :: pt
begin
definition  "\<pi> \<bullet> x = (case x of (Alts e1 e2) \<Rightarrow> Alts (\<pi> \<bullet> e1) (\<pi> \<bullet> e2) | (Arg v) \<Rightarrow> Arg (\<pi> \<bullet> v) | (Upd v) \<Rightarrow> Upd (\<pi> \<bullet> v) | (Dummy v) \<Rightarrow> Dummy (\<pi> \<bullet> v))"
instance
  by standard (auto simp add: permute_stack_elem_def split:stack_elem.split)
end

lemma Alts_eqvt[eqvt]: "\<pi> \<bullet> (Alts e1 e2) = Alts (\<pi> \<bullet> e1) (\<pi> \<bullet> e2)"
  and Arg_eqvt[eqvt]: "\<pi> \<bullet> (Arg v) = Arg (\<pi> \<bullet> v)"
  and Upd_eqvt[eqvt]: "\<pi> \<bullet> (Upd v) = Upd (\<pi> \<bullet> v)"
  and Dummy_eqvt[eqvt]: "\<pi> \<bullet> (Dummy v) = Dummy (\<pi> \<bullet> v)"
  by (auto simp add: permute_stack_elem_def split:stack_elem.split)

lemma supp_Alts[simp]: "supp (Alts e1 e2) = supp e1 \<union> supp e2" unfolding supp_def by (auto simp add: Collect_imp_eq Collect_neg_eq)
lemma supp_Arg[simp]: "supp (Arg v) = supp v"  unfolding supp_def by auto
lemma supp_Upd[simp]: "supp (Upd v) = supp v"  unfolding supp_def by auto
lemma supp_Dummy[simp]: "supp (Dummy v) = supp v"  unfolding supp_def by auto
lemma fresh_Alts[simp]: "a \<sharp> Alts e1 e2 = (a \<sharp> e1 \<and> a \<sharp> e2)" unfolding fresh_def by auto
lemma fresh_star_Alts[simp]: "a \<sharp>* Alts e1 e2 = (a \<sharp>* e1 \<and> a \<sharp>* e2)" unfolding fresh_star_def by auto
lemma fresh_Arg[simp]: "a \<sharp> Arg v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Upd[simp]: "a \<sharp> Upd v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Dummy[simp]: "a \<sharp> Dummy v = a \<sharp> v" unfolding fresh_def by auto
lemma fv_Alts[simp]: "fv (Alts e1 e2) = fv e1 \<union> fv e2"  unfolding fv_def by auto
lemma fv_Arg[simp]: "fv (Arg v) = fv v"  unfolding fv_def by auto
lemma fv_Upd[simp]: "fv (Upd v) = fv v"  unfolding fv_def by auto
lemma fv_Dummy[simp]: "fv (Dummy v) = fv v"  unfolding fv_def by auto

instance stack_elem :: fs
  by standard (case_tac x, auto simp add: finite_supp)

type_synonym stack = "stack_elem list"

fun ap :: "stack \<Rightarrow> var set" where
  "ap [] = {}"
| "ap (Alts e1 e2 # S) = ap S"
| "ap (Arg x # S) = insert x (ap S)"
| "ap (Upd x # S) = ap S"
| "ap (Dummy x # S) = ap S"
fun upds :: "stack \<Rightarrow> var set" where
  "upds [] = {}"
| "upds (Alts e1 e2 # S) = upds S"
| "upds (Upd x # S) = insert x (upds S)"
| "upds (Arg x # S) = upds S"
| "upds (Dummy x # S) = upds S"
fun dummies :: "stack \<Rightarrow> var set" where
  "dummies [] = {}"
| "dummies (Alts e1 e2 # S) = dummies S"
| "dummies (Upd x # S) = dummies S"
| "dummies (Arg x # S) = dummies S"
| "dummies (Dummy x # S) = insert x (dummies S)"
fun flattn :: "stack \<Rightarrow> var list" where
  "flattn [] = []"
| "flattn (Alts e1 e2 # S) = fv_list e1 @ fv_list e2 @ flattn S"
| "flattn (Upd x # S) = x # flattn S"
| "flattn (Arg x # S) = x # flattn S"
| "flattn (Dummy x # S) = x # flattn S"
fun upds_list :: "stack \<Rightarrow> var list" where
  "upds_list [] = []"
| "upds_list (Alts e1 e2 # S) = upds_list S"
| "upds_list (Upd x # S) = x # upds_list S"
| "upds_list (Arg x # S) = upds_list S"
| "upds_list (Dummy x # S) = upds_list S"

lemma set_upds_list[simp]:
  "set (upds_list S) = upds S"
  by (induction S rule: upds_list.induct) auto

lemma ups_fv_subset: "upds S \<subseteq> fv S"
  by (induction S rule: upds.induct) auto
lemma fresh_distinct_ups: "atom ` V \<sharp>* S \<Longrightarrow> V \<inter> upds S = {}"
   by (auto dest!: fresh_distinct_fv subsetD[OF ups_fv_subset])
lemma ap_fv_subset: "ap S \<subseteq> fv S"
  by (induction S rule: upds.induct) auto
lemma dummies_fv_subset: "dummies S \<subseteq> fv S"
  by (induction S rule: dummies.induct) auto

lemma fresh_flattn[simp]: "atom (a::var) \<sharp> flattn S \<longleftrightarrow> atom a \<sharp> S"
  by (induction S rule:flattn.induct) (auto simp add: fresh_Nil fresh_Cons fresh_append fresh_fv[OF finite_fv])
lemma fresh_star_flattn[simp]: "atom ` (as:: var set) \<sharp>* flattn S \<longleftrightarrow> atom ` as \<sharp>* S"
  by (auto simp add: fresh_star_def)
lemma fresh_upds_list[simp]: "atom a \<sharp> S \<Longrightarrow> atom (a::var) \<sharp> upds_list S"
  by (induction S rule:upds_list.induct) (auto simp add: fresh_Nil fresh_Cons fresh_append fresh_fv[OF finite_fv])
lemma fresh_star_upds_list[simp]: "atom ` (as:: var set) \<sharp>* S \<Longrightarrow> atom ` (as:: var set) \<sharp>* upds_list S"
  by (auto simp add: fresh_star_def)

lemma upds_append[simp]: "upds (S@S') = upds S \<union> upds S'"
  by (induction S rule: upds.induct) auto
lemma upds_map_Dummy[simp]: "upds (map Dummy l) = {}"
  by (induction l) auto

lemma upds_list_append[simp]: "upds_list (S@S') = upds_list S @ upds_list S'"
  by (induction S rule: upds.induct) auto
lemma upds_list_map_Dummy[simp]: "upds_list (map Dummy l) = []"
  by (induction l) auto

lemma dummies_append[simp]: "dummies (S@S') = dummies S \<union> dummies S'"
  by (induction S rule: dummies.induct) auto
lemma dummies_map_Dummy[simp]: "dummies (map Dummy l) = set l"
  by (induction l) auto

lemma map_Dummy_inj[simp]: "map Dummy l = map Dummy l' \<longleftrightarrow> l = l'"
  apply (induction l arbitrary: l')
  apply (case_tac [!] l')
  apply auto
  done

type_synonym conf = "(heap \<times> exp \<times> stack)"

inductive boring_step where
  "isVal e \<Longrightarrow> boring_step (\<Gamma>, e, Upd x # S)"


fun restr_stack :: "var set \<Rightarrow> stack \<Rightarrow> stack"
  where "restr_stack V [] = []"
      | "restr_stack V (Alts e1 e2 # S) = Alts e1 e2 # restr_stack V S"
      | "restr_stack V (Arg x # S) = Arg x # restr_stack V S"
      | "restr_stack V (Upd x # S) = (if x \<in> V then Upd x # restr_stack V S else restr_stack V S)"
      | "restr_stack V (Dummy x # S) = Dummy x # restr_stack V S"

lemma restr_stack_cong:
  "(\<And> x. x \<in> upds S \<Longrightarrow> x \<in> V \<longleftrightarrow> x \<in> V') \<Longrightarrow> restr_stack V S = restr_stack V' S"
  by (induction V S rule: restr_stack.induct) auto

lemma upds_restr_stack[simp]: "upds (restr_stack V S) = upds S \<inter> V"
  by (induction V S rule: restr_stack.induct) auto

lemma fresh_star_restict_stack[intro]:
  "a \<sharp>* S \<Longrightarrow> a \<sharp>* restr_stack V S"
  by (induction V S rule: restr_stack.induct) (auto simp add: fresh_star_Cons)

lemma restr_stack_restr_stack[simp]:
  "restr_stack V (restr_stack V' S) = restr_stack (V \<inter> V') S"
  by (induction V S rule: restr_stack.induct) auto

lemma Upd_eq_restr_stackD:
  assumes "Upd x # S = restr_stack V S'"
  shows "x \<in> V"
  using arg_cong[where f = upds, OF assms]
  by auto
lemma Upd_eq_restr_stackD2:
  assumes "restr_stack V S' = Upd x # S"
  shows "x \<in> V"
  using arg_cong[where f = upds, OF assms]
  by auto


lemma restr_stack_noop[simp]:
  "restr_stack V S = S \<longleftrightarrow> upds S \<subseteq> V"
  by (induction V S rule: restr_stack.induct)
     (auto dest: Upd_eq_restr_stackD2)
  

subsubsection \<open>Invariants of the semantics\<close>

inductive invariant :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "(\<And> x y. rel x y \<Longrightarrow> I x \<Longrightarrow> I y) \<Longrightarrow> invariant rel I"

lemmas invariant.intros[case_names step]

lemma invariantE:
  "invariant rel I \<Longrightarrow> rel x y \<Longrightarrow> I x \<Longrightarrow> I y" by (auto elim: invariant.cases)

lemma invariant_starE:
  "rtranclp rel x y \<Longrightarrow> invariant rel I \<Longrightarrow>  I x \<Longrightarrow> I y"
  by (induction rule: rtranclp.induct) (auto elim: invariantE)

lemma invariant_True:
  "invariant rel (\<lambda> _. True)"
by (auto intro: invariant.intros)

lemma invariant_conj:
  "invariant rel I1 \<Longrightarrow> invariant rel I2 \<Longrightarrow> invariant rel (\<lambda> x. I1 x \<and> I2 x)"
by (auto simp add: invariant.simps)


lemma rtranclp_invariant_induct[consumes 3, case_names base step]:
  assumes "r\<^sup>*\<^sup>* a b"
  assumes "invariant r I"
  assumes "I a"
  assumes "P a"
  assumes "(\<And>y z. r\<^sup>*\<^sup>* a y \<Longrightarrow> r y z \<Longrightarrow> I y \<Longrightarrow> I z \<Longrightarrow> P y \<Longrightarrow> P z)"
  shows "P b"
proof-
  from assms(1,3)
  have "P b" and "I b"
  proof(induction)
    case base
    from \<open>P a\<close> show "P a".
    from \<open>I a\<close> show "I a".
  next
    case (step y z)
    with \<open>I a\<close> have "P y" and "I y" by auto

    from assms(2) \<open>r y z\<close> \<open>I y\<close>
    show "I z" by (rule invariantE)

    from \<open>r\<^sup>*\<^sup>* a y\<close> \<open>r y z\<close> \<open>I y\<close> \<open>I z\<close> \<open>P y\<close>
    show "P z" by (rule assms(5))
  qed
  thus "P b" by-
qed


fun closed :: "conf \<Rightarrow> bool"
  where "closed (\<Gamma>, e, S) \<longleftrightarrow> fv (\<Gamma>, e, S) \<subseteq> domA \<Gamma> \<union> upds S"

fun heap_upds_ok where "heap_upds_ok (\<Gamma>,S) \<longleftrightarrow> domA \<Gamma> \<inter> upds S = {} \<and> distinct (upds_list S)"

abbreviation heap_upds_ok_conf :: "conf \<Rightarrow> bool"
  where "heap_upds_ok_conf c \<equiv> heap_upds_ok (fst c, snd (snd c))"

lemma heap_upds_okE: "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> upds S"
  by auto

lemma heap_upds_ok_Nil[simp]: "heap_upds_ok (\<Gamma>, [])" by auto
lemma heap_upds_ok_app1: "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (\<Gamma>,Arg x # S)" by auto
lemma heap_upds_ok_app2: "heap_upds_ok (\<Gamma>, Arg x # S) \<Longrightarrow> heap_upds_ok (\<Gamma>, S)" by auto
lemma heap_upds_ok_alts1: "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (\<Gamma>,Alts e1 e2 # S)" by auto
lemma heap_upds_ok_alts2: "heap_upds_ok (\<Gamma>, Alts e1 e2 # S) \<Longrightarrow> heap_upds_ok (\<Gamma>, S)" by auto

lemma heap_upds_ok_append:
  assumes "domA \<Delta> \<inter> upds S = {}"
  assumes "heap_upds_ok (\<Gamma>,S)"
  shows "heap_upds_ok (\<Delta>@\<Gamma>, S)"
  using assms
  unfolding heap_upds_ok.simps
  by auto

lemma heap_upds_ok_let:
  assumes "atom ` domA \<Delta> \<sharp>* S"
  assumes "heap_upds_ok (\<Gamma>, S)"
  shows "heap_upds_ok (\<Delta> @ \<Gamma>, S)"
using assms(2) fresh_distinct_fv[OF assms(1)]
by (auto intro: heap_upds_ok_append dest: subsetD[OF ups_fv_subset])

lemma heap_upds_ok_to_stack:
  "x \<in> domA \<Gamma> \<Longrightarrow> heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (delete x \<Gamma>, Upd x #S)"
  by (auto)

lemma heap_upds_ok_to_stack':
  "map_of \<Gamma> x = Some e \<Longrightarrow> heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (delete x \<Gamma>, Upd x #S)"
  by (metis Domain.DomainI domA_def fst_eq_Domain heap_upds_ok_to_stack map_of_SomeD)

lemma heap_upds_ok_delete:
  "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (delete x \<Gamma>, S)"
  by auto

lemma heap_upds_ok_restrictA:
  "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (restrictA V \<Gamma>, S)"
  by auto

lemma heap_upds_ok_restr_stack:
  "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (\<Gamma>, restr_stack V S)"
  apply auto
  by (induction V S rule: restr_stack.induct) auto

lemma heap_upds_ok_to_heap:
  "heap_upds_ok (\<Gamma>, Upd x # S) \<Longrightarrow> heap_upds_ok ((x,e) # \<Gamma>, S)"
  by auto

lemma heap_upds_ok_reorder:
  "x \<in> domA \<Gamma> \<Longrightarrow> heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok ((x,e) # delete x \<Gamma>, S)"
  by (intro heap_upds_ok_to_heap heap_upds_ok_to_stack)

lemma heap_upds_ok_upd:
"heap_upds_ok (\<Gamma>, Upd x # S) \<Longrightarrow> x \<notin> domA \<Gamma> \<and> x \<notin> upds S"
  by auto


lemmas heap_upds_ok_intros[intro] =
  heap_upds_ok_to_heap heap_upds_ok_to_stack heap_upds_ok_to_stack' heap_upds_ok_reorder
  heap_upds_ok_app1 heap_upds_ok_app2 heap_upds_ok_alts1 heap_upds_ok_alts2 heap_upds_ok_delete
  heap_upds_ok_restrictA heap_upds_ok_restr_stack
  heap_upds_ok_let
lemmas heap_upds_ok.simps[simp del]


end
