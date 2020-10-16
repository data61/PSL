(* Title:      Containers/Examples/Containers_TwoSat_Ex.thy
   Author:     Andreas Lochbihler, ETH Zurich *)

section \<open>Implementation of 2SAT using Containers\<close>

theory Containers_TwoSat_Ex imports
  TwoSat_Ex
  Containers_DFS_Ex
begin

lemma abort_parametric [transfer_rule]: includes lifting_syntax shows (* Move to Isabelle distribution *)
  "((=) ===> ((=) ===> A) ===> A) Code.abort Code.abort"
unfolding Code.abort_def by transfer_prover


instantiation uprod :: (finite_UNIV) finite_UNIV begin
definition finite_UNIV_uprod :: "('a uprod, bool) phantom"
where "finite_UNIV_uprod = Phantom('a uprod) (of_phantom (finite_UNIV :: ('a, bool) phantom))"
instance by standard(auto simp add: finite_UNIV_uprod_def finite_UNIV)
end

instantiation uprod :: (card_UNIV) card_UNIV begin
definition card_UNIV_uprod :: "('a uprod, nat) phantom"
where "card_UNIV_uprod = (let n = of_phantom (card_UNIV :: ('a, nat) phantom) in Phantom('a uprod) (n * (n + 1) div 2))"
instance by standard(auto simp add: card_UNIV_uprod_def card_UNIV Let_def card_UNIV_uprod)
end

text \<open>
  To instantiate the @{class ceq} type class for @{typ "'a uprod"}, we must make a small detour.
  As @{typ "'a uprod"}'s type definition uses HOL equality, we cannot implement a new notion of 
  equality that is parametrised by the equality relation. Instead, we define the subtype of all binary
  relations that contains only @{term "(=)"}, and define the parametrised equality relation @{term uprod_ceq}
  on the subtype. Then, the instantiation can pass the equality relation from @{term "CEQ('a :: ceq)"}
  to @{term uprod_ceq} because the type class axioms ensure that the obtained relation is equivalent
  to @{term "(=)"}.
\<close>

typedef 'a equal = "{(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool}" by simp

setup_lifting type_definition_equal

lift_definition uprod_eq :: "'a equal \<Rightarrow> 'a uprod \<Rightarrow> 'a uprod \<Rightarrow> bool"
is "\<lambda>eq (a, b) (c, d). eq a c \<and> eq b d \<or> eq b c \<and> eq a d"
by auto

lemma uprod_eq_simps [simp, code]:
  "uprod_eq eq (Upair a b) (Upair c d) \<longleftrightarrow> 
   Rep_equal eq a c \<and> Rep_equal eq b d \<or> Rep_equal eq b c \<and> Rep_equal eq a d"
  supply Upair.transfer[transfer_rule] by transfer simp


lift_definition (code_dt) ceq_equal :: "'a :: ceq equal option" is "CEQ('a)"
apply(cases "CEQ('a)")
subgoal by(simp)
subgoal by(rule forw_subst[where P="pred_option _"], assumption)(simp (no_asm_use); simp add: ceq)
done

instantiation uprod :: (ceq) ceq begin
definition ceq_uprod
where "ceq_uprod = map_option uprod_eq ceq_equal"
instance
  apply(standard)
  apply(clarsimp simp add: ceq_uprod_def split: option.split_asm)
  apply transfer
  apply(auto simp add: fun_eq_iff)
  done
end

text \<open>
  For comparison, we do a similar trick as for @{class ceq}.
\<close>

typedef 'a compare = "{f :: 'a comparator. comparator f}"
proof -
  have "partial_order_on UNIV {(x, y). x = y}"
    by(simp add: partial_order_on_def preorder_on_def refl_on_def trans_def antisym_def)
  then obtain ord :: "('a \<times> 'a) set" where lin: "linear_order ord"
    by(rule porder_extend_to_linorder)
  define f :: "'a comparator" where
    "f x y = (if (x, y) \<in> ord \<and> (y, x) \<in> ord then Eq else if (x, y) \<in> ord then Lt else Gt)" for x y
  have "comparator f"
  proof
    show "invert_order (f x y) = f y x" for x y using lin
      by(cases "x = y")(auto simp add: f_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def total_on_def)
    show "x = y" if "f x y = Eq" for x y using that lin
      by(auto simp add: f_def linear_order_on_def partial_order_on_def antisym_def split: if_split_asm)
    show "f x z = Lt" if "f x y = Lt" "f y z = Lt" for x y z using that lin
      by(auto simp add: f_def linear_order_on_def partial_order_on_def preorder_on_def split: if_split_asm dest: transD)
  qed
  thus ?thesis by auto
qed

setup_lifting type_definition_compare

lift_definition (code_dt) ccompare_comparator :: "'a :: ccompare compare option"
is "CCOMPARE('a)"
apply(cases "CCOMPARE('a)")
subgoal by simp
subgoal by(rule forw_subst[where P="pred_option _"], assumption)(simp (no_asm_use); simp add: ccompare)
done

lift_definition uprod_compare :: "'a compare \<Rightarrow> 'a uprod comparator"
is "\<lambda>compare (a, b) (c, d).
  let (x, y) = case compare a b of Lt \<Rightarrow> (a, b) | _ \<Rightarrow> (b, a);
      (x', y') = case compare c d of Lt \<Rightarrow> (c, d) | _ \<Rightarrow> (d, c)
  in case compare x x' of Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt | Eq \<Rightarrow> compare y y'"
subgoal for compare ab ab' cd cd'
  proof(cases ab; cases ab'; cases cd; cases cd'; hypsubst; clarsimp; elim disjE conjE; clarsimp)
    fix a b c d
    assume compare: "comparator compare"
    then interpret comparator compare .
    let ?xy = "case compare a b of Lt \<Rightarrow> (a, b) | _ \<Rightarrow> (b, a)" 
    let ?xy' = "case compare c d of Lt \<Rightarrow> (c, d) | _ \<Rightarrow> (d, c)"
    let ?yx = "case compare b a of Lt \<Rightarrow> (b, a) | _ \<Rightarrow> (a, b)"
    let ?yx' = "case compare d c of Lt \<Rightarrow> (d, c) | _ \<Rightarrow> (c, d)"
  
    have [simp]: "?xy = ?yx" "?xy' = ?yx'"
      by(auto split: order.split simp add: eq Gt_lt_conv Lt_lt_conv)
    let ?side = "\<lambda>xy xy'. case xy of (x, y) \<Rightarrow> case xy' of (x', y') \<Rightarrow> (case compare x x' of Eq \<Rightarrow> compare y y' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
    show "?side ?xy ?xy' = ?side ?xy ?yx'" "?side ?yx ?xy' = ?side ?xy ?xy'" "?side ?yx ?yx' = ?side ?xy ?xy'"
      by simp_all
  qed
done

lemma uprod_compare_simps [simp, code]:
  "uprod_compare compare (Upair a b) (Upair c d) =
   (let (x, y) = case Rep_compare compare a b of Lt \<Rightarrow> (a, b) | _ \<Rightarrow> (b, a);
        (x', y') = case Rep_compare compare c d of Lt \<Rightarrow> (c, d) | _ \<Rightarrow> (d, c)
    in case Rep_compare compare x x' of Eq \<Rightarrow> Rep_compare compare y y' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
  for compare supply Upair.transfer[transfer_rule]
  by transfer simp

lemma comparator_uprod_compare: "comparator (uprod_compare compare)" for compare
proof
  show "invert_order (uprod_compare compare x y) = uprod_compare compare y x" for x y
  proof(transfer, goal_cases)
    case (1 compare x y)
    then interpret comparator compare .
    show ?case by(auto split!: order.split prod.split simp add: eq Gt_lt_conv Lt_lt_conv sym dest: order.asym)
  qed
  show "x = y" if "uprod_compare compare x y = Eq" for x y using that
  proof(transfer, goal_cases)
    case (1 compare x y)
    from 1(1) interpret comparator compare .
    show ?case using 1(2) by(clarsimp split: order.split_asm prod.split_asm simp add: eq)
  qed
  show "uprod_compare compare x z = Lt" 
    if "uprod_compare compare x y = Lt" "uprod_compare compare y z = Lt" for x y z using that
  proof(transfer, goal_cases)
    case (1 compare x y z)
    from 1(1) interpret comparator compare .
    show ?case using 1(2-)
      by(auto split!: order.splits prod.split_asm simp add: eq Gt_lt_conv Lt_lt_conv elim: trans)
  qed
qed

instantiation uprod :: (ccompare) ccompare begin
definition ccompare_uprod
where "ccompare_uprod = map_option uprod_compare (ccompare_comparator :: 'a compare option)"
instance by standard(clarsimp simp add: ccompare_uprod_def comparator_uprod_compare)
end

instantiation uprod :: (set_impl) set_impl begin
definition "SET_IMPL('a uprod) = Phantom('a uprod) (of_phantom SET_IMPL('a))"
instance ..
end




(* Graph uses successor representation with function 
  -> let's write a code equation for imp_graph
  -> let's first define the successor operation for an individual vertex.
*)

function succs_of_clause :: "lit \<Rightarrow> lit uprod \<Rightarrow> lit set \<Rightarrow> lit set" where
  "succs_of_clause l (Upair l1 l2) = (if l = negate l1 then insert l2 else if l = negate l2 then insert l1 else id)"
  by(metis surj_pair uprod_exhaust) auto
termination by lexicographic_order

lemma succs_of_clause_split: "P (succs_of_clause l x) \<longleftrightarrow> (\<forall>l1 l2. x = Upair l1 l2 \<longrightarrow> P (succs_of_clause l (Upair l1 l2)))"
  by(cases x)(auto simp only:)

context begin

lemma commute_succs_of_clause: "comp_fun_commute (succs_of_clause l)"
  by unfold_locales(auto split: succs_of_clause_split)

interpretation comp_fun_commute "succs_of_clause l" for l by(rule commute_succs_of_clause)

lemma idem_succs_of_clause: "comp_fun_idem (succs_of_clause l)"
  by unfold_locales(auto split: succs_of_clause_split)

interpretation comp_fun_idem "succs_of_clause l" for l by(rule idem_succs_of_clause)

lift_definition succs_loop_body :: "lit \<Rightarrow> (lit uprod, lit set) comp_fun_idem" is
  "succs_of_clause" by(rule idem_succs_of_clause)

definition succ_imp_graph :: "cnf \<Rightarrow> lit \<Rightarrow> lit set"
  where "succ_imp_graph cnf l = set_fold_cfi (succs_loop_body l) {} cnf"

lemma succ_imp_graph_alt_def: 
  "succ_imp_graph cnf l = Finite_Set.fold (succs_of_clause l) {} cnf"
  unfolding succ_imp_graph_def by transfer simp

lemma succ_imp_graph_correct: 
  "finite cnf \<Longrightarrow> succ_imp_graph cnf l = {l'. (l, l') \<in> imp_graph cnf}"
  by(induction rule: finite_induct)(auto split: succs_of_clause_split simp add: succ_imp_graph_alt_def)

end

lemma imp_graph_code:
  "imp_graph cnf = 
  (if finite cnf then {(l, l'). l' \<in> succ_imp_graph cnf l} 
   else Code.abort (STR ''Infinite or invalid 2CNF formula'') (\<lambda>_. imp_graph cnf))"
by(auto simp add: succ_imp_graph_correct)

lift_definition imp_graph_impl :: "cnf \<Rightarrow> lit graph" is imp_graph .

lemmas [code] = imp_graph_code[containers_identify]

lemma UNIV_lit: "UNIV = range (\<lambda>(x, pos). Lit x pos)"
  apply(auto)
  subgoal for x by(cases x; auto)
  done

instantiation lit :: finite_UNIV begin
definition "finite_UNIV_lit = Phantom(lit) False"
instance by(standard)(auto simp add: finite_UNIV_lit_def UNIV_lit inj_on_def UNIV_Times_UNIV[symmetric] finite_cartesian_product_iff simp del: UNIV_Times_UNIV dest!: finite_imageD)
end

derive (eq) ceq lit
derive (rbt) set_impl lit
derive ccompare lit

export_code imp_graph_impl checking SML

lemma finite_vars_of_cnf: "finite cnf \<Longrightarrow> finite (vars_of_cnf cnf)"
by(clarsimp simp add: vars_of_cnf_def)

lemma satisfiable_code:
  "satisfiable cnf \<longleftrightarrow> 
  (if finite cnf \<and> is_2sat cnf then 
   let G = imp_graph cnf in \<forall>x\<in>vars_of_cnf cnf. \<not> (reachable G (Pos x) (Neg x) \<and> reachable G (Neg x) (Pos x))
   else Code.abort (STR ''Infinite or invalid 2CNF formula'') (\<lambda>_. satisfiable cnf))"
by(simp add: reachable_def finite_2sat_iff finite_vars_of_cnf Let_def)

lemmas [code] = satisfiable_code[containers_identify]

export_code satisfiable checking SML

subsection \<open>Memoize the implication graph's successor function\<close>

lemma succ_imp_graph_outside: "succ_imp_graph cnf l = {}" if "var l \<notin> vars_of_cnf cnf"
proof(cases "finite cnf")
  case True
  interpret comp_fun_idem "succs_of_clause l" by(rule idem_succs_of_clause)
  show ?thesis using True that
    by induction(auto simp add: succ_imp_graph_alt_def vars_of_cnf_def split: if_split_asm succs_of_clause_split)
next
  case False
  then show ?thesis by(simp add: succ_imp_graph_alt_def)
qed

lift_definition tabulate_graph :: "cnf \<Rightarrow> (lit, lit set) mapping" is
  "\<lambda>cnf x. if x \<notin> Domain (imp_graph cnf) then None else Some (imp_graph cnf `` {x})" .

primrec insert_mapping :: "'k \<times> 'v \<Rightarrow> ('k, 'v set) mapping \<Rightarrow> ('k, 'v set) mapping" where
  "insert_mapping (k, v) m = (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k {v} m | Some V \<Rightarrow> Mapping.update k (insert v V) m)"

lemma comp_fun_idem_insert_mapping: "comp_fun_idem insert_mapping"
  unfolding insert_mapping_def
  by(unfold_locales; transfer; auto simp add: Map_To_Mapping.map_apply_def fun_eq_iff split!: option.split)

context begin
interpretation comp_fun_idem insert_mapping by(rule comp_fun_idem_insert_mapping)

function insert_clause :: "clause \<Rightarrow> (lit, lit set) mapping \<Rightarrow> (lit, lit set) mapping" where
  "insert_clause (Upair l1 l2) = insert_mapping (negate l1, l2) \<circ> insert_mapping (negate l2, l1)"
  by(metis uprod_exhaust)(auto simp add: comp_fun_commute)
termination by lexicographic_order

lemma comp_fun_idem_insert_clause: "comp_fun_idem insert_clause"
  apply(unfold_locales)
  subgoal for x y by(cases x; cases y; simp; metis commute_left_comp comp_fun_commute rewriteL_comp_comp)
  subgoal for x by(cases x; simp; metis (no_types, hide_lams) commute_left_comp comp_assoc comp_fun_idem)
  done

lift_definition insert_clause' :: "(clause, (lit, lit set) mapping) comp_fun_idem" is "insert_clause"
  by(rule comp_fun_idem_insert_clause)

lemma tabulate_graph_code [code]:
  "tabulate_graph cnf = 
  (if finite cnf then set_fold_cfi insert_clause' Mapping.empty cnf 
   else Code.abort (STR ''Infinite clause set'') (\<lambda>_. tabulate_graph cnf))"
proof -
  interpret comp_fun_idem insert_clause by(rule comp_fun_idem_insert_clause)
  have * [symmetric]: "Finite_Set.fold insert_clause Mapping.empty cnf = tabulate_graph cnf"
    if "finite cnf" using that
  proof(induction)
    case empty
    then show ?case by(simp)(transfer; auto simp add: fun_eq_iff Map_To_Mapping.map_empty_def vars_of_cnf_def)
  next
    case (insert C cnf)
    show ?case by(cases C; simp add: insert; transfer)(auto simp add: fun_eq_iff Map_To_Mapping.map_apply_def split!: option.split)
  qed
  show ?thesis by(clarsimp)(transfer fixing: cnf; rule *)
qed

lemma succ_imp_graph_impl_code [code]:
  "succ_imp_graph cnf =
  (if finite cnf then let m = tabulate_graph cnf
   in (\<lambda>l. case Mapping.lookup m l of None \<Rightarrow> {} | Some succs' \<Rightarrow> succs')
   else Code.abort (STR ''Infinite clause set'') (\<lambda>_. succ_imp_graph cnf))"
  by transfer(auto simp add: succ_imp_graph_correct fun_eq_iff Map_To_Mapping.map_apply_def dest: succ_imp_graph_outside)
end

derive (rbt) mapping_impl lit

export_code satisfiable checking SML Scala Haskell? OCaml?


end
