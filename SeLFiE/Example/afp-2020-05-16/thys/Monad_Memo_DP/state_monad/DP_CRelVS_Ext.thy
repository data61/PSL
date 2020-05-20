theory DP_CRelVS_Ext
  imports "transform/Transform_Cmd"
begin

notation fun_app_lifted (infixl "." 999)
notation Transfer.Rel ("Rel")

thm map_cong
lemma mapT_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f x = g x"
  shows "map\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = map\<^sub>T . \<langle>g\<rangle> . \<langle>ys\<rangle>"
  unfolding map\<^sub>T_def 
  unfolding assms(1)
  using assms(2) by (induction ys) (auto simp: return_app_return)

thm fold_cong
lemma foldT_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f x = g x"
  shows "fold\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = fold\<^sub>T . \<langle>g\<rangle> . \<langle>ys\<rangle>"
  unfolding fold\<^sub>T_def
  unfolding assms(1)
  using assms(2) by (induction ys) (auto simp: return_app_return)


lemma abs_unit_cong:
  (* for lazy checkmem *)
  assumes "x = y"
  shows "(\<lambda>_::unit. x) = (\<lambda>_. y)"
  using assms ..

lemma App_cong:
  assumes "f x = g y"
  shows "App f x = App g y"
  unfolding App_def using assms .

lemmas [fundef_cong] =
  return_app_return_cong
  ifT_cong
  mapT_cong
  foldT_cong
  abs_unit_cong
  App_cong

context dp_consistency begin
context includes lifting_syntax begin

named_theorems dp_match_rule

lemma refl2:
  "is_equality R \<Longrightarrow> Rel R x x"
  unfolding is_equality_def Rel_def by simp

lemma rel_fun2:
  assumes "is_equality R0" "\<And>x. Rel R1 (f x) (g x)"
  shows "Rel (rel_fun R0 R1) f g"
  using assms unfolding is_equality_def Rel_def by auto

thm if_cong
lemma if\<^sub>T_cong2:
  assumes "Rel (=) b c" "c \<Longrightarrow> Rel (crel_vs R) x x\<^sub>T" "\<not>c \<Longrightarrow> Rel (crel_vs R) y y\<^sub>T"
  shows "Rel (crel_vs R) (if (Wrap b) then x else y) (if\<^sub>T \<langle>c\<rangle> x\<^sub>T y\<^sub>T)"
  using assms unfolding if\<^sub>T_def left_identity Rel_def Wrap_def
  by (auto split: if_split)

lemma if\<^sub>T_cong2':
  assumes "c \<Longrightarrow> Rel (crel_vs R) x x\<^sub>T" "\<not>c \<Longrightarrow> Rel (crel_vs R) y y\<^sub>T"
  shows "Rel (crel_vs R) (if Wrap c then x else y) (if\<^sub>T \<langle>c\<rangle> x\<^sub>T y\<^sub>T)"
  apply (rule if\<^sub>T_cong2[OF _ assms])
    apply (auto simp: Rel_def)
  done

(*

thm map_cong
lemma map1T_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f\<^sub>T . \<langle>x\<rangle> = g\<^sub>T . \<langle>x\<rangle>"
  shows "map1\<^sub>T . f\<^sub>T . \<langle>xs\<rangle> = map1\<^sub>T . g\<^sub>T . \<langle>ys\<rangle>"
  unfolding map1\<^sub>T_def 
  unfolding assms(1)
  using assms(2) apply (induction ys) apply (auto simp: return_app_return)
  subgoal
    apply (rule state.expand)
    apply (rule ext)
    unfolding fun_app_lifted_def
    unfolding bind_def return_def
    apply (auto split: prod.splits)
*)
lemma map\<^sub>T_transfer2:
  "Rel (crel_vs ((R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T list_all2 R1)) map map\<^sub>T"
  unfolding Rel_def by (fact map\<^sub>T_transfer)

lemma map\<^sub>T_cong2:
  assumes
    "is_equality R"
    "Rel R xs ys"
    "\<And>x. x\<in>set ys \<Longrightarrow> Rel (crel_vs S) (f x) (f\<^sub>T' x)"
  shows "Rel (crel_vs (list_all2 S)) (App (App map (Wrap f)) (Wrap xs)) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>ys\<rangle>)"
  unfolding map\<^sub>T_def
  unfolding return_app_return
  unfolding assms(2)[unfolded Rel_def assms(1)[unfolded is_equality_def]]
  using assms(3)
  unfolding Rel_def Wrap_def App_def
  apply (induction ys)
  apply (tactic \<open>Transform_Tactic.unfold_dp_defs_tac @{context} true true 1\<close>)
  subgoal premises by transfer_prover
  subgoal premises prems for a ys
    apply (tactic \<open>Transform_Tactic.unfold_dp_defs_tac @{context} true true 1\<close>)
    apply (unfold return_app_return Wrap_App_Wrap)
    supply [transfer_rule] =
      prems(2)[OF list.set_intros(1)]
      prems(1)[OF prems(2)[OF list.set_intros(2)], simplified]
    by transfer_prover
  done

lemma map\<^sub>T_cong2':
  assumes
    "\<And>x. x\<in>set xs \<Longrightarrow> Rel (crel_vs S) (f x) (f\<^sub>T' x)"
  shows "Rel (crel_vs (list_all2 S)) (map f xs) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>xs\<rangle>)"
  apply (rule map\<^sub>T_cong2[OF is_equality_eq _ assms, unfolded Wrap_def App_def])
   apply (auto simp: Rel_def)
  done


lemma fold\<^sub>T_transfer2:
  "Rel (crel_vs ((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1)) fold fold\<^sub>T"
  unfolding Rel_def by (fact fold\<^sub>T_transfer)

lemma fold\<^sub>T_cong2:
  assumes
    "is_equality R"
    "Rel R xs ys"
    "\<And>x. x\<in>set ys \<Longrightarrow> Rel (crel_vs (S ===> crel_vs S)) (f x) (f\<^sub>T' x)"
  shows
    "Rel (crel_vs (S ===> crel_vs S)) (fold f xs) (fold\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>ys\<rangle>)"
  unfolding fold\<^sub>T_def
  unfolding return_app_return
  unfolding assms(2)[unfolded Rel_def assms(1)[unfolded is_equality_def]]
  using assms(3)
  unfolding Rel_def
  apply (induction ys)
  apply (tactic \<open>Transform_Tactic.unfold_dp_defs_tac @{context} true true 1\<close>)
  subgoal premises by transfer_prover
  subgoal premises prems for a ys
    apply (tactic \<open>Transform_Tactic.unfold_dp_defs_tac @{context} true true 1\<close>)
    apply (unfold return_app_return Wrap_App_Wrap)
    supply [transfer_rule] =
      prems(2)[OF list.set_intros(1)]
      prems(1)[OF prems(2)[OF list.set_intros(2)], simplified]
    by transfer_prover
  done

thm BNF_Fixpoint_Base.case_prod_transfer
lemma prod_case_transfer2:
  assumes
    "Rel (R0 ===> R1 ===> crel_vs S) f g"
  shows "Rel (rel_prod R0 R1 ===> crel_vs S) (case_prod f) (case_prod g)"
  supply [transfer_rule] = assms[unfolded Rel_def]
  unfolding Rel_def by transfer_prover

lemma prod_case_cong2:
  assumes
    "is_equality R"
    "Rel R x y"
    "\<And>u v. y = (u, v) \<Longrightarrow> Rel (crel_vs S) (f u v) (g u v)"
  shows "Rel (crel_vs S) (case_prod f x) (\<langle>case_prod g\<rangle> . \<langle>y\<rangle>)"
  unfolding return_app_return
  using assms by (auto simp: is_equality_def Rel_def split: prod.split)

thm option.case_transfer
lemma option_case_transfer2:
  assumes
    "Rel (crel_vs S) f0 g0"
    "Rel (R ===> crel_vs S) f1 g1"
  shows "Rel (rel_option R ===> crel_vs S) (case_option f0 f1) (case_option g0 g1)"
  supply [transfer_rule] = assms[unfolded Rel_def]
  unfolding Rel_def by transfer_prover

thm option.case_cong
lemma option_case_cong2:
  assumes
    "is_equality R"
    "Rel R x y"
    "y = None \<Longrightarrow> Rel (crel_vs S) f0 g0"
    "\<And>x2. y = Some x2 \<Longrightarrow> Rel (crel_vs S) (f1 x2) (g1 x2)"
  shows "Rel (crel_vs S) (case_option f0 f1 x) (\<langle>case_option g0 g1\<rangle> . \<langle>y\<rangle>)"
  unfolding return_app_return
  using assms by (auto simp: is_equality_def Rel_def split: option.split)


thm list.case_transfer
lemma list_case_transfer2:
  assumes
    "Rel (crel_vs S) f0 g0"
    "Rel (R ===> list_all2 R ===> crel_vs S) f1 g1"
  shows "Rel (list_all2 R ===> crel_vs S) (case_list f0 f1) (case_list g0 g1)"
  supply [transfer_rule] = assms[unfolded Rel_def]
  unfolding Rel_def by transfer_prover


thm list.case_cong
lemma list_case_cong2:
  assumes
    "is_equality R"
    "Rel R x y"
    "x = Nil \<Longrightarrow> Rel (crel_vs S) f0 g0" 
    "\<And>x2 x2s. x = x2#x2s \<Longrightarrow> Rel (crel_vs S) (f1 x2 x2s) (g1 x2 x2s)"
  shows "Rel (crel_vs S) (case_list f0 f1 x) (\<langle>case_list g0 g1\<rangle> . \<langle>y\<rangle>)"
  unfolding return_app_return
  using assms by (auto simp: is_equality_def Rel_def split: list.split)

lemmas [dp_match_rule] =
  map\<^sub>T_cong2
  fold\<^sub>T_cong2
  if\<^sub>T_cong2

lemmas [dp_match_rule] =
  prod_case_cong2
  prod_case_transfer2
  option_case_cong2
  option_case_transfer2
  list_case_cong2
  list_case_transfer2

lemmas [dp_match_rule] =
  crel_vs_return
  crel_vs_fun_app
  rel_fun2
  refl2

lemmas [dp_match_rule] =
  map\<^sub>T_transfer2
  fold\<^sub>T_transfer2

thm dp_match_rule

end (* lifting_syntax *)
end (* dp_consistency *)

no_notation fun_app_lifted (infixl "." 999)
no_notation Transfer.Rel ("Rel")
end (* theory *)
