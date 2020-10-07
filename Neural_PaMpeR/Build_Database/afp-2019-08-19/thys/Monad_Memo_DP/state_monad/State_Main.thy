subsection \<open>Setup for the State Monad\<close>

theory State_Main
  imports
    "../transform/Transform_Cmd"
    Memory
begin

context includes state_monad_syntax begin

thm if_cong
lemma ifT_cong:
  assumes "b = c" "c \<Longrightarrow> x = u" "\<not>c \<Longrightarrow> y = v"
  shows "State_Monad_Ext.if\<^sub>T \<langle>b\<rangle> x y = State_Monad_Ext.if\<^sub>T \<langle>c\<rangle> u v"
  unfolding State_Monad_Ext.if\<^sub>T_def
  unfolding bind_left_identity
  using if_cong[OF assms] .

lemma return_app_return_cong:
  assumes "f x = g y"
  shows "\<langle>f\<rangle> . \<langle>x\<rangle> = \<langle>g\<rangle> . \<langle>y\<rangle>"
  unfolding State_Monad_Ext.return_app_return_meta assms ..

lemmas [fundef_cong] =
  return_app_return_cong
  ifT_cong
end

memoize_fun comp\<^sub>T: comp monadifies (state) comp_def
lemma (in dp_consistency) comp\<^sub>T_transfer[transfer_rule]:
  "crel_vs ((R1 ===>\<^sub>T R2) ===>\<^sub>T (R0 ===>\<^sub>T R1) ===>\<^sub>T (R0 ===>\<^sub>T R2)) comp comp\<^sub>T"
  apply memoize_combinator_init
  subgoal premises IH [transfer_rule] by memoize_unfold_defs transfer_prover
  done

memoize_fun map\<^sub>T: map monadifies (state) list.map
lemma (in dp_consistency) map\<^sub>T_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T list_all2 R1) map map\<^sub>T"
  apply memoize_combinator_init
  apply (erule list_all2_induct)
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  done

memoize_fun fold\<^sub>T: fold monadifies (state) fold.simps
lemma (in dp_consistency) fold\<^sub>T_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T"
  apply memoize_combinator_init
  apply (erule list_all2_induct)
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  done

context includes state_monad_syntax begin

thm map_cong
lemma mapT_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f x = g x"
  shows "map\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = map\<^sub>T . \<langle>g\<rangle> . \<langle>ys\<rangle>"
  unfolding map\<^sub>T_def 
  unfolding assms(1)
  using assms(2) by (induction ys) (auto simp: State_Monad_Ext.return_app_return_meta)

thm fold_cong
lemma foldT_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f x = g x"
  shows "fold\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = fold\<^sub>T . \<langle>g\<rangle> . \<langle>ys\<rangle>"
  unfolding fold\<^sub>T_def
  unfolding assms(1)
  using assms(2) by (induction ys) (auto simp: State_Monad_Ext.return_app_return_meta)

lemma abs_unit_cong:
  (* for lazy checkmem *)
  assumes "x = y"
  shows "(\<lambda>_::unit. x) = (\<lambda>_. y)"
  using assms ..

lemmas [fundef_cong] =
  return_app_return_cong
  ifT_cong
  mapT_cong
  foldT_cong
  abs_unit_cong
end

context dp_consistency begin
context includes lifting_syntax state_monad_syntax begin

named_theorems dp_match_rule

thm if_cong
lemma if\<^sub>T_cong2:
  assumes "Rel (=) b c" "c \<Longrightarrow> Rel (crel_vs R) x x\<^sub>T" "\<not>c \<Longrightarrow> Rel (crel_vs R) y y\<^sub>T"
  shows "Rel (crel_vs R) (if (Wrap b) then x else y) (State_Monad_Ext.if\<^sub>T \<langle>c\<rangle> x\<^sub>T y\<^sub>T)"
  using assms unfolding State_Monad_Ext.if\<^sub>T_def bind_left_identity Rel_def Wrap_def
  by (auto split: if_split)

lemma map\<^sub>T_cong2:
  assumes
    "is_equality R"
    "Rel R xs ys"
    "\<And>x. x\<in>set ys \<Longrightarrow> Rel (crel_vs S) (f x) (f\<^sub>T' x)"
  shows "Rel (crel_vs (list_all2 S)) (App (App map (Wrap f)) (Wrap xs)) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>ys\<rangle>)"
  unfolding map\<^sub>T_def
  unfolding State_Monad_Ext.return_app_return_meta
  unfolding assms(2)[unfolded Rel_def assms(1)[unfolded is_equality_def]]
  using assms(3)
  unfolding Rel_def Wrap_def App_def
  apply (induction ys)
  subgoal premises by (memoize_unfold_defs (state) map) transfer_prover
  subgoal premises prems for a ys
  apply (memoize_unfold_defs (state) map)
    apply (unfold State_Monad_Ext.return_app_return_meta Wrap_App_Wrap)
    supply [transfer_rule] =
      prems(2)[OF list.set_intros(1)]
      prems(1)[OF prems(2)[OF list.set_intros(2)], simplified]
    by transfer_prover
  done

lemma fold\<^sub>T_cong2:
  assumes
    "is_equality R"
    "Rel R xs ys"
    "\<And>x. x\<in>set ys \<Longrightarrow> Rel (crel_vs (S ===> crel_vs S)) (f x) (f\<^sub>T' x)"
  shows
    "Rel (crel_vs (S ===> crel_vs S)) (fold f xs) (fold\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>ys\<rangle>)"
  unfolding fold\<^sub>T_def
  unfolding State_Monad_Ext.return_app_return_meta
  unfolding assms(2)[unfolded Rel_def assms(1)[unfolded is_equality_def]]
  using assms(3)
  unfolding Rel_def
  apply (induction ys)
  subgoal premises by (memoize_unfold_defs (state) fold) transfer_prover
  subgoal premises prems for a ys
    apply (memoize_unfold_defs (state) fold)
    apply (unfold State_Monad_Ext.return_app_return_meta Wrap_App_Wrap)
    supply [transfer_rule] =
      prems(2)[OF list.set_intros(1)]
      prems(1)[OF prems(2)[OF list.set_intros(2)], simplified]
    by transfer_prover
  done

lemma refl2:
  "is_equality R \<Longrightarrow> Rel R x x"
  unfolding is_equality_def Rel_def by simp

lemma rel_fun2:
  assumes "is_equality R0" "\<And>x. Rel R1 (f x) (g x)"
  shows "Rel (rel_fun R0 R1) f g"
  using assms unfolding is_equality_def Rel_def by auto

lemma crel_vs_return_app_return:
  assumes "Rel R (f x) (g x)"
  shows "Rel R (App (Wrap f) (Wrap x)) (\<langle>g\<rangle> . \<langle>x\<rangle>)"
  using assms unfolding State_Monad_Ext.return_app_return_meta Wrap_App_Wrap .

thm option.case_cong[no_vars]
lemma option_case_cong':
"Rel (=) option' option \<Longrightarrow>
(option = None \<Longrightarrow> Rel R f1 g1) \<Longrightarrow>
(\<And>x2. option = Some x2 \<Longrightarrow> Rel R (f2 x2) (g2 x2)) \<Longrightarrow>
Rel R (case option' of None \<Rightarrow> f1 | Some x2 \<Rightarrow> f2 x2)
(case option of None \<Rightarrow> g1 | Some x2 \<Rightarrow> g2 x2)"
  unfolding Rel_def by (auto split: option.split)

thm prod.case_cong[no_vars]
lemma prod_case_cong': fixes prod prod' shows
"Rel (=) prod prod' \<Longrightarrow>
(\<And>x1 x2. prod' = (x1, x2) \<Longrightarrow> Rel R (f x1 x2) (g x1 x2)) \<Longrightarrow>
Rel R (case prod of (x1, x2) \<Rightarrow> f x1 x2)
(case prod' of (x1, x2) \<Rightarrow> g x1 x2)"
  unfolding Rel_def by (auto split: prod.splits)

thm nat.case_cong[no_vars]
lemma nat_case_cong': fixes nat nat' shows
"Rel (=) nat nat' \<Longrightarrow>
(nat' = 0 \<Longrightarrow> Rel R f1 g1) \<Longrightarrow>
(\<And>x2. nat' = Suc x2 \<Longrightarrow> Rel R (f2 x2) (g2 x2)) \<Longrightarrow>
Rel R (case nat of 0 \<Rightarrow> f1 | Suc x2 \<Rightarrow> f2 x2) (case nat' of 0 \<Rightarrow> g1 | Suc x2 \<Rightarrow> g2 x2)"
  unfolding Rel_def by (auto split: nat.splits)
  

lemmas [dp_match_rule] =
  prod_case_cong'
  option_case_cong'
  nat_case_cong'


lemmas [dp_match_rule] =
  crel_vs_return_app_return

lemmas [dp_match_rule] =
  map\<^sub>T_cong2
  fold\<^sub>T_cong2
  if\<^sub>T_cong2

lemmas [dp_match_rule] =
  crel_vs_return
  crel_vs_fun_app
  refl2
  rel_fun2

(*
lemmas [dp_match_rule] =
  crel_vs_checkmem_tupled
*)

end (* context lifting_syntax *)
end (* context dp_consistency *)


subsubsection \<open>Code Setup\<close>

lemmas [code_unfold] =
  state_mem_defs.checkmem_checkmem'[symmetric]
  state_mem_defs.checkmem'_def
  map\<^sub>T_def

end (* theory *)
