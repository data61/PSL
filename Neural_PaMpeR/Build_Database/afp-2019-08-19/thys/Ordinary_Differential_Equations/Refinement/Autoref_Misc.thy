(* TODO: Integrate into Misc*)
theory Autoref_Misc
imports
  Refine_Dflt_No_Comp
  "HOL-Analysis.Analysis"
begin

(*****************************)
(* Refine-Basic *)
(* TODO: Move to Refine_Basic *)
lemma nofail_RES_conv: "nofail m \<longleftrightarrow> (\<exists>M. m=RES M)" by (cases m) auto

(* TODO: Move, near SPEC_nofail  *)
lemma nofail_SPEC: "nofail m \<Longrightarrow> m \<le> SPEC (\<lambda>_. True)"
  by (simp add: pw_le_iff)

lemma nofail_SPEC_iff: "nofail m \<longleftrightarrow> m \<le> SPEC (\<lambda>_. True)"
  by (simp add: pw_le_iff)

lemma nofail_SPEC_triv_refine: "\<lbrakk> nofail m; \<And>x. \<Phi> x \<rbrakk> \<Longrightarrow> m \<le> SPEC \<Phi>"
  by (simp add: pw_le_iff)

(* TODO: Move *)
lemma bind_cong:
  assumes "m=m'"
  assumes "\<And>x. RETURN x \<le> m' \<Longrightarrow> f x = f' x"
  shows "bind m f = bind m' f'"
  using assms
  by (auto simp: refine_pw_simps pw_eq_iff pw_le_iff)


primrec the_RES where "the_RES (RES X) = X"
lemma the_RES_inv[simp]: "nofail m \<Longrightarrow> RES (the_RES m) = m"
  by (cases m) auto

lemma le_SPEC_UNIV_rule [refine_vcg]:
  "m \<le> SPEC (\<lambda>_. True) \<Longrightarrow> m \<le> RES UNIV" by auto

lemma nf_inres_RES[simp]: "nf_inres (RES X) x \<longleftrightarrow> x\<in>X"
  by (simp add: refine_pw_simps)

lemma nf_inres_SPEC[simp]: "nf_inres (SPEC \<Phi>) x \<longleftrightarrow> \<Phi> x"
  by (simp add: refine_pw_simps)

(* TODO: Move *)
lemma Let_refine':
  assumes "(m,m')\<in>R"
  assumes "(m,m')\<in>R \<Longrightarrow> f m \<le>\<Down>S (f' m')"
  shows "Let m f \<le> \<Down>S (Let m' f')"
  using assms by simp

lemma in_nres_rel_iff: "(a,b)\<in>\<langle>R\<rangle>nres_rel \<longleftrightarrow> a \<le>\<Down>R b"
  by (auto simp: nres_rel_def)

lemma inf_RETURN_RES:
  "inf (RETURN x) (RES X) = (if x\<in>X then RETURN x else SUCCEED)"
  "inf (RES X) (RETURN x) = (if x\<in>X then RETURN x else SUCCEED)"
  by (auto simp: pw_eq_iff refine_pw_simps)

(* TODO: MOve, test as default simp-rule *)
lemma inf_RETURN_SPEC[simp]:
  "inf (RETURN x) (SPEC (\<lambda>y. \<Phi> y)) = SPEC (\<lambda>y. y=x \<and> \<Phi> x)"
  "inf (SPEC (\<lambda>y. \<Phi> y)) (RETURN x) = SPEC (\<lambda>y. y=x \<and> \<Phi> x)"
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma RES_sng_eq_RETURN: "RES {x} = RETURN x"
  by simp

lemma nofail_inf_serialize:
  "\<lbrakk>nofail a; nofail b\<rbrakk> \<Longrightarrow> inf a b = do {x\<leftarrow>a; ASSUME (inres b x); RETURN x}"
  by (auto simp: pw_eq_iff refine_pw_simps)

definition lift_assn :: "('a \<times> 'b) set \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  \<comment> \<open>Lift assertion over refinement relation\<close>
  where "lift_assn R \<Phi> s \<equiv> \<exists>s'. (s,s')\<in>R \<and> \<Phi> s'"
lemma lift_assnI: "\<lbrakk>(s,s')\<in>R; \<Phi> s'\<rbrakk> \<Longrightarrow> lift_assn R \<Phi> s"
  unfolding lift_assn_def by auto

(* TODO: Replace original lemma *)
lemma case_option_refine[refine]:
  assumes "(x,x')\<in>Id"
  assumes "x=None \<Longrightarrow> fn \<le> \<Down>R fn'"
  assumes "\<And>v v'. \<lbrakk>x=Some v; (v,v')\<in>Id\<rbrakk> \<Longrightarrow> fs v \<le> \<Down>R (fs' v')"
  shows "case_option fn (\<lambda>v. fs v) x \<le> \<Down>R (case_option fn' (\<lambda>v'. fs' v') x')"
  using assms by (auto split: option.split)


definition GHOST :: "'a \<Rightarrow> 'a"
  \<comment> \<open>Ghost tag to mark ghost variables in let-expressions\<close>
  where [simp]: "GHOST \<equiv> \<lambda>x. x"
lemma GHOST_elim_Let: \<comment> \<open>Unfold rule to inline GHOST-Lets\<close>
  shows "(let x=GHOST m in f x) = f m" by simp



text \<open>The following set of rules executes a step on the LHS or RHS of
  a refinement proof obligation, without changing the other side.
  These kind of rules is useful for performing refinements with
  invisible steps.\<close>
lemma lhs_step_If:
  "\<lbrakk> b \<Longrightarrow> t \<le> m; \<not>b \<Longrightarrow> e \<le> m \<rbrakk> \<Longrightarrow> If b t e \<le> m" by simp

lemma lhs_step_RES:
  "\<lbrakk> \<And>x. x\<in>X \<Longrightarrow> RETURN x \<le> m  \<rbrakk> \<Longrightarrow> RES X \<le> m"
  by (simp add: pw_le_iff)

lemma lhs_step_SPEC:
  "\<lbrakk> \<And>x. \<Phi> x \<Longrightarrow> RETURN x \<le> m \<rbrakk> \<Longrightarrow> SPEC (\<lambda>x. \<Phi> x) \<le> m"
  by (simp add: pw_le_iff)

lemma lhs_step_bind:
  fixes m :: "'a nres" and f :: "'a \<Rightarrow> 'b nres"
  assumes "nofail m' \<Longrightarrow> nofail m"
  assumes "\<And>x. nf_inres m x \<Longrightarrow> f x \<le> m'"
  shows "do {x\<leftarrow>m; f x} \<le> m'"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast

lemma rhs_step_bind_RES:
  assumes "x'\<in>X'"
  assumes "m \<le> \<Down>R (f' x')"
  shows "m \<le> \<Down>R (RES X' \<bind> f')"
  using assms by (simp add: pw_le_iff refine_pw_simps) blast

lemma rhs_step_bind_SPEC:
  assumes "\<Phi> x'"
  assumes "m \<le> \<Down>R (f' x')"
  shows "m \<le> \<Down>R (SPEC \<Phi> \<bind> f')"
  using assms by (simp add: pw_le_iff refine_pw_simps) blast

lemma RES_bind_choose:
  assumes "x\<in>X"
  assumes "m \<le> f x"
  shows "m \<le> RES X \<bind> f"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma pw_RES_bind_choose:
  "nofail (RES X \<bind> f) \<longleftrightarrow> (\<forall>x\<in>X. nofail (f x))"
  "inres (RES X \<bind> f) y \<longleftrightarrow> (\<exists>x\<in>X. inres (f x) y)"
  by (auto simp: refine_pw_simps)


(* TODO: Move to Refine_Basic: Convenience*)
lemma use_spec_rule:
  assumes "m \<le> SPEC \<Psi>"
  assumes "m \<le> SPEC (\<lambda>s. \<Psi> s \<longrightarrow> \<Phi> s)"
  shows "m \<le> SPEC \<Phi>"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)

lemma strengthen_SPEC: "m \<le> SPEC \<Phi> \<Longrightarrow> m \<le> SPEC(\<lambda>s. inres m s \<and> \<Phi> s)"
  \<comment> \<open>Strengthen SPEC by adding trivial upper bound for result\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

lemma weaken_SPEC:
  "m \<le> SPEC \<Phi> \<Longrightarrow> (\<And>x. \<Phi> x \<Longrightarrow> \<Psi> x) \<Longrightarrow> m \<le> SPEC \<Psi>"
  by (force elim!: order_trans)


lemma ife_FAIL_to_ASSERT_cnv:
  "(if \<Phi> then m else FAIL) = op_nres_ASSERT_bnd \<Phi> m"
  by (cases \<Phi>, auto)



lemma param_op_nres_ASSERT_bnd[param]:
  assumes "\<Phi>' \<Longrightarrow> \<Phi>"
  assumes "\<lbrakk>\<Phi>'; \<Phi>\<rbrakk> \<Longrightarrow> (m,m')\<in>\<langle>R\<rangle>nres_rel"
  shows "(op_nres_ASSERT_bnd \<Phi> m, op_nres_ASSERT_bnd \<Phi>' m') \<in> \<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps nres_rel_def)

declare autoref_FAIL[param]


(*****************************)
(* Refine_Transfer *)
lemma (in transfer) transfer_sum[refine_transfer]:
  assumes "\<And>l. \<alpha> (fl l) \<le> Fl l"
  assumes "\<And>r. \<alpha> (fr r) \<le> Fr r"
  shows "\<alpha> (case_sum fl fr x) \<le> (case_sum Fl Fr x)"
  using assms by (auto split: sum.split)


(* TODO: Move *)
lemma nres_of_transfer[refine_transfer]: "nres_of x \<le> nres_of x" by simp



(*****************************)
(* Refine_Foreach  *)
(* TODO: Change in Refine_Foreach(?)! *)
declare FOREACH_patterns[autoref_op_pat_def]

(*****************************)
(* Refine_Recursion  *)

(*****************************)
(* Refine_While  *)
context begin interpretation autoref_syn .
(* TODO: Change in Refine_While *)
lemma [autoref_op_pat_def]:
  "WHILEIT I \<equiv> OP (WHILEIT I)"
  "WHILEI I \<equiv> OP (WHILEI I)"
  by auto
end

(*****************************)
(* Relators *)
lemma set_relD: "(s,s')\<in>\<langle>R\<rangle>set_rel \<Longrightarrow> x\<in>s \<Longrightarrow> \<exists>x'\<in>s'. (x,x')\<in>R"
  unfolding set_rel_def by blast

lemma set_relE[consumes 2]:
  assumes "(s,s')\<in>\<langle>R\<rangle>set_rel" "x\<in>s"
  obtains x' where "x'\<in>s'" "(x,x')\<in>R"
  using set_relD[OF assms] ..

lemma param_prod': "\<lbrakk>
  \<And>a b a' b'. \<lbrakk>p=(a,b); p'=(a',b')\<rbrakk> \<Longrightarrow> (f a b,f' a' b')\<in>R
  \<rbrakk> \<Longrightarrow> (case_prod f p, case_prod f' p')\<in>R"
  by (auto split: prod.split)



(*****************************)
(* Parametricity-HOL *)

lemma dropWhile_param[param]:
  "(dropWhile, dropWhile) \<in> (a \<rightarrow> bool_rel) \<rightarrow> \<langle>a\<rangle>list_rel \<rightarrow> \<langle>a\<rangle>list_rel"
  unfolding dropWhile_def by parametricity

term takeWhile
lemma takeWhile_param[param]:
  "(takeWhile, takeWhile) \<in> (a \<rightarrow> bool_rel) \<rightarrow> \<langle>a\<rangle>list_rel \<rightarrow> \<langle>a\<rangle>list_rel"
  unfolding takeWhile_def by parametricity

(*****************************)
(* Autoref-HOL  *)
lemmas [autoref_rules] = dropWhile_param takeWhile_param


(*****************************)
(* Autoref-Tool *)

method_setup autoref_solve_id_op = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Id_Ops.id_tac (Config.put Autoref_Id_Ops.cfg_ss_id_op false ctxt)
  ))
\<close>


(*****************************)
(* Autoref_Monadic  *)

(* TODO: Replace! *)
text \<open>Default setup of the autoref-tool for the monadic framework.\<close>

lemma autoref_monadicI1:
  assumes "(b,a)\<in>\<langle>R\<rangle>nres_rel"
  assumes "RETURN c \<le> b"
  shows "(RETURN c, a)\<in>\<langle>R\<rangle>nres_rel" "RETURN c \<le>\<Down>R a"
  using assms
  unfolding nres_rel_def
  by simp_all

lemma autoref_monadicI2:
  assumes "(b,a)\<in>\<langle>R\<rangle>nres_rel"
  assumes "nres_of c \<le> b"
  shows "(nres_of c, a)\<in>\<langle>R\<rangle>nres_rel" "nres_of c \<le> \<Down>R a"
  using assms
  unfolding nres_rel_def
  by simp_all

lemmas autoref_monadicI = autoref_monadicI1 autoref_monadicI2

ML \<open>
  structure Autoref_Monadic = struct

    val cfg_plain = Attrib.setup_config_bool @{binding autoref_plain} (K false)

    fun autoref_monadic_tac ctxt = let
      open Autoref_Tacticals
      val ctxt = Autoref_Phases.init_data ctxt
      val plain = Config.get ctxt cfg_plain
      val trans_thms = if plain then [] else @{thms the_resI}

    in
      resolve_tac ctxt @{thms autoref_monadicI}
      THEN'
      IF_SOLVED (Autoref_Phases.all_phases_tac ctxt)
        (RefineG_Transfer.post_transfer_tac trans_thms ctxt)
        (K all_tac) (* Autoref failed *)

    end
  end
\<close>

method_setup autoref_monadic = \<open>let
    open Refine_Util Autoref_Monadic
    val autoref_flags =
          parse_bool_config "trace" Autoref_Phases.cfg_trace
      ||  parse_bool_config "debug" Autoref_Phases.cfg_debug
      ||  parse_bool_config "plain" Autoref_Monadic.cfg_plain

  in
    parse_paren_lists autoref_flags
    >>
    ( fn _ => fn ctxt => SIMPLE_METHOD' (
      let
        val ctxt = Config.put Autoref_Phases.cfg_keep_goal true ctxt
      in autoref_monadic_tac ctxt end
    ))

  end

\<close>
 "Automatic Refinement and Determinization for the Monadic Refinement Framework"

(* Move to Refine Transfer *)
lemma dres_unit_simps[refine_transfer_post_simp]:
  "dbind (dRETURN (u::unit)) f = f ()"
  by auto

lemma Let_dRETURN_simp[refine_transfer_post_simp]:
  "Let m dRETURN = dRETURN m" by auto

(* TODO: Move *)
lemmas [refine_transfer_post_simp] = dres_monad_laws


subsection \<open>things added by Fabian\<close>

bundle art = [[goals_limit=1, autoref_trace, autoref_trace_failed_id, autoref_keep_goal]]

definition [simp, autoref_tag_defs]: "TRANSFER_tag P == P"
lemma TRANSFER_tagI: "P ==> TRANSFER_tag P" by simp
abbreviation "TRANSFER P \<equiv> PREFER_tag (TRANSFER_tag P)"
declaration
\<open>
let
  val _ = ()
in Tagged_Solver.declare_solver @{thms TRANSFER_tagI} @{binding TRANSFER}
        "transfer"
        (RefineG_Transfer.post_transfer_tac [])
end\<close>

(* TODO: check for usage in Autoref? *)
method_setup refine_vcg =
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac (add_thms @ Refine.vcg.get ctxt) ctxt THEN_ALL_NEW_FWD
      (TRY o
        (Method.assm_tac ctxt
        ORELSE' SOLVED' (clarsimp_tac ctxt THEN_ALL_NEW Method.assm_tac ctxt)
        ORELSE' Refine.post_tac ctxt))
  ))\<close>
  "Refinement framework: Generate refinement and verification conditions"

lemmas [autoref_rules] = autoref_rec_nat \<comment> \<open>TODO: add to Autoref\<close>
lemma \<comment> \<open>TODO: needed  because @{thm dres.transfer_rec_nat} expects one argument,
  but functions with more arguments defined by primrec take several arguments\<close>
  uncurry_rec_nat: "rec_nat (\<lambda>a b. fn a b) (\<lambda>n rr a b. fs n rr a b) n a b =
  rec_nat (\<lambda>(a,b). fn a b) (\<lambda>n rr (a,b). fs n (\<lambda>a b. rr (a,b)) a b) n (a,b)"
  apply (induction n arbitrary: a b)
   apply (auto split: prod.splits)
  apply metis
  done

attribute_setup refine_vcg_def =
  \<open>Scan.succeed (Thm.declaration_attribute (fn A =>
    Refine.vcg.add_thm ((A RS @{thm eq_refl}) RS @{thm order.trans})))\<close>

definition comp2 (infixl "o2" 55) where "comp2 f g x y \<equiv> f (g x y)"
definition comp3 (infixl "o3" 55) where "comp3 f g x y z \<equiv> f (g x y z)"
definition comp4 (infixl "o4" 55) where "comp4 f g w x y z \<equiv> f (g w x y z)"
definition comp5 (infixl "o5" 55) where "comp5 f g w x y z a \<equiv> f (g w x y z a)"
definition comp6 (infixl "o6" 55) where "comp6 f g w x y z a b \<equiv> f (g w x y z a b)"
lemmas comps =
  comp_def[abs_def]
  comp2_def[abs_def]
  comp3_def[abs_def]
  comp4_def[abs_def]
  comp5_def[abs_def]
  comp6_def[abs_def]

locale autoref_op_pat_def = fixes x
begin
lemma [autoref_op_pat_def]: "x \<equiv> Autoref_Tagging.OP x"
  by simp
end

bundle autoref_syntax begin
no_notation vec_nth (infixl "$" 90)
no_notation funcset (infixr "\<rightarrow>" 60)
notation Autoref_Tagging.APP (infixl "$" 900)
notation rel_ANNOT (infix ":::" 10)
notation ind_ANNOT (infix "::#" 10)
notation "Autoref_Tagging.OP" ("OP")
notation Autoref_Tagging.ABS (binder "\<lambda>''" 10)
end

definition "THE_NRES = case_option SUCCEED RETURN"

context includes autoref_syntax begin
schematic_goal THE_NRES_impl:
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued R"
  assumes [autoref_rules]: "(xi, x) \<in> \<langle>R\<rangle>option_rel"
  shows "(nres_of ?x, THE_NRES $ x) \<in> \<langle>R\<rangle>nres_rel"
  unfolding THE_NRES_def
  by (autoref_monadic)
end

concrete_definition THE_DRES uses THE_NRES_impl
lemmas [autoref_rules] = THE_DRES.refine

lemma THE_NRES_refine[THEN order_trans, refine_vcg]:
  "THE_NRES x \<le> SPEC (\<lambda>r. x = Some r)"
  by (auto simp: THE_NRES_def split: option.splits)

definition "CHECK f P = (if P then RETURN () else let _ = f () in SUCCEED)"
definition "CHECK_dres f P = (if P then dRETURN () else let _ = f () in dSUCCEED)"
context includes autoref_syntax begin
lemma CHECK_refine[refine_transfer]:
  "nres_of (CHECK_dres f x) \<le> CHECK f x"
  by (auto simp: CHECK_dres_def CHECK_def)

lemma CHECK_impl[autoref_rules]:
  "(CHECK, CHECK) \<in> (unit_rel \<rightarrow> A) \<rightarrow> bool_rel \<rightarrow> \<langle>unit_rel\<rangle>nres_rel"
  by (auto simp add: CHECK_def nres_rel_def)

definition [simp]: "op_nres_CHECK_bnd f \<Phi> m \<equiv> do {CHECK f \<Phi>; m}"
lemma id_CHECK[autoref_op_pat_def]:
  "do {CHECK f \<Phi>; m} \<equiv> OP op_nres_CHECK_bnd $ f $ \<Phi> $m"
  by simp

lemma op_nres_CHECK_bnd[autoref_rules]:
  "(\<Phi> \<Longrightarrow> (m', m) \<in> \<langle>R\<rangle>nres_rel) \<Longrightarrow>
    (\<Phi>', \<Phi>) \<in> bool_rel \<Longrightarrow>
    (f', f) \<in> unit_rel \<rightarrow> A \<Longrightarrow>
    (do {CHECK f' \<Phi>'; m'}, op_nres_CHECK_bnd $ f $ \<Phi> $ m) \<in> \<langle>R\<rangle>nres_rel"
  by (simp add: CHECK_def nres_rel_def)

lemma CHECK_rule[refine_vcg]:
  assumes "P \<Longrightarrow> RETURN () \<le> R"
  shows "CHECK f P \<le> R"
  using assms
  by (auto simp: CHECK_def)

lemma SPEC_allI:
  assumes "\<And>x. f \<le> SPEC (P x)"
  shows "f \<le> SPEC (\<lambda>r. \<forall>x. P x r)"
  using assms
  by (intro pw_leI) (auto intro!: SPEC_nofail dest!: inres_SPEC)

lemma SPEC_BallI:
  assumes "nofail f"
  assumes "\<And>x. x \<in> X \<Longrightarrow> f \<le> SPEC (P x)"
  shows "f \<le> SPEC (\<lambda>r. \<forall>x\<in>X. P x r)"
  using assms
  by (intro pw_leI) (force intro!: SPEC_nofail dest!: inres_SPEC)

lemma map_option_param[param]: "(map_option, map_option) \<in> (R \<rightarrow> S) \<rightarrow> \<langle>R\<rangle>option_rel \<rightarrow> \<langle>S\<rangle>option_rel"
  by (auto simp: option_rel_def fun_relD)

lemma those_param[param]: "(those, those) \<in> \<langle>\<langle>R\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_rel\<rangle>option_rel"
  unfolding those_def
  by parametricity

lemma image_param[param]:
  shows "single_valued A \<Longrightarrow> single_valued B \<Longrightarrow>
    ((`), (`)) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>B\<rangle>set_rel"
  by (force simp: set_rel_def fun_rel_def elim!: single_valued_as_brE)

end

lemma Up_Down_SPECI:
  assumes a5: "single_valued R"
  assumes a2: "single_valued (S\<inverse>)"
  assumes "SPEC Q \<le> \<Down> (S\<inverse> O R) (SPEC P)"
  shows "\<Up> R (\<Down> S (SPEC Q)) \<le> SPEC P"
proof -
  have "x \<in> Domain R" if a1: "(x, y) \<in> S" and a3: "Q y" for x y
  proof -
    obtain cc :: "('a \<times> 'b) set \<Rightarrow> ('c \<times> 'a) set \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c"
      and bb :: "('a \<times> 'b) set \<Rightarrow> ('c \<times> 'a) set \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b"
      and aa :: "('a \<times> 'b) set \<Rightarrow> ('c \<times> 'a) set \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" where
      f4: "\<forall>x0 x1 x2 x3. (\<exists>v4 v5 v6. x3 = v4 \<and> x2 = v6 \<and> (v4, v5) \<in> x1 \<and> (v5, v6) \<in> x0) = (x3 = cc x0 x1 x2 x3 \<and> x2 = bb x0 x1 x2 x3 \<and> (cc x0 x1 x2 x3, aa x0 x1 x2 x3) \<in> x1 \<and> (aa x0 x1 x2 x3, bb x0 x1 x2 x3) \<in> x0)"
      by moura
    have f5: "RETURN y \<le> \<Down> (S\<inverse> O R) (SPEC P)"
      using a3 by (meson assms(3) dual_order.trans ireturn_rule)
    obtain bba :: "'b set \<Rightarrow> ('c \<times> 'b) set \<Rightarrow> 'c \<Rightarrow> 'b" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> (x2, v3) \<in> x1) = (bba x0 x1 x2 \<in> x0 \<and> (x2, bba x0 x1 x2) \<in> x1)"
      by moura
    then have "y = cc R (S\<inverse>) (bba (Collect P) (S\<inverse> O R) y) y"
      "bba (Collect P) (S\<inverse> O R) y = bb R (S\<inverse>) (bba (Collect P) (S\<inverse> O R) y) y"
      "(cc R (S\<inverse>) (bba (Collect P) (S\<inverse> O R) y) y, aa R (S\<inverse>) (bba (Collect P) (S\<inverse> O R) y) y) \<in> S\<inverse>"
      "(aa R (S\<inverse>) (bba (Collect P) (S\<inverse> O R) y) y, bb R (S\<inverse>) (bba (Collect P) (S\<inverse> O R) y) y) \<in> R"
      using f5 f4 by (meson RETURN_RES_refine_iff relcomp.cases)+
    then show ?thesis
      using a2 a1 by (metis Domain.simps converse.intros single_valued_def)
  qed
  moreover
  from assms have a1: "Collect Q \<subseteq> (S\<inverse> O R)\<inverse> `` Collect P"
    by (auto simp: conc_fun_def)
  have "P x" if Q: "Q z" and a3: "(y, z) \<in> S" and a4: "(y, x) \<in> R" for x y z
  proof -
    obtain bb :: "'b set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> 'c \<Rightarrow> 'b" where
      f7: "\<forall>x0 x1 x2. (\<exists>v3. (v3, x2) \<in> x1 \<and> v3 \<in> x0) = ((bb x0 x1 x2, x2) \<in> x1 \<and> bb x0 x1 x2 \<in> x0)"
      by moura
    have f8: "z \<in> (S\<inverse> O R)\<inverse> `` Collect P"
      using Q a1 by fastforce
    obtain cc :: "('a \<times> 'c) set \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'c" and aa :: "('a \<times> 'c) set \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'a" where
      f9: "z = cc S y z \<and> y = aa S y z \<and> (aa S y z, cc S y z) \<in> S"
      using a3 by simp
    then have f10: "(bb (Collect P) ((S\<inverse> O R)\<inverse>) (cc S y z), cc S y z) \<in> (S\<inverse> O R)\<inverse> \<and> bb (Collect P) ((S\<inverse> O R)\<inverse>) (cc S y z) \<in> Collect P"
      using f8 f7 by (metis (no_types) ImageE)
    have "(z, y) \<in> S\<inverse>"
      using a3 by force
    then show ?thesis
      using f10 f9 a2 a5 a4 by (metis converse.cases mem_Collect_eq relcompEpair single_valued_def)
  qed
  ultimately show ?thesis
    by (auto simp: conc_fun_def abs_fun_def)
qed


lemma nres_rel_comp: "\<langle>A\<rangle>nres_rel O \<langle>B\<rangle>nres_rel = \<langle>A O B\<rangle> nres_rel"
  unfolding nres_rel_def
  apply (auto simp: nres_rel_def conc_fun_def converse_relcomp relcomp_Image split: )
  apply (subst converse_relcomp)
  apply (subst relcomp_Image)
  apply (auto split: nres.splits)
  apply (meson Image_mono RES_leof_RES_iff equalityE le_RES_nofailI leofD leof_lift leof_trans)
  apply (rule relcompI)
   defer apply force
  apply (auto simp: converse_relcomp relcomp_Image)
  done

lemma nres_rel_mono: "A \<subseteq> B \<Longrightarrow> \<langle>A\<rangle>nres_rel \<subseteq> \<langle>B\<rangle>nres_rel"
  apply (auto simp: nres_rel_def conc_fun_def)
  apply (split nres.splits)+
  apply auto
  by (meson Image_mono RES_leof_RES_iff converse_mono equalityE le_RES_nofailI leofD leof_lift leof_trans)

text \<open>TODO: move!!\<close>

lemma \<comment> \<open>TODO: needed  because @{thm dres.transfer_rec_list} expects one argument,
  but functions with more arguments defined by primrec take several arguments\<close>
  uncurry_rec_list: "rec_list (\<lambda>a b. fn a b) (\<lambda>x xs rr a b. fs x xs rr a b) xs a b =
         rec_list (\<lambda>(a,b). fn a b) (\<lambda>x xs rr (a,b). fs x xs (\<lambda>a b. rr (a,b)) a b) xs (a,b)"
  apply (induction xs arbitrary: a b)
   apply (auto split: prod.splits)
  apply metis
  done


lemma Id_br: "Id = br (\<lambda>x. x) top"
  by (auto simp: br_def)

lemma br_rel_prod: "br a I \<times>\<^sub>r br b J = br (\<lambda>(x, y). (a x, b y)) (\<lambda>(x, y). I x \<and> J y)"
  by (auto simp: br_def)

lemma br_list_rel: "\<langle>br a I\<rangle>list_rel = br (map a) (list_all I)"
  apply (auto simp: br_def list_rel_def list_all_iff list_all2_iff split_beta' Ball_def
      in_set_zip intro!: nth_equalityI)
   apply force
  by (metis in_set_conv_nth)

lemma brD: "(c,a)\<in>br \<alpha> I \<Longrightarrow> a = \<alpha> c \<and> I c"
  by (simp add: br_def)


primrec nres_of_nress :: "('b \<Rightarrow> bool) \<Rightarrow> 'b nres list \<Rightarrow> 'b list nres"
  where "nres_of_nress P [] = RETURN []"
  | "nres_of_nress P (x#xs) = do {r \<leftarrow> x; rs \<leftarrow> nres_of_nress P xs; RETURN (r#rs)}"

lemma nres_of_nress_SPEC[THEN order_trans, refine_vcg]:
  assumes [refine_vcg]: "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> SPEC P"
  shows "nres_of_nress P xs \<le> SPEC (list_all P)"
  using assms
  apply (induction xs)
    apply (simp add: )
  apply (simp add:)
  apply (intro refine_vcg)
  subgoal for x xs
    apply (rule order_trans[of _ "SPEC P"])
       apply auto
    apply refine_vcg
    done
  done
context includes autoref_syntax begin
lemma [autoref_op_pat_def]: "nres_of_nress P x \<equiv> (OP (nres_of_nress P) $ x)"
  by auto
lemma nres_of_nress_alt_def[abs_def]:
  "nres_of_nress P xs = rec_list (RETURN []) (\<lambda>x xs xsa. x \<bind> (\<lambda>r. xsa \<bind> (\<lambda>rs. RETURN (r # rs)))) xs"
  by (induction xs) auto

schematic_goal nres_of_nress_impl:
  "(?r, nres_of_nress P $ x) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>nres_rel"
  if [autoref_rules]: "(xi, x) \<in> \<langle>\<langle>A\<rangle>nres_rel\<rangle>list_rel"
  unfolding nres_of_nress_alt_def
  by autoref
concrete_definition nres_of_nress_impl uses nres_of_nress_impl
lemmas [autoref_rules] = nres_of_nress_impl.refine

lemma nres_of_nress_impl_map:
  "nres_of_nress_impl (map f x) =
  rec_list (RETURN []) (\<lambda>x xs r. do { fx \<leftarrow> f x; r \<leftarrow> r; RETURN (fx # r)}) x"
  by (induction x) (auto simp: nres_of_nress_impl_def)

definition [refine_vcg_def]: "list_spec X = SPEC (\<lambda>xs. set xs = X)"

end


lemma
  insert_mem_set_rel_iff:
  assumes "single_valued A"
  shows "(insert x (set xs), XXS) \<in> \<langle>A\<rangle>set_rel \<longleftrightarrow> (\<exists>X XS. (x, X) \<in> A \<and> (set xs, XS) \<in> \<langle>A\<rangle>set_rel \<and> XXS = insert X XS)"
  using assms
  apply (auto simp: set_rel_def single_valuedD)
  subgoal for a
    apply (cases "x \<in> set xs")
    subgoal by (rule exI[where x=a]) auto
    subgoal
      apply (rule exI[where x=a])
      apply auto
      apply (rule exI[where x="{y\<in>XXS. (\<exists>x\<in>set xs. (x, y) \<in> A)}"])
      apply auto
      subgoal by (drule bspec, assumption) auto
      subgoal by (meson single_valuedD)
      done
    done
  done


lemma image_mem_set_rel_iff:
  shows "(f ` x, y) \<in> \<langle>R\<rangle>set_rel \<longleftrightarrow> (x, y) \<in> \<langle>br f top O R\<rangle>set_rel"
proof -
  have "z \<in> Domain ({(c, a). a = f c} O R)"
    if "f ` x \<subseteq> Domain R" "z \<in> x"
    for z
  proof -
    have "(f z, fun_of_rel R (f z)) \<in> R"
      using that
      by (auto intro!: for_in_RI)
    then show ?thesis
      by (auto intro!: Domain.DomainI[where b="fun_of_rel R (f z)"] relcompI[where b="f z"])
  qed
  then show ?thesis
    by (auto simp: set_rel_def relcomp.simps br_def)
qed

lemma finite_list_set_rel[autoref_rules]: "(\<lambda>_. True, finite) \<in> \<langle>A\<rangle>list_set_rel \<rightarrow> bool_rel"
  by (auto simp: list_set_rel_def br_def)

lemma list_set_rel_finiteD: "(xs, X) \<in> \<langle>A\<rangle>list_set_rel \<Longrightarrow> finite X"
  by (auto simp: list_set_rel_def br_def)

lemma set_rel_br: "\<langle>br a I\<rangle>set_rel = br ((`) a) (\<lambda>X. Ball X I)"
  by (auto simp: set_rel_def br_def)

lemma set_rel_sv:
  "\<langle>R\<rangle>set_rel = {(S,S'). S'=R``S \<and> S\<subseteq>Domain R}"
  if "single_valued R"
  using that
  by (auto simp: set_rel_def set_rel_br elim!: single_valued_as_brE)
     (auto simp: br_def)

lemma list_ex_rec_list: "list_ex P xs = rec_list False (\<lambda>x xs b. P x \<or> b) xs"
  by (induct xs) simp_all

lemma list_ex_param[autoref_rules, param]:
  "(list_ex, list_ex) \<in> (A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
  unfolding list_ex_rec_list
  by parametricity

lemma zip_param[autoref_rules, param]:
  "(zip, zip) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A \<times>\<^sub>r A\<rangle>list_rel"
  by (rule param_zip)

lemma ex_br_conj_iff:
  "(\<exists>x. (y, x) \<in> br a I \<and> P x) \<longleftrightarrow> I y \<and> P (a y)"
  by (auto intro!: brI dest!: brD)

setup \<open>
  let
    fun higher_order_rl_of assms ctxt thm =
      let
        val ((_, [thm']), ctxt') = Variable.import true [thm] ctxt
      in
        case Thm.concl_of thm' of
          @{mpat "Trueprop ((_,?t)\<in>_)"} => let
            val (f0, args0) = strip_comb t
            val nargs = Thm.nprems_of thm' - length assms
            val (applied, args) = chop (length args0 - nargs) args0
            val f = betapplys (f0, applied)
          in
            if length args = 0 then
              thm
            else let
              val cT = TVar(("'c",0), @{sort type})
              val c = Var (("c",0),cT)
              val R = Var (("R",0), HOLogic.mk_setT (HOLogic.mk_prodT (cT, fastype_of f)))
              val goal =
                HOLogic.mk_mem (HOLogic.mk_prod (c,f), R)
                |> HOLogic.mk_Trueprop
                |> Thm.cterm_of ctxt
              val res_thm = Goal.prove_internal ctxt' (map (Thm.cprem_of thm') assms) goal (fn prems =>
                REPEAT (resolve_tac ctxt' @{thms fun_relI} 1)
                THEN (resolve_tac ctxt' [thm] 1)
                THEN (REPEAT (resolve_tac ctxt' prems 1))
                THEN (ALLGOALS (assume_tac ctxt'))
              )
            in
              singleton (Variable.export ctxt' ctxt) res_thm
            end
          end
        | _ => raise THM("Expected autoref rule",~1,[thm])
      end

    fun higher_order_rl_attr assms =
      Thm.rule_attribute [] (higher_order_rl_of assms o Context.proof_of)
  in
    Attrib.setup @{binding autoref_higher_order_rule}
      (Scan.optional (Scan.lift(Args.parens (Scan.repeat Parse.nat))) [] >>
       higher_order_rl_attr) "Autoref: Convert rule to higher-order form"
  end
\<close>

end