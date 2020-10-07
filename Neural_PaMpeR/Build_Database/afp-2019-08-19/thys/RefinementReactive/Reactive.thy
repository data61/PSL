theory Reactive
  imports Temporal Refinement
begin
  section\<open>Reactive Systems\<close>

  text\<open>
    In this section we introduce reactive systems which are modeled as 
    monotonic property transformers where properties are predicates on
    traces. We start with introducing some examples that uses LTL to
    specify global behaviour on traces, and later we introduce property
    transformers based on symbolic transition systems.
\<close>

  definition "HAVOC = [:x \<leadsto> y . True:]"
  definition "ASSERT_LIVE = {. \<box> \<diamond> (\<lambda> x . x 0).}"
  definition "GUARANTY_LIVE = [:x \<leadsto> y . \<box> \<diamond> (\<lambda> y . y 0):]"
  definition "AE = ASSERT_LIVE o HAVOC"
  definition "SKIP = [:x \<leadsto> y . x = y:]"

  lemma [simp]: "SKIP = id"
    by (auto simp add: fun_eq_iff SKIP_def demonic_def)

  definition "REQ_RESP = [: \<box>(\<lambda> xs ys . xs (0::nat) \<longrightarrow> (\<diamond> (\<lambda> ys . ys (0::nat))) ys) :]"
  definition "FAIL = \<bottom>"

  lemma "HAVOC o ASSERT_LIVE = FAIL"
    by (auto simp add: HAVOC_def AE_def FAIL_def ASSERT_LIVE_def fun_eq_iff assert_def demonic_def always_def at_fun_def le_fun_def eventually_def)
    

  lemma "HAVOC o AE = FAIL"
    by (auto simp add: HAVOC_def AE_def FAIL_def ASSERT_LIVE_def fun_eq_iff assert_def demonic_def always_def at_fun_def le_fun_def eventually_def)

  lemma "HAVOC o ASSERT_LIVE = FAIL"
    by (auto simp add: HAVOC_def AE_def FAIL_def ASSERT_LIVE_def fun_eq_iff assert_def demonic_def always_def  at_fun_def eventually_def)

  lemma "SKIP o AE = AE"
    by simp

  lemma "(REQ_RESP o AE) = AE"
    proof (auto simp add: fun_eq_iff HAVOC_def AE_def FAIL_def REQ_RESP_def ASSERT_LIVE_def  assert_def 
      demonic_def always_def le_fun_def eventually_def at_fun_def)
      fix x :: "'a \<Rightarrow> bool" 
      fix xa :: "nat \<Rightarrow> bool" 
      fix xb :: nat
      assume "\<forall>xb::nat \<Rightarrow> bool . (\<forall>x. xa x \<longrightarrow> Ex (xb[x ..])) \<longrightarrow> (\<forall>x. \<exists>a. xb (x + a)) \<and> All x"
      then have "(\<forall>x. xa x \<longrightarrow> Ex (xa[x ..])) \<longrightarrow> (\<forall>x. \<exists>a. xa (x + a)) \<and> All x"
        by auto
      then show "\<exists>x. xa (xb + x)"
        by (auto, rule_tac x = 0 in exI, simp)
    next
      fix x :: "'a \<Rightarrow> bool" 
      fix xa :: "nat \<Rightarrow> bool" 
      fix xb :: 'a
      assume "\<forall>xb::nat \<Rightarrow> bool . (\<forall>x. xa x \<longrightarrow> Ex (xb[x ..])) \<longrightarrow> (\<forall>x. \<exists>a. xb (x + a)) \<and> All x"
      from this show "x xb"
        by (metis at_trace_def le0)
    next
      fix x :: "'a \<Rightarrow> bool" and xa :: "nat \<Rightarrow> bool" and xb :: "nat \<Rightarrow> bool" and xc :: nat
      assume A: "\<forall>x. xa x \<longrightarrow> Ex (xb[x ..])"
      assume B: "\<forall>x. \<exists>xb. xa (x + xb)"
      have "\<exists>x1. xc \<le> AbsNat x1" by (metis (full_types) le_add2 plus_Nat_def)
      thus "\<exists>x. xb (xc + x)" using A B by (metis AbsNat_plus add.commute at_trace_def le_Suc_ex trans_le_add2)
   qed


  subsection\<open>Symbolic transition systems\<close>
  
  text\<open>
    In this section we introduce property transformers basend on symbolic
    transition systems. These are systems with local state. The execution
    starts in some initial state, and with some input value the system computes
    a new state and an output value. Then using the current state, and a 
    new input value the system computes a new state, and a new output, and
    so on. The system may fail if at some point the input and the current 
    state do not statisfy a required predicate.

    In the folowing definitions the variables $u$, $x$, $y$ stand for the
    state of the system, the input, and the output respectively. The $init$ 
    is the property that the initial state should satisfy. The predicate
    $p$ is the precondition of the input and the current state, and the
    relation $r$ gives the next state and the output based on the
    input and the current state.
\<close>
 
  definition "fail_sys init p r x = (\<exists> n u y . u \<in> init \<and> (\<forall> i < n . r (u i) (u (Suc i)) (x i) (y i)) \<and> (\<not> p (u n) (u (Suc n)) (x n)))"
  definition "run r u x y = (\<forall> i . r (u i) (u (Suc i)) (x i) (y i))"
  definition "LocalSystem init p r q x = (\<not> fail_sys init p r x \<and> (\<forall> u y . (u \<in> init \<and> run r u x y) \<longrightarrow> q y))"

  lemma "fail (LocalSystem init p r) = fail_sys init p r"
    by (simp add: fun_eq_iff LocalSystem_def fail_def fail_sys_def run_def)

  definition "inpt_st r u u' x =  (\<exists> y . r u u' x y)"

  definition "lft_pred_st p u x = p (u (0::nat)) (u 1) (x (0::nat))"

  definition "lft_pred_loc_st p u x = p (u (0::nat)) (x (0::nat))"

  definition "lft_rel_st r u x y = r (u (0::nat)) (u 1) (x (0::nat)) (y (0::nat))"

  definition "prec_st p r = -((lft_pred_st (inpt_st r)) until -(lft_pred_st p))"

  lemma prec_st_simp: "prec_st p r u x = (\<forall> n . (\<forall> i < n . inpt_st r (u i) (u (Suc i)) (x i)) \<longrightarrow> p (u n) (u (Suc n)) (x n))"
    by (simp add: prec_st_def until_def lft_pred_st_def inpt_st_def at_fun_def, metis)

  definition "SymSystem init p r = [:z \<leadsto>  u, x . u \<in> init \<and> z = x:] o {.u, x . prec_st p r u x.} o 
      [:u, x \<leadsto> y . (\<box> (lft_rel_st r)) u x y :]"

  lemma SymSystem_rel: "SymSystem init p r = {. x . \<forall>u. u \<in> init \<longrightarrow> prec_st p r u x .} \<circ> 
    [: x \<leadsto> y . \<exists> u . u \<in> init \<and> (\<box> lft_rel_st r) u x y :] "
    proof -
      have [simp]:  "((\<lambda>z (u, x). u \<in> init \<and> z = x) OO (\<lambda>(x, y). (\<box> lft_rel_st r) x y)) = (\<lambda>x y. \<exists>u. u \<in> init \<and> (\<box> lft_rel_st r) u x y)"
        by auto
      show ?thesis by  (simp add: SymSystem_def demonic_assert_comp comp_assoc demonic_demonic)
    qed

  theorem "SymSystem init p r q x = LocalSystem init p r q x"
    proof
      assume "SymSystem init p r q x"
      then show "LocalSystem init p r q x"
        apply (auto simp add: SymSystem_def LocalSystem_def assert_def 
          demonic_def prec_st_simp lft_rel_st_def lft_pred_st_def inpt_st_def
          always_def  le_fun_def fail_sys_def run_def at_fun_def)
        by metis
    next
      assume "LocalSystem init p r q x"
      then show "SymSystem init p r q x"
        apply (auto simp add: SymSystem_def LocalSystem_def assert_def 
          demonic_def prec_st_simp lft_rel_st_def lft_pred_st_def inpt_st_def
          always_def  le_fun_def fail_sys_def run_def at_fun_def)
        by metis
    qed

  definition "local_init init S = Inf (S ` init)"

  definition "zip_set A B = {u . ((fst o u) \<in> A) \<and> ((snd o u) \<in> B)}"
  definition nzip:: "('x \<Rightarrow> 'a) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> ('a\<times>'b)" (infixl "||" 65) where "(xs || ys) i = (xs i, ys i)"

  lemma [simp]: "fst \<circ> x || y = x"
    by (simp add: fun_eq_iff nzip_def)

  lemma [simp]: "snd \<circ> x || y = y"
    by (simp add: fun_eq_iff nzip_def)

  lemma [simp]: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> (x || y) \<in> zip_set A B"
    by (simp add: zip_set_def)

  lemma local_demonic_init: "local_init init (\<lambda> u . {. x . p u x.} o [:x \<leadsto> y . r u x y :]) = 
        [:z \<leadsto> u, x . u \<in> init \<and> z = x:] o {.u, x . p u x.} o [:u, x \<leadsto> y . r u x y :]"
    by (auto simp add: fun_eq_iff demonic_def assert_def local_init_def le_fun_def)

  lemma local_init_comp: "u' \<in> init' \<Longrightarrow> (\<forall> u. sconjunctive (S u)) \<Longrightarrow> (local_init init S) o (local_init init' S') 
                       = local_init (zip_set init init') (\<lambda> u . (S (fst o u)) o (S' (snd o u)))"
      proof (subst fun_eq_iff, auto)
        fix x :: 'f
        assume A: "u' \<in> init'"
        assume "\<forall> u . sconjunctive (S u)"
        from this have [simp]: "\<And> u . sconjunctive (S u)" by simp
        from A have [simp]: "\<And> y . S y (INF y' \<in> init'. S' y' x) =  (INF y' \<in> init' . S y (S' y' x))"
          by (simp add: sconjunctive_INF_simp image_comp)

        have [simp]: "(INF y \<in> init . (INF y' \<in> init' . S y (S' y' x))) \<le> (INF u \<in> zip_set init init'. S (fst \<circ> u) (S' (snd \<circ> u) x))"
          proof (rule INF_greatest, auto simp add: zip_set_def)
            fix u :: "'a \<Rightarrow> 'c \<times> 'b"
            assume [simp]: "fst \<circ> u \<in> init"
            assume [simp]: "snd \<circ> u \<in> init'"
            have "(INF y \<in> init. INF y' \<in> init'. S y (S' y' x)) \<le> (INF y' \<in> init'. S (fst o u) (S' y' x))"
              by (rule INF_lower, simp)
            also have "... \<le> S (fst o u) (S' (snd o u) x)"
              by (rule INF_lower, simp)
            finally show "(INF y \<in> init. INF y' \<in> init'. S y (S' y' x)) \<le> S (fst o u) (S' (snd o u) x)"
              by simp
          qed
        have [simp]: "(INF u \<in> zip_set init init'. S (fst \<circ> u) (S' (snd \<circ> u) x)) \<le> (INF y \<in> init . (INF y' \<in> init' . S y (S' y' x)))"
          proof (rule INF_greatest, rule INF_greatest)
            fix y :: "'a \<Rightarrow> 'c" and y':: "'a \<Rightarrow> 'b"
            assume [simp]: "y \<in> init"
            assume [simp]: "y' \<in> init'"
            have "(INF u \<in> zip_set init init'. S (fst \<circ> u) (S' (snd \<circ> u) x)) \<le> S (fst o (y || y')) (S' (snd o (y || y')) x)"
              by (rule INF_lower, simp)
            also have "... \<le>  S y (S' y' x)"
              by simp
            finally show "(INF u :: 'a \<Rightarrow> 'c \<times> 'b \<in> zip_set init init'. S (fst \<circ> u) (S' (snd \<circ> u) x)) \<le> S y (S' y' x)"
              by simp
          qed
        have "local_init init S (local_init init' S' x) = (INF y \<in> init. S y (INF y' \<in> init'. S' y' x)) "
          by (simp add: local_init_def image_comp)
        also have "... = (INF y \<in> init . (INF y' \<in> init' . S y (S' y' x)))"
          by simp
        also have "... = (INF u \<in> zip_set init init'. S (fst \<circ> u) \<circ> S' (snd \<circ> u)) x"
         by (rule antisym) (simp_all add: image_comp)
        also have "... = local_init (zip_set init init') (\<lambda> u . (S (fst o u)) o (S' (snd o u))) x"
          by (simp add: local_init_def)
        finally show "local_init init S (local_init init' S' x) = local_init (zip_set init init') (\<lambda>u::'a \<Rightarrow> 'c \<times> 'b. S (fst \<circ> u) \<circ> S' (snd \<circ> u)) x"
          by simp
      qed

  lemma init_state: "[:z \<leadsto> u, x . u \<in> init \<and> z = x:] o {.u, x . p u x.} o [:u, x \<leadsto> y . r u x y :] 
      = [:z \<leadsto> u, x . z = x:] o {.u, x . u \<in> init \<longrightarrow> p u x.} o [:u, x \<leadsto> y . u \<in> init \<and> r u x y :]"
    by (auto simp add: fun_eq_iff demonic_def assert_def local_init_def le_fun_def)

  lemma always_lft_rel_comp: "(\<box> lft_rel_st r) (fst \<circ> u) OO (\<box> lft_rel_st r') (snd \<circ> u) 
              = (\<box> lft_rel_st (\<lambda> (u, v) (u', v') . ((r u u') OO (r' v v')))) u"
    proof (auto simp add: fun_eq_iff lft_rel_st_def always_def at_fun_def relcompp_exists)
      fix x::"nat \<Rightarrow>'a" and
          y::"nat \<Rightarrow> 'b" and
          v::"nat \<Rightarrow> 'c" and
          n:: nat
      assume "\<forall>i . r (fst (u i)) (fst (u (Suc i))) (x i) (v i)"
      and "\<forall>i . r' (snd (u i)) (snd (u (Suc i))) (v i) (y i)"
      from this show "(case u n of (u, v) \<Rightarrow> \<lambda>(u', v'). r u u' OO r' v v') (u (Suc n)) (x n) (y n)"
        by (metis (mono_tags, lifting)  prod.case_eq_if relcompp.relcompI)
    next
      fix x::"nat \<Rightarrow>'a" and
          z::"nat \<Rightarrow> 'b"
      define a where "a n = (SOME y . r (fst (u n)) (fst (u (Suc n))) (x n) y \<and> r' (snd (u n)) (snd (u (Suc n))) y (z n))"
        for n
      assume "\<forall>i . (case u i of (u, v) \<Rightarrow> \<lambda>(u', v'). r u u' OO r' v v') (u (Suc i)) (x i) (z i)"
      from this and a_def have "(\<forall>i :: nat. r (fst (u i)) (fst (u (Suc i))) (x i) (a i)) \<and> (\<forall>i :: nat. r' (snd (u i)) (snd (u (Suc i))) (a i) (z i))"
        apply auto
          apply (metis (mono_tags, lifting) pick_middlep prod.collapse split_conv tfl_some)
          by (metis (mono_tags, lifting) pick_middlep prod.collapse split_conv tfl_some)
     from this show "\<exists> a . (\<forall>i . r (fst (u i)) (fst (u (Suc i))) (x i) (a i)) \<and> (\<forall>i . r' (snd (u i)) (snd (u (Suc i))) (a i) (z i))"
      by blast
    qed

 theorem SymSystem_comp: "u' \<in> init' \<Longrightarrow> SymSystem init p r o SymSystem init' p' r' 
                   = [:z \<leadsto> u, x . fst o u \<in> init \<and> snd o u \<in> init' \<and> z = x:] 
                   o {. u, x . prec_st p r (fst \<circ> u) x \<and> (\<forall>y. (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> prec_st p' r' (snd \<circ> u) y) .} 
                   o [: u, x \<leadsto> y . (\<box> lft_rel_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v')) u x y :]"
                   (is "?p \<Longrightarrow> ?S  = ?T")
    proof -
      assume A: "?p"
      have "?S = 
        [: z \<leadsto> (u, x) . u \<in> init \<and> z = x :] \<circ> {.x, y. prec_st p r x y.} \<circ>
        [: id (\<lambda>(u, x). id ((\<box> lft_rel_st r) u x)) :] \<circ>
        ([: z \<leadsto> u, x . u \<in> init' \<and> z = x :] \<circ> {.x, y. prec_st p' r' x y.} \<circ>
        [: id (\<lambda>(u, x). id ((\<box> lft_rel_st r') u x)) :])"
        by (unfold SymSystem_def, simp)
      also have "... =  local_init init (\<lambda>u::nat \<Rightarrow> 'e. {. id (prec_st p r u) .} \<circ> [: id (\<lambda>x. id ((\<box> lft_rel_st r) u x)) :]) \<circ>
          local_init init' (\<lambda>u. {. id (prec_st p' r' u) .} \<circ> [: id (\<lambda>x::nat \<Rightarrow> 'd. id ((\<box> lft_rel_st r') u x)) :])"
        by (unfold local_demonic_init [THEN sym], simp)
      also from A have "... = local_init (zip_set init init')
            (\<lambda>u. {. prec_st p r (fst \<circ> u) .} \<circ> [: (\<box> lft_rel_st r) (fst \<circ> u) :] \<circ> ({. prec_st p' r' (snd \<circ> u) .} \<circ> [: (\<box> lft_rel_st r') (snd \<circ> u) :]))"
              by (simp add: local_init_comp)
      also have " ... = local_init (zip_set init init')
         (\<lambda>u. {. prec_st p r (fst \<circ> u) .} \<circ> [: (\<box> lft_rel_st r) (fst \<circ> u) :] \<circ> {. prec_st p' r' (snd \<circ> u) .} \<circ> [: (\<box> lft_rel_st r') (snd \<circ> u) :])"
      by (simp add: comp_assoc [THEN sym])
      also have "... =  local_init (zip_set init init')
        (\<lambda>u.{. x . prec_st p r (fst \<circ> u) x \<and> (\<forall>y. (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> prec_st p' r' (snd \<circ> u) y) .} \<circ>
            [: (\<box> lft_rel_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v')) u :]) "
         by (simp add: assert_demonic_comp always_lft_rel_comp)
    also have "... = local_init (zip_set init init')
     (\<lambda>u.{.x. prec_st p r (fst \<circ> u) x \<and> (\<forall>y::nat \<Rightarrow> 'd. (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> prec_st p' r' (snd \<circ> u) y).} \<circ>
         [: id (\<lambda>x::nat \<Rightarrow> 'c. id ((\<box> lft_rel_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v')) u x)) :])"
       by simp
    also have "... = ?T"
     by (unfold local_demonic_init, simp add: zip_set_def)
   finally show ?thesis by simp
   qed

  lemma always_lft_rel_comp_a: "(\<box> lft_rel_st r) u OO (\<box> lft_rel_st r') v 
              = (\<box> lft_rel_st (\<lambda> (u, v) (u', v') . ((r u u') OO (r' v v')))) (u || v)"
      by (unfold always_lft_rel_comp [THEN sym], auto)


  theorem SymSystem_comp_a: "u' \<in> init' \<Longrightarrow> SymSystem init p r o SymSystem init' p' r' 
                   = {.x . \<forall> u v . u \<in> init \<and> v \<in> init' \<longrightarrow> (prec_st p r u x \<and> (\<forall>y. (\<box> lft_rel_st r) u x y \<longrightarrow> prec_st p' r' v y)) .} 
                   o [: x \<leadsto> y . \<exists> u v . u \<in> init \<and> v \<in> init' \<and> (\<box> lft_rel_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v')) (u || v) x y :]"
                   (is "?p \<Longrightarrow> ?S = ?T")
    proof -
      assume A: "u' \<in> init'"
      from A have [simp]: "(\<lambda>x. (\<forall>u. u \<in> init \<longrightarrow> prec_st p r u x) \<and> (\<forall>y. (\<exists>u. u \<in> init \<and> (\<box> lft_rel_st r) u x y) \<longrightarrow> (\<forall>u. u \<in> init' \<longrightarrow> prec_st p' r' u y)))
          = (\<lambda>x. \<forall>u v. u \<in> init \<and> v \<in> init' \<longrightarrow> prec_st p r u x \<and> (\<forall>y. (\<box> lft_rel_st r) u x y \<longrightarrow> prec_st p' r' v y))"
          by (auto simp add: fun_eq_iff)
      have [simp]: "(\<lambda>x y. \<exists>u. u \<in> init \<and> (\<box> lft_rel_st r) u x y) OO (\<lambda>x y. \<exists>u. u \<in> init' \<and> (\<box> lft_rel_st r') u x y) 
        = (\<lambda> x y . \<exists> u v . u \<in> init \<and> v \<in> init' \<and> (((\<box> lft_rel_st r) u) OO ((\<box> lft_rel_st r') v)) x y)"
        by (auto simp add: fun_eq_iff)

      from A have "?S = {.x . \<forall>u . u \<in> init \<longrightarrow> prec_st p r u x.} \<circ> 
            [: x \<leadsto> y . \<exists>u::nat \<Rightarrow> 'e. u \<in> init \<and> (\<box> lft_rel_st r) u x y :] \<circ>
            ({.x. \<forall>u . u \<in> init' \<longrightarrow> prec_st p' r' u x.} \<circ> [: x \<leadsto> y . \<exists>u . u \<in> init' \<and> (\<box> lft_rel_st r') u x y :])"
        by (simp add: SymSystem_rel)
       also have "... = {. \<lambda>x . \<forall>u . u \<in> init \<longrightarrow> prec_st p r u x .} \<circ> [: x \<leadsto> y . \<exists>u . u \<in> init \<and> (\<box> lft_rel_st r) u x y :] \<circ> 
          {. x . \<forall>u . u \<in> init' \<longrightarrow> prec_st p' r' u x .} \<circ> [: x \<leadsto> y . \<exists>u . u \<in> init' \<and> (\<box> lft_rel_st r') u x y :]"
          by (simp add: comp_assoc [THEN sym])
       also have "... = ?T"
          by (simp add: assert_demonic_comp always_lft_rel_comp_a)
      finally show ?thesis
        by simp
     qed

  text\<open>We show next that the composition of two SymSystem $S$ and $S'$ is not equal to the SymSystem of the 
  compostion of local transitions of $S$ and $S'$\<close>

  definition "initS = {u . fst (u (0::nat)) = (0::nat)}"
  definition "localPrecS = (\<top>:: nat \<times> nat  \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool)"
  definition "localRelS = (\<lambda> (u::nat, v) (u', v'::nat) (x::nat) (y::nat) . u = 0 \<and> u' = 1 \<and> v = v')"

  definition "initS' = (\<top>::(nat \<Rightarrow> (nat \<times> nat)) set)"
  definition "localPrecS' = (\<bottom>:: nat \<times> nat  \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool)"
  definition "localRelS' = (\<lambda> (u::nat, v) (u', v'::nat) (x::nat) (y::nat) . u = u')"

  definition "symbS = SymSystem initS localPrecS localRelS"
  definition "symbS' = SymSystem initS' localPrecS' localRelS'"

  definition "localPrecSS' = (\<lambda>(u::nat, v::nat) (u', v') (x::nat) . 0 < u)"
  definition "localRelSS' = (\<lambda> (u, v::nat) (u'::nat, v'::nat) (x::nat) (z::nat) . (u::nat) = 0 \<and> u' = 1)"

  lemma localSS'_aux: "( \<lambda>x. \<forall> (a::nat) (aa::nat) (b::nat). \<not> (case x of (x::nat, u::nat, v::nat) \<Rightarrow> \<lambda>ab. u = 0 \<and> 
    (case ab of (y, u', v') \<Rightarrow> u' = Suc 0 \<and> v = v')) (a, aa, b)) 
    = (\<lambda> (x, u, v) . u > 0)"
    by (auto simp add: fun_eq_iff)


  lemma localSS'_aux_b: "((\<lambda>(x, u, v) ab. u = 0 \<and> (case ab of (y, u', v') \<Rightarrow> u' = Suc 0 \<and> v = v')) OO (\<lambda>(x, u, v) (y, u', v'). u = u')) 
    = (\<lambda> (x, u, v) (y, u', v') . u = 0 \<and> u' = 1)"
    by (simp add: fun_eq_iff relcompp_exists)

  lemma "{.x, (u, v) . localPrecS (u, v) (a,b) x.} o [:x, (u,v) \<leadsto> y, (u',v') . localRelS (u,v) (u',v') x y:] o 
         {.x, (u, v) . localPrecS' (u, v) (c, d) x.} o [:x, (u,v) \<leadsto> y, (u',v') . localRelS' (u,v) (u',v') x y:]
       = {.x, (u, v) . localPrecSS' (u, v) (e, f) x.} o [:x, (u,v) \<leadsto> y, (u',v') . localRelSS' (u,v) (u',v') x y:]"
    by (simp add: assert_demonic_comp localPrecS'_def localPrecS_def localRelS_def localRelS'_def 
      relcompp_exists localPrecSS'_def localRelSS'_def localSS'_aux localSS'_aux_b)

  lemma [simp]: "[: \<bottom>::('a \<Rightarrow> 'b => ('c::boolean_algebra)) :] = \<top>"
    by (simp add: fun_eq_iff demonic_def)

  definition "symbSS' = SymSystem initS localPrecSS' localRelSS'"

  lemma symbSS'_aux: "( \<lambda>x. \<forall>u. fst (u 0) = 0 \<longrightarrow>
                (\<forall>n. (\<forall>i<n. Ex ((case u i of (u, v) \<Rightarrow> \<lambda>(u', v'::nat) x z. u = 0 \<and> u' = Suc 0) (u (Suc i)) (x i))) 
                \<longrightarrow> (case u n of (u, v) \<Rightarrow> \<lambda>(u', v') x. 0 < u) (u (Suc n)) (x n)) ) = \<bottom>"
    apply (auto simp add: fun_eq_iff)
    by (rule_tac x = "\<lambda> i . (i::nat, i)" in exI, simp)

  lemma symbSS': "symbSS' = \<bottom>"
    by (simp add: symbSS'_def SymSystem_rel initS_def localPrecSS'_def localRelSS'_def prec_st_simp inpt_st_def symbSS'_aux)

  lemma symbS: "symbS = \<top>"
    proof (simp add: symbS_def SymSystem_rel initS_def localPrecS_def localRelS_def)
      have [simp]: "(\<lambda>x. \<forall>u. fst (u 0) = 0 \<longrightarrow> prec_st \<top> (\<lambda> (u, v) (u', v') x y . u = 0 \<and> u' = Suc 0 \<and> v = v') u x) = \<top>"
        by (simp_all add: fun_eq_iff prec_st_def always_def lft_rel_st_def at_fun_def lft_pred_st_def inpt_st_def until_def)
  
    have [simp]: "(\<lambda>x y. \<exists>u. fst (u 0) = 0 \<and> (\<box> lft_rel_st (\<lambda> (u, v) (u', v') (x) (y). u = 0 \<and> u' = Suc 0 \<and> v = v')) u x y) = \<bottom>"
      proof (auto simp add: fun_eq_iff always_def lft_rel_st_def at_fun_def)
      fix x::"nat \<Rightarrow> 'a" and xa :: "nat \<Rightarrow> 'b" and u::"nat \<Rightarrow> nat \<times> 'c"
      assume A: "\<forall>a . (case u a of (e, f) \<Rightarrow> \<lambda>(u', v') x y. e = 0 \<and> u' = Suc 0 \<and> f = v') (u (Suc a)) (x a) (xa a)" 
      {fix n:: nat
        from A have "fst (u n) = 0 \<and> fst (u (Suc n)) = Suc 0"
          by (drule_tac x = n in spec, case_tac "u n", case_tac "u (Suc n)", auto)
      }
      note B = this
      then have "fst (u (Suc 0)) =  0" by auto
      moreover have "fst (u (Suc 0)) =  Suc 0" using B [of 0] by auto
      ultimately show "(0) < fst (u (0))" by auto
    qed

    show "{. \<lambda>x. \<forall>u. fst (u 0) = 0 \<longrightarrow> prec_st \<top> (\<lambda>(u, v) (u', v') x y. u = 0 \<and> u' = Suc 0 \<and> v = v') u x .} \<circ>
            [: \<lambda> x y . \<exists>u . fst (u 0) = 0 \<and> (\<box> lft_rel_st (\<lambda>(u, v) (u', v') x y. u = 0 \<and> u' = Suc 0 \<and> v = v')) u x y :] =
            \<top>"
      by simp
    qed

  lemma "symbS o symbS' \<noteq> symbSS'"
    by (simp add: symbSS' symbS fun_eq_iff)

  lemma prec_st_inpt: "prec_st (inpt_st r) r = (\<box> (lft_pred_st (inpt_st r)))"
    by (simp add: prec_st_def neg_until_always)

  lemma "grd (SymSystem init p r) = Sup ((- prec_st p r \<squnion> (\<box> (lft_pred_st (inpt_st r)))) ` init)"
    proof (unfold fun_eq_iff, auto simp add: grd_def SymSystem_rel demonic_def assert_def)
      fix x :: "nat \<Rightarrow> 'a" and  xa :: "nat \<Rightarrow> 'b" and  u :: "nat \<Rightarrow> 'c"
      assume "\<forall>xa::nat \<Rightarrow> 'c\<in>init. prec_st p r xa x \<and> \<not> (\<box> lft_pred_st (inpt_st r)) xa x"
      and "u \<in> init"
      and "(\<box> lft_rel_st r) u x xa"
      then show "False"
        by (auto simp add: always_def lft_pred_st_def inpt_st_def at_fun_def lft_rel_st_def)
    next
      fix x :: "nat \<Rightarrow> 'a" and  xa :: "nat \<Rightarrow> 'c"
      assume B: "xa \<in> init"
      assume "(\<lambda>y . \<exists>u . u \<in> init \<and> (\<box> lft_rel_st r) u x y) \<le> \<bottom>"
      then have A: "\<forall> y u . u \<notin> init \<or> \<not> (\<box> lft_rel_st r) u x y"
        by auto
      let ?y = "\<lambda> n . (SOME z . r (xa n) (xa (Suc n)) (x n) z)"
      from B and A have "\<not> (\<box> lft_rel_st r) xa x ?y" by simp
      moreover assume "(\<box> lft_pred_st (inpt_st r)) xa x"
      ultimately show "False"
        apply (simp add: always_def lft_pred_st_def inpt_st_def at_fun_def lft_rel_st_def)
        by (metis (full_types) tfl_some)
   qed

 
  definition "guard S = {.((grd S)::'a\<Rightarrow>bool).} o S"

  lemma "((grd (local_init init S))::'a\<Rightarrow>bool) = Sup ((grd o S) ` init)"
    by (simp add: fun_eq_iff local_init_def assert_def grd_def)

  lemma "u \<in> init \<Longrightarrow> guard ([:z \<leadsto> u, x . u \<in> init \<and> z = x:] o {.u, x . p u x.} o [:u, x \<leadsto> y . r u x y :])
      = [:z \<leadsto> u, x . u \<in> init \<and> z = x:] o {.u, x . u \<in> init \<and> (\<exists>a. a \<in> init \<and> (p a x \<longrightarrow> Ex (r a x))) \<and> p u x.} o [:u, x \<leadsto> y . ((r u x y)::bool) :]"
    by (auto simp add: fun_eq_iff local_init_def guard_def grd_def assert_def demonic_def le_fun_def)

  lemma inpt_str_comp_aux: "(\<forall>n. (\<forall>i<n. inpt_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v') (u i) (u (Suc i)) (x i)) \<longrightarrow>
        inpt_st r (fst (u n)) (fst (u (Suc n))) (x n) \<and> (\<forall>y. r (fst (u n)) (fst (u (Suc n))) (x n) y \<longrightarrow> inpt_st r' (snd (u n)) (snd (u (Suc n))) y)) \<longrightarrow>
        (\<forall> i < n . inpt_st r ((fst o u) i) ((fst o u) (Suc i)) (x i) \<and> (\<forall>y. r (fst (u i)) (fst (u (Suc i))) (x i) y \<longrightarrow> inpt_st r' (snd (u i)) (snd (u (Suc i))) y))"
        (is "(\<forall> n . ?p n) \<longrightarrow> ?q n")
    proof (induction n)
      case 0
      show ?case by auto
    next
      case (Suc n)
      show ?case
        proof auto
          fix i::nat
          assume B: "\<forall> n . ?p n"
          then have A: "?p n" (is "?A \<longrightarrow> ?B")
               by simp
          from Suc and B have C: "?q n"
            by simp
          assume "i < Suc n"
          then show "inpt_st r (fst (u i)) (fst (u (Suc i))) (x i)"
            proof cases
              assume "i < n"
              then show ?thesis
                by (metis Suc.IH B comp_apply)
           next
             assume "\<not> i < n"
             from this and \<open>i < Suc n\<close> have [simp]: "i = n" by simp
             show ?thesis
               proof cases
                assume "?A"
                from this and A have D: "?B" by simp
                from D show ?thesis
                  by (metis \<open>i = n\<close>)
              next
                assume "\<not> ?A"
                then obtain j where j: "j < n \<and> \<not> inpt_st (\<lambda> (u, v) . \<lambda> (u', v') . r u u' OO r' v v') (u j) (u (Suc j)) (x j)"
                  by auto
                with C have "inpt_st r (fst (u j)) (fst (u (Suc j))) (x j) \<and> (\<forall>y. r (fst (u j)) (fst (u (Suc j))) (x j) y \<longrightarrow> inpt_st r' (snd (u j)) (snd (u (Suc j))) y)"
                  by auto
                with j show ?thesis
                  apply (case_tac "u j")
                  apply (case_tac "u (Suc j)")
                  apply (simp add: inpt_st_def)
                  by (metis relcompp.relcompI)
              qed
         qed
     next
          fix i::nat fix y :: 'e
          assume B: "\<forall> n . ?p n"
          then have A: "?p n" (is "?A \<longrightarrow> ?B")
               by simp
          from Suc and B have C: "\<forall>i<n. inpt_st r (fst (u i)) (fst (u (Suc i))) (x i) \<and> (\<forall>y. r (fst (u i)) (fst (u (Suc i))) (x i) y \<longrightarrow> inpt_st r' (snd (u i)) (snd (u (Suc i))) y)"
            by simp
          assume E: "r (fst (u i)) (fst (u (Suc i))) (x i) y"
          assume "i < Suc n"
          then show "inpt_st r' (snd (u i)) (snd (u (Suc i))) y"
            proof cases
              assume "i < n"
              from this and E and C show ?thesis
                by simp
           next
             assume "\<not> i < n"
             from this and \<open>i < Suc n\<close> have [simp]: "i = n" by simp
             show ?thesis
               proof (cases ?A)
                case True
                with A have D: "?B" by simp
                from D and E show ?thesis
                  by (metis \<open>i = n\<close>)
              next
                case False
                then obtain j where j: "j < n \<and> \<not> inpt_st (\<lambda> (u, v) . \<lambda> (u', v') . r u u' OO r' v v') (u j) (u (Suc j)) (x j)"
                  by auto
                with C have "inpt_st r (fst (u j)) (fst (u (Suc j))) (x j) \<and> (\<forall>y. r (fst (u j)) (fst (u (Suc j))) (x j) y \<longrightarrow> inpt_st r' (snd (u j)) (snd (u (Suc j))) y)"
                  by auto
                with j show ?thesis
                  by (case_tac "u j", case_tac "u (Suc j)", simp add: inpt_st_def, metis relcompp.relcompI)
              qed
         qed
     qed
  qed
                     
  lemma inpt_str_comp_aux_a: "(\<forall>n. (\<forall>i<n. inpt_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v') (u i) (u (Suc i)) (x i)) \<longrightarrow>
        inpt_st r (fst (u n)) (fst (u (Suc n))) (x n) \<and> (\<forall>y. r (fst (u n)) (fst (u (Suc n))) (x n) y \<longrightarrow> inpt_st r' (snd (u n)) (snd (u (Suc n))) y)) \<Longrightarrow>
        inpt_st r ((fst o u) n) ((fst o u) (Suc n)) (x n) \<and> (\<forall>y. r (fst (u n)) (fst (u (Suc n))) (x n) y \<longrightarrow> inpt_st r' (snd (u n)) (snd (u (Suc n))) y)"
    by (cut_tac n = "Suc n" and r = r and r' = r' and u = u and x = x in inpt_str_comp_aux, simp)

  definition "rel_st r r' = (\<lambda> (u, v) (u', v') x z . inpt_st r u u' x \<and> (\<forall> y . r u u' x y \<longrightarrow> inpt_st r' v v' y) \<and> (r u u' OO r' v v') x z)"

  lemma inpt_str_comp_a: "(prec_st (inpt_st r) r (fst \<circ> u) x \<and> (\<forall>y. (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> prec_st (inpt_st r') r' (snd \<circ> u) y)) = 
    prec_st (\<lambda> u u' x . inpt_st r (fst u) (fst u') x \<and> (\<forall> y . r (fst u) (fst u') x y \<longrightarrow> (inpt_st r' (snd u) (snd u') y))) (\<lambda>(u, v) (u', v'). r u u' OO r' v v') u x"
    proof (auto simp add: prec_st_inpt prec_st_simp)
      fix n:: nat
      assume "(\<box> lft_pred_st (inpt_st r)) (fst \<circ> u) x"
      then show "inpt_st r (fst (u n)) (fst (u (Suc n))) (x n)"
        by (simp add: always_def lft_pred_st_def at_fun_def)
    next
      fix n:: nat and y :: 'c
      assume A: "(\<box> lft_pred_st (inpt_st r)) (fst \<circ> u) x"
      assume B: "r (fst (u n)) (fst (u (Suc n))) (x n) y"
      assume C: "\<forall>i<n. inpt_st (\<lambda>(u::'a, v::'d) (u'::'a, v'::'d). r u u' OO r' v v') (u i) (u (Suc i)) (x i)"
      let ?y = "\<lambda> i . (if i = n then y else (SOME y . r ((fst o u) i) ((fst o u) (Suc i)) (x i) y))"
      assume "\<forall>y . (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> (\<box> lft_pred_st (inpt_st r')) (snd \<circ> u) y"
      then have D: "(\<box> lft_rel_st r) (fst \<circ> u) x ?y \<longrightarrow> (\<box> lft_pred_st (inpt_st r')) (snd \<circ> u) ?y"
        by simp
      from A and B have E: "(\<box> lft_rel_st r) (fst \<circ> u) x ?y"
        apply (auto simp add: always_def at_fun_def lft_rel_st_def lft_pred_st_def inpt_st_def)
        by (metis tfl_some)
      from D and E have "(\<box> lft_pred_st (inpt_st r')) (snd \<circ> u) ?y" by simp

      from A and E and this show "inpt_st r' (snd (u n)) (snd (u (Suc n))) y"
        apply (simp add: always_def lft_pred_st_def at_fun_def)
        apply (drule_tac x = n in spec)
        apply (drule_tac x = n in spec)
        by (drule_tac x = n in spec, simp)
    next
      assume "\<forall> n . (\<forall>i<n. inpt_st (\<lambda>(u::'a, v::'d) (u'::'a, v'::'d). r u u' OO r' v v') (u i) (u (Suc i)) (x i)) \<longrightarrow>
            inpt_st r (fst (u n)) (fst (u (Suc n))) (x n) \<and> (\<forall>y::'c. r (fst (u n)) (fst (u (Suc n))) (x n) y \<longrightarrow> inpt_st r' (snd (u n)) (snd (u (Suc n))) y)"
      then show "(\<box> lft_pred_st (inpt_st r)) (fst \<circ> u) x"
        apply (auto simp add: always_def lft_pred_st_def at_fun_def)
        apply (drule inpt_str_comp_aux_a)
        by auto
   next
      fix y::"nat \<Rightarrow> 'c"
      assume "\<forall> n . (\<forall>i<n. inpt_st (\<lambda>(u::'a, v::'d) (u'::'a, v'::'d). r u u' OO r' v v') (u i) (u (Suc i)) (x i)) \<longrightarrow>
            inpt_st r (fst (u n)) (fst (u (Suc n))) (x n) \<and> (\<forall>y::'c. r (fst (u n)) (fst (u (Suc n))) (x n) y \<longrightarrow> inpt_st r' (snd (u n)) (snd (u (Suc n))) y)"
      moreover assume " (\<box> lft_rel_st r) (fst \<circ> u) x y"
      ultimately show "(\<box> lft_pred_st (inpt_st r')) (snd \<circ> u) y"
        apply (auto simp add: always_def lft_pred_st_def at_fun_def)
        apply (drule inpt_str_comp_aux_a)
        by (auto simp add:  lft_rel_st_def)
   qed

  lemma inpt_str_comp_b: "prec_st (\<lambda> u u' x . inpt_st r (fst u) (fst u') x \<and> 
    (\<forall> y . r (fst u) (fst u') x y \<longrightarrow> (inpt_st r' (snd u) (snd u') y))) (\<lambda>(u, v) (u', v'). r u u' OO r' v v') u x
    =  (\<box> (lft_pred_st (inpt_st (rel_st r r')))) u x"
    proof (auto simp add: prec_st_simp always_def lft_pred_st_def at_fun_def rel_st_def)
      fix m::nat
      assume A: "\<forall>n . (\<forall>i<n. inpt_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v') (u i) (u (Suc i)) (x i)) \<longrightarrow>
                      inpt_st r (fst (u n)) (fst (u (Suc n))) (x n) 
                      \<and> (\<forall>y. r (fst (u n)) (fst (u (Suc n))) (x n) y \<longrightarrow> inpt_st r' (snd (u n)) (snd (u (Suc n))) y)" (is "\<forall> n . ?p n \<longrightarrow> ?q n \<and> ?r n")
      then have "?q m" 
        by (drule_tac n = m in inpt_str_comp_aux_a, simp)
      then obtain y where B: "r ((fst \<circ> u) m) ((fst \<circ> u) (Suc m)) (x m) y" by (auto simp add: inpt_st_def)
      from A have "?r m"
        by (drule_tac n = m in inpt_str_comp_aux_a, simp)
      from this B show "inpt_st (\<lambda>(u, v) (u', v') (x::'c) z. inpt_st r u u' x \<and> (\<forall>y. r u u' x y 
          \<longrightarrow> inpt_st r' v v' y) \<and> (r u u' OO r' v v') x z) (u m) (u (Suc m)) (x m)"
      apply (case_tac "u m")
      apply (case_tac "u (Suc m)")     
      apply (simp add: inpt_st_def)
      by (metis relcompp.relcompI)
    next
      fix m::nat
      assume " \<forall> m. inpt_st (\<lambda>(u, v) (u', v') (x) z. inpt_st r u u' x \<and> (\<forall>y. r u u' x y \<longrightarrow> inpt_st r' v v' y) 
          \<and> (r u u' OO r' v v') x z) (u m) (u (Suc m)) (x m)" (is "\<forall> m . ?p m")
      then have "?p m" by simp
      then show " inpt_st r (fst (u m)) (fst (u (Suc m))) (x m)"
        apply (simp add: inpt_st_def)
        by (case_tac "u m", case_tac "u (Suc m)", simp)
    next
      fix m::nat and y :: 'e
      assume " \<forall> m. inpt_st (\<lambda>(u, v) (u', v') (x) z. inpt_st r u u' x \<and> (\<forall>y. r u u' x y \<longrightarrow> inpt_st r' v v' y) 
          \<and> (r u u' OO r' v v') x z) (u m) (u (Suc m)) (x m)" (is "\<forall> m . ?p m")
      then have "?p m" by simp
      moreover assume "r (fst (u m)) (fst (u (Suc m))) (x m) y"
      ultimately show " inpt_st r' (snd (u m)) (snd (u (Suc m))) y"
        apply (simp add: inpt_st_def)
        by (case_tac "u m", case_tac "u (Suc m)", simp)
    qed

  lemma inpt_str_comp: "(prec_st (inpt_st r) r (fst \<circ> u) x \<and> (\<forall>y. (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> prec_st (inpt_st r') r' (snd \<circ> u) y)) 
               = (\<box> (lft_pred_st (inpt_st (rel_st r r')))) u x"
    by (simp add: inpt_str_comp_a inpt_str_comp_b)

  lemma RSysTmp_inpt_comp: "u' \<in> init' \<Longrightarrow> SymSystem init (inpt_st r) r o SymSystem init'(inpt_st r') r' 
      =  SymSystem (zip_set init init') (inpt_st (rel_st r r')) (rel_st r r')"
    proof -
      assume A : "u' \<in> init'"
      have [simp]: "( \<lambda>x y. (case x of (x, xa) \<Rightarrow> (\<box> lft_pred_st (inpt_st (rel_st r r'))) x xa) \<and> 
        (case x of (x, xa) \<Rightarrow> (\<box> lft_rel_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v')) x xa) y)
        =  (\<lambda>(x, y). (\<box> lft_rel_st (rel_st r r')) x y)" (is "?a = ?b")
        proof (auto simp add: fun_eq_iff always_def at_fun_def lft_pred_st_def lft_rel_st_def rel_st_def inpt_st_def)
          fix a :: "nat \<Rightarrow> 'e \<times> 'a" and  b :: "nat \<Rightarrow> 'c" and  x :: "nat \<Rightarrow> 'b" and  xa :: nat
          assume "\<forall>xa::nat. (case a xa of (u::'e, v::'a) \<Rightarrow> \<lambda>(u'::'e, v'::'a). r u u' OO r' v v') (a (Suc xa)) (b xa) (x xa)" (is "\<forall> xa . ?P xa")
          then have A: "?P xa" by simp
          assume "\<forall>x . Ex ((case a x of (u, v) \<Rightarrow> \<lambda>(u', v') (x) z. Ex (r u u' x) \<and> (\<forall>y. r u u' x y \<longrightarrow> Ex (r' v v' y)) \<and> (r u u' OO r' v v') x z) (a (Suc x)) (b x))" (is "\<forall> xa . ?Q xa")
          then have "?Q xa" by simp
          from this and A show "(case a xa of (u, v) \<Rightarrow> \<lambda>(u', v') (x) z. Ex (r u u' x) \<and> (\<forall>y. r u u' x y \<longrightarrow> Ex (r' v v' y)) \<and> (r u u' OO r' v v') x z) (a (Suc xa)) (b xa) (x xa)"
            by (case_tac "a xa", case_tac "a (Suc xa)", simp)
        next
          fix a :: "nat \<Rightarrow> 'e \<times> 'a" and  b :: "nat \<Rightarrow> 'c" and  x :: "nat \<Rightarrow> 'b" and xa :: nat
          assume "\<forall>xa . (case a xa of (u::'e, v::'a) \<Rightarrow> \<lambda>(u'::'e, v'::'a) (x::'c) z::'b. Ex (r u u' x) \<and> (\<forall>y::'d. r u u' x y \<longrightarrow> Ex (r' v v' y)) \<and> (r u u' OO r' v v') x z) (a (Suc xa)) (b xa) (x xa)" (is "\<forall> xa . ?Q xa")
          then have "?Q xa" by simp
          then show "(case a xa of (u::'e, v::'a) \<Rightarrow> \<lambda>(u'::'e, v'::'a). r u u' OO r' v v') (a (Suc xa)) (b xa) (x xa)"
          by (case_tac "a xa", case_tac "a (Suc xa)", simp)
        qed
      
     from A have "SymSystem init (inpt_st r) r o SymSystem init'(inpt_st r') r' = [: z \<leadsto> u, x . fst \<circ> u \<in> init \<and> snd \<circ> u \<in> init' \<and> z = x :] \<circ>
      ({.u, x . prec_st (inpt_st r) r (fst \<circ> u) x \<and> (\<forall>y::nat \<Rightarrow> 'd. (\<box> lft_rel_st r) (fst \<circ> u) x y \<longrightarrow> prec_st (inpt_st r') r' (snd \<circ> u) y).} \<circ>
      [:  (\<lambda>(u, x).  ((\<box> lft_rel_st (\<lambda>(u, v) (u', v'). r u u' OO r' v v')) u x)) :])"
      by (unfold SymSystem_comp, simp add: comp_assoc)
      also have "... = [: z \<leadsto> u, x . fst \<circ> u \<in> init \<and> snd \<circ> u \<in> init' \<and> z = x :] \<circ> ({. x, y . (\<box> lft_pred_st (inpt_st (rel_st r r'))) x y .} \<circ> [: ?b :])"
          by (subst assert_demonic, simp add: inpt_str_comp)
      also have "... = SymSystem (zip_set init init') (inpt_st (rel_st r r')) (rel_st r r')"
        by (simp add: SymSystem_def prec_st_inpt comp_assoc zip_set_def)
      finally show ?thesis by simp
    qed

  definition "GrdSymSystem init r = [:z \<leadsto> u, x . u \<in> init \<and> z = x:] o trs (\<lambda> (u, x) y . (\<box>(lft_rel_st r)) u x y)"

  lemma inpt_always: "inpt (\<lambda>(x, y). (\<box> lft_rel_st r) x y) = (\<lambda>(x, y). (\<box> lft_pred_st (inpt_st r)) x y)"
    proof (auto simp add: fun_eq_iff)
    fix a :: "nat \<Rightarrow> 'a" and  b :: "nat \<Rightarrow> 'b"
    assume "inpt (\<lambda>(x, y).(\<box> lft_rel_st r) x y) (a, b)"
    then show "(\<box> lft_pred_st (inpt_st r)) a b"
      by (auto simp add: inpt_def lft_pred_st_def inpt_st_def always_def at_fun_def lft_rel_st_def)
    next
      fix a :: "nat \<Rightarrow> 'a" and  b :: "nat \<Rightarrow> 'b"
      let ?y = "\<lambda> n . (SOME y . r (a n) (a (Suc n)) (b n) y)"
      assume "(\<box> lft_pred_st (inpt_st r)) a b"
      then have "(\<box> lft_rel_st r) a b ?y"
        apply (auto simp add: always_def at_fun_def lft_rel_st_def inpt_st_def lft_pred_st_def)
        by (metis tfl_some)
      then show "inpt (\<lambda>(x, y). (\<box> lft_rel_st r) x y) (a, b)"
        by (auto simp add: inpt_def)
    qed

  lemma "GrdSymSystem init r = SymSystem init (inpt_st r) r"
    by (simp add: GrdSymSystem_def SymSystem_def trs_def  prec_st_inpt comp_assoc inpt_always)

  subsection\<open>Example: COUNTER\<close>
  text\<open>
    In this section we introduce an example counter that counts how many times
    the input variable $x$ is true. The input is a sequence of boolen values
    and the output is a sequence of natural numbers. The output at some moment in 
    time is the number of true values seen so far in the input.

    We defined the system counter in two different ways and we show that the
    two definitions are equivalent. The first definition takes the entire 
    input sequence and it computes the corresponding output sequence. We introduce
    the second version of the counter as a reactive system based on a symbolic
    transition system. We use a local variable to record the number of true
    values seen so far, and initially the local variable is zero. At every step
    we increase the local variable if the input is true. The output of the
    system at every step is equal to the local variable.
\<close>

  primrec count :: "bool trace \<Rightarrow> nat trace" where
    "count x 0 = (if x 0 then 1 else 0)" |
    "count x (Suc n) = (if x (Suc n) then count x n + 1 else count x n)"

  definition "Counter_global n = {.x . (\<forall> k . count x k \<le> n).} o [:x \<leadsto> y . y = count x:]"

  definition "prec_count M u u' x = (u \<le> M)"
  definition "rel_count u u' x y = ((x \<longrightarrow> u' = Suc u) \<and> (\<not> x \<longrightarrow> u' = u) \<and> y = u')"

  lemma counter_a_aux: "u 0 = 0 \<Longrightarrow> \<forall>i < n. (x i \<longrightarrow> u (Suc i) = Suc (u i)) \<and> (\<not> x i \<longrightarrow> u (Suc i) = u i) \<Longrightarrow> (\<forall> i < n . count x i = u (Suc i))"
      proof (induction n)
        case 0
        show ?case by simp
      next
        case (Suc n)
        {fix j::nat
          assume "\<forall>i<Suc n. (x i \<longrightarrow> u (Suc i) = Suc (u i)) \<and> (\<not> x i \<longrightarrow> u (Suc i) = u i)"
          and "j < Suc n"
          and "u (0::nat) = (0::nat)"
          from this and Suc have "count x j = u (Suc j)"
            by (case_tac j, auto)
        }
        from Suc and this show ?case 
          by auto
      qed

  lemma counter_b_aux: "u 0 = 0 \<Longrightarrow> \<forall>n. (xa n \<longrightarrow> u (Suc n) = Suc (u n)) \<and> (\<not> xa n \<longrightarrow> u (Suc n) = u n) \<and> xb n = u (Suc n) 
                \<Longrightarrow> count xa n = u (Suc n)"
    by (induction n, simp_all)

  definition "COUNTER M = SymSystem {u . u 0 = 0} (prec_count M) rel_count"

  lemma "COUNTER = Counter_global"
    proof -
      have A:"(\<lambda>x y . \<exists>u::nat \<Rightarrow> nat. u (0::nat) = (0::nat) \<and> (\<box> lft_rel_st rel_count) u x y)
        = (\<lambda> x y . y = count x)"
        proof (simp add: fun_eq_iff lft_rel_st_def rel_count_def always_def at_fun_def, safe)
          fix x :: "nat \<Rightarrow> bool" and  xa :: "nat \<Rightarrow> nat" and u:: "nat \<Rightarrow> nat" and xb :: nat
          assume A: "u 0 = 0"
          assume B: "\<forall>xb . (x xb \<longrightarrow> u (Suc xb) = Suc (u xb)) \<and> (\<not> x xb \<longrightarrow> u (Suc xb) = u xb) \<and> xa xb = u (Suc xb)"
          from A and this have "count x xb = xa xb"
             by (drule_tac counter_b_aux, auto)
          then show "xa xb = count x xb" by simp
        next
          fix x::"nat \<Rightarrow> bool" and xa::"nat \<Rightarrow> nat"
          define u where "u i = (if i = 0 then 0 else count x (i - 1))" for i
          assume B: "\<forall>xb::nat. xa xb = count x xb"
          {fix xb::nat
          from u_def and B have "u 0 = 0 \<and> ( (x xb \<longrightarrow> u (Suc xb) = Suc (u xb)) \<and> (\<not> x xb \<longrightarrow> u (Suc xb) = u xb) \<and> xa xb = u (Suc xb))"
            by (case_tac xb, auto)
          }
          then show "\<exists>u::nat \<Rightarrow> nat. u 0 = 0 \<and> (\<forall>xb. (x xb \<longrightarrow> u (Suc xb) = Suc (u xb)) \<and> (\<not> x xb \<longrightarrow> u (Suc xb) = u xb) \<and> 
              xa xb = u (Suc xb))"
          by auto
       qed
      {fix x :: nat
        have "(\<lambda>xa . \<forall>u . u (0::nat) = (0::nat) \<longrightarrow> prec_st (prec_count x) rel_count u xa) = 
          (\<lambda>xa::nat \<Rightarrow> bool. \<forall>k::nat. count xa k \<le> x)"
        proof (simp add: fun_eq_iff lft_rel_st_def  prec_st_def until_def 
            lft_pred_st_def prec_count_def at_fun_def inpt_st_def rel_count_def, safe)
          fix xa::"nat \<Rightarrow> bool" and k:: nat
          define uu where "uu i = (if i = 0 then 0 else count xa (i - 1))" for i
          assume "(\<forall>u . u 0 = 0 \<longrightarrow> (\<forall>xb . (\<exists>x<xb. xa x \<and> u (Suc x) \<noteq> Suc (u x) \<or> \<not> xa x \<and> u (Suc x) \<noteq> u x) \<or> u xb \<le> x))" (is "\<forall> u . ?s u")
          then have "?s uu" (is "?p \<longrightarrow> (\<forall>xb . (\<exists> x < xb . ?q xb x) \<or> ?r xb)")
            by auto
          from this and uu_def  have "(\<forall>xb . (\<exists> x < xb . ?q xb x) \<or> ?r xb)"
            by simp
          then have "(\<exists> x < (Suc k) . ?q (Suc k) x) \<or> ?r (Suc k)"
            by simp
          then obtain xb where "xb < (Suc k) \<and> (?q (Suc k) xb \<or> ?r (Suc k))"
            by auto
          from this and uu_def show "count xa k \<le> x"
             by (case_tac xb, auto)
        next 
          fix xa:: "nat \<Rightarrow> bool" and  u::"nat \<Rightarrow> nat" and xaa::nat
          assume C: "\<forall>k::nat. count xa k \<le> x"
          assume A: "u (0::nat) = (0::nat)"
          assume B: "\<not> u xaa \<le> x"
          from A and B have D: "xaa > 0"
            by (metis le0 neq0_conv)
          from this and B and C have "count xa (xaa - 1) \<noteq> u xaa"
            by metis
          from this and D have E: "\<exists>i < xaa. count xa i \<noteq> u (Suc i)"
            by (metis One_nat_def Suc_diff_1 diff_Suc_less)
          have "u 0 = 0 \<Longrightarrow> \<forall>i<xaa. (xa i \<longrightarrow> u (Suc i) = Suc (u i)) \<and> (\<not> xa i \<longrightarrow> u (Suc i) = u i) \<Longrightarrow> \<forall>i<xaa. count xa i = u (Suc i)"
            by (rule counter_a_aux, simp)
          from this and A and E show "(\<exists>x<xaa. xa x \<and> u (Suc x) \<noteq> Suc (u x) \<or> \<not> xa x \<and> u (Suc x) \<noteq> u x)"
            by auto
        qed
        }
      note B = this
     show ?thesis
      by (simp add: fun_eq_iff COUNTER_def SymSystem_rel Counter_global_def A B)

   qed
 

  subsection\<open>Example: LIVE\<close>

  text\<open>
    The last example of this formalization introduces a system which does some
    local computation, and ensures some global liveness property.
    We show that this example is the fusion of a symbolic transition system and a demonic
    choice which ensures the liveness property of the output sequence.
    We also show that asumming some liveness property for the input, we can refine
    the example into an executable system that does not ensure the liveness
    property of the output on its own, but relies on the liveness of the input.
\<close>

  definition "rel_ex u u' x y = (((x \<and> u' = u + (1::int)) \<or> (\<not> x \<and> u' = u - 1) \<or> u' = 0) \<and> (y = (u' = 0)))"
  definition "prec_ex u u' x = (-1 \<le> u \<and> u \<le> 3)"

  definition "LIVE = [:x \<leadsto> u, x' . u (0::nat) = 0 \<and> x = x':] o {.u, x . prec_st prec_ex rel_ex u x.} 
    o [:u, x \<leadsto> y . (\<box>(\<lambda> u x y . rel_ex (u 0) (u 1) (x 0) (y 0))) u x y  \<and> (\<box> (\<diamond> (\<lambda> y . y 0))) y :]"

  lemma LIVE_fusion: "LIVE = (SymSystem {u . u 0 = 0} prec_ex rel_ex) \<parallel> [:x \<leadsto> y . (\<box> (\<diamond> (\<lambda> y . y 0))) y:]"
    proof -
      define init where "init = {u . u (0::nat) = (0::int)}"
      then have A: "(\<lambda> i::nat . 0::int) \<in> init"
        by simp
      then have "([: x \<leadsto> (u, y). u \<in> init \<and> x = y :] \<circ> {.(x, y). prec_st prec_ex rel_ex x y .} \<circ> [: \<lambda>(x, y). (\<box> lft_rel_st rel_ex) x y :]) \<parallel>
          [: \<lambda>x. \<box> \<diamond> (\<lambda>y. y 0) :] =
          [: x \<leadsto> (u, y). u \<in> init \<and> x = y :] \<circ> {. (x, y). prec_st prec_ex rel_ex x y .} \<circ>
          [: (u, x) \<leadsto> y. (\<box> lft_rel_st rel_ex) u x y \<and> (\<box> \<diamond> (\<lambda>y. y 0)) y :]"
        by (unfold fusion_spec_local_a, auto)
      then show ?thesis 
        by (simp add: init_def SymSystem_def)
          (auto simp add: LIVE_def lft_rel_st_def always_def at_fun_def)
   qed

  definition "preca_ex x = (x 1 = (\<not>x 0))"

  lemma monotonic_SymSystem[simp]: "mono (SymSystem init p r)"
    by (simp add: SymSystem_def)

  lemma event_ex_aux_a: "a 0 = (0::int) \<Longrightarrow> \<forall>n. xa (Suc n) = (\<not> xa n) \<Longrightarrow> 
        \<forall>n. (xa n \<and> a (Suc n) = a n + 1 \<or> \<not> xa n \<and> a (Suc n) = a n - 1 \<or> a (Suc n) = 0) \<Longrightarrow> 
        (a n = -1 \<longrightarrow> xa n) \<and> (a n = 1 \<longrightarrow> \<not> xa n) \<and> -1 \<le> a n \<and> a n \<le> 1"
    proof (induction n)
      case 0
      show ?case
        by (metis "0.prems"(1) le_minus_one_simps(1) minus_zero zero_le_one zero_neq_neg_one)
    next
      case (Suc n)
      {assume "a (Suc n) = - (1::int)" from this and Suc have "xa (Suc n)"
        by (metis add.commute add_le_same_cancel2 not_one_le_zero zero_neq_neg_one)}
      note A = this
      {assume "a (Suc n) = (1::int)" and "xa (Suc n)" from this and Suc have "False"
        by (metis eq_iff le_iff_diff_le_0 not_one_le_zero)}
      note B = this
      {assume "a n \<noteq> - (1::int)" from this and Suc have " - (1::int) \<le> a (Suc n)" 
         by (metis add.commute monoid_add_class.add.left_neutral le_less not_le right_minus uminus_add_conv_diff zle_add1_eq_le)}
      note C = this
      {assume "a n = - (1::int)" from this and Suc have " - (1::int) \<le> a (Suc n)"
        by (metis add.commute le_minus_one_simps(4) monoid_add_class.add.right_neutral not_le right_minus zle_add1_eq_le)}
      note D = this
      from C and D and Suc have  E: " - (1::int) \<le> a (Suc n)" by auto
      from Suc have F: "a (Suc n) \<le> (1::int)"
        by (metis eq_iff int_one_le_iff_zero_less le_iff_diff_le_0 le_less not_le zle_add1_eq_le)
      from A B E F show ?case by auto
    qed

  lemma event_ex_aux: "a 0 = (0::int) \<Longrightarrow> \<forall>n. xa (Suc n) = (\<not> xa n) \<Longrightarrow> 
         \<forall>n. (xa n \<and> a (Suc n) = a n + 1 \<or> \<not> xa n \<and> a (Suc n) = a n - 1 \<or> a (Suc n) = 0) \<Longrightarrow> 
        (\<forall> n . (a n = -1 \<longrightarrow> xa n) \<and> (a n = 1 \<longrightarrow> \<not> xa n) \<and> -1 \<le> a n \<and> a n \<le> 1)"
    by (clarify, drule event_ex_aux_a, auto)

  lemma "{.\<box> preca_ex.} o LIVE \<le> SymSystem {u . u 0 = 0} prec_ex rel_ex"
    proof (unfold LIVE_fusion SymSystem_def, rule fusion_local_refinement, simp_all)
      fix z::"nat \<Rightarrow> bool" and u :: "nat \<Rightarrow> int" and x::"nat \<Rightarrow> bool"
      assume A: "u 0 = 0"
      assume "(\<box> preca_ex) z"
      then have B: "\<forall>x::nat. z (Suc x) = (\<not> z x)"  
        by (auto simp add: preca_ex_def lft_rel_st_def rel_ex_def always_def at_fun_def)
      assume "(\<box> lft_rel_st rel_ex) u z x"
      then have C: "\<forall>xa . (z xa \<and> u (Suc xa) = u xa + 1 \<or> \<not> z xa \<and> u (Suc xa) = u xa - 1 \<or> u (Suc xa) = 0) \<and> x xa = (u (Suc xa) = 0)"
        by (auto simp add: preca_ex_def lft_rel_st_def rel_ex_def always_def at_fun_def)
      have D: "(\<forall> n . (u n = -1 \<longrightarrow> z n) \<and> (u n = 1 \<longrightarrow> \<not> z n) \<and> -1 \<le> u n \<and> u n \<le> 1)"
        by (cut_tac A B C, rule event_ex_aux, auto)
      {
          fix a::nat
          {assume "u (Suc a) = 0" from this A B C have "\<exists>b . u (Suc (a + b)) = 0"
            by (metis monoid_add_class.add.right_neutral)}
          note 1 = this
          {assume "u (Suc a) = -1" from this A B C D have "\<exists>b . u (Suc (a + b)) = 0" 
            by (metis add_Suc_right diff_minus_eq_add diff_self monoid_add_class.add.right_neutral)}
          note 2 = this
          {assume "u (Suc a) = 1" from this A B C D have "\<exists>b . u (Suc (a + b)) = 0" 
            by (metis add_Suc_right diff_self monoid_add_class.add.right_neutral)}
          note 3 = this
          from 1 2 3 A B C D have "\<exists>b . x (a + b)"
            by (simp, metis diff_0 int_one_le_iff_zero_less le_less not_le zle_diff1_eq)
      }
      then show "(\<box> \<diamond> (\<lambda>y . y 0)) x"
        by (simp add: always_def eventually_def preca_ex_def at_fun_def rel_ex_def lft_rel_st_def)
   qed
  end
