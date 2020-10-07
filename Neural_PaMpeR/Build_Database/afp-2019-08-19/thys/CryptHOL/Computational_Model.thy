(* Title: Computational_Model.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Oracle combinators\<close>

theory Computational_Model imports 
  Generative_Probabilistic_Value
begin

type_synonym security = nat
type_synonym advantage = "security \<Rightarrow> real"

type_synonym ('\<sigma>, 'call, 'ret) oracle' = "'\<sigma> \<Rightarrow> 'call \<Rightarrow> ('ret \<times> '\<sigma>) spmf"
type_synonym ('\<sigma>, 'call, 'ret) "oracle" = "security \<Rightarrow> ('\<sigma>, 'call, 'ret) oracle' \<times> '\<sigma>"

print_translation \<comment> \<open>pretty printing for @{typ "('\<sigma>, 'call, 'ret) oracle"}\<close> \<open>
  let
    fun tr' [Const (@{type_syntax nat}, _), 
      Const (@{type_syntax prod}, _) $ 
        (Const (@{type_syntax fun}, _) $ s1 $ 
          (Const (@{type_syntax fun}, _) $ call $
            (Const (@{type_syntax pmf}, _) $
              (Const (@{type_syntax option}, _) $
                (Const (@{type_syntax prod}, _) $ ret $ s2))))) $
        s3] =
      if s1 = s2 andalso s1 = s3 then Syntax.const @{type_syntax oracle} $ s1 $ call $ ret
      else raise Match;
  in [(@{type_syntax "fun"}, K tr')]
  end
\<close>
typ "('\<sigma>, 'call, 'ret) oracle"

subsection \<open>Shared state\<close>

context includes \<I>.lifting lifting_syntax begin

lift_definition plus_\<I> :: "('out, 'ret) \<I> \<Rightarrow> ('out', 'ret') \<I> \<Rightarrow> ('out + 'out', 'ret + 'ret') \<I>" (infix "\<oplus>\<^sub>\<I>" 500)
is "\<lambda>resp1 resp2. \<lambda>out. case out of Inl out' \<Rightarrow> Inl ` resp1 out' | Inr out' \<Rightarrow> Inr ` resp2 out'" .

lemma plus_\<I>_sel [simp]:
  shows outs_plus_\<I>: "outs_\<I> (plus_\<I> \<I>l \<I>r) = outs_\<I> \<I>l <+> outs_\<I> \<I>r"
  and responses_plus_\<I>_Inl: "responses_\<I> (plus_\<I> \<I>l \<I>r) (Inl x) = Inl ` responses_\<I> \<I>l x"
  and responses_plus_\<I>_Inr: "responses_\<I> (plus_\<I> \<I>l \<I>r) (Inr y) = Inr ` responses_\<I> \<I>r y"
by(transfer; auto split: sum.split_asm; fail)+

lemma vimage_Inl_Plus [simp]: "Inl -` (A <+> B) = A" 
  and vimage_Inr_Plus [simp]: "Inr -` (A <+> B) = B"
by auto

lemma vimage_Inl_image_Inr: "Inl -` Inr ` A = {}"
  and vimage_Inr_image_Inl: "Inr -` Inl ` A = {}"
by auto

lemma plus_\<I>_parametric [transfer_rule]:
  "(rel_\<I> C R ===> rel_\<I> C' R' ===> rel_\<I> (rel_sum C C') (rel_sum R R')) plus_\<I> plus_\<I>"
apply(rule rel_funI rel_\<I>I)+
subgoal premises [transfer_rule] by(simp; rule conjI; transfer_prover)
apply(erule rel_sum.cases; clarsimp simp add: inj_vimage_image_eq vimage_Inl_image_Inr empty_transfer vimage_Inr_image_Inl)
subgoal premises [transfer_rule] by transfer_prover
subgoal premises [transfer_rule] by transfer_prover
done

lifting_update \<I>.lifting
lifting_forget \<I>.lifting

lemma \<I>_trivial_plus_\<I> [simp]: "\<I>_trivial (\<I>\<^sub>1 \<oplus>\<^sub>\<I> \<I>\<^sub>2) \<longleftrightarrow> \<I>_trivial \<I>\<^sub>1 \<and> \<I>_trivial \<I>\<^sub>2"
by(auto simp add: \<I>_trivial_def)

end

context
  fixes left :: "('s, 'a, 'b) oracle'"
  and right :: "('s,'c, 'd) oracle'"
  and s :: "'s"
begin

primrec plus_oracle :: "'a + 'c \<Rightarrow> (('b + 'd) \<times> 's) spmf"
where
  "plus_oracle (Inl a) = map_spmf (apfst Inl) (left s a)"
| "plus_oracle (Inr b) = map_spmf (apfst Inr) (right s b)"

lemma lossless_plus_oracleI [intro, simp]:
  "\<lbrakk> \<And>a. x = Inl a \<Longrightarrow> lossless_spmf (left s a); 
     \<And>b. x = Inr b \<Longrightarrow> lossless_spmf (right s b) \<rbrakk>
  \<Longrightarrow> lossless_spmf (plus_oracle x)"
by(cases x) simp_all

lemma plus_oracle_split:
  "P (plus_oracle lr) \<longleftrightarrow>
  (\<forall>x. lr = Inl x \<longrightarrow> P (map_spmf (apfst Inl) (left s x))) \<and>
  (\<forall>y. lr = Inr y \<longrightarrow> P (map_spmf (apfst Inr) (right s y)))"
by(cases lr) auto

lemma plus_oracle_split_asm:
  "P (plus_oracle lr) \<longleftrightarrow>
  \<not> ((\<exists>x. lr = Inl x \<and> \<not> P (map_spmf (apfst Inl) (left s x))) \<or>
     (\<exists>y. lr = Inr y \<and> \<not> P (map_spmf (apfst Inr) (right s y))))"
by(cases lr) auto

end

notation plus_oracle (infix "\<oplus>\<^sub>O" 500)

context
  fixes left :: "('s, 'a, 'b) oracle'"
  and right :: "('s,'c, 'd) oracle'"
begin

lemma WT_plus_oracleI [intro!]:
  "\<lbrakk> \<I>l \<turnstile>c left s \<surd>; \<I>r \<turnstile>c right s \<surd> \<rbrakk> \<Longrightarrow> \<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd>"
by(rule WT_calleeI)(auto elim!: WT_calleeD simp add: inj_image_mem_iff)

lemma WT_plus_oracleD1:
  assumes "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd> " (is "?\<I> \<turnstile>c ?callee s \<surd>")
  shows "\<I>l \<turnstile>c left s \<surd>"
proof(rule WT_calleeI)
  fix call ret s'
  assume "call \<in> outs_\<I> \<I>l" "(ret, s') \<in> set_spmf (left s call)"
  hence "(Inl ret, s') \<in> set_spmf (?callee s (Inl call))" "Inl call \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    by(auto intro: rev_image_eqI)
  hence "Inl ret \<in> responses_\<I> ?\<I> (Inl call)" by(rule WT_calleeD[OF assms])
  then show "ret \<in> responses_\<I> \<I>l call" by(simp add: inj_image_mem_iff)
qed

lemma WT_plus_oracleD2:
  assumes "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd> " (is "?\<I> \<turnstile>c ?callee s \<surd>")
  shows "\<I>r \<turnstile>c right s \<surd>"
proof(rule WT_calleeI)
  fix call ret s'
  assume "call \<in> outs_\<I> \<I>r" "(ret, s') \<in> set_spmf (right s call)"
  hence "(Inr ret, s') \<in> set_spmf (?callee s (Inr call))" "Inr call \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    by(auto intro: rev_image_eqI)
  hence "Inr ret \<in> responses_\<I> ?\<I> (Inr call)" by(rule WT_calleeD[OF assms])
  then show "ret \<in> responses_\<I> \<I>r call" by(simp add: inj_image_mem_iff)
qed

lemma WT_plus_oracle_iff [simp]: "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd> \<longleftrightarrow> \<I>l \<turnstile>c left s \<surd> \<and> \<I>r \<turnstile>c right s \<surd>"
by(blast dest: WT_plus_oracleD1 WT_plus_oracleD2)

lemma callee_invariant_on_plus_oracle [simp]:
  "callee_invariant_on (left \<oplus>\<^sub>O right) I (\<I>l \<oplus>\<^sub>\<I> \<I>r) \<longleftrightarrow>
   callee_invariant_on left I \<I>l \<and> callee_invariant_on right I \<I>r"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume ?lhs
  then interpret plus: callee_invariant_on "left \<oplus>\<^sub>O right" I "\<I>l \<oplus>\<^sub>\<I> \<I>r" .
  show "callee_invariant_on left I \<I>l"
  proof
    fix s x y s'
    assume "(y, s') \<in> set_spmf (left s x)" and "I s" and "x \<in> outs_\<I> \<I>l"
    then have "(Inl y, s') \<in> set_spmf ((left \<oplus>\<^sub>O right) s (Inl x))"
      by(auto intro: rev_image_eqI)
    then show "I s'" using \<open>I s\<close> by(rule plus.callee_invariant)(simp add: \<open>x \<in> outs_\<I> \<I>l\<close>)
  next
    show "\<I>l \<turnstile>c left s \<surd>" if "I s" for s using plus.WT_callee[OF that] by simp
  qed
  show "callee_invariant_on right I \<I>r"
  proof
    fix s x y s'
    assume "(y, s') \<in> set_spmf (right s x)" and "I s" and "x \<in> outs_\<I> \<I>r"
    then have "(Inr y, s') \<in> set_spmf ((left \<oplus>\<^sub>O right) s (Inr x))"
      by(auto intro: rev_image_eqI)
    then show "I s'" using \<open>I s\<close> by(rule plus.callee_invariant)(simp add: \<open>x \<in> outs_\<I> \<I>r\<close>)
  next
    show "\<I>r \<turnstile>c right s \<surd>" if "I s" for s using plus.WT_callee[OF that] by simp
  qed
next
  assume ?rhs
  interpret left: callee_invariant_on left I \<I>l using \<open>?rhs\<close> by simp
  interpret right: callee_invariant_on right I \<I>r using \<open>?rhs\<close> by simp
  show ?lhs
  proof
    fix s x y s'
    assume "(y, s') \<in> set_spmf ((left \<oplus>\<^sub>O right) s x)" and "I s" and "x \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    then have "(projl y, s') \<in> set_spmf (left s (projl x)) \<and> projl x \<in> outs_\<I> \<I>l \<or>
      (projr y, s') \<in> set_spmf (right s (projr x)) \<and> projr x \<in> outs_\<I> \<I>r"
      by (cases x)  auto
    then show "I s'" using \<open>I s\<close> 
      by (auto dest: left.callee_invariant right.callee_invariant)
  next
    show "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd>" if "I s" for s 
      using left.WT_callee[OF that] right.WT_callee[OF that] by simp
  qed
qed

lemma callee_invariant_plus_oracle [simp]:
  "callee_invariant (left \<oplus>\<^sub>O right) I \<longleftrightarrow>
   callee_invariant left I \<and> callee_invariant right I"
  (is "?lhs \<longleftrightarrow>  ?rhs")
proof -
  have "?lhs \<longleftrightarrow> callee_invariant_on (left \<oplus>\<^sub>O right) I (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)"
    by(rule callee_invariant_on_cong)(auto split: plus_oracle_split_asm)
  also have "\<dots> \<longleftrightarrow> ?rhs" by(rule callee_invariant_on_plus_oracle)
  finally show ?thesis .
qed

lemma plus_oracle_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> A ===> rel_spmf (rel_prod B S))
   ===> (S ===> C ===> rel_spmf (rel_prod D S))
   ===> S ===> rel_sum A C ===> rel_spmf (rel_prod (rel_sum B D) S))
   plus_oracle plus_oracle"
unfolding plus_oracle_def[abs_def] by transfer_prover

lemma rel_spmf_plus_oracle:
  "\<lbrakk> \<And>q1' q2'. \<lbrakk> q1 = Inl q1'; q2 = Inl q2' \<rbrakk> \<Longrightarrow> rel_spmf (rel_prod B S) (left1 s1 q1') (left2 s2 q2');
    \<And>q1' q2'. \<lbrakk> q1 = Inr q1'; q2 = Inr q2' \<rbrakk> \<Longrightarrow> rel_spmf (rel_prod D S) (right1 s1 q1') (right2 s2 q2');
    S s1 s2; rel_sum A C q1 q2 \<rbrakk>
  \<Longrightarrow> rel_spmf (rel_prod (rel_sum B D) S) ((left1 \<oplus>\<^sub>O right1) s1 q1) ((left2 \<oplus>\<^sub>O right2) s2 q2)"
apply(erule rel_sum.cases; clarsimp)
 apply(erule meta_allE)+
 apply(erule meta_impE, rule refl)+
 subgoal premises [transfer_rule] by transfer_prover
apply(erule meta_allE)+
apply(erule meta_impE, rule refl)+
subgoal premises [transfer_rule] by transfer_prover
done

end

subsection \<open>Shared state with aborts\<close>

context
  fixes left :: "('s, 'a, 'b option) oracle'"
  and right :: "('s,'c, 'd option) oracle'"
  and s :: "'s"
begin

primrec plus_oracle_stop :: "'a + 'c \<Rightarrow> (('b + 'd) option \<times> 's) spmf"
where
  "plus_oracle_stop (Inl a) = map_spmf (apfst (map_option Inl)) (left s a)"
| "plus_oracle_stop (Inr b) = map_spmf (apfst (map_option Inr)) (right s b)"

lemma lossless_plus_oracle_stopI [intro, simp]:
  "\<lbrakk> \<And>a. x = Inl a \<Longrightarrow> lossless_spmf (left s a); 
     \<And>b. x = Inr b \<Longrightarrow> lossless_spmf (right s b) \<rbrakk>
  \<Longrightarrow> lossless_spmf (plus_oracle_stop x)"
by(cases x) simp_all

lemma plus_oracle_stop_split:
  "P (plus_oracle_stop lr) \<longleftrightarrow>
  (\<forall>x. lr = Inl x \<longrightarrow> P (map_spmf (apfst (map_option Inl)) (left s x))) \<and>
  (\<forall>y. lr = Inr y \<longrightarrow> P (map_spmf (apfst (map_option Inr)) (right s y)))"
by(cases lr) auto

lemma plus_oracle_stop_split_asm:
  "P (plus_oracle_stop lr) \<longleftrightarrow>
  \<not> ((\<exists>x. lr = Inl x \<and> \<not> P (map_spmf (apfst (map_option Inl)) (left s x))) \<or>
     (\<exists>y. lr = Inr y \<and> \<not> P (map_spmf (apfst (map_option Inr)) (right s y))))"
by(cases lr) auto

end

notation plus_oracle_stop (infix "\<oplus>\<^sub>O\<^sup>S" 500)

subsection \<open>Disjoint state\<close>

context
  fixes left :: "('s1, 'a, 'b) oracle'"
  and right :: "('s2, 'c, 'd) oracle'"
begin

fun parallel_oracle :: "('s1 \<times> 's2, 'a + 'c, 'b + 'd) oracle'"
where
  "parallel_oracle (s1, s2) (Inl a) = map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 a)"
| "parallel_oracle (s1, s2) (Inr b) = map_spmf (map_prod Inr (Pair s1)) (right s2 b)"

lemma parallel_oracle_def:
  "parallel_oracle = (\<lambda>(s1, s2). case_sum (\<lambda>a. map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 a)) (\<lambda>b. map_spmf (map_prod Inr (Pair s1)) (right s2 b)))"
by(auto intro!: ext split: sum.split)

lemma lossless_parallel_oracle [simp]:
  "lossless_spmf (parallel_oracle s12 xy) \<longleftrightarrow>
   (\<forall>x. xy = Inl x \<longrightarrow> lossless_spmf (left (fst s12) x)) \<and>
   (\<forall>y. xy = Inr y \<longrightarrow> lossless_spmf (right (snd s12) y))"
by(cases s12; cases xy) simp_all

lemma parallel_oracle_split:
  "P (parallel_oracle s1s2 lr) \<longleftrightarrow>
  (\<forall>s1 s2 x. s1s2 = (s1, s2) \<longrightarrow> lr = Inl x \<longrightarrow> P (map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 x))) \<and>
  (\<forall>s1 s2 y. s1s2 = (s1, s2) \<longrightarrow> lr = Inr y \<longrightarrow> P (map_spmf (map_prod Inr (Pair s1)) (right s2 y)))"
by(cases s1s2; cases lr) auto

lemma parallel_oracle_split_asm:
  "P (parallel_oracle s1s2 lr) \<longleftrightarrow>
  \<not> ((\<exists>s1 s2 x. s1s2 = (s1, s2) \<and> lr = Inl x \<and> \<not> P (map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 x))) \<or>
     (\<exists>s1 s2 y. s1s2 = (s1, s2) \<and> lr = Inr y \<and> \<not> P (map_spmf (map_prod Inr (Pair s1)) (right s2 y))))"
by(cases s1s2; cases lr) auto

lemma WT_parallel_oracle [intro!, simp]:
  "\<lbrakk> \<I>l \<turnstile>c left sl \<surd>; \<I>r \<turnstile>c right sr \<surd> \<rbrakk> \<Longrightarrow> plus_\<I> \<I>l \<I>r \<turnstile>c parallel_oracle (sl, sr) \<surd>"
by(rule WT_calleeI)(auto elim!: WT_calleeD simp add: inj_image_mem_iff)

lemma callee_invariant_parallel_oracleI [simp, intro]:
  assumes "callee_invariant_on left Il \<I>l" "callee_invariant_on right Ir \<I>r"
  shows "callee_invariant_on parallel_oracle (pred_prod Il Ir) (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
proof
  interpret left: callee_invariant_on left Il \<I>l by fact
  interpret right: callee_invariant_on right Ir \<I>r by fact

  show "pred_prod Il Ir s12'"
    if "(y, s12') \<in> set_spmf (parallel_oracle s12 x)" and "pred_prod Il Ir s12" and "x \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    for s12 x y s12' using that
    by(cases s12; cases s12; cases x)(auto dest: left.callee_invariant right.callee_invariant)

  show "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c local.parallel_oracle s \<surd>" if "pred_prod Il Ir s" for s using that
    by(cases s)(simp add: left.WT_callee right.WT_callee)
qed

end

lemma parallel_oracle_parametric:
  includes lifting_syntax shows
  "((S1 ===> CALL1 ===> rel_spmf (rel_prod (=) S1)) 
  ===> (S2 ===> CALL2 ===> rel_spmf (rel_prod (=) S2))
  ===> rel_prod S1 S2 ===> rel_sum CALL1 CALL2 ===> rel_spmf (rel_prod (=) (rel_prod S1 S2)))
  parallel_oracle parallel_oracle"
unfolding parallel_oracle_def[abs_def] by (fold relator_eq)transfer_prover

subsection \<open>Indexed oracles\<close>

definition family_oracle :: "('i \<Rightarrow> ('s, 'a, 'b) oracle') \<Rightarrow> ('i \<Rightarrow> 's, 'i \<times> 'a, 'b) oracle'"
where "family_oracle f s = (\<lambda>(i, x). map_spmf (\<lambda>(y, s'). (y, s(i := s'))) (f i (s i) x))"

lemma family_oracle_apply [simp]:
  "family_oracle f s (i, x) = map_spmf (apsnd (fun_upd s i)) (f i (s i) x)"
by(simp add: family_oracle_def apsnd_def map_prod_def)

lemma lossless_family_oracle:
  "lossless_spmf (family_oracle f s ix) \<longleftrightarrow> lossless_spmf (f (fst ix) (s (fst ix)) (snd ix))"
by(simp add: family_oracle_def split_beta)

subsection \<open>State extension\<close>

definition extend_state_oracle :: "('call, 'ret, 's) callee \<Rightarrow> ('call, 'ret, 's' \<times> 's) callee" ("\<dagger>_" [1000] 1000)
where "extend_state_oracle callee = (\<lambda>(s', s) x. map_spmf (\<lambda>(y, s). (y, (s', s))) (callee s x))"

lemma extend_state_oracle_simps [simp]:
  "extend_state_oracle callee (s', s) x = map_spmf (\<lambda>(y, s). (y, (s', s))) (callee s x)"
by(simp add: extend_state_oracle_def)

context includes lifting_syntax begin
lemma extend_state_oracle_parametric [transfer_rule]:
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> rel_prod S' S ===> C ===> rel_spmf (rel_prod R (rel_prod S' S)))
  extend_state_oracle extend_state_oracle"
unfolding extend_state_oracle_def[abs_def] by transfer_prover

lemma extend_state_oracle_transfer:
  "((S ===> C ===> rel_spmf (rel_prod R S)) 
  ===> rel_prod2 S ===> C ===> rel_spmf (rel_prod R (rel_prod2 S)))
  (\<lambda>oracle. oracle) extend_state_oracle"
unfolding extend_state_oracle_def[abs_def]
apply(rule rel_funI)+
apply clarsimp
apply(drule (1) rel_funD)+
apply(auto simp add: spmf_rel_map split_def dest: rel_funD intro: rel_spmf_mono)
done
end

lemma callee_invariant_extend_state_oracle_const [simp]:
  "callee_invariant \<dagger>oracle (\<lambda>(s', s). I s')"
by unfold_locales auto

lemma callee_invariant_extend_state_oracle_const':
  "callee_invariant \<dagger>oracle (\<lambda>s. I (fst s))"
by unfold_locales auto

definition lift_stop_oracle :: "('call, 'ret, 's) callee \<Rightarrow> ('call, 'ret option, 's) callee"
where "lift_stop_oracle oracle s x = map_spmf (apfst Some) (oracle s x)"

lemma lift_stop_oracle_apply [simp]: "lift_stop_oracle  oracle s x = map_spmf (apfst Some) (oracle s x)"
  by(fact lift_stop_oracle_def)
  
context includes lifting_syntax begin

lemma lift_stop_oracle_transfer:
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> (S ===> C ===> rel_spmf (rel_prod (pcr_Some R) S)))
   (\<lambda>x. x) lift_stop_oracle"
unfolding lift_stop_oracle_def
apply(rule rel_funI)+
apply(drule (1) rel_funD)+
apply(simp add: spmf_rel_map apfst_def prod.rel_map)
done

end

section \<open>Combining GPVs\<close>

subsection \<open>Shared state without interrupts\<close>

context
  fixes left :: "'s \<Rightarrow> 'x1 \<Rightarrow> ('y1 \<times> 's, 'call, 'ret) gpv"
  and right :: "'s \<Rightarrow> 'x2 \<Rightarrow> ('y2 \<times> 's, 'call, 'ret) gpv"
begin

primrec plus_intercept :: "'s \<Rightarrow> 'x1 + 'x2 \<Rightarrow> (('y1 + 'y2) \<times> 's, 'call, 'ret) gpv"
where
  "plus_intercept s (Inl x) = map_gpv (apfst Inl) id (left s x)"
| "plus_intercept s (Inr x) = map_gpv (apfst Inr) id (right s x)"

end

lemma plus_intercept_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> X1 ===> rel_gpv (rel_prod Y1 S) C)
  ===> (S ===> X2 ===> rel_gpv (rel_prod Y2 S) C)
  ===> S ===> rel_sum X1 X2 ===> rel_gpv (rel_prod (rel_sum Y1 Y2) S) C)
  plus_intercept plus_intercept"
unfolding plus_intercept_def[abs_def] by transfer_prover

lemma interaction_bounded_by_plus_intercept [interaction_bound]:
  fixes left right
  shows "\<lbrakk> \<And>x'. x = Inl x' \<Longrightarrow> interaction_bounded_by P (left s x') (n x');
    \<And>y. x = Inr y \<Longrightarrow> interaction_bounded_by P (right s y) (m y) \<rbrakk>
  \<Longrightarrow> interaction_bounded_by P (plus_intercept left right s x) (case x of Inl x \<Rightarrow> n x | Inr y \<Rightarrow> m y)"
by(simp split!: sum.split add: interaction_bounded_by_map_gpv_id)

subsection \<open>Shared state with interrupts\<close>

context 
  fixes left :: "'s \<Rightarrow> 'x1 \<Rightarrow> ('y1 option \<times> 's, 'call, 'ret) gpv"
  and right :: "'s \<Rightarrow> 'x2 \<Rightarrow> ('y2 option \<times> 's, 'call, 'ret) gpv"
begin

primrec plus_intercept_stop :: "'s \<Rightarrow> 'x1 + 'x2 \<Rightarrow> (('y1 + 'y2) option \<times> 's, 'call, 'ret) gpv"
where
  "plus_intercept_stop s (Inl x) = map_gpv (apfst (map_option Inl)) id (left s x)"
| "plus_intercept_stop s (Inr x) = map_gpv (apfst (map_option Inr)) id (right s x)"

end

lemma plus_intercept_stop_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> X1 ===> rel_gpv (rel_prod (rel_option Y1) S) C)
  ===> (S ===> X2 ===> rel_gpv (rel_prod (rel_option Y2) S) C)
  ===> S ===> rel_sum X1 X2 ===> rel_gpv (rel_prod (rel_option (rel_sum Y1 Y2)) S) C)
  plus_intercept_stop plus_intercept_stop"
unfolding plus_intercept_stop_def by transfer_prover

end
