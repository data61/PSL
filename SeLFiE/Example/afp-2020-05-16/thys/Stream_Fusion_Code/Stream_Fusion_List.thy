(* Title: Stream_Fusion_List.thy
 Authors: Alexandra Maximova, ETH Zurich
          Andreas Lochbihler, ETH Zurich
*)

section \<open>Stream fusion for finite lists\<close>

theory Stream_Fusion_List
imports Stream_Fusion
begin

lemma map_option_mono [partial_function_mono]: (* To be moved to HOL *)
  "mono_option f \<Longrightarrow> mono_option (\<lambda>x. map_option g (f x))"
apply (rule monotoneI)
apply (drule (1) monotoneD)
apply (auto simp add: flat_ord_def split: option.split)
done

subsection \<open>The type of generators for finite lists\<close>

datatype ('a, 's) step = Done | is_Skip: Skip 's | is_Yield: Yield 'a 's

type_synonym ('a, 's) raw_generator = "'s \<Rightarrow> ('a,'s) step"

text \<open>
  Raw generators may not end in @{const Done}, but may lead to infinitely many @{const Yield}s 
  in a row. Such generators cannot be converted to finite lists, because it corresponds to an
  infinite list. Therefore, we introduce the type of generators that always end in @{const Done}
  after finitely many steps.
\<close>

inductive_set terminates_on :: "('a, 's) raw_generator \<Rightarrow> 's set"
  for g :: "('a, 's) raw_generator"
where
  stop: "g s = Done \<Longrightarrow> s \<in> terminates_on g"
| pause: "\<lbrakk> g s = Skip s'; s' \<in> terminates_on g \<rbrakk> \<Longrightarrow> s \<in> terminates_on g"
| unfold: "\<lbrakk> g s = Yield a s'; s' \<in> terminates_on g \<rbrakk> \<Longrightarrow> s \<in> terminates_on g"

definition terminates :: "('a, 's) raw_generator \<Rightarrow> bool"
where "terminates g \<longleftrightarrow> (terminates_on g = UNIV)"

lemma terminatesI [intro?]:
  "(\<And>s. s \<in> terminates_on g) \<Longrightarrow> terminates g"
by (auto simp add: terminates_def)

lemma terminatesD:
  "terminates g \<Longrightarrow> s \<in> terminates_on g"
by (auto simp add: terminates_def)

lemma terminates_on_stop:
  "terminates_on (\<lambda>_. Done) = UNIV"
by (auto intro: terminates_on.stop)

lemma wf_terminates:
  assumes "wf R"
  and skip: "\<And>s s'. g s = Skip s' \<Longrightarrow> (s',s) \<in> R"
  and yield: "\<And>s s' a. g s = Yield a s' \<Longrightarrow> (s',s) \<in> R"
  shows "terminates g"
proof (rule terminatesI)
  fix s
  from \<open>wf R\<close> show "s \<in> terminates_on g"
  proof (induction rule: wf_induct [rule_format, consumes 1, case_names wf])
    case (wf s)
    show ?case
    proof (cases "g s")
      case (Skip s')
      hence "(s', s) \<in> R" by (rule skip)
      hence "s' \<in> terminates_on g" by (rule wf.IH)
      with Skip show ?thesis by (rule terminates_on.pause)
    next
      case (Yield a s')
      hence "(s', s) \<in> R" by (rule yield)
      hence "s' \<in> terminates_on g" by (rule wf.IH)
      with Yield show ?thesis by (rule terminates_on.unfold)
    qed (rule terminates_on.stop)
  qed
qed

context fixes g :: "('a, 's) raw_generator" begin

partial_function (option) terminates_within :: "'s \<Rightarrow> nat option" where
  "terminates_within s = (case g s of
     Done \<Rightarrow> Some 0
  | Skip s' \<Rightarrow> map_option (\<lambda>n. n + 1) (terminates_within s')
  | Yield a s' \<Rightarrow> map_option (\<lambda>n. n + 1) (terminates_within s'))"

lemma terminates_on_conv_dom_terminates_within:
  "terminates_on g = dom terminates_within"
proof (rule set_eqI iffI)+
  fix s
  assume "s \<in> terminates_on g"
  hence "\<exists>n. terminates_within s = Some n"
    by induction (subst terminates_within.simps, simp add: split_beta)+
  then show "s \<in> dom terminates_within" by blast
next
  fix s
  assume "s \<in> dom terminates_within"
  then obtain n where "terminates_within s = Some n" by blast
  then show "s \<in> terminates_on g"
  proof (induction rule: terminates_within.raw_induct[rotated 1, consumes 1])
    case (1 terminates_within s s')
    show ?case
    proof(cases "g s")
      case Done
      thus ?thesis by (simp add: terminates_on.stop)
    next
      case (Skip s')
      hence "s' \<in> terminates_on g" using 1 by(auto)
      thus ?thesis using \<open>g s = Skip s'\<close> by (simp add: terminates_on.pause)
    next
      case (Yield a s')
      hence "s' \<in> terminates_on g" using 1 by(auto)
      thus ?thesis using \<open>g s = Yield a s'\<close> by (auto intro: terminates_on.unfold)
    qed
  qed
qed

end

lemma terminates_wfE:
  assumes "terminates g"
  obtains R 
  where "wf R"
    "\<And>s s'. (g s = Skip s') \<Longrightarrow> (s',s) \<in> R"
    "\<And>s a s'. (g s = Yield a s') \<Longrightarrow> (s',s) \<in> R"
proof -
  let ?R = "measure (\<lambda>s. the (terminates_within g s)) :: ('a \<times> 'a) set"
  have "wf ?R" by simp
  moreover {
    fix s s'
    assume "g s = Skip s'"
    moreover from assms have "s' \<in> terminates_on g" by (rule terminatesD)
    then obtain n where "terminates_within g s' = Some n"
      unfolding terminates_on_conv_dom_terminates_within by (auto)
    ultimately have "the (terminates_within g s') < the (terminates_within g s)"
      by (simp add: terminates_within.simps)
    hence "(s',s) \<in> ?R" by (auto)
  } moreover {
    fix s s' a
    assume 2: "g s = Yield a s'"
    moreover from assms have "s' \<in> terminates_on g" by (rule terminatesD)
    then obtain n where "terminates_within g s' = Some n"
      unfolding terminates_on_conv_dom_terminates_within by (auto)
    ultimately have "(s',s) \<in> ?R"
      by simp (subst terminates_within.simps, simp add: split_beta)
  } ultimately 
  show thesis by (rule that)
qed

typedef ('a,'s) generator = "{g :: ('a,'s) raw_generator. terminates g}"
  morphisms generator Generator
proof
  show "(\<lambda>_. Done) \<in> ?generator"
    by (simp add: terminates_on_stop terminates_def)
qed

setup_lifting type_definition_generator

subsection \<open>Conversion to @{typ "'a list"}\<close>

context fixes g :: "('a, 's) generator" begin

function unstream :: "'s \<Rightarrow> 'a list"
where
  "unstream s = (case generator g s of
     Done \<Rightarrow> []
   | Skip s' \<Rightarrow> unstream s'
   | Yield x s' \<Rightarrow> x # unstream s')"
by pat_completeness auto
termination
proof -
  have "terminates (generator g)" using generator[of g] by simp
  thus ?thesis by(rule terminates_wfE)(erule "termination")
qed

lemma unstream_simps [simp]:
  "generator g s = Done \<Longrightarrow> unstream s = []"
  "generator g s = Skip s' \<Longrightarrow> unstream s = unstream s'"
  "generator g s = Yield x s' \<Longrightarrow> unstream s = x # unstream s'"
by(simp_all)

declare unstream.simps[simp del]

function force :: "'s \<Rightarrow> ('a \<times> 's) option"
where
  "force s = (case generator g s of Done \<Rightarrow> None 
     | Skip s' \<Rightarrow> force s'
     | Yield x s' \<Rightarrow> Some (x, s'))"
by pat_completeness auto
termination
proof -
  have "terminates (generator g)" using generator[of g] by simp
  thus ?thesis by(rule terminates_wfE)(rule "termination")
qed

lemma force_simps [simp]:
  "generator g s = Done \<Longrightarrow> force s = None"
  "generator g s = Skip s' \<Longrightarrow> force s = force s'"
  "generator g s = Yield x s' \<Longrightarrow> force s = Some (x, s')"
by(simp_all)

declare force.simps[simp del]

lemma unstream_force_None [simp]: "force s = None \<Longrightarrow> unstream s = []"
proof(induction s rule: force.induct)
  case (1 s)
  thus ?case by(cases "generator g s") simp_all
qed

lemma unstream_force_Some [simp]: "force s = Some (x, s') \<Longrightarrow> unstream s = x # unstream s'"
proof(induction s rule: force.induct)
  case (1 s)
  thus ?case by(cases "generator g s") simp_all
qed

end

setup \<open>Context.theory_map (Stream_Fusion.add_unstream @{const_name unstream})\<close>

subsection \<open>Producers\<close>

subsubsection \<open>Conversion to streams\<close>

fun stream_raw :: "'a list \<Rightarrow> ('a, 'a list) step"
where
  "stream_raw [] = Done"
| "stream_raw (x # xs) = Yield x xs"

lemma terminates_stream_raw: "terminates stream_raw"
proof (rule terminatesI)
  fix s :: "'a list"
  show "s \<in> terminates_on stream_raw"
    by(induction s)(auto intro: terminates_on.intros)
qed

lift_definition stream :: "('a, 'a list) generator" is "stream_raw" by(rule terminates_stream_raw)

lemma unstream_stream: "unstream stream xs = xs"
by(induction xs)(auto simp add: stream.rep_eq)

subsubsection \<open>@{const replicate}\<close>

fun replicate_raw :: "'a \<Rightarrow> ('a, nat) raw_generator"
where
  "replicate_raw a 0 = Done"
| "replicate_raw a (Suc n) = Yield a n"
 
lemma terminates_replicate_raw: "terminates (replicate_raw a)"
proof (rule terminatesI)
  fix s :: "nat"
  show "s \<in> terminates_on (replicate_raw a)"
    by(induction s)(auto intro: terminates_on.intros)
qed

lift_definition replicate_prod :: "'a \<Rightarrow> ('a, nat) generator" is "replicate_raw"
by(rule terminates_replicate_raw)

lemma unstream_replicate_prod [stream_fusion]: "unstream (replicate_prod x) n = replicate n x"
by(induction n)(simp_all add: replicate_prod.rep_eq)

subsubsection \<open>@{const upt}\<close>

definition upt_raw :: "nat \<Rightarrow> (nat, nat) raw_generator"
where "upt_raw n m = (if m \<ge> n then Done else Yield m (Suc m))"

lemma terminates_upt_raw: "terminates (upt_raw n)"
proof (rule terminatesI)
  fix s :: nat
  show "s \<in> terminates_on (upt_raw n)"
    by(induction "n-s" arbitrary: s rule: nat.induct)(auto 4 3 simp add: upt_raw_def intro: terminates_on.intros)
qed

lift_definition upt_prod :: "nat \<Rightarrow> (nat, nat) generator" is "upt_raw" by(rule terminates_upt_raw)

lemma unstream_upt_prod [stream_fusion]: "unstream (upt_prod n) m = upt m n"
by(induction "n-m" arbitrary: n m)(simp_all add: upt_prod.rep_eq upt_conv_Cons upt_raw_def unstream.simps)


subsubsection \<open>@{const upto}\<close>

definition upto_raw :: "int \<Rightarrow> (int, int) raw_generator"
where "upto_raw n m = (if m \<le> n then Yield m (m + 1) else Done)"

lemma terminates_upto_raw: "terminates (upto_raw n)"
proof (rule terminatesI)
  fix s :: int
  show "s \<in> terminates_on (upto_raw n)"
    by(induction "nat(n-s+1)" arbitrary: s)(auto 4 3 simp add: upto_raw_def intro: terminates_on.intros)
qed

lift_definition upto_prod :: "int \<Rightarrow> (int, int) generator" is "upto_raw" by (rule terminates_upto_raw)

lemma unstream_upto_prod [stream_fusion]: "unstream (upto_prod n) m = upto m n"
by(induction "nat (n - m + 1)" arbitrary: m)(simp_all add: upto_prod.rep_eq upto.simps upto_raw_def)

subsubsection \<open>@{term "[]"}\<close>

lift_definition Nil_prod :: "('a, unit) generator" is "\<lambda>_. Done"
by(auto simp add: terminates_def intro: terminates_on.intros)

lemma generator_Nil_prod: "generator Nil_prod = (\<lambda>_. Done)"
by(fact Nil_prod.rep_eq)

lemma unstream_Nil_prod [stream_fusion]: "unstream Nil_prod () = []"
by(simp add: generator_Nil_prod)

subsection \<open>Consumers\<close>

subsubsection \<open>@{const nth}\<close>

context fixes g :: "('a, 's) generator" begin

definition nth_cons :: "'s \<Rightarrow> nat \<Rightarrow> 'a" 
where [stream_fusion]: "nth_cons s n = unstream g s ! n"

lemma nth_cons_code [code]:
  "nth_cons s n =
  (case generator g s of Done => undefined n
    | Skip s' => nth_cons s' n
    | Yield x s' => (case n of 0 => x | Suc n' => nth_cons s' n'))"
by(cases "generator g s")(simp_all add: nth_cons_def nth_def split: nat.split)

end

subsubsection \<open>@{term length}\<close>

context fixes g :: "('a, 's) generator" begin

definition length_cons :: "'s \<Rightarrow> nat"
where "length_cons s = length (unstream g s)"

lemma length_cons_code [code]:
  "length_cons s =
    (case generator g s of
      Done \<Rightarrow> 0
    | Skip s' \<Rightarrow> length_cons s'
    | Yield a s' \<Rightarrow> 1 + length_cons s')"
by(cases "generator g s")(simp_all add: length_cons_def)

definition gen_length_cons :: "nat \<Rightarrow> 's \<Rightarrow> nat"
where "gen_length_cons n s = n + length (unstream g s)"

lemma gen_length_cons_code [code]:
  "gen_length_cons n s = (case generator g s of
     Done \<Rightarrow> n | Skip s' \<Rightarrow> gen_length_cons n s' | Yield a s' \<Rightarrow> gen_length_cons (Suc n) s')"
by(simp add: gen_length_cons_def split: step.split)

lemma unstream_gen_length [stream_fusion]: "gen_length_cons 0 s = length (unstream g s)"
by(simp add: gen_length_cons_def)

lemma unstream_gen_length2 [stream_fusion]: "gen_length_cons n s = List.gen_length n (unstream g s)"
by(simp add: List.gen_length_def gen_length_cons_def)

end

subsubsection \<open>@{const foldr}\<close>

context 
  fixes g :: "('a, 's) generator"
  and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  and z :: "'b"
begin

definition foldr_cons :: "'s \<Rightarrow> 'b"
where [stream_fusion]: "foldr_cons s = foldr f (unstream g s) z"

lemma foldr_cons_code [code]:
  "foldr_cons s =
    (case generator g s of
      Done \<Rightarrow> z
    | Skip s' \<Rightarrow> foldr_cons s'
    | Yield a s' \<Rightarrow> f a (foldr_cons s'))"
by(cases "generator g s")(simp_all add: foldr_cons_def)

end

subsubsection \<open>@{const foldl}\<close>

context
  fixes g :: "('b, 's) generator"
  and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
begin

definition foldl_cons :: "'a \<Rightarrow> 's \<Rightarrow> 'a"
where [stream_fusion]: "foldl_cons z s = foldl f z (unstream g s)"

lemma foldl_cons_code [code]:
  "foldl_cons z s =
    (case generator g s of
      Done \<Rightarrow> z
    | Skip s' \<Rightarrow> foldl_cons z s'
    | Yield a s' \<Rightarrow> foldl_cons (f z a) s')"
by (cases "generator g s")(simp_all add: foldl_cons_def)

end

subsubsection \<open>@{const fold}\<close>

context
  fixes g :: "('a, 's) generator"
  and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
begin

definition fold_cons :: "'b \<Rightarrow> 's \<Rightarrow> 'b"
where [stream_fusion]: "fold_cons z s = fold f (unstream g s) z"

lemma fold_cons_code [code]:
  "fold_cons z s =
    (case generator g s of
      Done \<Rightarrow> z
    | Skip s' \<Rightarrow> fold_cons z s'
    | Yield a s' \<Rightarrow> fold_cons (f a z) s')"
by (cases "generator g s")(simp_all add: fold_cons_def)

end

subsubsection \<open>@{const List.null}\<close>

definition null_cons :: "('a, 's) generator \<Rightarrow> 's \<Rightarrow> bool"
where [stream_fusion]: "null_cons g s = List.null (unstream g s)"

lemma null_cons_code [code]:
  "null_cons g s = (case generator g s of Done \<Rightarrow> True | Skip s' \<Rightarrow> null_cons g s' | Yield _ _ \<Rightarrow> False)"
by(cases "generator g s")(simp_all add: null_cons_def null_def)

subsubsection \<open>@{const hd}\<close>

context fixes g :: "('a, 's) generator" begin

definition hd_cons :: "'s \<Rightarrow> 'a"
where [stream_fusion]: "hd_cons s = hd (unstream g s)"

lemma hd_cons_code [code]:
  "hd_cons s =
    (case generator g s of
      Done \<Rightarrow> undefined
    | Skip s' \<Rightarrow> hd_cons s'
    | Yield a s' \<Rightarrow> a)"
by (cases "generator g s")(simp_all add: hd_cons_def hd_def)

end

subsubsection \<open>@{const last}\<close>

context fixes g :: "('a, 's) generator" begin

definition last_cons :: "'a option \<Rightarrow> 's \<Rightarrow> 'a"
where "last_cons x s = (if unstream g s = [] then the x else last (unstream g s))"

lemma last_cons_code [code]:
  "last_cons x s =
  (case generator g s of Done \<Rightarrow> the x
             | Skip s' \<Rightarrow> last_cons x s'
             | Yield a s' \<Rightarrow> last_cons (Some a) s')"
by (cases "generator g s")(simp_all add: last_cons_def)

lemma unstream_last_cons [stream_fusion]: "last_cons None s = last (unstream g s)"
by (simp add: last_cons_def last_def option.the_def)

end

subsubsection \<open>@{const sum_list}\<close>

context fixes g :: "('a :: monoid_add, 's) generator" begin

definition sum_list_cons :: "'s \<Rightarrow> 'a"
where [stream_fusion]: "sum_list_cons s = sum_list (unstream g s)"

lemma sum_list_cons_code [code]:
  "sum_list_cons s =
    (case generator g s of
      Done \<Rightarrow> 0
    | Skip s' \<Rightarrow> sum_list_cons s'
    | Yield a s' \<Rightarrow> a + sum_list_cons s')"
by (cases "generator g s")(simp_all add: sum_list_cons_def)

end

subsubsection \<open>@{const list_all2}\<close>

context
  fixes g :: "('a, 's1) generator"
  and h :: "('b, 's2) generator"
  and P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

definition list_all2_cons :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [stream_fusion]: "list_all2_cons sg sh = list_all2 P (unstream g sg) (unstream h sh)"

definition list_all2_cons1 :: "'a \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where "list_all2_cons1 x sg' sh = list_all2 P (x # unstream g sg') (unstream h sh)"

lemma list_all2_cons_code [code]:
  "list_all2_cons sg sh = 
  (case generator g sg of
     Done \<Rightarrow> null_cons h sh
   | Skip sg' \<Rightarrow> list_all2_cons sg' sh
   | Yield a sg' \<Rightarrow> list_all2_cons1 a sg' sh)"
by(simp split: step.split add: list_all2_cons_def null_cons_def List.null_def list_all2_cons1_def)

lemma list_all2_cons1_code [code]:
  "list_all2_cons1 x sg' sh = 
  (case generator h sh of
     Done \<Rightarrow> False
   | Skip sh' \<Rightarrow> list_all2_cons1 x sg' sh'
   | Yield y sh' \<Rightarrow> P x y \<and> list_all2_cons sg' sh')"
by(simp split: step.split add: list_all2_cons_def null_cons_def List.null_def list_all2_cons1_def)

end

subsubsection \<open>@{const list_all}\<close>

context
  fixes g :: "('a, 's) generator"
  and P :: "'a \<Rightarrow> bool"
begin

definition list_all_cons :: "'s \<Rightarrow> bool"
where [stream_fusion]: "list_all_cons s = list_all P (unstream g s)"

lemma list_all_cons_code [code]:
  "list_all_cons s \<longleftrightarrow>
  (case generator g s of
    Done \<Rightarrow> True | Skip s' \<Rightarrow> list_all_cons s' | Yield x s' \<Rightarrow> P x \<and> list_all_cons s')"
by(simp add: list_all_cons_def split: step.split)

end

subsubsection \<open>@{const ord.lexordp}\<close>

context ord begin

definition lexord_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [code del]: "lexord_fusion g1 g2 s1 s2 = ord_class.lexordp (unstream g1 s1) (unstream g2 s2)"

definition lexord_eq_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [code del]: "lexord_eq_fusion g1 g2 s1 s2 = lexordp_eq (unstream g1 s1) (unstream g2 s2)"

lemma lexord_fusion_code:
  "lexord_fusion g1 g2 s1 s2 \<longleftrightarrow>
  (case generator g1 s1 of
     Done \<Rightarrow> \<not> null_cons g2 s2
   | Skip s1' \<Rightarrow> lexord_fusion g1 g2 s1' s2
   | Yield x s1' \<Rightarrow> 
     (case force g2 s2 of
        None \<Rightarrow> False
      | Some (y, s2') \<Rightarrow> x < y \<or> \<not> y < x \<and> lexord_fusion g1 g2 s1' s2'))"
unfolding lexord_fusion_def
by(cases "generator g1 s1" "force g2 s2" rule: step.exhaust[case_product option.exhaust])(auto simp add: null_cons_def null_def)

lemma lexord_eq_fusion_code:
  "lexord_eq_fusion g1 g2 s1 s2 \<longleftrightarrow>
  (case generator g1 s1 of
     Done \<Rightarrow> True
   | Skip s1' \<Rightarrow> lexord_eq_fusion g1 g2 s1' s2
   | Yield x s1' \<Rightarrow>
     (case force g2 s2 of
        None \<Rightarrow> False
      | Some (y, s2') \<Rightarrow> x < y \<or> \<not> y < x \<and> lexord_eq_fusion g1 g2 s1' s2'))"
unfolding lexord_eq_fusion_def
by(cases "generator g1 s1" "force g2 s2" rule: step.exhaust[case_product option.exhaust]) auto

end

lemmas [code] =
  lexord_fusion_code ord.lexord_fusion_code
  lexord_eq_fusion_code ord.lexord_eq_fusion_code

lemmas [stream_fusion] =
  lexord_fusion_def ord.lexord_fusion_def
  lexord_eq_fusion_def ord.lexord_eq_fusion_def

subsection \<open>Transformers\<close>

subsubsection \<open>@{const map}\<close>

definition map_raw :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('b, 's) raw_generator"
where
  "map_raw f g s = (case g s of
     Done \<Rightarrow> Done
   | Skip s' \<Rightarrow> Skip s'
   | Yield a s' \<Rightarrow> Yield (f a) s')"

lemma terminates_map_raw: 
  assumes "terminates g"
  shows "terminates (map_raw f g)"
proof (rule terminatesI)
  fix s
  from assms
  have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "s \<in> terminates_on (map_raw f g)"
    by (induction s)(auto intro: terminates_on.intros simp add: map_raw_def)
qed

lift_definition map_trans :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) generator \<Rightarrow> ('b, 's) generator" is "map_raw"
by (rule terminates_map_raw)

lemma unstream_map_trans [stream_fusion]: "unstream (map_trans f g) s = map f (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  show ?case using "1.IH" by (cases "generator g s")(simp_all add: map_trans.rep_eq map_raw_def)
qed

subsubsection \<open>@{const drop}\<close>

fun drop_raw :: "('a, 's) raw_generator \<Rightarrow> ('a, (nat \<times> 's)) raw_generator"
where
  "drop_raw g (n, s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (n, s')
   | Yield a s' \<Rightarrow> (case n of 0 \<Rightarrow> Yield a (0, s') | Suc n \<Rightarrow> Skip (n, s')))"

lemma terminates_drop_raw:
  assumes "terminates g"
  shows "terminates (drop_raw g)"
proof (rule terminatesI)
  fix st :: "nat \<times> 'a"
  obtain n s where "st = (n, s)" by(cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  thus "st \<in> terminates_on (drop_raw g)" unfolding \<open>st = (n, s)\<close>
    apply(induction arbitrary: n)
    apply(case_tac [!] n)
    apply(auto intro: terminates_on.intros)
    done
qed

lift_definition drop_trans :: "('a, 's) generator \<Rightarrow> ('a, nat \<times> 's) generator" is "drop_raw"
by (rule terminates_drop_raw)

lemma unstream_drop_trans [stream_fusion]: "unstream (drop_trans g) (n, s) = drop n (unstream g s)"
proof (induction s arbitrary: n taking: g rule: unstream.induct)
  case (1 s)
  show ?case using "1.IH"(1)[of _ n] "1.IH"(2)[of _ _ n] "1.IH"(2)[of _ _ "n - 1"]
    by(cases "generator g s" "n" rule: step.exhaust[case_product nat.exhaust])
      (simp_all add: drop_trans.rep_eq)
qed

subsubsection \<open>@{const dropWhile}\<close>

fun dropWhile_raw :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('a, bool \<times> 's) raw_generator"
  \<comment> \<open>Boolean flag indicates whether we are still in dropping phase\<close>
where
  "dropWhile_raw P g (True, s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (True, s')
   | Yield a s' \<Rightarrow> (if P a then Skip (True, s') else Yield a (False, s')))"
| "dropWhile_raw P g (False, s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (False, s') | Yield a s' \<Rightarrow> Yield a (False, s'))"

lemma terminates_dropWhile_raw:
  assumes "terminates g"
  shows "terminates (dropWhile_raw P g)"
proof (rule terminatesI)
  fix st :: "bool \<times> 'a"
  obtain b s where "st = (b, s)" by (cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on (dropWhile_raw P g)" unfolding \<open>st = (b, s)\<close>
  proof (induction s arbitrary: b)
    case (stop s b)
    then show ?case by (cases b)(simp_all add: terminates_on.stop)
  next
    case (pause s s' b)
    then show ?case by (cases b)(simp_all add: terminates_on.pause)
  next
    case (unfold s a s' b)
    then show ?case
      by(cases b)(cases "P a", auto intro: terminates_on.pause terminates_on.unfold)
   qed
qed

lift_definition dropWhile_trans :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's) generator \<Rightarrow> ('a, bool \<times> 's) generator"
is "dropWhile_raw" by (rule terminates_dropWhile_raw)

lemma unstream_dropWhile_trans_False:
  "unstream (dropWhile_trans P g) (False, s) = unstream g s"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by (cases "generator g s")(simp_all add: dropWhile_trans.rep_eq)
qed

lemma unstream_dropWhile_trans [stream_fusion]:
  "unstream (dropWhile_trans P g) (True, s) = dropWhile P (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case
  proof(cases "generator g s")
    case (Yield a s')
    then show ?thesis using "1.IH"(2) unstream_dropWhile_trans_False
      by (cases "P a")(simp_all add: dropWhile_trans.rep_eq)
  qed(simp_all add: dropWhile_trans.rep_eq)
qed

subsubsection \<open>@{const take}\<close>

fun take_raw :: "('a, 's) raw_generator \<Rightarrow> ('a, (nat \<times> 's)) raw_generator"
where
  "take_raw g (0, s) = Done"
| "take_raw g (Suc n, s) = (case g s of 
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (Suc n, s') | Yield a s' \<Rightarrow> Yield a (n, s'))"

lemma terminates_take_raw:
  assumes "terminates g"
  shows "terminates (take_raw g)"
proof (rule terminatesI)
  fix st :: "nat \<times> 'a"
  obtain n s where "st = (n, s)" by(cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  thus "st \<in> terminates_on (take_raw g)" unfolding \<open>st = (n, s)\<close>
    apply(induction s arbitrary: n)
    apply(case_tac [!] n)
    apply(auto intro: terminates_on.intros)
    done
qed

lift_definition take_trans :: "('a, 's) generator \<Rightarrow> ('a, nat \<times> 's) generator" is "take_raw"
by (rule terminates_take_raw)

lemma unstream_take_trans [stream_fusion]: "unstream (take_trans g) (n, s) = take n (unstream g s)" 
proof (induction s arbitrary: n taking: g rule: unstream.induct)
  case (1 s)
  show ?case using "1.IH"(1)[of _ n] "1.IH"(2)
    by(cases "generator g s" n rule: step.exhaust[case_product nat.exhaust])
      (simp_all add: take_trans.rep_eq)
qed

subsubsection \<open>@{const takeWhile}\<close>

definition takeWhile_raw :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('a, 's) raw_generator"
where
  "takeWhile_raw P g s = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip s' | Yield a s' \<Rightarrow> if P a then Yield a s' else Done)"

lemma terminates_takeWhile_raw: 
  assumes "terminates g"
  shows "terminates (takeWhile_raw P g)"
proof (rule terminatesI)
  fix s
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  thus "s \<in> terminates_on (takeWhile_raw P g)"
  proof (induction s rule: terminates_on.induct)
    case (unfold s a s')
    then show ?case by(cases "P a")(auto simp add: takeWhile_raw_def intro: terminates_on.intros)
  qed(auto intro: terminates_on.intros simp add: takeWhile_raw_def)
qed

lift_definition takeWhile_trans :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's) generator \<Rightarrow> ('a, 's) generator"
is "takeWhile_raw" by (rule terminates_takeWhile_raw)

lemma unstream_takeWhile_trans [stream_fusion]:
  "unstream (takeWhile_trans P g) s = takeWhile P (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by(cases "generator g s")(simp_all add: takeWhile_trans.rep_eq takeWhile_raw_def)
qed

subsubsection\<open>@{const append}\<close>

fun append_raw :: "('a, 'sg) raw_generator \<Rightarrow> ('a, 'sh) raw_generator \<Rightarrow> 'sh \<Rightarrow> ('a, 'sg + 'sh) raw_generator"
where
  "append_raw g h sh_start (Inl sg) = (case g sg of
     Done \<Rightarrow> Skip (Inr sh_start) | Skip sg' \<Rightarrow> Skip (Inl sg') | Yield a sg' \<Rightarrow> Yield a (Inl sg'))"
| "append_raw g h sh_start (Inr sh) = (case h sh of
     Done \<Rightarrow> Done | Skip sh' \<Rightarrow> Skip (Inr sh') | Yield a sh' \<Rightarrow> Yield a (Inr sh'))"

lemma terminates_on_append_raw_Inr: 
  assumes "terminates h"
  shows "Inr sh \<in> terminates_on (append_raw g h sh_start)"
proof -
  from assms have "sh \<in> terminates_on h" by (simp add: terminates_def)
  thus ?thesis by(induction sh)(auto intro: terminates_on.intros)
qed

lemma terminates_append_raw:
  assumes "terminates g" "terminates h"
  shows "terminates (append_raw g h sh_start)"
proof (rule terminatesI)
  fix s
  show "s \<in> terminates_on (append_raw g h sh_start)"
  proof (cases s)
    case (Inl sg)
    from \<open>terminates g\<close> have "sg \<in> terminates_on g" by (simp add: terminates_def)
    thus "s \<in> terminates_on (append_raw g h sh_start)" unfolding Inl
      by induction(auto intro: terminates_on.intros terminates_on_append_raw_Inr[OF \<open>terminates h\<close>])
  qed(simp add: terminates_on_append_raw_Inr[OF \<open>terminates h\<close>])
qed

lift_definition append_trans :: "('a, 'sg) generator \<Rightarrow> ('a, 'sh) generator \<Rightarrow> 'sh \<Rightarrow> ('a, 'sg + 'sh) generator"
is "append_raw" by (rule terminates_append_raw)

lemma unstream_append_trans_Inr: "unstream (append_trans g h sh) (Inr sh') = unstream h sh'"
proof (induction sh' taking: h rule: unstream.induct)
  case (1 sh')
  then show ?case by (cases "generator h sh'")(simp_all add: append_trans.rep_eq)
qed

lemma unstream_append_trans [stream_fusion]:
  "unstream (append_trans g h sh) (Inl sg) = append (unstream g sg) (unstream h sh)"
proof(induction sg taking: g rule: unstream.induct)
  case (1 sg)
  then show ?case using unstream_append_trans_Inr 
    by (cases "generator g sg")(simp_all add: append_trans.rep_eq)
qed

subsubsection\<open>@{const filter}\<close>

definition filter_raw :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('a, 's) raw_generator"
where 
  "filter_raw P g s = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip s' | Yield a s' \<Rightarrow> if P a then Yield a s' else Skip s')"

lemma terminates_filter_raw:
  assumes "terminates g"
  shows "terminates (filter_raw P g)"
proof (rule terminatesI)
  fix s
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  thus "s \<in> terminates_on (filter_raw P g)"
  proof(induction s)
    case (unfold s a s')
    thus ?case
      by(cases "P a")(auto intro: terminates_on.intros simp add: filter_raw_def)
  qed(auto intro: terminates_on.intros simp add: filter_raw_def)
qed

lift_definition filter_trans :: "('a \<Rightarrow> bool) \<Rightarrow> ('a,'s) generator \<Rightarrow> ('a,'s) generator"
is "filter_raw" by (rule terminates_filter_raw)

lemma unstream_filter_trans [stream_fusion]: "unstream (filter_trans P g) s = filter P (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by(cases "generator g s")(simp_all add: filter_trans.rep_eq filter_raw_def)
qed

subsubsection\<open>@{const zip}\<close>

fun zip_raw :: "('a, 'sg) raw_generator \<Rightarrow> ('b, 'sh) raw_generator \<Rightarrow> ('a \<times> 'b, 'sg \<times> 'sh \<times> 'a option) raw_generator"
  \<comment> \<open>We search first the left list for the next element and cache it in the @{typ "'a option"}
        part of the state once we found one\<close>
where
  "zip_raw g h (sg, sh, None) = (case g sg of
      Done \<Rightarrow> Done | Skip sg' \<Rightarrow> Skip (sg', sh, None) | Yield a sg' \<Rightarrow> Skip (sg', sh, Some a))"
| "zip_raw g h (sg, sh, Some a) = (case h sh of
      Done \<Rightarrow> Done | Skip sh' \<Rightarrow> Skip (sg, sh', Some a) | Yield b sh' \<Rightarrow> Yield (a, b) (sg, sh', None))"

lemma terminates_zip_raw: 
  assumes "terminates g" "terminates h"
  shows "terminates (zip_raw g h)"
proof (rule terminatesI)
  fix s :: "'a \<times> 'c \<times> 'b option"
  obtain sg sh m where "s = (sg, sh, m)" by(cases s)
  show "s \<in> terminates_on (zip_raw g h)" 
  proof(cases m)
    case None
    from \<open>terminates g\<close> have "sg \<in> terminates_on g" by (simp add: terminates_def)
    then show ?thesis unfolding \<open>s = (sg, sh, m)\<close> None
    proof (induction sg arbitrary: sh)
      case (unfold sg a sg')
      from \<open>terminates h\<close> have "sh \<in> terminates_on h" by (simp add: terminates_def)
      hence "(sg', sh, Some a) \<in> terminates_on (zip_raw g h)"
        by induction(auto intro: terminates_on.intros unfold.IH)
      thus ?case using unfold.hyps by(auto intro: terminates_on.pause)
    qed(simp_all add: terminates_on.stop terminates_on.pause)
  next
    case (Some a')
    from \<open>terminates h\<close> have "sh \<in> terminates_on h" by (simp add: terminates_def)
    thus ?thesis unfolding \<open>s = (sg, sh, m)\<close> Some
    proof (induction sh arbitrary: sg a')
      case (unfold sh b sh')
      from \<open>terminates g\<close> have "sg \<in> terminates_on g" by (simp add: terminates_def)
      hence "(sg, sh', None) \<in> terminates_on (zip_raw g h)"
        by induction(auto intro: terminates_on.intros unfold.IH)
      thus ?case using unfold.hyps by(auto intro: terminates_on.unfold)
    qed(simp_all add: terminates_on.stop terminates_on.pause)
  qed
qed

lift_definition zip_trans :: "('a, 'sg) generator \<Rightarrow> ('b, 'sh) generator \<Rightarrow> ('a \<times> 'b,'sg \<times> 'sh \<times> 'a option) generator"
is "zip_raw" by (rule terminates_zip_raw)

lemma unstream_zip_trans [stream_fusion]:
  "unstream (zip_trans g h) (sg, sh, None) = zip (unstream g sg) (unstream h sh)"        
proof (induction sg arbitrary: sh taking: g rule: unstream.induct)
  case (1 sg)
  then show ?case
  proof (cases "generator g sg")
    case (Yield a sg')
    note IH = "1.IH"(2)[OF Yield]
    have "unstream (zip_trans g h) (sg', sh, Some a) = zip (a # (unstream g sg')) (unstream h sh)"
    proof(induction sh taking: h rule: unstream.induct)
      case (1 sh)
      then show ?case using IH by(cases "generator h sh")(simp_all add: zip_trans.rep_eq)
    qed
    then show ?thesis using Yield by (simp add: zip_trans.rep_eq)
  qed(simp_all add: zip_trans.rep_eq)
qed

subsubsection \<open>@{const tl}\<close>

fun tl_raw :: "('a, 'sg) raw_generator \<Rightarrow> ('a, bool \<times> 'sg) raw_generator"
  \<comment> \<open>The Boolean flag stores whether we have already skipped the first element\<close>
where
  "tl_raw g (False, sg) = (case g sg of
      Done \<Rightarrow> Done | Skip sg' \<Rightarrow> Skip (False, sg') | Yield a sg' \<Rightarrow> Skip (True,sg'))"
| "tl_raw g (True, sg) = (case g sg of
      Done \<Rightarrow> Done | Skip sg' \<Rightarrow> Skip (True, sg') | Yield a sg' \<Rightarrow> Yield a (True, sg'))"

lemma terminates_tl_raw: 
  assumes "terminates g"
  shows "terminates (tl_raw g)"
proof (rule terminatesI)
  fix s :: "bool \<times> 'a"
  obtain b sg where "s = (b, sg)" by(cases s)
  { fix sg
    from assms have "sg \<in> terminates_on g" by(simp add: terminates_def)
    hence "(True, sg) \<in> terminates_on (tl_raw g)"
      by(induction sg)(auto intro: terminates_on.intros) }
  moreover from assms have "sg \<in> terminates_on g" by(simp add: terminates_def)
  hence "(False, sg) \<in> terminates_on (tl_raw g)"
    by(induction sg)(auto intro: terminates_on.intros calculation)
  ultimately show "s \<in> terminates_on (tl_raw g)" using \<open>s = (b, sg)\<close>
    by(cases b) simp_all
qed

lift_definition tl_trans :: "('a, 'sg) generator \<Rightarrow> ('a, bool \<times> 'sg) generator"
is "tl_raw" by(rule terminates_tl_raw)

lemma unstream_tl_trans_True: "unstream (tl_trans g) (True, s) = unstream g s"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  show ?case using "1.IH" by (cases "generator g s")(simp_all add: tl_trans.rep_eq)
qed

lemma unstream_tl_trans [stream_fusion]: "unstream (tl_trans g) (False, s) = tl (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case using unstream_tl_trans_True
    by (cases "generator g s")(simp_all add: tl_trans.rep_eq)
qed

subsubsection \<open>@{const butlast}\<close>

fun butlast_raw :: "('a, 's) raw_generator \<Rightarrow> ('a, 'a option \<times> 's) raw_generator"
  \<comment> \<open>The @{typ "'a option"} caches the previous element we have seen\<close>
where
  "butlast_raw g (None,s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (None, s') | Yield a s' \<Rightarrow> Skip (Some a, s'))"
| "butlast_raw g (Some b, s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (Some b, s') | Yield a s' \<Rightarrow> Yield b (Some a, s'))"

lemma terminates_butlast_raw:
  assumes "terminates g"
  shows "terminates (butlast_raw g)"
proof (rule terminatesI)
  fix st :: "'b option \<times> 'a"
  obtain ma s where "st = (ma,s)" by (cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on (butlast_raw g)" unfolding \<open>st = (ma, s)\<close>
    apply(induction s arbitrary: ma)
    apply(case_tac [!] ma)
    apply(auto intro: terminates_on.intros)
    done
qed

lift_definition butlast_trans :: "('a,'s) generator \<Rightarrow> ('a, 'a option \<times> 's) generator"
is "butlast_raw" by (rule terminates_butlast_raw)

lemma unstream_butlast_trans_Some:
  "unstream (butlast_trans g) (Some b,s) = butlast (b # (unstream g s))"
proof (induction s arbitrary: b taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by (cases "generator g s")(simp_all add: butlast_trans.rep_eq)
qed

lemma unstream_butlast_trans [stream_fusion]:
  "unstream (butlast_trans g) (None, s) = butlast (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case using 1 unstream_butlast_trans_Some[of g]
    by (cases "generator g s")(simp_all add: butlast_trans.rep_eq)
qed

subsubsection \<open>@{const concat}\<close>

text \<open>
  We only do the easy version here where
  the generator has type @{typ "('a list,'s) generator"}, not @{typ "(('a, 'si) generator, 's) generator"}
\<close>

fun concat_raw :: "('a list, 's) raw_generator \<Rightarrow> ('a, 'a list \<times> 's) raw_generator"
where
  "concat_raw g ([], s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip ([], s') | Yield xs s' \<Rightarrow> Skip (xs, s'))"
| "concat_raw g (x # xs, s) = Yield x (xs, s)"

lemma terminates_concat_raw: 
  assumes "terminates g"
  shows "terminates (concat_raw g)"
proof (rule terminatesI)
  fix st :: "'b list \<times> 'a"
  obtain xs s where "st = (xs, s)" by (cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on (concat_raw g)" unfolding \<open>st = (xs, s)\<close>
  proof (induction s arbitrary: xs)
    case (stop s xs)
    then show ?case by (induction xs)(auto intro: terminates_on.stop terminates_on.unfold)
  next
    case (pause s s' xs)
    then show ?case by (induction xs)(auto intro: terminates_on.pause terminates_on.unfold)
  next
    case (unfold s a s' xs)
    then show ?case by (induction xs)(auto intro: terminates_on.pause terminates_on.unfold)
  qed
qed

lift_definition concat_trans :: "('a list, 's) generator \<Rightarrow> ('a, 'a list \<times> 's) generator"
is "concat_raw" by (rule terminates_concat_raw)

lemma unstream_concat_trans_gen: "unstream (concat_trans g) (xs, s) = xs @ (concat (unstream g s))"
proof (induction s arbitrary: xs taking: g rule: unstream.induct)
  case (1 s)
  then show "unstream (concat_trans g) (xs, s) = xs @ (concat (unstream g s))"
  proof (cases "generator g s")
    case Done
    then show ?thesis by (induction xs)(simp_all add: concat_trans.rep_eq)
  next
    case (Skip s')
    then show ?thesis using "1.IH"(1)[of s' Nil]
      by (induction xs)(simp_all add: concat_trans.rep_eq)
  next
    case (Yield a s')
    then show ?thesis using "1.IH"(2)[of a s' a]
      by (induction xs)(simp_all add: concat_trans.rep_eq)
  qed
qed

lemma unstream_concat_trans [stream_fusion]:
  "unstream (concat_trans g) ([], s) = concat (unstream g s)"
by(simp only: unstream_concat_trans_gen append_Nil)

subsubsection \<open>@{const splice}\<close>

datatype ('a, 'b) splice_state = Left 'a 'b | Right 'a 'b | Left_only 'a | Right_only 'b

fun splice_raw :: "('a, 'sg) raw_generator \<Rightarrow> ('a, 'sh) raw_generator \<Rightarrow> ('a, ('sg, 'sh) splice_state) raw_generator"
where
  "splice_raw g h (Left_only sg) = (case g sg of
     Done \<Rightarrow> Done | Skip sg' \<Rightarrow> Skip (Left_only sg') | Yield a sg' \<Rightarrow> Yield a (Left_only sg'))"
| "splice_raw g h (Left sg sh) = (case g sg of
     Done \<Rightarrow> Skip (Right_only sh) | Skip sg' \<Rightarrow> Skip (Left sg' sh) | Yield a sg' \<Rightarrow> Yield a (Right sg' sh))"
| "splice_raw g h (Right_only sh) = (case h sh of
     Done \<Rightarrow> Done | Skip sh' \<Rightarrow> Skip (Right_only sh') | Yield a sh' \<Rightarrow> Yield a (Right_only sh'))"
| "splice_raw g h (Right sg sh) = (case h sh of
     Done \<Rightarrow> Skip (Left_only sg) | Skip sh' \<Rightarrow> Skip (Right sg sh') | Yield a sh' \<Rightarrow> Yield a (Left sg sh'))"

lemma terminates_splice_raw: 
  assumes g: "terminates g" and h: "terminates h"
  shows "terminates (splice_raw g h)"
proof (rule terminatesI)
  fix s
  { fix sg
    from g have "sg \<in> terminates_on g" by (simp add: terminates_def)
    hence "Left_only sg \<in> terminates_on (splice_raw g h)"
      by induction(auto intro: terminates_on.intros)
  } moreover {
    fix sh
    from h have "sh \<in> terminates_on h" by (simp add: terminates_def)
    hence "Right_only sh \<in> terminates_on (splice_raw g h)"
      by induction(auto intro: terminates_on.intros)
  } moreover {
    fix sg sh
    from g have "sg \<in> terminates_on g" by (simp add: terminates_def)
    hence "Left sg sh \<in> terminates_on (splice_raw g h)"
    proof (induction sg arbitrary: sh)
      case (unfold sg a sg')
      from h have "sh \<in> terminates_on h" by (simp add: terminates_def)
      hence "Right sg' sh \<in> terminates_on (splice_raw g h)"
        by induction(auto intro: terminates_on.intros unfold.IH calculation)
      thus ?case using unfold.hyps by (auto intro: terminates_on.unfold)
    qed(auto intro: terminates_on.intros calculation)
  } moreover {
    fix sg sh
    from h have "sh \<in> terminates_on h" by (simp add: terminates_def)
    hence "Right sg sh \<in> terminates_on (splice_raw g h)"
      by(induction sh arbitrary: sg)(auto intro: terminates_on.intros calculation) }
  ultimately show "s \<in> terminates_on (splice_raw g h)" by(cases s)(simp_all)
qed

lift_definition splice_trans :: "('a, 'sg) generator \<Rightarrow> ('a, 'sh) generator \<Rightarrow> ('a, ('sg, 'sh) splice_state) generator"
is "splice_raw" by (rule terminates_splice_raw)

lemma unstream_splice_trans_Right_only: "unstream (splice_trans g h) (Right_only sh) = unstream h sh" 
proof (induction sh taking: h rule: unstream.induct)
  case (1 sh)
  then show ?case by (cases "generator h sh")(simp_all add: splice_trans.rep_eq)
qed

lemma unstream_splice_trans_Left_only: "unstream (splice_trans g h) (Left_only sg) = unstream g sg"
proof (induction sg taking: g rule: unstream.induct)
  case (1 sg)
  then show ?case by (cases "generator g sg")(simp_all add: splice_trans.rep_eq)
qed

lemma unstream_splice_trans [stream_fusion]:
  "unstream (splice_trans g h) (Left sg sh) = splice (unstream g sg) (unstream h sh)"
proof (induction sg arbitrary: sh taking: g rule: unstream.induct)
  case (1 sg sh)
  then show ?case
  proof (cases "generator g sg")
    case Done
    with unstream_splice_trans_Right_only[of g h]
    show ?thesis by (simp add: splice_trans.rep_eq)
  next
    case (Skip sg')
    then show ?thesis using "1.IH"(1) by (simp add: splice_trans.rep_eq)
  next
    case (Yield a sg')
    note IH = "1.IH"(2)[OF Yield]

    have "a # (unstream (splice_trans g h) (Right sg' sh)) = splice (unstream g sg) (unstream h sh)"
    proof (induction sh taking: h rule: unstream.induct)
      case (1 sh)
      show ?case
      proof (cases "generator h sh")
        case Done
        with unstream_splice_trans_Left_only[of g h sg']
        show ?thesis using Yield by (simp add: splice_trans.rep_eq)
      next
        case (Skip sh')
        then show ?thesis using Yield "1.IH"(1) "1.prems" by(simp add: splice_trans.rep_eq)
      next
        case (Yield b sh')
        then show ?thesis using IH \<open>generator g sg = Yield a sg'\<close>
          by (simp add: splice_trans.rep_eq)
      qed
    qed
    then show ?thesis using Yield by (simp add: splice_trans.rep_eq)
  qed
qed


subsubsection \<open>@{const list_update}\<close>

fun list_update_raw :: "('a,'s) raw_generator \<Rightarrow> 'a \<Rightarrow> ('a, nat \<times> 's) raw_generator"
where
  "list_update_raw g b (n, s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (n, s') 
   | Yield a s' \<Rightarrow> if n = 0 then Yield a (0,s')
                   else if n = 1 then Yield b (0, s')
                   else Yield a (n - 1, s'))"

lemma terminates_list_update_raw:
  assumes "terminates g"
  shows "terminates (list_update_raw g b)"
proof (rule terminatesI)
  fix st :: "nat \<times> 'a"
  obtain n s where "st = (n, s)" by (cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on (list_update_raw g b)" unfolding \<open>st = (n, s)\<close>
  proof (induction s arbitrary: n)
    case (unfold s a s' n)
    then show "(n, s) \<in> terminates_on (list_update_raw g b)"
      by(cases "n = 0 \<or> n = 1")(auto intro: terminates_on.unfold)
  qed(simp_all add: terminates_on.stop terminates_on.pause)
qed

lift_definition list_update_trans :: "('a,'s) generator \<Rightarrow> 'a \<Rightarrow> ('a, nat \<times> 's)  generator"
is "list_update_raw" by (rule terminates_list_update_raw)

lemma unstream_lift_update_trans_None: "unstream (list_update_trans g b) (0, s) = unstream g s"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by (cases "generator g s")(simp_all add: list_update_trans.rep_eq)
qed

lemma unstream_list_update_trans [stream_fusion]:
  "unstream (list_update_trans g b) (Suc n, s) = list_update (unstream g s) n b"
proof(induction s arbitrary: n taking: g rule: unstream.induct)
  case (1 s)
  then show ?case
  proof (cases "generator g s")
    case Done
    then show ?thesis by (simp add: list_update_trans.rep_eq)
  next
    case (Skip s')
    then show ?thesis using "1.IH"(1) by (simp add: list_update_trans.rep_eq)
  next
    case (Yield a s')
    then show ?thesis using unstream_lift_update_trans_None[of g b s'] "1.IH"(2) 
      by (cases n)(simp_all add: list_update_trans.rep_eq)
  qed
qed

subsubsection \<open>@{const removeAll}\<close>

definition removeAll_raw :: "'a \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('a, 's) raw_generator"
where
 "removeAll_raw b g s = (case g s of
    Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip s' | Yield a s' \<Rightarrow> if a = b then Skip s' else Yield a s')"

lemma terminates_removeAll_raw:
  assumes "terminates g"
  shows "terminates (removeAll_raw b g)"
proof (rule terminatesI)
  fix s
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "s \<in> terminates_on (removeAll_raw b g)"
  proof(induction s)
    case (unfold s a s')
    then show ?case
      by(cases "a = b")(auto intro: terminates_on.intros simp add: removeAll_raw_def)
  qed(auto intro: terminates_on.intros simp add: removeAll_raw_def)
qed

lift_definition removeAll_trans :: "'a \<Rightarrow> ('a, 's) generator \<Rightarrow> ('a, 's) generator"
is "removeAll_raw" by (rule terminates_removeAll_raw)

lemma unstream_removeAll_trans [stream_fusion]:
  "unstream (removeAll_trans b g) s = removeAll b (unstream g s)"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case
  proof(cases "generator g s")
    case (Yield a s')
    then show ?thesis using "1.IH"(2)
      by(cases "a = b")(simp_all add: removeAll_trans.rep_eq removeAll_raw_def)
  qed(auto simp add: removeAll_trans.rep_eq removeAll_raw_def)
qed

subsubsection \<open>@{const remove1}\<close>

fun remove1_raw :: "'a \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('a, bool \<times> 's) raw_generator"
where
  "remove1_raw x g (b, s) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (b, s') 
   | Yield y s' \<Rightarrow> if b \<and> x = y then Skip (False, s') else Yield y (b, s'))"

lemma terminates_remove1_raw: 
  assumes "terminates g"
  shows "terminates (remove1_raw b g)"
proof (rule terminatesI)
  fix st :: "bool \<times> 'a"
  obtain c s where "st = (c, s)" by (cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on (remove1_raw b g)" unfolding \<open>st = (c, s)\<close>
  proof (induction s arbitrary: c)
    case (stop s)
    then show ?case by (cases c)(simp_all add: terminates_on.stop)
  next
    case (pause s s')
    then show ?case by (cases c)(simp_all add: terminates_on.pause)
  next
    case (unfold s a s')
    then show ?case
      by(cases c)(cases "a = b", auto intro: terminates_on.intros)
   qed
qed

lift_definition remove1_trans :: "'a \<Rightarrow> ('a, 's) generator \<Rightarrow> ('a, bool \<times> 's) generator "
is "remove1_raw" by (rule terminates_remove1_raw)

lemma unstream_remove1_trans_False: "unstream (remove1_trans b g) (False, s) = unstream g s"
proof (induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by (cases "generator g s")(simp_all add: remove1_trans.rep_eq)
qed

lemma unstream_remove1_trans [stream_fusion]:
  "unstream (remove1_trans b g) (True, s) = remove1 b (unstream g s)"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case
  proof (cases "generator g s")
    case (Yield a s')
    then show ?thesis
      using Yield "1.IH"(2) unstream_remove1_trans_False[of b g]
      by (cases "a = b")(simp_all add: remove1_trans.rep_eq)
  qed(simp_all add: remove1_trans.rep_eq)
qed

subsubsection \<open>@{term "(#)"}\<close>

fun Cons_raw :: "'a \<Rightarrow> ('a, 's) raw_generator \<Rightarrow> ('a, bool \<times> 's) raw_generator"
where
  "Cons_raw x g (b, s) = (if b then Yield x (False, s) else case g s of
    Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (False, s') | Yield y s' \<Rightarrow> Yield y (False, s'))"

lemma terminates_Cons_raw: 
  assumes "terminates g"
  shows "terminates (Cons_raw x g)"
proof (rule terminatesI)
  fix st :: "bool \<times> 'a"
  obtain b s where "st = (b, s)" by (cases st)
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  hence "(False, s) \<in> terminates_on (Cons_raw x g)"
    by(induction s arbitrary: b)(auto intro: terminates_on.intros)
  then show "st \<in> terminates_on (Cons_raw x g)" unfolding \<open>st = (b, s)\<close>
    by(cases b)(auto intro: terminates_on.intros)
qed

lift_definition Cons_trans :: "'a \<Rightarrow> ('a, 's) generator \<Rightarrow> ('a, bool \<times> 's) generator"
is Cons_raw by(rule terminates_Cons_raw)

lemma unstream_Cons_trans_False: "unstream (Cons_trans x g) (False, s) = unstream g s"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  then show ?case by(cases "generator g s")(auto simp add: Cons_trans.rep_eq)
qed

text \<open>
  We do not declare @{const Cons_trans} as a transformer.
  Otherwise, literal lists would be transformed into streams which adds a significant overhead
  to the stream state.
\<close>
lemma unstream_Cons_trans: "unstream (Cons_trans x g) (True, s) = x # unstream g s"
using unstream_Cons_trans_False[of x g s] by(simp add: Cons_trans.rep_eq)

subsubsection \<open>@{const List.maps}\<close>

text \<open>Stream version based on Coutts \cite{Coutts2010PhD}.\<close>

text \<open>
  We restrict the function for generating the inner lists to terminating
  generators because the code generator does not directly supported nesting abstract
  datatypes in other types.
\<close>

fun maps_raw
  :: "('a \<Rightarrow> ('b, 'sg) generator \<times> 'sg) \<Rightarrow> ('a, 's) raw_generator
  \<Rightarrow> ('b, 's \<times> (('b, 'sg) generator \<times> 'sg) option) raw_generator"
where
  "maps_raw f g (s, None) = (case g s of
    Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (s', None) | Yield x s' \<Rightarrow> Skip (s', Some (f x)))"
| "maps_raw f g (s, Some (g'', s'')) = (case generator g'' s'' of
    Done \<Rightarrow> Skip (s, None) | Skip s' \<Rightarrow> Skip (s, Some (g'', s')) | Yield x s' \<Rightarrow> Yield x (s, Some (g'', s')))"

lemma terminates_on_maps_raw_Some: 
  assumes "(s, None) \<in> terminates_on (maps_raw f g)"
  shows "(s, Some (g'', s'')) \<in> terminates_on (maps_raw f g)"
proof -
  from generator[of g''] have "s'' \<in> terminates_on (generator g'')" by (simp add: terminates_def)
  thus ?thesis by(induction)(auto intro: terminates_on.intros assms)
qed

lemma terminates_maps_raw: 
  assumes "terminates g"
  shows "terminates (maps_raw f g)"
proof
  fix st :: "'a \<times> (('c, 'd) generator \<times> 'd) option"
  obtain s mgs where "st = (s, mgs)" by(cases st) 
  from assms have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on (maps_raw f g)" unfolding \<open>st = (s, mgs)\<close>
    apply(induction arbitrary: mgs)
    apply(case_tac [!] mgs)
    apply(auto intro: terminates_on.intros intro!: terminates_on_maps_raw_Some)
    done
qed

lift_definition maps_trans :: "('a \<Rightarrow> ('b, 'sg) generator \<times> 'sg) \<Rightarrow> ('a, 's) generator
  \<Rightarrow> ('b, 's \<times> (('b, 'sg) generator \<times> 'sg) option) generator"
is "maps_raw" by(rule terminates_maps_raw)

lemma unstream_maps_trans_Some:
  "unstream (maps_trans f g) (s, Some (g'', s'')) = unstream g'' s'' @ unstream (maps_trans f g) (s, None)"
proof(induction s'' taking: g'' rule: unstream.induct)
  case (1 s'')
  then show ?case by(cases "generator g'' s''")(simp_all add: maps_trans.rep_eq)
qed

lemma unstream_maps_trans:
  "unstream (maps_trans f g) (s, None) = List.maps (case_prod unstream \<circ> f) (unstream g s)"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  thus ?case
  proof(cases "generator g s")
    case (Yield x s')
    with "1.IH"(2)[OF this] show ?thesis
      using unstream_maps_trans_Some[of f g _ "fst (f x)" "snd (f x)"]
      by(simp add: maps_trans.rep_eq maps_simps split_def)
  qed(simp_all add: maps_trans.rep_eq maps_simps)
qed

text \<open>
  The rule @{thm [source] unstream_map_trans} is too complicated for fusion because of @{term split},
  which does not arise naturally from stream fusion rules. Moreover, according to Farmer et al.
  \cite{FarmerHoenerGill2014PEPM}, this fusion is too general for further optimisations because the
  generators of the inner list are generated by the outer generator and therefore compilers may
  think that is was not known statically. 

  Instead, they propose a weaker version using \<open>flatten\<close> below.
  (More precisely, Coutts already mentions this approach in his PhD thesis \cite{Coutts2010PhD},
  but dismisses it because it requires a stronger rewriting engine than GHC has. But Isabelle's
  simplifier language is sufficiently powerful.
\<close>

fun fix_step :: "'a \<Rightarrow> ('b, 's) step \<Rightarrow> ('b, 'a \<times> 's) step"
where
  "fix_step a Done = Done"
| "fix_step a (Skip s) = Skip (a, s)"
| "fix_step a (Yield x s) = Yield x (a, s)"

fun fix_gen_raw :: "('a \<Rightarrow> ('b, 's) raw_generator) \<Rightarrow> ('b, 'a \<times> 's) raw_generator"
where "fix_gen_raw g (a, s) = fix_step a (g a s)"

lemma terminates_fix_gen_raw:
  assumes "\<And>x. terminates (g x)"
  shows "terminates (fix_gen_raw g)"
proof
  fix st :: "'a \<times> 'b"
  obtain a s where "st = (a, s)" by(cases st)
  from assms[of a] have "s \<in> terminates_on (g a)" by (simp add: terminates_def)
  then show "st \<in> terminates_on (fix_gen_raw g)" unfolding \<open>st = (a, s)\<close>
    by(induction)(auto intro: terminates_on.intros)
qed

lift_definition fix_gen :: "('a \<Rightarrow> ('b, 's) generator) \<Rightarrow> ('b, 'a \<times> 's) generator"
is "fix_gen_raw" by(rule terminates_fix_gen_raw)

lemma unstream_fix_gen: "unstream (fix_gen g) (a, s) = unstream (g a) s"
proof(induction s taking: "g a" rule: unstream.induct)
  case (1 s)
  thus ?case by(cases "generator (g a) s")(simp_all add: fix_gen.rep_eq)
qed

context 
  fixes f :: "('a \<Rightarrow> 's')"
  and g'' :: "('b, 's') raw_generator"
  and g :: "('a, 's) raw_generator"
begin

fun flatten_raw :: "('b, 's \<times> 's' option) raw_generator"
where
  "flatten_raw (s, None) = (case g s of
     Done \<Rightarrow> Done | Skip s' \<Rightarrow> Skip (s', None) | Yield x s' \<Rightarrow> Skip (s', Some (f x)))"
| "flatten_raw (s, Some s'') = (case g'' s'' of
     Done \<Rightarrow> Skip (s, None) | Skip s' \<Rightarrow> Skip (s, Some s') | Yield x s' \<Rightarrow> Yield x (s, Some s'))"

lemma terminates_flatten_raw: 
  assumes "terminates g''" "terminates g"
  shows "terminates flatten_raw"
proof
  fix st :: "'s \<times> 's' option"
  obtain s ms where "st = (s, ms)" by(cases st)
  { fix s s''
    assume s: "(s, None) \<in> terminates_on flatten_raw"
    from \<open>terminates g''\<close> have "s'' \<in> terminates_on g''" by (simp add: terminates_def)
    hence "(s, Some s'') \<in> terminates_on flatten_raw"
      by(induction)(auto intro: terminates_on.intros s) }
  note Some = this
  from \<open>terminates g\<close> have "s \<in> terminates_on g" by (simp add: terminates_def)
  then show "st \<in> terminates_on flatten_raw" unfolding \<open>st = (s, ms)\<close>
    apply(induction arbitrary: ms)
    apply(case_tac [!] ms)
    apply(auto intro: terminates_on.intros intro!: Some)
    done
qed

end

lift_definition flatten :: "('a \<Rightarrow> 's') \<Rightarrow> ('b, 's') generator \<Rightarrow> ('a, 's) generator \<Rightarrow> ('b, 's \<times> 's' option) generator"
is "flatten_raw" by(fact terminates_flatten_raw)

lemma unstream_flatten_Some:
  "unstream (flatten f g'' g) (s, Some s') = unstream g'' s' @ unstream (flatten f g'' g) (s, None)"
proof(induction s' taking: g'' rule: unstream.induct)
  case (1 s')
  thus ?case by(cases "generator g'' s'")(simp_all add: flatten.rep_eq)
qed

text \<open>HO rewrite equations can express the variable capture in the generator unlike GHC rules\<close>

lemma unstream_flatten_fix_gen [stream_fusion]:
  "unstream (flatten (\<lambda>s. (s, f s)) (fix_gen g'') g) (s, None) =
   List.maps (\<lambda>s'. unstream (g'' s') (f s')) (unstream g s)"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  thus ?case
  proof(cases "generator g s")
    case (Yield x s')
    with "1.IH"(2)[OF this] unstream_flatten_Some[of "\<lambda>s. (s, f s)" "fix_gen g''" g]
    show ?thesis
      by(subst (1 3) unstream.simps)(simp add: flatten.rep_eq maps_simps unstream_fix_gen)
  qed(simp_all add: flatten.rep_eq maps_simps)
qed

text \<open>
  Separate fusion rule when the inner generator does not depend on the elements of the outer stream.
\<close>
lemma unstream_flatten [stream_fusion]:
  "unstream (flatten f g'' g) (s, None) = List.maps (\<lambda>s'. unstream g'' (f s')) (unstream g s)"
proof(induction s taking: g rule: unstream.induct)
  case (1 s)
  thus ?case 
  proof(cases "generator g s")
    case (Yield x s')
    with "1.IH"(2)[OF this] show ?thesis
      using unstream_flatten_Some[of f g'' g s' "f x"]
      by(simp add: flatten.rep_eq maps_simps o_def)
  qed(simp_all add: maps_simps flatten.rep_eq)
qed

end
