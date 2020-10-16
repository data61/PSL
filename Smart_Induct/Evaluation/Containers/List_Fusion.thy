(*  Title:      Containers/List_Fusion.thy
    Author:     Andreas Lochbihler, KIT *)

theory List_Fusion
imports 
  Main
begin

section \<open>Shortcut fusion for lists\<close>

lemma Option_map_mono [partial_function_mono]:
  "mono_option f \<Longrightarrow> mono_option (\<lambda>x. map_option g (f x))"
apply(rule monotoneI)
apply(drule (1) monotoneD)
apply(auto simp add: map_option_case flat_ord_def split: option.split)
done

lemma list_all2_coinduct [consumes 1, case_names Nil Cons, case_conclusion Cons hd tl, coinduct pred: list_all2]:
  assumes X: "X xs ys"
  and Nil': "\<And>xs ys. X xs ys \<Longrightarrow> xs = [] \<longleftrightarrow> ys = []"
  and Cons': "\<And>xs ys. \<lbrakk> X xs ys; xs \<noteq> []; ys \<noteq> [] \<rbrakk> \<Longrightarrow> A (hd xs) (hd ys) \<and> (X (tl xs) (tl ys) \<or> list_all2 A (tl xs) (tl ys))"
  shows "list_all2 A xs ys"
using X
proof(induction xs arbitrary: ys)
  case Nil
  from Nil'[OF this] show ?case by simp
next
  case (Cons x xs)
  from Nil'[OF Cons.prems] Cons'[OF Cons.prems] Cons.IH
  show ?case by(auto simp add: neq_Nil_conv)
qed



subsection \<open>The type of generators for finite lists\<close>

type_synonym ('a, 's) raw_generator = "('s \<Rightarrow> bool) \<times> ('s \<Rightarrow> 'a \<times> 's)"

inductive_set terminates_on :: "('a, 's) raw_generator \<Rightarrow> 's set"
  for g :: "('a, 's) raw_generator"
where
  stop: "\<not> fst g s \<Longrightarrow> s \<in> terminates_on g"
| unfold: "\<lbrakk> fst g s; snd (snd g s) \<in> terminates_on g \<rbrakk> \<Longrightarrow> s \<in> terminates_on g"

definition terminates :: "('a, 's) raw_generator \<Rightarrow> bool"
where "terminates g \<longleftrightarrow> (terminates_on g = UNIV)"

lemma terminatesI [intro?]:
  "(\<And>s. s \<in> terminates_on g) \<Longrightarrow> terminates g"
by(auto simp add: terminates_def)

lemma terminatesD:
  "terminates g \<Longrightarrow> s \<in> terminates_on g"
by(auto simp add: terminates_def)

lemma terminates_on_stop:
  "terminates_on (\<lambda>_. False, next) = UNIV"
by(auto intro: terminates_on.stop)

lemma wf_terminates:
  assumes "wf R"
  and step: "\<And>s. fst g s \<Longrightarrow> (snd (snd g s), s) \<in> R"
  shows "terminates g"
proof(rule terminatesI)
  fix s
  from \<open>wf R\<close> show "s \<in> terminates_on g"
  proof(induction rule: wf_induct[rule_format, consumes 1, case_names wf])
    case (wf s)
    show ?case
    proof(cases "fst g s")
      case True
      hence "(snd (snd g s), s) \<in> R" by(rule step)
      hence "snd (snd g s) \<in> terminates_on g" by(rule wf.IH)
      with True show ?thesis by(rule terminates_on.unfold)
    qed(rule terminates_on.stop)
  qed
qed

lemma terminates_wfD:
  assumes "terminates g"
  shows "wf {(snd (snd g s), s) | s . fst g s}"
proof(rule wfUNIVI)
  fix thesis s
  assume wf [rule_format]: "\<forall>s. (\<forall>s'. (s', s) \<in> {(snd (snd g s), s) |s. fst g s} \<longrightarrow> thesis s') \<longrightarrow> thesis s"
  from assms have "s \<in> terminates_on g" by(auto simp add: terminates_def)
  thus "thesis s" by induct (auto intro: wf)
qed

lemma terminates_wfE:
  assumes "terminates g"
  obtains R where "wf R" "\<And>s. fst g s \<Longrightarrow> (snd (snd g s), s) \<in> R"
by(rule that)(rule terminates_wfD[OF assms], simp)

context fixes g :: "('a, 's) raw_generator" begin

partial_function (option) terminates_within :: "'s \<Rightarrow> nat option"
where
  "terminates_within s =
   (let (has_next, next) = g
    in if has_next s then 
          map_option (\<lambda>n. n + 1) (terminates_within (snd (next s))) 
       else Some 0)"

lemma terminates_on_conv_dom_terminates_within:
  "terminates_on g = dom terminates_within"
proof(safe)
  fix s
  assume "s \<in> terminates_on g"
  then show "\<exists>n. terminates_within s = Some n"
    by(induct)(subst terminates_within.simps, simp add: split_beta)+
next
  fix s n
  assume "terminates_within s = Some n"
  then show "s \<in> terminates_on g"
    by(induct rule: terminates_within.raw_induct[rotated 1, consumes 1])(auto simp add: split_beta split: if_split_asm intro: terminates_on.intros)
qed

end

lemma terminates_within_unfold:
  "has_next s \<Longrightarrow> 
  terminates_within (has_next, next) s = map_option (\<lambda>n. n + 1) (terminates_within (has_next, next) (snd (next s)))"
by(simp add: terminates_within.simps)

typedef ('a, 's) generator = "{g :: ('a, 's) raw_generator. terminates g}"
  morphisms generator Generator
proof
  show "(\<lambda>_. False, undefined) \<in> ?generator"
    by(simp add: terminates_on_stop terminates_def)
qed

setup_lifting type_definition_generator

lemma terminates_on_generator_eq_UNIV:
  "terminates_on (generator g) = UNIV"
by transfer(simp add: terminates_def)

lemma terminates_within_stop:
  "terminates_within (\<lambda>_. False, next) s = Some 0"
by(simp add: terminates_within.simps)

lemma terminates_within_generator_neq_None:
  "terminates_within (generator g) s \<noteq> None"
by(transfer)(auto simp add: terminates_def terminates_on_conv_dom_terminates_within)

locale list = 
  fixes g :: "('a, 's) generator" begin

definition has_next :: "'s \<Rightarrow> bool"
where "has_next = fst (generator g)"

definition "next" :: "'s \<Rightarrow> 'a \<times> 's"
where "next = snd (generator g)"

function unfoldr :: "'s \<Rightarrow> 'a list"
where "unfoldr s = (if has_next s then let (a, s') = next s in a # unfoldr s' else [])"
by pat_completeness auto
termination
proof -
  have "terminates (generator g)" using generator[of g] by simp
  thus ?thesis
    by(rule terminates_wfE)(erule "termination", metis has_next_def next_def snd_conv)
qed

declare unfoldr.simps [simp del]

lemma unfoldr_simps:
  "has_next s \<Longrightarrow> unfoldr s = fst (next s) # unfoldr (snd (next s))"
  "\<not> has_next s \<Longrightarrow> unfoldr s = []"
by(simp_all add: unfoldr.simps split_beta)

end

declare 
  list.has_next_def[code]
  list.next_def[code]
  list.unfoldr.simps[code]

context includes lifting_syntax
begin

lemma generator_has_next_transfer [transfer_rule]: 
  "(pcr_generator (=) (=) ===> (=)) fst list.has_next"
by(auto simp add: generator.pcr_cr_eq cr_generator_def list.has_next_def dest: sym)

lemma generator_next_transfer [transfer_rule]:
  "(pcr_generator (=) (=) ===> (=)) snd list.next"
by(auto simp add: generator.pcr_cr_eq cr_generator_def list.next_def)

end

lemma unfoldr_eq_Nil_iff [iff]:
  "list.unfoldr g s = [] \<longleftrightarrow> \<not> list.has_next g s"
by(subst list.unfoldr.simps)(simp add: split_beta)

lemma Nil_eq_unfoldr_iff [simp]:
  "[] = list.unfoldr g s \<longleftrightarrow> \<not> list.has_next g s"
by(auto intro: sym dest: sym)

subsection \<open>Generators for @{typ "'a list"}\<close>

primrec list_has_next :: "'a list \<Rightarrow> bool"
where
  "list_has_next [] \<longleftrightarrow> False"
| "list_has_next (x # xs) \<longleftrightarrow> True"

primrec list_next :: "'a list \<Rightarrow> 'a \<times> 'a list"
where
  "list_next (x # xs) = (x, xs)"

lemma terminates_list_generator: "terminates (list_has_next, list_next)"
proof
  fix xs
  show "xs \<in> terminates_on (list_has_next, list_next)"
    by(induct xs)(auto intro: terminates_on.intros)
qed

lift_definition list_generator :: "('a, 'a list) generator" 
  is "(list_has_next, list_next)"
by(rule terminates_list_generator)

lemma has_next_list_generator [simp]: 
  "list.has_next list_generator = list_has_next"
by transfer simp

lemma next_list_generator [simp]: 
  "list.next list_generator = list_next"
by transfer simp

lemma unfoldr_list_generator:
  "list.unfoldr list_generator xs = xs"
by(induct xs)(simp_all add: list.unfoldr_simps)

lemma terminates_replicate_generator:
  "terminates (\<lambda>n :: nat. 0 < n, \<lambda>n. (a, n - 1))"
by(rule wf_terminates)(lexicographic_order)

lift_definition replicate_generator :: "'a \<Rightarrow> ('a, nat) generator"
  is "\<lambda>a. (\<lambda>n. 0 < n, \<lambda>n. (a, n - 1))"
by(rule terminates_replicate_generator)

lemma has_next_replicate_generator [simp]:
  "list.has_next (replicate_generator a) n \<longleftrightarrow> 0 < n"
by transfer simp

lemma next_replicate_generator [simp]:
  "list.next (replicate_generator a) n = (a, n - 1)"
by transfer simp

lemma unfoldr_replicate_generator:
  "list.unfoldr (replicate_generator a) n = replicate n a"
by(induct n)(simp_all add: list.unfoldr_simps)

context fixes f :: "'a \<Rightarrow> 'b" begin

lift_definition map_generator :: "('a, 's) generator \<Rightarrow> ('b, 's) generator"
  is "\<lambda>(has_next, next). (has_next, \<lambda>s. let (a, s') = next s in (f a, s'))"
by(erule terminates_wfE)(erule wf_terminates, auto simp add: split_beta)

lemma has_next_map_generator [simp]:
  "list.has_next (map_generator g) = list.has_next g"
by transfer clarsimp

lemma next_map_generator [simp]:
  "list.next (map_generator g) = apfst f \<circ> list.next g"
by transfer(simp add: fun_eq_iff split_beta apfst_def map_prod_def)

lemma unfoldr_map_generator:
  "list.unfoldr (map_generator g) = map f \<circ> list.unfoldr g"
  (is "?lhs = ?rhs")
proof(rule ext)
  fix s
  show "?lhs s = ?rhs s"
    by(induct s taking: "map_generator g" rule: list.unfoldr.induct)
      (subst (1 2) list.unfoldr.simps, auto simp add: split_beta apfst_def map_prod_def)
qed

end

context fixes g1 :: "('a, 's1) raw_generator"
  and g2 :: "('a, 's2) raw_generator" 
begin

fun append_has_next :: "'s1 \<times> 's2 + 's2 \<Rightarrow> bool"
where
  "append_has_next (Inl (s1, s2)) \<longleftrightarrow> fst g1 s1 \<or> fst g2 s2"
| "append_has_next (Inr s2) \<longleftrightarrow> fst g2 s2"

fun append_next :: "'s1 \<times> 's2 + 's2 \<Rightarrow> 'a \<times> ('s1 \<times> 's2 + 's2)"
where
  "append_next (Inl (s1, s2)) = 
  (if fst g1 s1 then 
     let (x, s1') = snd g1 s1 in (x, Inl (s1', s2)) 
   else append_next (Inr s2))"
| "append_next (Inr s2) = (let (x, s2') = snd g2 s2 in (x, Inr s2'))"

end

lift_definition append_generator :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> ('a, 's1 \<times> 's2 + 's2) generator"
  is "\<lambda>g1 g2. (append_has_next g1 g2, append_next g1 g2)"
proof(rule terminatesI, safe)
  fix has_next1 and next1 :: "'s1 \<Rightarrow> 'a \<times> 's1"
    and has_next2 and next2 :: "'s2 \<Rightarrow> 'a \<times> 's2"
    and s
  assume t1: "terminates (has_next1, next1)" 
    and t2: "terminates (has_next2, next2)"
  let ?has_next = "append_has_next (has_next1, next1) (has_next2, next2)"
  let ?next = "append_next (has_next1, next1) (has_next2, next2)"
  note [simp] = split_beta
    and [intro] = terminates_on.intros
  { fix s2 :: 's2
    from t2 have "s2 \<in> terminates_on (has_next2, next2)" by(rule terminatesD)
    hence "Inr s2 \<in> terminates_on (?has_next, ?next)" by induct auto }
  note Inr' = this

  show "s \<in> terminates_on (?has_next, ?next)"
  proof(cases s)
    case Inr thus ?thesis by(simp add: Inr')
  next
    case (Inl s1s2)
    moreover obtain s1 s2 where "s1s2 = (s1, s2)" by(cases s1s2)
    ultimately have s: "s = Inl (s1, s2)" by simp
    from t1 have "s1 \<in> terminates_on (has_next1, next1)" by(rule terminatesD)
    thus ?thesis unfolding s
    proof induct
      case stop thus ?case
        by(cases "has_next2 s2")(auto simp add: Inr')
    qed auto
  qed
qed

definition append_init :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's1 \<times> 's2 + 's2"
where "append_init s1 s2 = Inl (s1, s2)"

lemma has_next_append_generator [simp]:
  "list.has_next (append_generator g1 g2) (Inl (s1, s2)) \<longleftrightarrow>
   list.has_next g1 s1 \<or> list.has_next g2 s2"
  "list.has_next (append_generator g1 g2) (Inr s2) \<longleftrightarrow> list.has_next g2 s2"
by(transfer, simp)+

lemma next_append_generator [simp]:
  "list.next (append_generator g1 g2) (Inl (s1, s2)) =
  (if list.has_next g1 s1 then 
     let (x, s1') = list.next g1 s1 in (x, Inl (s1', s2))
   else list.next (append_generator g1 g2) (Inr s2))"
  "list.next (append_generator g1 g2) (Inr s2) = apsnd Inr (list.next g2 s2)"
by(transfer, simp add: apsnd_def map_prod_def)+

lemma unfoldr_append_generator_Inr: 
  "list.unfoldr (append_generator g1 g2) (Inr s2) = list.unfoldr g2 s2"
by(induct s2 taking: g2 rule: list.unfoldr.induct)(subst (1 2) list.unfoldr.simps, auto split: prod.splits)

lemma unfoldr_append_generator_Inl:
  "list.unfoldr (append_generator g1 g2) (Inl (s1, s2)) = 
   list.unfoldr g1 s1 @ list.unfoldr g2 s2"
apply(induct s1 taking: g1 rule: list.unfoldr.induct)
apply(subst (1 2 3) list.unfoldr.simps)
apply(auto split: prod.splits simp add: apsnd_def map_prod_def unfoldr_append_generator_Inr)
apply(simp add: list.unfoldr_simps)
done

lemma unfoldr_append_generator:
  "list.unfoldr (append_generator g1 g2) (append_init s1 s2) =
   list.unfoldr g1 s1 @ list.unfoldr g2 s2"
by(simp add: unfoldr_append_generator_Inl append_init_def)


lift_definition zip_generator :: "('a, 's1) generator \<Rightarrow> ('b, 's2) generator \<Rightarrow> ('a \<times> 'b, 's1 \<times> 's2) generator"
  is "\<lambda>(has_next1, next1) (has_next2, next2). 
      (\<lambda>(s1, s2). has_next1 s1 \<and> has_next2 s2, 
       \<lambda>(s1, s2). let (x, s1') = next1 s1; (y, s2') = next2 s2
                  in ((x, y), (s1', s2')))"
proof(rule terminatesI, safe)
  fix has_next1 next1 has_next2 next2 s1 s2
  assume t1: "terminates (has_next1, next1)" 
    and t2: "terminates (has_next2, next2)"
  have "s1 \<in> terminates_on (has_next1, next1)" "s2 \<in> terminates_on (has_next2, next2)"
    using t1 t2 by(simp_all add: terminatesD)
  thus "(s1, s2) \<in> terminates_on (\<lambda>(s1, s2). has_next1 s1 \<and> has_next2 s2, \<lambda>(s1, s2). let (x, s1') = next1 s1; (y, s2') = next2 s2 in ((x, y), (s1', s2')))"
    by(induct arbitrary: s2)(auto 4 3 elim: terminates_on.cases intro: terminates_on.intros simp add: split_beta Let_def)
qed

abbreviation (input) zip_init :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's1 \<times> 's2"
where "zip_init \<equiv> Pair"

lemma has_next_zip_generator [simp]: 
  "list.has_next (zip_generator g1 g2) (s1, s2) \<longleftrightarrow> 
   list.has_next g1 s1 \<and> list.has_next g2 s2"
by transfer clarsimp

lemma next_zip_generator [simp]: 
  "list.next (zip_generator g1 g2) (s1, s2) = 
  ((fst (list.next g1 s1), fst (list.next g2 s2)), 
   (snd (list.next g1 s1), snd (list.next g2 s2)))"
by transfer(simp add: split_beta)

lemma unfoldr_zip_generator:
  "list.unfoldr (zip_generator g1 g2) (zip_init s1 s2) = 
   zip (list.unfoldr g1 s1) (list.unfoldr g2 s2)"
by(induct "(s1, s2)" arbitrary: s1 s2 taking: "zip_generator g1 g2" rule: list.unfoldr.induct)
  (subst (1 2 3) list.unfoldr.simps, auto 9 2 simp add: split_beta)

context fixes bound :: nat begin

lift_definition upt_generator :: "(nat, nat) generator"
  is "(\<lambda>n. n < bound, \<lambda>n. (n, Suc n))"
by(rule wf_terminates)(relation "measure (\<lambda>n. bound - n)", auto)

lemma has_next_upt_generator [simp]:
  "list.has_next upt_generator n \<longleftrightarrow> n < bound"
by transfer simp

lemma next_upt_generator [simp]:
  "list.next upt_generator n = (n, Suc n)"
by transfer simp

lemma unfoldr_upt_generator:
  "list.unfoldr upt_generator n = [n..<bound]"
by(induct "bound - n" arbitrary: n)(simp_all add: list.unfoldr_simps upt_conv_Cons)

end

context fixes bound :: int begin

lift_definition upto_generator :: "(int, int) generator"
  is "(\<lambda>n. n \<le> bound, \<lambda>n. (n, n + 1))"
by(rule wf_terminates)(relation "measure (\<lambda>n. nat (bound + 1 - n))", auto)

lemma has_next_upto_generator [simp]:
  "list.has_next upto_generator n \<longleftrightarrow> n \<le> bound"
by transfer simp

lemma next_upto_generator [simp]:
  "list.next upto_generator n = (n, n + 1)"
by transfer simp

lemma unfoldr_upto_generator:
  "list.unfoldr upto_generator n = [n..bound]"
by(induct n taking: upto_generator rule: list.unfoldr.induct)(subst list.unfoldr.simps, subst upto.simps, auto)

end

context
  fixes P :: "'a \<Rightarrow> bool"
begin

context 
  fixes g :: "('a, 's) raw_generator"
begin

inductive filter_has_next :: "'s \<Rightarrow> bool"
where
  "\<lbrakk> fst g s; P (fst (snd g s)) \<rbrakk> \<Longrightarrow> filter_has_next s"
| "\<lbrakk> fst g s; \<not> P (fst (snd g s)); filter_has_next (snd (snd g s)) \<rbrakk> \<Longrightarrow> filter_has_next s"

partial_function (tailrec) filter_next :: "'s \<Rightarrow> 'a \<times> 's"
where
  "filter_next s = (let (x, s') = snd g s in if P x then (x, s') else filter_next s')"

end

lift_definition filter_generator :: "('a, 's) generator \<Rightarrow> ('a, 's) generator"
  is "\<lambda>g. (filter_has_next g, filter_next g)"
proof(rule wf_terminates)
  fix g :: "('a, 's) raw_generator" and s
  let ?R = "{(snd (snd g s), s) | s. fst g s}"
  let ?g = "(filter_has_next g, filter_next g)"
  assume "terminates g"
  thus "wf (?R\<^sup>+)" by(rule terminates_wfD[THEN wf_trancl])
  assume "fst ?g s"
  hence "filter_has_next g s" by simp
  thus "(snd (snd ?g s), s) \<in> ?R\<^sup>+"
    by induct(subst filter_next.simps, auto simp add: split_beta filter_next.simps split del: if_split intro: trancl_into_trancl)
qed

lemma has_next_filter_generator:
  "list.has_next (filter_generator g) s \<longleftrightarrow>
  list.has_next g s \<and> (let (x, s') = list.next g s in if P x then True else list.has_next (filter_generator g) s')"
apply(transfer)
apply simp
apply(subst filter_has_next.simps)
apply auto
done

lemma next_filter_generator:
   "list.next (filter_generator g) s =
   (let (x, s') = list.next g s
    in if P x then (x, s') else list.next (filter_generator g) s')"
apply transfer
apply simp
apply(subst filter_next.simps)
apply(simp cong: if_cong)
done

lemma has_next_filter_generator_induct [consumes 1, case_names find step]:
  assumes "list.has_next (filter_generator g) s"
  and find: "\<And>s. \<lbrakk> list.has_next g s; P (fst (list.next g s)) \<rbrakk> \<Longrightarrow> Q s"
  and step: "\<And>s. \<lbrakk> list.has_next g s; \<not> P (fst (list.next g s)); Q (snd (list.next g s)) \<rbrakk> \<Longrightarrow> Q s"
  shows "Q s"
using assms by transfer(auto elim: filter_has_next.induct)

lemma filter_generator_empty_conv:
  "list.has_next (filter_generator g) s \<longleftrightarrow> (\<exists>x\<in>set (list.unfoldr g s). P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  thus ?rhs
  proof(induct rule: has_next_filter_generator_induct)
    case (find s)
    thus ?case
      by(cases "list.next g s")(subst list.unfoldr.simps, auto)
  next
    case (step s)
    thus ?case
      by(cases "list.next g s")(subst list.unfoldr.simps, auto)
  qed
next
  assume ?rhs
  then obtain x where "x \<in> set (list.unfoldr g s)" "P x" by blast
  thus ?lhs
  proof(induct xs\<equiv>"list.unfoldr g s" arbitrary: s)
    case Nil thus ?case by(simp del: Nil_eq_unfoldr_iff)
  next
    case (Cons x' xs)
    from \<open>x' # xs = list.unfoldr g s\<close>[symmetric, simp]
    have [simp]: "fst (list.next g s) = x' \<and> list.has_next g s \<and> list.unfoldr g (snd (list.next g s)) = xs"
      by(subst (asm) list.unfoldr.simps)(simp add: split_beta split: if_split_asm)
    from Cons.hyps(1)[of "snd (list.next g s)"] \<open>x \<in> set (list.unfoldr g s)\<close> \<open>P x\<close> show ?case
      by(subst has_next_filter_generator)(auto simp add: split_beta)
  qed
qed

lemma unfoldr_filter_generator:
  "list.unfoldr (filter_generator g) s = filter P (list.unfoldr g s)"
unfolding list_all2_eq
proof(coinduction arbitrary: s)
  case Nil
  thus ?case by(simp add: filter_empty_conv filter_generator_empty_conv)
next
  case (Cons s)
  hence "list.has_next (filter_generator g) s" by simp
  thus ?case
  proof(induction rule: has_next_filter_generator_induct)
    case (find s)
    thus ?case
      apply(subst (1 2 3 5) list.unfoldr.simps)
      apply(subst (1 2) has_next_filter_generator)
      apply(subst next_filter_generator)
      apply(simp add: split_beta)
      apply(rule disjI1 exI conjI refl)+
      apply(subst next_filter_generator)
      apply(simp add: split_beta)
      done
  next
    case (step s)
    from step.hyps
    have "list.unfoldr (filter_generator g) s = list.unfoldr (filter_generator g) (snd (list.next g s))"
      apply(subst (1 2) list.unfoldr.simps)
      apply(subst has_next_filter_generator)
      apply(subst next_filter_generator)
      apply(auto simp add: split_beta)
      done
    moreover from step.hyps
    have "filter P (list.unfoldr g (snd (list.next g s))) = filter P (list.unfoldr g s)"
      by(subst (2) list.unfoldr.simps)(auto simp add: split_beta)
    ultimately show ?case using step.IH by simp
  qed
qed

end

subsection \<open>Destroying lists\<close>

definition hd_fusion :: "('a, 's) generator \<Rightarrow> 's \<Rightarrow> 'a"
where "hd_fusion g s = hd (list.unfoldr g s)"

lemma hd_fusion_code [code]:
  "hd_fusion g s = (if list.has_next g s then fst (list.next g s) else undefined)"
unfolding hd_fusion_def
by(subst list.unfoldr.simps)(simp add: hd_def split_beta)

declare hd_fusion_def [symmetric, code_unfold]

definition fold_fusion :: "('a, 's) generator \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 's \<Rightarrow> 'b \<Rightarrow> 'b"
where "fold_fusion g f s = fold f (list.unfoldr g s)"

lemma fold_fusion_code [code]:
  "fold_fusion g f s b =
  (if list.has_next g s then
     let (x, s') = list.next g s
     in fold_fusion g f s' (f x b)
   else b)"
unfolding fold_fusion_def
by(subst list.unfoldr.simps)(simp add: split_beta)

declare fold_fusion_def[symmetric, code_unfold]

definition gen_length_fusion :: "('a, 's) generator \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> nat"
where "gen_length_fusion g n s = n + length (list.unfoldr g s)"

lemma gen_length_fusion_code [code]:
  "gen_length_fusion g n s =
  (if list.has_next g s then gen_length_fusion g (Suc n) (snd (list.next g s)) else n)"
unfolding gen_length_fusion_def
by(subst list.unfoldr.simps)(simp add: split_beta)

definition length_fusion :: "('a, 's) generator \<Rightarrow> 's \<Rightarrow> nat"
where "length_fusion g s = length (list.unfoldr g s)"

lemma length_fusion_code [code]:
  "length_fusion g = gen_length_fusion g 0"
by(simp add: fun_eq_iff length_fusion_def gen_length_fusion_def)

declare length_fusion_def[symmetric, code_unfold]

definition map_fusion :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) generator \<Rightarrow> 's \<Rightarrow> 'b list"
where "map_fusion f g s = map f (list.unfoldr g s)"

lemma map_fusion_code [code]:
  "map_fusion f g s =
  (if list.has_next g s then
     let (x, s') = list.next g s
     in f x # map_fusion f g s'
   else [])"
unfolding map_fusion_def
by(subst list.unfoldr.simps)(simp add: split_beta)

declare map_fusion_def[symmetric, code_unfold]

definition append_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 'a list"
where "append_fusion g1 g2 s1 s2 = list.unfoldr g1 s1 @ list.unfoldr g2 s2"

lemma append_fusion [code]:
  "append_fusion g1 g2 s1 s2 =
  (if list.has_next g1 s1 then
     let (x, s1') = list.next g1 s1
     in x # append_fusion g1 g2 s1' s2
   else list.unfoldr g2 s2)"
unfolding append_fusion_def
by(subst list.unfoldr.simps)(simp add: split_beta)

declare append_fusion_def[symmetric, code_unfold]

definition zip_fusion :: "('a, 's1) generator \<Rightarrow> ('b, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> ('a \<times> 'b) list"
where "zip_fusion g1 g2 s1 s2 = zip (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

lemma zip_fusion_code [code]:
  "zip_fusion g1 g2 s1 s2 =
  (if list.has_next g1 s1 \<and> list.has_next g2 s2 then
     let (x, s1') = list.next g1 s1;
         (y, s2') = list.next g2 s2
     in (x, y) # zip_fusion g1 g2 s1' s2'
   else [])"
unfolding zip_fusion_def
by(subst (1 2) list.unfoldr.simps)(simp add: split_beta)

declare zip_fusion_def[symmetric, code_unfold]

definition list_all_fusion :: "('a, 's) generator \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
where "list_all_fusion g P s = List.list_all P (list.unfoldr g s)"

lemma list_all_fusion_code [code]:
  "list_all_fusion g P s \<longleftrightarrow>
  (list.has_next g s \<longrightarrow>
   (let (x, s') = list.next g s
    in P x \<and> list_all_fusion g P s'))"
unfolding list_all_fusion_def
by(subst list.unfoldr.simps)(simp add: split_beta)

declare list_all_fusion_def[symmetric, code_unfold]

definition list_all2_fusion :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 's1) generator \<Rightarrow> ('b, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "list_all2_fusion P g1 g2 s1 s2 = 
   list_all2 P (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

lemma list_all2_fusion_code [code]:
  "list_all2_fusion P g1 g2 s1 s2 =
  (if list.has_next g1 s1 then
     list.has_next g2 s2 \<and>
     (let (x, s1') = list.next g1 s1;
          (y, s2') = list.next g2 s2
      in P x y \<and> list_all2_fusion P g1 g2 s1' s2')
   else \<not> list.has_next g2 s2)"
unfolding list_all2_fusion_def
by(subst (1 2) list.unfoldr.simps)(simp add: split_beta)

declare list_all2_fusion_def[symmetric, code_unfold]

definition singleton_list_fusion :: "('a, 'state) generator \<Rightarrow> 'state \<Rightarrow> bool"
where "singleton_list_fusion gen state = (case list.unfoldr gen state of [_] \<Rightarrow> True | _ \<Rightarrow> False)"

lemma singleton_list_fusion_code [code]:
  "singleton_list_fusion g s \<longleftrightarrow>
  list.has_next g s \<and> \<not> list.has_next g (snd (list.next g s))"
by(auto 4 5 simp add: singleton_list_fusion_def split: list.split if_split_asm prod.splits elim: list.unfoldr.elims dest: sym)

end
