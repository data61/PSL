(*  Title:      JinjaThreads/Basic/Aux.thy
    Author:     Andreas Lochbihler, David von Oheimb, Tobias Nipkow

    Based on the Jinja theory Common/Aux.thy by David von Oheimb and Tobias Nipkow
*)

section \<open>Auxiliary Definitions and Lemmata\<close>

theory Auxiliary
imports
  Complex_Main
  "HOL-Library.Transitive_Closure_Table"
  "HOL-Library.Predicate_Compile_Alternative_Defs"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.Infinite_Set"
  FinFun.FinFun
begin

unbundle finfun_syntax

(* FIXME move and possibly turn into a general simproc *)
lemma nat_add_max_le[simp]:
  "((n::nat) + max i j \<le> m) = (n + i \<le> m \<and> n + j \<le> m)"
 (*<*)by arith(*>*)

lemma Suc_add_max_le[simp]:
  "(Suc(n + max i j) \<le> m) = (Suc(n + i) \<le> m \<and> Suc(n + j) \<le> m)"
(*<*)by arith(*>*)

lemma less_min_eq1:
  "(a :: 'a :: order) < b \<Longrightarrow> min a b = a"
by(auto simp add: min_def order_less_imp_le)

lemma less_min_eq2:
  "(a :: 'a :: order) > b \<Longrightarrow> min a b = b"
by(auto simp add: min_def order_less_imp_le)

no_notation floor ("\<lfloor>_\<rfloor>")
notation Some ("(\<lfloor>_\<rfloor>)")

(*<*)
declare
 option.splits[split]
 Let_def[simp]
 subset_insertI2 [simp]
(*>*)

declare not_Cons_self [no_atp] 

lemma Option_bind_eq_None_conv:
  "x \<bind> y = None \<longleftrightarrow> x = None \<or> (\<exists>x'. x = Some x' \<and> y x' = None)"
by(cases x) simp_all

lemma Option_bind_eq_Some_conv:
  "x \<bind> y = Some z \<longleftrightarrow> (\<exists>x'. x = Some x' \<and> y x' = Some z)"
by(cases x) simp_all

lemma map_upds_xchg_snd:
  "\<lbrakk> length xs \<le> length ys; length xs \<le> length zs; \<forall>i. i < length xs \<longrightarrow> ys ! i = zs ! i \<rbrakk>
  \<Longrightarrow> f(xs [\<mapsto>] ys) = f(xs [\<mapsto>] zs)"
proof(induct xs arbitrary: ys zs f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note IH = \<open>\<And>f ys zs. \<lbrakk> length xs \<le> length ys; length xs \<le> length zs; \<forall>i<length xs. ys ! i = zs ! i\<rbrakk>
             \<Longrightarrow> f(xs [\<mapsto>] ys) = f(xs [\<mapsto>] zs)\<close>
  note leny = \<open>length (x # xs) \<le> length ys\<close>
  note lenz = \<open>length (x # xs) \<le> length zs\<close>
  note nth = \<open>\<forall>i<length (x # xs). ys ! i = zs ! i\<close>
  from lenz obtain z zs' where zs [simp]: "zs = z # zs'" by(cases zs, auto)
  from leny obtain y ys' where ys [simp]: "ys = y # ys'" by(cases ys, auto)
  from lenz leny nth have "(f(x \<mapsto> y))(xs [\<mapsto>] ys') = (f(x \<mapsto> y))(xs [\<mapsto>] zs')"
    by-(rule IH, auto)
  moreover from nth have "y = z" by auto
  ultimately show ?case by(simp add: map_upds_def)
qed

subsection \<open>\<open>distinct_fst\<close>\<close>
 
definition
  distinct_fst  :: "('a \<times> 'b) list \<Rightarrow> bool"
where
  "distinct_fst  \<equiv>  distinct \<circ> map fst"

lemma distinct_fst_Nil [simp]:
  "distinct_fst []"
 (*<*)
apply (unfold distinct_fst_def)
apply (simp (no_asm))
done
(*>*)

lemma distinct_fst_Cons [simp]:
  "distinct_fst ((k,x)#kxs) = (distinct_fst kxs \<and> (\<forall>y. (k,y) \<notin> set kxs))"
(*<*)
apply (unfold distinct_fst_def)
apply (auto simp:image_def)
done
(*>*)

lemma distinct_fstD: "\<lbrakk> distinct_fst xs; (x, y) \<in> set xs; (x, z) \<in> set xs \<rbrakk> \<Longrightarrow> y = z"
by(induct xs) auto

lemma map_of_SomeI:
  "\<lbrakk> distinct_fst kxs; (k,x) \<in> set kxs \<rbrakk> \<Longrightarrow> map_of kxs k = Some x"
(*<*)by (induct kxs) (auto simp:fun_upd_apply)(*>*)

lemma rel_option_Some1:
  "rel_option R (Some x) y \<longleftrightarrow> (\<exists>y'. y = Some y' \<and> R x y')"
by(cases y) simp_all

lemma rel_option_Some2:
  "rel_option R x (Some y) \<longleftrightarrow> (\<exists>x'. x = Some x' \<and> R x' y)"
by(cases x) simp_all

subsection \<open>Using @{term list_all2} for relations\<close>

definition
  fun_of :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "fun_of S \<equiv> \<lambda>x y. (x,y) \<in> S"

text \<open>Convenience lemmas\<close>
(*<*)
declare fun_of_def [simp]
(*>*)
lemma rel_list_all2_Cons [iff]:
  "list_all2 (fun_of S) (x#xs) (y#ys) = 
   ((x,y) \<in> S \<and> list_all2 (fun_of S) xs ys)"
  (*<*)by simp(*>*)

lemma rel_list_all2_Cons1:
  "list_all2 (fun_of S) (x#xs) ys = 
  (\<exists>z zs. ys = z#zs \<and> (x,z) \<in> S \<and> list_all2 (fun_of S) xs zs)"
  (*<*)by (cases ys) auto(*>*)

lemma rel_list_all2_Cons2:
  "list_all2 (fun_of S) xs (y#ys) = 
  (\<exists>z zs. xs = z#zs \<and> (z,y) \<in> S \<and> list_all2 (fun_of S) zs ys)"
  (*<*)by (cases xs) auto(*>*)

lemma rel_list_all2_refl:
  "(\<And>x. (x,x) \<in> S) \<Longrightarrow> list_all2 (fun_of S) xs xs"
  (*<*)by (simp add: list_all2_refl)(*>*)

lemma rel_list_all2_antisym:
  "\<lbrakk> (\<And>x y. \<lbrakk>(x,y) \<in> S; (y,x) \<in> T\<rbrakk> \<Longrightarrow> x = y); 
     list_all2 (fun_of S) xs ys; list_all2 (fun_of T) ys xs \<rbrakk> \<Longrightarrow> xs = ys"
  (*<*)by (rule list_all2_antisym) auto(*>*)

lemma rel_list_all2_trans: 
  "\<lbrakk> \<And>a b c. \<lbrakk>(a,b) \<in> R; (b,c) \<in> S\<rbrakk> \<Longrightarrow> (a,c) \<in> T;
    list_all2 (fun_of R) as bs; list_all2 (fun_of S) bs cs\<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of T) as cs"
  (*<*)by (rule list_all2_trans) auto(*>*)

lemma rel_list_all2_update_cong:
  "\<lbrakk> i<size xs; list_all2 (fun_of S) xs ys; (x,y) \<in> S \<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of S) (xs[i:=x]) (ys[i:=y])"
  (*<*)by (simp add: list_all2_update_cong)(*>*)

lemma rel_list_all2_nthD:
  "\<lbrakk> list_all2 (fun_of S) xs ys; p < size xs \<rbrakk> \<Longrightarrow> (xs!p,ys!p) \<in> S"
  (*<*)by (drule list_all2_nthD) auto(*>*)

lemma rel_list_all2I:
  "\<lbrakk> length a = length b; \<And>n. n < length a \<Longrightarrow> (a!n,b!n) \<in> S \<rbrakk> \<Longrightarrow> list_all2 (fun_of S) a b"
  (*<*)by (erule list_all2_all_nthI) simp(*>*)

(*<*)declare fun_of_def [simp del](*>*)


lemma list_all2_induct[consumes 1, case_names Nil Cons]:
  assumes major: "list_all2 P xs ys"
  and Nil: "Q [] []"
  and Cons: "\<And>x xs y ys. \<lbrakk> P x y; list_all2 P xs ys; Q xs ys \<rbrakk> \<Longrightarrow> Q (x # xs) (y # ys)"
  shows "Q xs ys"
using major
by(induct xs arbitrary: ys)(auto simp add: list_all2_Cons1 Nil intro!: Cons)

lemma list_all2_split:
  assumes major: "list_all2 P xs ys"
  and split: "\<And>x y. P x y \<Longrightarrow> \<exists>z. Q x z \<and> R z y"
  shows "\<exists>zs. list_all2 Q xs zs \<and> list_all2 R zs ys"
using major
by(induct rule: list_all2_induct)(auto dest: split)

lemma list_all2_refl_conv:
  "list_all2 P xs xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x x)"
unfolding list_all2_conv_all_nth Ball_def in_set_conv_nth
by auto

lemma list_all2_op_eq [simp]:
  "list_all2 (=) xs ys \<longleftrightarrow> xs = ys"
by(induct xs arbitrary: ys)(auto simp add: list_all2_Cons1)

lemmas filter_replicate_conv = filter_replicate

lemma length_greater_Suc_0_conv: "Suc 0 < length xs \<longleftrightarrow> (\<exists>x x' xs'. xs = x # x' # xs')"
by(cases xs, auto simp add: neq_Nil_conv)

lemmas zip_same_conv = zip_same_conv_map

lemma nth_Cons_subtract: "0 < n \<Longrightarrow> (x # xs) ! n = xs ! (n - 1)"
by(auto simp add: nth_Cons split: nat.split)

lemma f_nth_set:
  "\<lbrakk> f (xs ! n) = v; n < length xs \<rbrakk> \<Longrightarrow> v \<in> f ` set xs"
unfolding set_conv_nth by auto

lemma nth_concat_eqI:
  "\<lbrakk> n = sum_list (map length (take i xss)) + k; i < length xss; k < length (xss ! i); x = xss ! i ! k \<rbrakk>
  \<Longrightarrow> concat xss ! n = x"
apply(induct xss arbitrary: n i k)
 apply simp
apply simp
apply(case_tac i)
 apply(simp add: nth_append)
apply(simp add: nth_append)
done

lemma replicate_eq_append_conv: 
  "(replicate n x = xs @ ys) = (\<exists>m\<le>n. xs = replicate m x \<and> ys = replicate (n-m) x)"
proof(induct n arbitrary: xs ys)
  case 0 thus ?case by simp
next
  case (Suc n xs ys)
  have IH: "\<And>xs ys. (replicate n x = xs @ ys) = (\<exists>m\<le>n. xs = replicate m x \<and> ys = replicate (n - m) x)" by fact
  show ?case
  proof(unfold replicate_Suc, rule iffI)
    assume a: "x # replicate n x = xs @ ys"
    show "\<exists>m\<le>Suc n. xs = replicate m x \<and> ys = replicate (Suc n - m) x"
    proof(cases xs)
      case Nil
      thus ?thesis using a
        by(auto)
    next
      case (Cons X XS)
      with a have x: "x = X" and "replicate n x = XS @ ys" by auto
      hence "\<exists>m\<le>n. XS = replicate m x \<and> ys = replicate (n - m) x"
        by -(rule IH[THEN iffD1])
      then obtain m where "m \<le> n" and XS: "XS = replicate m x" and ys: "ys = replicate (n - m) x" by blast
      with x Cons show ?thesis
        by(fastforce)
    qed
  next
    assume "\<exists>m\<le>Suc n. xs = replicate m x \<and> ys = replicate (Suc n - m) x"
    then obtain m where m: "m \<le> Suc n" and xs: "xs = replicate m x" and ys: "ys = replicate (Suc n - m) x" by blast
    thus "x # replicate n x = xs @ ys"
      by(simp add: replicate_add[THEN sym])
  qed
qed

lemma replicate_Suc_snoc:
  "replicate (Suc n) x = replicate n x @ [x]"
by (metis replicate_Suc replicate_append_same)

lemma map_eq_append_conv:
  "map f xs = ys @ zs \<longleftrightarrow> (\<exists>ys' zs'. map f ys' = ys \<and> map f zs' = zs \<and> xs = ys' @ zs')"
apply(rule iffI)
 apply(metis append_eq_conv_conj append_take_drop_id drop_map take_map)
by(clarsimp)

lemma append_eq_map_conv:
  "ys @ zs = map f xs \<longleftrightarrow> (\<exists>ys' zs'. map f ys' = ys \<and> map f zs' = zs \<and> xs = ys' @ zs')"
unfolding map_eq_append_conv[symmetric]
by auto

lemma map_eq_map_conv:
  "map f xs = map g ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = g y) xs ys"
apply(induct xs arbitrary: ys)
apply(auto simp add: list_all2_Cons1 Cons_eq_map_conv)
done

lemma map_eq_all_nth_conv:
  "map f xs = ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>n < length xs. f (xs ! n) = ys ! n)"
apply(induct xs arbitrary: ys)
apply(fastforce simp add: nth_Cons Suc_length_conv split: nat.splits)+
done



lemma take_eq_take_le_eq:
  "\<lbrakk> take n xs = take n ys; m \<le> n \<rbrakk> \<Longrightarrow> take m xs = take m ys"
by(metis min.absorb_iff1 take_take)

lemma take_list_update_beyond:
  "n \<le> m \<Longrightarrow> take n (xs[m := x]) = take n xs"
by(cases "n \<le> length xs")(rule nth_take_lemma, simp_all)

lemma hd_drop_conv_nth:
  "n < length xs \<Longrightarrow> hd (drop n xs) = xs ! n"
by(rule hd_drop_conv_nth) (metis list.size(3) not_less0)

lemma set_tl_subset: "set (tl xs) \<subseteq> set xs"
by(cases xs) auto

lemma tl_conv_drop: "tl xs = drop 1 xs"
by(cases xs) simp_all

lemma takeWhile_eq_Nil_dropWhile_eq_Nil_imp_Nil:
  "\<lbrakk> takeWhile P xs = []; dropWhile P xs = [] \<rbrakk> \<Longrightarrow> xs = []"
by (metis dropWhile_eq_drop drop_0 list.size(3))

lemma takeWhile_eq_Nil_conv:
  "takeWhile P xs = [] \<longleftrightarrow> (xs = [] \<or> \<not> P (hd xs))"
by(cases xs) simp_all

lemma dropWhile_append1': "dropWhile P xs \<noteq> [] \<Longrightarrow> dropWhile P (xs @ ys) = dropWhile P xs @ ys"
by(cases xs) auto

lemma dropWhile_append2': "dropWhile P xs = [] \<Longrightarrow> dropWhile P (xs @ ys) = dropWhile P ys"
by(simp)

lemma takeWhile_append1': "dropWhile P xs \<noteq> [] \<Longrightarrow> takeWhile P (xs @ ys) = takeWhile P xs"
by auto

lemma takeWhile_takeWhile: "takeWhile P (takeWhile Q xs) = takeWhile (\<lambda>x. P x \<and> Q x) xs"
by(induct xs) simp_all

lemma dropWhile_eq_ConsD:
  "dropWhile P xs = y # ys \<Longrightarrow> y \<in> set xs \<and> \<not> P y"
by(induct xs)(auto split: if_split_asm)

lemma dropWhile_eq_hd_conv: "dropWhile P xs = hd xs # rest \<longleftrightarrow> xs \<noteq> [] \<and> rest = tl xs \<and> \<not> P (hd xs)"
by (metis append_Nil append_is_Nil_conv dropWhile_eq_Cons_conv list.sel(1) neq_Nil_conv takeWhile_dropWhile_id takeWhile_eq_Nil_conv list.sel(3))

lemma dropWhile_eq_same_conv: "dropWhile P xs = xs \<longleftrightarrow> (xs = [] \<or> \<not> P (hd xs))"
by (metis dropWhile.simps(1) eq_Nil_appendI hd_dropWhile takeWhile_dropWhile_id takeWhile_eq_Nil_conv)

lemma subset_code [code_unfold]:
  "set xs \<subseteq> set ys \<longleftrightarrow> (\<forall>x \<in> set xs. x \<in> set ys)"
by(rule Set.subset_eq)

lemma eval_bot [simp]:
  "Predicate.eval bot = (\<lambda>_. False)"
by(auto simp add: fun_eq_iff)

lemma not_is_emptyE:
  assumes "\<not> Predicate.is_empty P"
  obtains x where "Predicate.eval P x"
using assms
by(fastforce simp add: Predicate.is_empty_def bot_pred_def intro!: pred_iffI)

lemma is_emptyD:
  assumes "Predicate.is_empty P"
  shows "Predicate.eval P x \<Longrightarrow> False"
using assms
by(simp add: Predicate.is_empty_def bot_pred_def bot_apply Set.empty_def)

lemma eval_bind_conv:
  "Predicate.eval (P \<bind> R) y = (\<exists>x. Predicate.eval P x \<and> Predicate.eval (R x) y)"
by(blast elim: bindE intro: bindI)

lemma eval_single_conv: "Predicate.eval (Predicate.single a) b \<longleftrightarrow> a = b"
by(blast intro: singleI elim: singleE)


lemma conj_asm_conv_imp:
  "(A \<and> B \<Longrightarrow> PROP C) \<equiv> (A \<Longrightarrow> B \<Longrightarrow> PROP C)" 
apply(rule equal_intr_rule)
 apply(erule meta_mp)
 apply(erule (1) conjI)
apply(erule meta_impE)
 apply(erule conjunct1)
apply(erule meta_mp)
apply(erule conjunct2)
done

lemma meta_all_eq_conv: "(\<And>a. a = b \<Longrightarrow> PROP P a) \<equiv> PROP P b"
apply(rule equal_intr_rule)
 apply(erule meta_allE)
 apply(erule meta_mp)
 apply(rule refl)
apply(hypsubst)
apply assumption
done

lemma meta_all_eq_conv2: "(\<And>a. b = a \<Longrightarrow> PROP P a) \<equiv> PROP P b"
apply(rule equal_intr_rule)
 apply(erule meta_allE)
 apply(erule meta_mp)
 apply(rule refl)
apply(hypsubst)
apply assumption
done

lemma disj_split:
  "P (a \<or> b) \<longleftrightarrow> (a \<longrightarrow> P True) \<and> (b \<longrightarrow> P True) \<and> (\<not> a \<and> \<not> b \<longrightarrow> P False)"
apply(cases a)
apply(case_tac [!] b)
apply auto
done

lemma disj_split_asm:
  "P (a \<or> b) \<longleftrightarrow> \<not> (a \<and> \<not> P True \<or> b \<and> \<not> P True \<or> \<not> a \<and> \<not> b \<and> \<not> P False)"
apply(auto simp add: disj_split[of P])
done

lemma disjCE:
  assumes "P \<or> Q"
  obtains P | "Q" "\<not> P"
using assms by blast

lemma case_option_conv_if:
  "(case v of None \<Rightarrow> f | Some x \<Rightarrow> g x) = (if \<exists>a. v = Some a then g (the v) else f)"
by(simp)

lemma LetI: "(\<And>x. x = t \<Longrightarrow> P x) \<Longrightarrow> let x = t in P x"
by(simp)

(* rearrange parameters and premises to allow application of one-point-rules *)
(* adapted from Tools/induct.ML and Isabelle Developer Workshop 2010 *)

simproc_setup rearrange_eqs ("Pure.all t") = \<open>
let
  fun swap_params_conv ctxt i j cv =
    let
      fun conv1 0 ctxt = Conv.forall_conv (cv o snd) ctxt
        | conv1 k ctxt =
            Conv.rewr_conv @{thm swap_params} then_conv
            Conv.forall_conv (conv1 (k - 1) o snd) ctxt
      fun conv2 0 ctxt = conv1 j ctxt
        | conv2 k ctxt = Conv.forall_conv (conv2 (k - 1) o snd) ctxt
    in conv2 i ctxt end;

  fun swap_prems_conv 0 = Conv.all_conv
    | swap_prems_conv i =
        Conv.implies_concl_conv (swap_prems_conv (i - 1)) then_conv
        Conv.rewr_conv Drule.swap_prems_eq;

  fun find_eq ctxt t =
    let
      val l = length (Logic.strip_params t);
      val Hs = Logic.strip_assums_hyp t;
      fun find (i, (_ $ (Const ("HOL.eq", _) $ Bound j $ _))) = SOME (i, j)
        | find (i, (_ $ (Const ("HOL.eq", _) $ _ $ Bound j))) = SOME (i, j)
        | find _ = NONE
    in
      (case get_first find (map_index I Hs) of
        NONE => NONE
      | SOME (0, 0) => NONE
      | SOME (i, j) => SOME (i, l - j - 1, j))
    end;

  fun mk_swap_rrule ctxt ct =
    (case find_eq ctxt (Thm.term_of ct) of
      NONE => NONE
    | SOME (i, k, j) => SOME (swap_params_conv ctxt k j (K (swap_prems_conv i)) ct))
in
  fn _ => mk_swap_rrule
end
\<close>
declare [[simproc del: rearrange_eqs]]
lemmas meta_onepoint = meta_all_eq_conv meta_all_eq_conv2

lemma meta_all2_eq_conv: "(\<And>a b. a = c \<Longrightarrow> PROP P a b) \<equiv> (\<And>b. PROP P c b)"
apply(rule equal_intr_rule)
 apply(erule meta_allE)+
 apply(erule meta_mp)
 apply(rule refl)
apply(erule meta_allE)
apply simp
done

lemma meta_all3_eq_conv: "(\<And>a b c. a = d \<Longrightarrow> PROP P a b c) \<equiv> (\<And>b c. PROP P d b c)"
apply(rule equal_intr_rule)
 apply(erule meta_allE)+
 apply(erule meta_mp)
 apply(rule refl)
apply(erule meta_allE)+
apply simp
done

lemma meta_all4_eq_conv: "(\<And>a b c d. a = e \<Longrightarrow> PROP P a b c d) \<equiv> (\<And>b c d. PROP P e b c d)"
apply(rule equal_intr_rule)
 apply(erule meta_allE)+
 apply(erule meta_mp)
 apply(rule refl)
apply(erule meta_allE)+
apply simp
done

lemma meta_all5_eq_conv: "(\<And>a b c d e. a = f \<Longrightarrow> PROP P a b c d e) \<equiv> (\<And>b c d e. PROP P f b c d e)"
apply(rule equal_intr_rule)
 apply(erule meta_allE)+
 apply(erule meta_mp)
 apply(rule refl)
apply(erule meta_allE)+
apply simp
done

lemma inj_on_image_mem_iff:
  "\<lbrakk> inj_on f A; B \<subseteq> A; a \<in> A \<rbrakk> \<Longrightarrow> f a \<in> f ` B \<longleftrightarrow> a \<in> B"
by(metis inv_into_f_eq inv_into_image_cancel rev_image_eqI)

lemma sum_hom:
  assumes hom_add [simp]: "\<And>a b. f (a + b) = f a + f b"
  and hom_0 [simp]: "f 0 = 0"
  shows "sum (f \<circ> h) A = f (sum h A)"
proof(cases "finite A")
  case False thus ?thesis by simp
next
  case True thus ?thesis
    by(induct) simp_all
qed

lemma sum_upto_add_nat:
  "a \<le> b \<Longrightarrow> sum f {..<(a :: nat)} + sum f {a..<b} = sum f {..<b}"
by (metis atLeast0LessThan le0 sum.atLeastLessThan_concat)

lemma nat_fun_sum_eq_conv:
  fixes f :: "'a \<Rightarrow> nat"
  shows "(\<lambda>a. f a + g a) = (\<lambda>a. 0) \<longleftrightarrow> f = (\<lambda>a .0) \<and> g = (\<lambda>a. 0)"
by(auto simp add: fun_eq_iff)


lemma in_ran_conv: "v \<in> ran m \<longleftrightarrow> (\<exists>k. m k = Some v)"
by(simp add: ran_def)

lemma map_le_dom_eq_conv_eq:
  "\<lbrakk> m \<subseteq>\<^sub>m m'; dom m = dom m' \<rbrakk> \<Longrightarrow> m = m'"
by (metis map_le_antisym map_le_def)

lemma map_leI:
  "(\<And>k v. f k = Some v \<Longrightarrow> g k = Some v) \<Longrightarrow> f \<subseteq>\<^sub>m g"
unfolding map_le_def by auto

lemma map_le_SomeD: "\<lbrakk> m \<subseteq>\<^sub>m m'; m x = \<lfloor>y\<rfloor> \<rbrakk> \<Longrightarrow> m' x = \<lfloor>y\<rfloor>"
by(auto simp add: map_le_def dest: bspec)

lemma map_le_same_upd:
  "f x = None \<Longrightarrow> f \<subseteq>\<^sub>m f(x \<mapsto> y)"
by(auto simp add: map_le_def)

lemma map_upd_map_add: "X(V \<mapsto> v) = (X ++ [V \<mapsto> v])"
by(simp)




lemma foldr_filter_conv:
  "foldr f (filter P xs) = foldr (\<lambda>x s. if P x then f x s else s) xs"
by(induct xs)(auto intro: ext)

lemma foldr_insert_conv_set:
  "foldr insert xs A = A \<union> set xs"
by(induct xs arbitrary: A) auto

lemma snd_o_Pair_conv_id: "snd o Pair a = id"
by(simp add: o_def id_def)

lemma if_intro:
  "\<lbrakk> P \<Longrightarrow> A; \<not> P \<Longrightarrow> B \<rbrakk> \<Longrightarrow> if P then A else B"
by(auto)

lemma ex_set_conv: "(\<exists>x. x \<in> set xs) \<longleftrightarrow> xs \<noteq> []"
apply(auto)
apply(auto simp add: neq_Nil_conv)
done

lemma subset_Un1: "A \<subseteq> B \<Longrightarrow> A \<subseteq> B \<union> C" by blast
lemma subset_Un2: "A \<subseteq> C \<Longrightarrow> A \<subseteq> B \<union> C" by blast
lemma subset_insert: "A \<subseteq> B \<Longrightarrow> A \<subseteq> insert a B" by blast
lemma UNION_subsetD: "\<lbrakk> (\<Union>x\<in>A. f x) \<subseteq> B; a \<in> A \<rbrakk> \<Longrightarrow> f a \<subseteq> B" by blast

lemma Collect_eq_singleton_conv:
  "{a. P a} = {a} \<longleftrightarrow> P a \<and> (\<forall>a'. P a' \<longrightarrow> a = a')"
by(auto)

lemma Collect_conv_UN_singleton: "{f x|x. x \<in> P} = (\<Union>x\<in>P. {f x})"
by blast

lemma if_else_if_else_eq_if_else [simp]:
  "(if b then x else if b then y else z) = (if b then x else z)"
by(simp)

lemma rec_prod_split [simp]: "old.rec_prod = case_prod"
by(simp add: fun_eq_iff)

lemma inj_Pair_snd [simp]: "inj (Pair x)"
by(rule injI) auto

lemma rtranclp_False [simp]: "(\<lambda>a b. False)\<^sup>*\<^sup>* = (=)"
by(auto simp add: fun_eq_iff elim: rtranclp_induct)

lemmas rtranclp_induct3 =
  rtranclp_induct[where a="(ax, ay, az)" and b="(bx, by, bz)", split_rule, consumes 1, case_names refl step]

lemmas tranclp_induct3 =
  tranclp_induct[where a="(ax, ay, az)" and b="(bx, by, bz)", split_rule, consumes 1, case_names refl step]

lemmas rtranclp_induct4 =
  rtranclp_induct[where a="(ax, ay, az, aw)" and b="(bx, by, bz, bw)", split_rule, consumes 1, case_names refl step]

lemmas tranclp_induct4 =
  tranclp_induct[where a="(ax, ay, az, aw)" and b="(bx, by, bz, bw)", split_rule, consumes 1, case_names refl step]

lemmas converse_tranclp_induct2 =
  converse_tranclp_induct [of _ "(ax,ay)" "(bx,by)", split_rule,
                 consumes 1, case_names base step]

lemma wfP_induct' [consumes 1, case_names wfP]:
  "\<lbrakk>wfP r; \<And>x. (\<And>y. r y x \<Longrightarrow> P y) \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P a"
by(blast intro: wfP_induct)

lemma wfP_induct2 [consumes 1, case_names wfP]:
  "\<lbrakk>wfP r; \<And>x x'. (\<And>y y'. r (y, y') (x, x') \<Longrightarrow> P y y') \<Longrightarrow> P x x' \<rbrakk> \<Longrightarrow> P x x'"
by(drule wfP_induct'[where P="\<lambda>(x, y). P x y"]) blast+

lemma wfP_minimalE:
  assumes "wfP r"
  and "P x"
  obtains z where "P z" "r^** z x" "\<And>y. r y z \<Longrightarrow> \<not> P y"
proof -
  let ?Q = "\<lambda>x'. P x' \<and> r^** x' x"
  from \<open>P x\<close> have "?Q x" by blast
  from \<open>wfP r\<close> have "\<And>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. r y z \<longrightarrow> y \<notin> Q)"
    unfolding wfP_eq_minimal by blast
  from this[rule_format, of "Collect ?Q"] \<open>?Q x\<close>
  obtain z where "?Q z" and min: "\<And>y. r y z \<Longrightarrow> \<not> ?Q y" by auto
  from \<open>?Q z\<close> have "P z" "r^** z x" by auto
  moreover
  { fix y
    assume "r y z"
    hence "\<not> ?Q y" by(rule min)
    moreover from \<open>r y z\<close> \<open>r^** z x\<close> have "r^** y x"
      by(rule converse_rtranclp_into_rtranclp)
    ultimately have "\<not> P y" by blast }
  ultimately show thesis ..
qed

lemma coinduct_set_wf [consumes 3, case_names coinduct, case_conclusion coinduct wait step]: 
  assumes "mono f" "wf r" "(a, b) \<in> X"
  and step: "\<And>x b. (x, b) \<in> X \<Longrightarrow> (\<exists>b'. (b', b) \<in> r \<and> (x, b') \<in> X) \<or> (x \<in> f (fst ` X \<union> gfp f))"
  shows "a \<in> gfp f"
proof -
  from \<open>(a, b) \<in> X\<close> have "a \<in> fst ` X" by(auto intro: rev_image_eqI)
  moreover
  { fix a b
    assume "(a, b) \<in> X"
    with \<open>wf r\<close> have "a \<in> f (fst ` X \<union> gfp f)"
      by(induct)(blast dest: step) }
  hence "fst ` X \<subseteq> f (fst ` X \<union> gfp f)" by(auto)
  ultimately show ?thesis by(rule coinduct_set[OF \<open>mono f\<close>])
qed

subsection \<open>reflexive transitive closure for label relations\<close>

inductive converse3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
where
  converse3pI: "r a b c \<Longrightarrow> converse3p r c b a"

lemma converse3p_converse3p: "converse3p (converse3p r) = r"
by(auto intro: converse3pI intro!: ext elim: converse3p.cases)

lemma converse3pD: "converse3p r c b a \<Longrightarrow> r a b c"
by(auto elim: converse3p.cases)

inductive rtrancl3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where 
  rtrancl3p_refl [intro!, simp]: "rtrancl3p r a [] a"
| rtrancl3p_step: "\<lbrakk> rtrancl3p r a bs a'; r a' b a'' \<rbrakk> \<Longrightarrow> rtrancl3p r a (bs @ [b]) a''"

lemmas rtrancl3p_induct3 =
  rtrancl3p.induct[of _ "(ax,ay,az)" _ "(cx,cy,cz)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas rtrancl3p_induct4 = 
  rtrancl3p.induct[of _ "(ax,ay,az,aw)" _ "(cx,cy,cz,cw)", split_format (complete),
                 consumes 1, case_names refl step]

lemma rtrancl3p_induct4' [consumes 1, case_names refl step]:
  assumes major: "rtrancl3p r (ax, (ay, az), aw) bs (cx, (cy, cz), cw)"
  and refl: "\<And>a aa b ba. P a aa b ba [] a aa b ba"
  and step: "\<And>a aa b ba bs ab ac bb bc bd ad ae be bf.
       \<lbrakk> rtrancl3p r (a, (aa, b), ba) bs (ab, (ac, bb), bc);
         P a aa b ba bs ab ac bb bc; r (ab, (ac, bb), bc) bd (ad, (ae, be), bf) \<rbrakk>
       \<Longrightarrow> P a aa b ba (bs @ [bd]) ad ae be bf"
  shows "P ax ay az aw bs cx cy cz cw"
using major
apply -
apply(drule_tac P="\<lambda>(a, (aa, b), ba) bs (cx, (cy, cz), cw). P a aa b ba bs cx cy cz cw" in rtrancl3p.induct)
by(auto intro: refl step)

lemma rtrancl3p_induct1:
  "\<lbrakk> rtrancl3p r a bs c; P a; \<And>bs c b d. \<lbrakk> rtrancl3p r a bs c; r c b d; P c \<rbrakk> \<Longrightarrow> P d \<rbrakk> \<Longrightarrow> P c"
apply(induct rule: rtrancl3p.induct)
apply(auto)
done

inductive_cases rtrancl3p_cases:
  "rtrancl3p r x [] y"
  "rtrancl3p r x (b # bs) y"

lemma rtrancl3p_trans [trans]:
  assumes one: "rtrancl3p r a bs a'"
  and two: "rtrancl3p r a' bs' a''"
  shows "rtrancl3p r a (bs @ bs') a''"
using two one
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by simp
next
  case rtrancl3p_step thus ?case
    by(auto simp only: append_assoc[symmetric] intro: rtrancl3p.rtrancl3p_step)
qed

lemma rtrancl3p_step_converse:
  assumes step: "r a b a'"
  and stepify: "rtrancl3p r a' bs a''"
  shows "rtrancl3p r a (b # bs) a''"
using stepify step
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl 
  with rtrancl3p.rtrancl3p_refl[where r=r and a=a] show ?case 
    by(auto dest: rtrancl3p.rtrancl3p_step simp del: rtrancl3p.rtrancl3p_refl)
next
  case rtrancl3p_step thus ?case
    unfolding append_Cons[symmetric]
    by -(rule rtrancl3p.rtrancl3p_step)
qed

lemma converse_rtrancl3p_step:
  "rtrancl3p r a (b # bs) a'' \<Longrightarrow> \<exists>a'. r a b a' \<and> rtrancl3p r a' bs a''"
apply(induct bs arbitrary: a'' rule: rev_induct)
 apply(erule rtrancl3p.cases)
  apply(clarsimp)+
 apply(erule rtrancl3p.cases)
  apply(clarsimp)
  apply(rule_tac x="a''a" in exI)
  apply(clarsimp)
 apply(clarsimp)
apply(erule rtrancl3p.cases)
 apply(clarsimp)
apply(clarsimp)
by(fastforce intro: rtrancl3p_step)

lemma converse_rtrancl3pD:
  "rtrancl3p (converse3p r) a' bs a \<Longrightarrow> rtrancl3p r a (rev bs) a'"
apply(induct rule: rtrancl3p.induct)
 apply(fastforce intro: rtrancl3p.intros)
apply(auto dest: converse3pD intro: rtrancl3p_step_converse)
done

lemma rtrancl3p_converseD:
  "rtrancl3p r a bs a' \<Longrightarrow> rtrancl3p (converse3p r) a' (rev bs) a"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case
    by(auto intro: rtrancl3p.intros)
next
  case rtrancl3p_step thus ?case
    by(auto intro: rtrancl3p_step_converse converse3p.intros)
qed

lemma rtrancl3p_converse_induct [consumes 1, case_names refl step]:
  assumes ih: "rtrancl3p r a bs a''"
  and refl: "\<And>a. P a [] a"
  and step: "\<And>a b a' bs a''. \<lbrakk> rtrancl3p r a' bs a''; r a b a'; P a' bs a'' \<rbrakk> \<Longrightarrow> P a (b # bs) a''"
  shows "P a bs a''"
  using ih
proof(induct bs arbitrary: a a'')
  case Nil thus ?case
    by(auto elim: rtrancl3p.cases intro: refl)
next
  case Cons thus ?case
    by(auto dest!: converse_rtrancl3p_step intro: step)
qed  

lemma rtrancl3p_converse_induct' [consumes 1, case_names refl step]:
  assumes ih: "rtrancl3p r a bs a''"
  and refl: "P a'' []"
  and step: "\<And>a b a' bs. \<lbrakk> rtrancl3p r a' bs a''; r a b a'; P a' bs \<rbrakk> \<Longrightarrow> P a (b # bs)"
  shows "P a bs"
using rtrancl3p_converse_induct[OF ih, where P="\<lambda>a bs a'. a' = a'' \<longrightarrow> P a bs"]
by(auto intro: refl step)

lemma rtrancl3p_converseE[consumes 1, case_names refl step]:
  "\<lbrakk> rtrancl3p r a bs a'';
     \<lbrakk> a = a''; bs = [] \<rbrakk> \<Longrightarrow> thesis;
     \<And>bs' b a'. \<lbrakk> bs = b # bs'; r a b a'; rtrancl3p r a' bs' a'' \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(induct rule: rtrancl3p_converse_induct)(auto)


lemma rtrancl3p_induct' [consumes 1, case_names refl step]:
  assumes major: "rtrancl3p r a bs c"
  and refl: "P a [] a"
  and step: "\<And>bs a' b a''. \<lbrakk> rtrancl3p r a bs a'; P a bs a'; r a' b a'' \<rbrakk>
             \<Longrightarrow> P a (bs @ [b]) a''"
  shows "P a bs c"
proof -
  from major have "(P a [] a \<and> (\<forall>bs a' b a''. rtrancl3p r a bs a' \<and> P a bs a' \<and> r a' b a'' \<longrightarrow> P a (bs @ [b]) a'')) \<longrightarrow> P a bs c"
    by-(erule rtrancl3p.induct, blast+)
  with refl step show ?thesis by blast
qed

lemma r_into_rtrancl3p:
  "r a b a' \<Longrightarrow> rtrancl3p r a [b] a'"
by(rule rtrancl3p_step_converse) auto

lemma rtrancl3p_appendE:
  assumes "rtrancl3p r a (bs @ bs') a''"
  obtains a' where "rtrancl3p r a bs a'" "rtrancl3p r a' bs' a''"
using assms
apply(induct a "bs @ bs'" arbitrary: bs rule: rtrancl3p_converse_induct')
apply(fastforce intro: rtrancl3p_step_converse simp add: Cons_eq_append_conv)+
done

lemma rtrancl3p_Cons:
  "rtrancl3p r a (b # bs) a' \<longleftrightarrow> (\<exists>a''. r a b a'' \<and> rtrancl3p r a'' bs a')"
by(auto intro: rtrancl3p_step_converse converse_rtrancl3p_step)

lemma rtrancl3p_Nil:
  "rtrancl3p r a [] a' \<longleftrightarrow> a = a'"
by(auto elim: rtrancl3p_cases)

definition invariant3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where "invariant3p r I \<longleftrightarrow> (\<forall>s tl s'. s \<in> I \<longrightarrow> r s tl s' \<longrightarrow> s' \<in> I)"

lemma invariant3pI: "(\<And>s tl s'. \<lbrakk> s \<in> I; r s tl s' \<rbrakk> \<Longrightarrow> s' \<in> I) \<Longrightarrow> invariant3p r I"
unfolding invariant3p_def by blast

lemma invariant3pD: "\<And>tl. \<lbrakk> invariant3p r I; r s tl s'; s \<in> I \<rbrakk> \<Longrightarrow> s' \<in> I"
unfolding invariant3p_def by(blast)

lemma invariant3p_rtrancl3p: 
  assumes inv: "invariant3p r I"
  and rtrancl: "rtrancl3p r a bs a'"
  and start: "a \<in> I"
  shows "a' \<in> I"
using rtrancl start by(induct)(auto dest: invariant3pD[OF inv])

lemma invariant3p_UNIV [simp, intro!]:
  "invariant3p r UNIV"
by(blast intro: invariant3pI)

lemma invarinat3p_empty [simp, intro!]:
  "invariant3p r {}"
by(blast intro: invariant3pI)

lemma invariant3p_IntI [simp, intro]:
  "\<lbrakk> invariant3p r I; invariant3p r J \<rbrakk> \<Longrightarrow> invariant3p r (I \<inter> J)"
by(blast dest: invariant3pD intro: invariant3pI)

subsection \<open>Concatenation for @{typ String.literal}\<close>

definition concat :: "String.literal list \<Rightarrow> String.literal"
  where [code_abbrev, code del]: "concat = sum_list"

lemma explode_add [simp]:
  "String.explode (s + t) = String.explode s @ String.explode t"
  by (fact plus_literal.rep_eq)

code_printing
  constant concat \<rightharpoonup>
    (SML) "String.concat"
    and (Haskell) "concat"
    and (OCaml) "String.concat \"\""

hide_const (open) concat

end
