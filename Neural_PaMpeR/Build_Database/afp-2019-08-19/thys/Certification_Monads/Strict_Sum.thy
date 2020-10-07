(* Title:     Xml
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>A Sum Type with Bottom Element\<close>

theory Strict_Sum
imports
  "HOL-Library.Monad_Syntax"
  Error_Syntax
  Partial_Function_MR.Partial_Function_MR
begin

datatype (dead 'e, 'a) sum_bot (infixr "+\<^sub>\<bottom>" 10) = Bottom | Left 'e | Right 'a for map: sum_bot_map


subsection \<open>Setup for Partial Functions\<close>

abbreviation sum_bot_ord :: "'e +\<^sub>\<bottom> 'a \<Rightarrow> 'e +\<^sub>\<bottom> 'a \<Rightarrow> bool"
where
  "sum_bot_ord \<equiv> flat_ord Bottom"

interpretation sum_bot:
  partial_function_definitions sum_bot_ord "flat_lub Bottom"
  by (rule flat_interpretation)

declaration \<open>
Partial_Function.init
  "sum_bot"
  @{term sum_bot.fixp_fun}
  @{term sum_bot.mono_body}
  @{thm sum_bot.fixp_rule_uc}
  @{thm sum_bot.fixp_induct_uc}
  NONE
\<close>


subsection \<open>Monad Setup\<close>

fun bind :: "'e +\<^sub>\<bottom> 'a \<Rightarrow> ('a \<Rightarrow> ('e +\<^sub>\<bottom> 'b)) \<Rightarrow> 'e +\<^sub>\<bottom> 'b"
where
  "bind Bottom f = Bottom" |
  "bind (Left e) f = Left e" |
  "bind (Right x) f = f x"

lemma bind_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. ys = Right x \<Longrightarrow> f x = g x"
  shows "bind xs f = bind ys g"
  using assms by (cases ys) simp_all

abbreviation mono_sum_bot :: "(('a \<Rightarrow> ('e +\<^sub>\<bottom> 'b)) \<Rightarrow> 'f +\<^sub>\<bottom> 'c) \<Rightarrow> bool"
where
  "mono_sum_bot \<equiv> monotone (fun_ord sum_bot_ord) sum_bot_ord"

(* TODO: perhaps use Partial_Function.bind_mono to proof this result immediately *)
lemma bind_mono [partial_function_mono]:
  assumes mf: "mono_sum_bot B" and mg: "\<And>y. mono_sum_bot (\<lambda>f. C y f)"
  shows "mono_sum_bot (\<lambda>f. bind (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b +\<^sub>\<bottom> 'c"
  assume fg: "fun_ord sum_bot_ord f g"
  with mf have "sum_bot_ord (B f) (B g)" by (rule monotoneD [of _ _ _ f g])
  then have "sum_bot_ord (bind (B f) (\<lambda>y. C y f)) (bind (B g) (\<lambda>y. C y f))"
    unfolding flat_ord_def by auto
  also from mg have "\<And>y'. sum_bot_ord (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  then have "sum_bot_ord (bind (B g) (\<lambda>y'. C y' f)) (bind (B g) (\<lambda>y'. C y' g))"
    unfolding flat_ord_def by (cases "B g") auto
  finally (sum_bot.leq_trans)
  show "sum_bot_ord (bind (B f) (\<lambda>y. C y f)) (bind (B g) (\<lambda>y'. C y' g))" .
qed

adhoc_overloading
  Monad_Syntax.bind bind

hide_const (open) bind

fun catch_error :: "'e +\<^sub>\<bottom> 'a \<Rightarrow> ('e \<Rightarrow> ('f +\<^sub>\<bottom> 'a)) \<Rightarrow> 'f +\<^sub>\<bottom> 'a"
where
  "catch_error Bottom f = Bottom " |
  "catch_error (Left a) f = f a" |
  "catch_error (Right a) f = Right a"

adhoc_overloading
  Error_Syntax.catch catch_error

lemma catch_mono [partial_function_mono]:
  assumes mf: "mono_sum_bot B" and mg: "\<And>y. mono_sum_bot (\<lambda>f. C y f)"
  shows "mono_sum_bot (\<lambda>f. try (B f) catch (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b +\<^sub>\<bottom> 'c"
  assume fg: "fun_ord sum_bot_ord f g"
  with mf have "sum_bot_ord (B f) (B g)" by (rule monotoneD [of _ _ _ f g])
  then have "sum_bot_ord (try (B f) catch (\<lambda>y. C y f)) (try (B g) catch (\<lambda>y. C y f))"
    unfolding flat_ord_def by auto
  also from mg
  have "\<And>y'. sum_bot_ord (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  then have "sum_bot_ord (try (B g) catch (\<lambda>y'. C y' f)) (try (B g) catch (\<lambda>y'. C y' g))"
    unfolding flat_ord_def by (cases "B g") auto
  finally (sum_bot.leq_trans)
    show "sum_bot_ord (try (B f) catch (\<lambda>y. C y f)) (try (B g) catch (\<lambda>y'. C y' g))" .
qed

definition error :: "'e \<Rightarrow> 'e +\<^sub>\<bottom> 'a"
where
  [simp]: "error x = Left x"

definition return :: "'a \<Rightarrow> 'e +\<^sub>\<bottom> 'a"
where
  [simp]: "return x = Right x"

fun map_sum_bot :: "('a \<Rightarrow> ('e +\<^sub>\<bottom> 'b)) \<Rightarrow> 'a list \<Rightarrow> 'e +\<^sub>\<bottom> 'b list"
where
  "map_sum_bot f [] = return []" |
  "map_sum_bot f (x#xs) = do {
    y \<leftarrow> f x;
    ys \<leftarrow> map_sum_bot f xs;
    return (y # ys)
  }"

lemma map_sum_bot_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "map_sum_bot f xs = map_sum_bot g ys"
  unfolding assms(1) using assms(2) by (induct ys) auto

lemmas sum_bot_const_mono =
  sum_bot.const_mono [of "fun_ord sum_bot_ord"]

lemma map_sum_bot_mono [partial_function_mono]:
  fixes C :: "'a \<Rightarrow> ('b \<Rightarrow> ('e +\<^sub>\<bottom> 'c)) \<Rightarrow> 'e +\<^sub>\<bottom> 'd"
  assumes "\<And>y. y \<in> set B \<Longrightarrow> mono_sum_bot (C y)"
  shows "mono_sum_bot (\<lambda>f. map_sum_bot (\<lambda>y. C y f) B)"
  using assms by (induct B) (auto intro!: partial_function_mono)

abbreviation update_error :: "'e +\<^sub>\<bottom> 'a \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> 'f +\<^sub>\<bottom> 'a"
where
  "update_error r f \<equiv> try r catch (\<lambda> e. error (f e))"

adhoc_overloading
  Error_Syntax.update_error update_error

fun sumbot :: "'e + 'a \<Rightarrow> 'e +\<^sub>\<bottom> 'a"
where
  "sumbot (Inl x) = Left x" |
  "sumbot (Inr x) = Right x"

code_datatype sumbot

lemma [code]:
  "bind (sumbot a) f = (case a of Inl b \<Rightarrow> sumbot (Inl b) | Inr a \<Rightarrow> f a)"
  by (cases a) auto

lemma [code]:
  "(try (sumbot a) catch f) = (case a of Inl b \<Rightarrow> f b | Inr a \<Rightarrow> sumbot (Inr a))"
  by (cases a) auto

lemma [code]: "Right x = sumbot (Inr x)" by simp

lemma [code]: "Left x = sumbot (Inl x)" by simp

lemma [code]: "return x = sumbot (Inr x)" by simp

lemma [code]: "error x = sumbot (Inl x)" by simp

lemma [code]:
  "case_sum_bot f g h (sumbot p) = case_sum g h p"
  by (cases p) auto


subsection \<open>Connection to @{theory Partial_Function_MR.Partial_Function_MR}\<close>

lemma sum_bot_map_mono [partial_function_mono]:
  assumes mf: "mono_sum_bot B"
  shows "mono_sum_bot (\<lambda>f. sum_bot_map h (B f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b +\<^sub>\<bottom> 'c"
  assume fg: "fun_ord sum_bot_ord f g"
  with mf have "sum_bot_ord (B f) (B g)" by (rule monotoneD [of _ _ _ f g])
  then show "sum_bot_ord (sum_bot_map h (B f)) (sum_bot_map h (B g))"
    unfolding flat_ord_def by auto    
qed

declaration \<open>
Partial_Function_MR.init 
  "sum_bot" 
  (fn (mt, t_to_ss, mtT, msT, t_to_sTs) =>
      list_comb (Const (@{const_name sum_bot_map}, t_to_sTs ---> mtT --> msT), t_to_ss) $ mt)
  (fn (commonTs, argTs) => Type (@{type_name sum_bot}, commonTs @ argTs))
  (fn mT => Term.dest_Type mT |> #2 |> (fn [err, res] => ([err], [res]))) 
  @{thms sum_bot.map_comp} 
  @{thms sum_bot.map_ident}
\<close>

end

