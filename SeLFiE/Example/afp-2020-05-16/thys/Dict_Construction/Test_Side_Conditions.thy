subsection \<open>Contrived side conditions\<close>

theory Test_Side_Conditions
imports Dict_Construction
begin

ML \<open>
fun assert_alt_total ctxt term = @{assert} (Side_Conditions.is_total ctxt term)
\<close>

fun head where
"head (x # _) = x"

local_setup \<open>snd o Side_Conditions.mk_side @{thms head.simps} NONE\<close>

lemma head_side_eq: "head_side xs \<longleftrightarrow> xs \<noteq> []"
by (cases xs) (auto intro: head_side.intros elim: head_side.cases)

declaration \<open>K (Side_Conditions.set_alt @{term head} @{thm head_side_eq})\<close>

fun map where
"map f [] = []" |
"map f (x # xs) = f x # map f xs"

local_setup \<open>snd o Side_Conditions.mk_side @{thms map.simps} (SOME @{thms map.induct})\<close>
thm map_side.intros

ML \<open>assert_alt_total @{context} @{term map}\<close>

experiment begin

  text \<open>Functions that use partial functions always in their domain are processed correctly.\<close>

  fun tail where
  "tail (_ # xs) = xs"

  local_setup \<open>snd o Side_Conditions.mk_side @{thms tail.simps} NONE\<close>

  lemma tail_side_eq: "tail_side xs \<longleftrightarrow> xs \<noteq> []"
  by (cases xs) (auto intro: tail_side.intros elim: tail_side.cases)

  declaration \<open>K (Side_Conditions.set_alt @{term tail} @{thm tail_side_eq})\<close>

  function map' where
  "map' f xs = (if xs = [] then [] else f (head xs) # map' f (tail xs))"
  by auto

  termination
    apply (relation "measure (size \<circ> snd)")
    apply rule
    subgoal for f xs by (cases xs) auto
    done

  local_setup \<open>snd o Side_Conditions.mk_side @{thms map'.simps} (SOME @{thms map'.induct})\<close>
  thm map'_side.intros

  ML \<open>assert_alt_total @{context} @{term map'}\<close>

end

lemma map_cong:
  assumes "xs = ys" "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "map f xs = map g ys"
unfolding assms(1)
using assms(2)
by (induction ys) auto

definition map_head where
"map_head xs = map head xs"

experiment begin

  declare map_cong[fundef_cong]

  local_setup \<open>snd o Side_Conditions.mk_side @{thms map_head_def} NONE\<close>
  thm map_head_side.intros

  lemma "map_head_side xs \<longleftrightarrow> (\<forall>x \<in> set xs. x \<noteq> [])"
  by (auto intro: map_head_side.intros elim: map_head_side.cases)

  definition map_head' where
  "map_head' xss = map (map head) xss"

  local_setup \<open>snd o Side_Conditions.mk_side @{thms map_head'_def} NONE\<close>
  thm map_head'_side.intros

  lemma "map_head'_side xss \<longleftrightarrow> (\<forall>xs \<in> set xss. \<forall>x \<in> set xs. x \<noteq> [])"
  by (auto intro: map_head'_side.intros elim: map_head'_side.cases)

end

experiment begin

  local_setup \<open>snd o Side_Conditions.mk_side @{thms map_head_def} NONE\<close>
  term map_head_side
  thm map_head_side.intros

  lemma "\<not> map_head_side xs"
  by (auto elim: map_head_side.cases)

end


definition head_known where
"head_known xs = head (3 # xs)"

local_setup \<open>snd o Side_Conditions.mk_side @{thms head_known_def} NONE\<close>
thm head_known_side.intros

ML\<open>assert_alt_total @{context} @{term head_known}\<close>

fun odd :: "nat \<Rightarrow> bool" and even where
"odd 0 \<longleftrightarrow> False" |
"even 0 \<longleftrightarrow> True" |
"odd (Suc n) \<longleftrightarrow> even n" |
"even (Suc n) \<longleftrightarrow> odd n"

local_setup \<open>snd o Side_Conditions.mk_side @{thms odd.simps even.simps} (SOME @{thms odd_even.induct})\<close>
thm odd_side_even_side.intros

ML\<open>assert_alt_total @{context} @{term odd}\<close>
ML\<open>assert_alt_total @{context} @{term even}\<close>

definition odd_known where
"odd_known = odd (Suc 0)"

local_setup \<open>snd o Side_Conditions.mk_side @{thms odd_known_def} NONE\<close>
thm odd_known_side.intros

ML\<open>assert_alt_total @{context} @{term odd_known}\<close>

end