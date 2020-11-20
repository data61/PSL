theory Finiteness
  imports Main "HOL-Eisbach.Eisbach_Tools"
begin

section \<open>Two Eisbach proof methods for finiteness of sets\<close>
text \<open>
  The first method is intended to act more conservatively (think \<open>safe\<close>), leaving subgoals
  for the user where it couldn't proceed any further.
  The second method is more powerful, acting more in a succeed-or-die manner,
  similarly to \<open>force\<close> and friends.
  The examples in the second section should give a good impression of where these methods
  can help.
\<close>

text \<open>This slot is intended to provide more \<open>intro\<close> theorems for finite sets.\<close>
named_theorems finite

(* Trick from Dan Matichuk on isabelle-users *)
method add_finite_Collect_simproc methods m =
  match termI in H[simproc add: finite_Collect]:_ \<Rightarrow> m

(* Trick from Dan Matichuk on isabelle-users.
   Turns a structured method into a simple one.
*)
method_setup simple_method =
 \<open>Method.text_closure >> (fn m => fn ctxt =>
   let
     val facts = Method.get_facts ctxt
     val insert' = Method.Basic (K (Method.insert facts))
     val m' = Method.Combinator (Method.no_combinator_info, Method.Then, [insert', m])
   in Method.evaluate m' ctxt end)\<close>

method finite_tup =
  match conclusion in
    "finite (_ \<times> _)" \<Rightarrow> \<open>rule finite_cartesian_product; finite_tup\<close> \<bar>
    "finite S" for S :: "(_ * _) set" \<Rightarrow>
      \<open>print_term S, (rule finite_subset[where A = S and B = "fst ` S \<times> snd ` S"]; finite_tup?
        | (rule finite_subset; assumption?; fastforce))\<close> \<bar>
    "finite X" for X \<Rightarrow>
      \<open>print_term X, (simp add: image_def, finite_tup?)?,
                (solves \<open>(rule finite_subset; assumption?; fastforce)\<close>)?\<close> \<bar>
    _ \<Rightarrow> \<open>fastforce simp: image_def\<close>

method finite_search =
  match conclusion in
    "finite (_ \<times> _)" \<Rightarrow> \<open>rule finite_cartesian_product; finite_search\<close> \<bar>
    "finite (_ ` _)" \<Rightarrow> \<open>simp; finite_search | rule finite_imageI; finite_search\<close> \<bar>
    "finite S" for S :: "(_ * _) set" \<Rightarrow>
      \<open>print_term S, (solves \<open>rule finite_subset; auto\<close>
        | rule finite_subset[where A = S and B = "fst ` S \<times> snd ` S"]; finite_tup?)\<close> \<bar>
    "finite (Collect f)" for f \<Rightarrow>
      \<open>print_term f, (add_finite_Collect_simproc simp)?;
        (solves \<open>auto intro: finite\<close>
       | print_term v, simp?, rule finite; (assumption | finite_search)
       | rule finite_imageI; finite_search
       | rule finite_vimageI; finite_search
       | print_term x, rule finite_subset; assumption?; fastforce)\<close> \<bar>
    "finite X" for X \<Rightarrow>
      \<open>print_term X,
        (rule finite; (assumption | finite_search) 
       |(simp add: image_def, finite_search?)?,
          (solves \<open>(rule finite_subset; assumption?; fastforce)\<close>)?)\<close> \<bar>
    _ \<Rightarrow> \<open>fastforce simp: image_def\<close>

method finite = simple_method finite_search

section \<open>Tests\<close>

subsection \<open>Counterexamples\<close>

lemma inj_finite_single:
  assumes "inj f"
  shows "finite {y. x = f y}"
using assms Collect_mem_eq Collect_mono_iff infinite_iff_countable_subset inj_eq not_finite_existsD
      rangeI
by fastforce

lemmas inj_finite_single[finite]

text \<open>It's hard to guess the right set\<close>
lemma inj_finite_single':
  assumes "inj f"
  shows "finite {z. f z = x}"
apply (rule finite_subset[of _ "{z. x = f z}"])
apply blast
using assms by finite

(* Due to Lars Hupel *)
definition select :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "select f S = {z | z. \<exists>x \<in> S. f x = Some z}"

lemma select_finite:
  assumes "finite S"
  shows "finite (select f S)"
using assms unfolding select_def by finite

lemmas inj_finite_single'[finite]

subsection \<open>Working Examples\<close>

lemma
  assumes "finite A"
  shows "finite {x. x \<in> A \<and> P x}"
using assms by finite_search

lemma collect_pair_finite[finite]:
  assumes "finite {x. P x}" "finite {x. Q x}"
  shows "finite {(x, y) . P x \<and> Q y \<and> R x y}"
using assms by - finite

lemma collect_pair_finite'[finite]:
  assumes "finite {(x, y). P x y}"
  shows "finite {(x, y) . P x y \<and> R x y}"
using assms by - finite

text \<open>This is what we actually need in this theory\<close>
lemma collect_pair_finite''[finite]:
  assumes "finite {(x, y). P x \<and> Q y}"
  shows "finite {(x, y) . P x \<and> Q y \<and> R x y}"
using assms by - finite

lemma finite_imageI':
  assumes "finite {(x, y). P x y}"
  shows "finite {f x y | x y. P x y}"
using assms by finite

lemma
  assumes "finite (A \<times> B)"
  shows "finite {(x, y) | x y. x \<in> A \<and> y \<in> B \<and> R x y}"
using assms by - finite

lemma finite_imageI'':
  assumes "finite (A \<times> B)"
  shows "finite {f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y}"
using assms by - finite

text \<open>\<open>finite_Collect\<close> can also rewrite to \<open>vimage\<close>\<close>
lemma
  assumes "inj f" "finite S"
  shows "finite {y. \<exists> x \<in> S. x = f y}"
using assms by - finite

lemma
  assumes "inj f" "finite S"
  shows "finite {y. \<exists> x \<in> S. f y = x}"
using assms by - finite

text \<open>Another counter-example\<close>
lemma
  assumes "finite (A \<times> B)"
  shows "finite {f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y \<and> Q x y \<and> T x \<and> TT y}" (is "finite ?S")
proof -
  have "?S = (\<lambda> (x, y). f x y) ` {(x, y). x \<in> A \<and> y \<in> B \<and> R x y \<and> Q x y \<and> T x \<and> TT y}"
  by auto
  also have "finite \<dots>" using assms by - finite
  ultimately show ?thesis by simp
qed

text \<open>
  Easier proof. The problem for our method is that the simproc fails to turn ?S into the form used
  in the proof above.
  Note that the declaration of the \<open>finite\<close> attribute below is the only one that is \<^emph>\<open>necessary\<close> in
  this theory.
\<close>
lemma
  notes finite_imageI''[finite]
  assumes "finite (A \<times> B)"
  shows "finite {f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y \<and> Q x y \<and> T x \<and> TT y}" (is "finite ?S")
using assms by finite

lemma
  assumes "finite A" "finite B"
  shows "finite {(x, y) | x y. x \<in> A \<and> y \<in> B \<and> R y \<and> S x}"
using assms by - finite

lemma
  fixes P Q R :: "'a \<Rightarrow> bool"
  assumes "finite {x. P x \<and> R x}"
  shows "finite {x. P x \<and> Q x \<and> R x}"
using assms by - finite

lemma R:
  assumes "finite A" "A = B"
  shows "finite B"
using assms by finite

lemma pairwise_finiteI:
  assumes "finite {b. \<exists>a. P a b}" (is "finite ?B")
  assumes "finite {a. \<exists>b. P a b}"
  shows "finite {(a,b). P a b}" (is "finite ?C")
using assms by - finite

lemma pairwise_finiteI3:
  assumes "finite {b. \<exists>a c. P a b c}"
  assumes "finite {a. \<exists>b c. P a b c}"
  assumes "finite {c. \<exists>a b. P a b c}"
  shows "finite {(a,b,c). P a b c}" (is "finite ?C")
using assms by - finite

lemma pairwise_finiteI4:
  assumes "finite {b. \<exists>a c d. P a b c d}"
  assumes "finite {a. \<exists>b c d. P a b c d}"
  assumes "finite {c. \<exists>a b d. P a b c d}"
  assumes "finite {d. \<exists>a b c. P a b c d}"
  shows "finite {(a,b,c,d). P a b c d}" (is "finite ?C")
using assms by - finite

lemma finite_ex_and1:
  assumes "finite {b. \<exists>a. P a b}" (is "finite ?A")
  shows "finite {b. \<exists>a. P a b \<and> Q a b}" (is "finite ?B")
using assms by - finite

lemma finite_ex_and2:
  assumes "finite {b. \<exists>a. Q a b}" (is "finite ?A")
  shows "finite {b. \<exists>a. P a b \<and> Q a b}" (is "finite ?B")
using assms by - finite

text \<open>
  This is the only lemma where our methods cannot help us so far due to the fairly
  complex argument that is used in the interactive proof.
\<close>
lemma finite_set_of_finite_funs2:
  fixes A :: "'a set" 
    and B :: "'b set"
    and C :: "'c set"
    and d :: "'c" 
  assumes "finite A"
    and "finite B"
    and "finite C"
  shows "finite {f. \<forall>x. \<forall>y. (x \<in> A \<and> y \<in> B \<longrightarrow> f x y \<in> C) \<and> (x \<notin> A \<longrightarrow> f x y = d) \<and> (y \<notin> B \<longrightarrow> f x y = d)}"
        (is "finite ?S")
proof -
  let ?R = "{g. \<forall>x. (x \<in> B \<longrightarrow> g x \<in> C) \<and> (x \<notin> B \<longrightarrow> g x = d)}"
  let ?Q = "{f. \<forall>x. (x \<in> A \<longrightarrow> f x \<in> ?R) \<and> (x \<notin> A \<longrightarrow> f x = (\<lambda>y. d))}"
  from finite_set_of_finite_funs[OF assms(2,3)] have "finite ?R" .
  from finite_set_of_finite_funs[OF assms(1) this, of "\<lambda> y. d"] have "finite ?Q" .
  moreover have "?S = ?Q" by auto (case_tac "xa \<in> A", auto)
  ultimately show ?thesis by simp
qed

end
