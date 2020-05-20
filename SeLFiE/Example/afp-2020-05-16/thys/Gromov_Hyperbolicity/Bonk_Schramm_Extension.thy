(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>The Bonk Schramm extension\<close>

theory Bonk_Schramm_Extension
  imports Morse_Gromov_Theorem
begin

text \<open>We want to show that any metric space is isometrically embedded in a
metric space which is geodesic (i.e., there is an embedded geodesic between any
two points) and complete. There are many such constructions, but a very interesting one
has been given by Bonk and Schramm in~\cite{bonk_schramm}, together with an additional property of the
completion: if the space is delta-hyperbolic (in the sense of Gromov), then its
completion also is, with the same constant delta. It follows in particular that a $0$-hyperbolic
space embeds in a $0$-hyperbolic geodesic space, i.e., a metric tree (there is an easier
direct construction in this case).

Another embedding of a metric space in a geodesic one is constructed by Mineyev~\cite{mineyev},
it is more canonical in a sense (isometries of the original space extend
to the new space), but it is not clear if it preserves hyperbolicity.

The argument of Bonk and Schramm goes as follows:
- first, if one wants to add the middle of a pair of points $a$ and $b$ in a space $E$, there is a
nice formula for the distance on a new space $E \cup \{*\}$ (where $*$ will by construction be a middle
of $a$ and $b$).
- by transfinite induction on all the pair of points in the space, one adds
all the missing middles
- then one completes the space
- then one adds all the middles
- then one goes on like that, transfinitely many times
- at some point, the process stops for cardinality reasons

The resulting space is complete and has middles for all pairs of points. It is then
standard that it is geodesic (this is proved in \verb+Geodesic_Spaces.thy+).

Implementing this construction in Isabelle is interesting and nontrivial,
as transfinite induction is not that easy, especially when intermingled with metric completion
(i.e., taking the quotient space of all Cauchy sequences). In particular, taking sequences of
metric completions would mean changing types at each step, along a transfinite number of steps.
It does not seem possible to do it naively in this way.

We avoid taking quotients in the middle of the argument, as this is too messy.
Instead, we define a pseudo-distance (i.e., a function satisyfing the
triangular inequality, but such that $d(x,y)$ can vanish even if $x$ and $y$ are different)
on an increasing set, which should contain middles and limits of Cauchy sequences
(identified with their defining Cauchy sequence). Thus, we consider a datatype containing
points in the original space and closed under two operations: taking a pair of points in the datatype
(we think of the resulting pair as the middle of the pair) and taking a sequence with
values in the datatype (we think of the resulting sequence as the limit of the sequence if
it is Cauchy, for a distance yet to be defined, and as something we discard if the sequence
is not Cauchy).

Defining such an object is apparently not trivial. However, it is
well defined, for cardinality reasons, as this process will end
after the continuum cardinality iterations (as a sequence taking value in the continuum
cardinality is in fact contained in a strictly smaller ordinal, which means that all
sequences in the construction will appear at a step strictly before the continuum cardinality).
The datatype construction in Isabelle/HOL contains these cardinality considerations
as an automatic process, and is thus able to construct the datatype directly,
without the need for any additional proof!

Then, we define a wellorder on the datatype, such that every middle and every sequence appear
after each of its ancestors. This construction of a wellorder should work for any datatype,
but we provide a naive proof in our use case.

Then, we define, inductively on $z$, a pseudodistance on the pair of points in
$\{x : x \leq z\}$. In the induction, one should add one point at a time. If it is
a middle, one uses the Bonk-Schramm recipe. If it is a sequence, then either the sequence
is Cauchy and one uses the limit of the distances to the points in the sequence,
or it is not Cauchy and one discards the new point by setting $d(a,a) = 1$.
(This means that, in the Bonk-Schramm recipe, we only use the points with $d(x,x) = 0$,
and show the triangular inequality there).

In the end, we obtain a space with a pseudodistance. The desired space is obtained
by quotienting out the space $\{x : d(x,x) = 0\}$ by the equivalence relation
given by $d(x,y) = 0$. The triangular inequality for the pseudo-distance shows
that it descends to a genuine distance on the quotient. This is the desired
geodesic complete extension of the original space.
\<close>

subsection \<open>Unfolded Bonk Schramm extension\<close>

text \<open>The unfolded Bonk Schramm extension, as explained at the beginning of this file, is a type made
of the initial type, adding all possible middles and all possible limits of Cauchy sequences,
without any quotienting process\<close>

datatype 'a Bonk_Schramm_extension_unfolded =
  basepoint 'a
  | middle "'a Bonk_Schramm_extension_unfolded" "'a Bonk_Schramm_extension_unfolded"
  | would_be_Cauchy "nat \<Rightarrow> 'a Bonk_Schramm_extension_unfolded"

context metric_space
begin

text \<open>The construction of the distance will be done by transfinite induction,
with respect to a well-order for which the basepoints form an initial segment,
and for which middles of would-be Cauchy sequences are larger than the elements
they are made of. We will first prove the existence of such a well-order.

The idea is first to construct a function \verb+map_aux+ to another type, with a
well-order \verb+wo_aux+, such
that the image of \verb+middle a b+ is larger than the images of \verb+a+ and
\verb+b+ (take for instance the successor of the maximum of the two), and likewise
for a Cauchy sequence. A definition by induction works if the target cardinal is large
enough.

Then, pullback the well-order \verb+wo_aux+ by the map \verb+map_aux+: this gives a relation
that satisfies all the required properties, except that two different elements can be equal for
the order. Extending it essentially arbitrarily to distinguish between all elements (this is done
in Lemma \verb+Well_order_pullback+) gives the desired well-order\<close>

definition Bonk_Schramm_extension_unfolded_wo where
  "Bonk_Schramm_extension_unfolded_wo = (SOME (r::'a Bonk_Schramm_extension_unfolded rel).
      well_order_on UNIV r
      \<and> (\<forall>x \<in> range basepoint. \<forall>y \<in> - range basepoint. (x, y) \<in> r)
      \<and> (\<forall> a b. (a, middle a b) \<in> r)
      \<and> (\<forall> a b. (b, middle a b) \<in> r)
      \<and> (\<forall> u n. (u n, would_be_Cauchy u) \<in> r))"

text \<open>We prove the existence of the well order\<close>

definition wo_aux where
  "wo_aux = (SOME (r:: (nat + 'a Bonk_Schramm_extension_unfolded set) rel).
      Card_order r \<and> \<not>finite(Field r) \<and> regularCard r \<and> |UNIV::'a Bonk_Schramm_extension_unfolded set| <o r)"

lemma wo_aux_exists:
  "Card_order wo_aux \<and> \<not>finite (Field wo_aux) \<and> regularCard wo_aux \<and> |UNIV::'a Bonk_Schramm_extension_unfolded set| <o wo_aux"
proof -
  have *: "\<forall>r \<in> {|UNIV::'a Bonk_Schramm_extension_unfolded set|}. Card_order r" by auto
  have **: "\<exists>(r::(nat + 'a Bonk_Schramm_extension_unfolded set) rel).
    Card_order r \<and> \<not>finite(Field r) \<and> regularCard r \<and> ( |UNIV::'a Bonk_Schramm_extension_unfolded set| <o r)"
    by (metis card_of_card_order_on Field_card_of singletonI infinite_regularCard_exists[OF *])
  then show ?thesis unfolding wo_aux_def using someI_ex[OF **] by auto
qed

interpretation wo_aux: wo_rel wo_aux
  using wo_aux_exists Card_order_wo_rel by auto

primrec map_aux::"'a Bonk_Schramm_extension_unfolded \<Rightarrow> nat + 'a Bonk_Schramm_extension_unfolded set" where
  "map_aux (basepoint x) = wo_aux.zero"
  | "map_aux (middle a b) = wo_aux.suc ({map_aux a} \<union> {map_aux b})"
  | "map_aux (would_be_Cauchy u) = wo_aux.suc ((map_aux o u)`UNIV)"

lemma map_aux_AboveS_not_empty:
  assumes "map_aux`S \<subseteq> Field wo_aux"
  shows "wo_aux.AboveS (map_aux`S) \<noteq> {}"
apply (rule AboveS_not_empty_in_regularCard'[of S])
using wo_aux_exists assms apply auto
using card_of_UNIV ordLeq_ordLess_trans by blast

lemma map_aux_in_Field:
  "map_aux x \<in> Field wo_aux"
proof (induction)
  case (basepoint x)
  have "wo_aux.zero \<in> Field wo_aux"
    using Card_order_infinite_not_under wo_aux_exists under_empty wo_aux.zero_in_Field by fastforce
  then show ?case by auto
next
  case mid: (middle a b)
  have "({map_aux a} \<union> {map_aux b}) \<subseteq> Field wo_aux" using mid.IH by auto
  then have "wo_aux.AboveS ({map_aux a} \<union> {map_aux b}) \<noteq> {}"
    using map_aux_AboveS_not_empty[of "{a} \<union> {b}"] by auto
  then show ?case
    by (simp add: AboveS_Field wo_aux.suc_def)
next
  case cauchy: (would_be_Cauchy u)
  have "(map_aux o u)`UNIV \<subseteq> Field wo_aux" using cauchy.IH by auto
  then have "wo_aux.AboveS ((map_aux o u)`UNIV) \<noteq> {}"
    using map_aux_AboveS_not_empty[of "u`(UNIV)"] by (simp add: image_image)
  then show ?case
    by (simp add: AboveS_Field wo_aux.suc_def)
qed

lemma middle_rel_a:
  "(map_aux a, map_aux (middle a b)) \<in> wo_aux - Id"
proof -
  have *: "({map_aux a} \<union> {map_aux b}) \<subseteq> Field wo_aux" using map_aux_in_Field by auto
  then have "wo_aux.AboveS ({map_aux a} \<union> {map_aux b}) \<noteq> {}"
    using map_aux_AboveS_not_empty[of "{a} \<union> {b}"] by auto
  then show ?thesis
    using * by (simp add: wo_aux.suc_greater Id_def)
qed

lemma middle_rel_b:
  "(map_aux b, map_aux (middle a b)) \<in> wo_aux - Id"
proof -
  have *: "({map_aux a} \<union> {map_aux b}) \<subseteq> Field wo_aux" using map_aux_in_Field by auto
  then have "wo_aux.AboveS ({map_aux a} \<union> {map_aux b}) \<noteq> {}"
    using map_aux_AboveS_not_empty[of "{a} \<union> {b}"] by auto
  then show ?thesis
    using * by (simp add: wo_aux.suc_greater Id_def)
qed

lemma cauchy_rel:
  "(map_aux (u n), map_aux (would_be_Cauchy u)) \<in> wo_aux - Id"
proof -
  have *: "(map_aux o u)`UNIV \<subseteq> Field wo_aux" using map_aux_in_Field by auto
  then have "wo_aux.AboveS ((map_aux o u)`UNIV) \<noteq> {}"
    using map_aux_AboveS_not_empty[of "u`(UNIV)"] by (simp add: image_image)
  then show ?thesis
    using * by (simp add: wo_aux.suc_greater Id_def)
qed

text \<open>From the above properties of \verb+wo_aux+, it follows using \verb+Well_order_pullback+
that an order satisfying all the properties we want of \verb+Bonk_Schramm_extension_unfolded_wo+
exists. Hence, we get the following lemma.\<close>

lemma Bonk_Schramm_extension_unfolded_wo_props:
  "well_order_on UNIV Bonk_Schramm_extension_unfolded_wo"
  "\<forall>x \<in> range basepoint. \<forall>y \<in> - range basepoint. (x, y) \<in> Bonk_Schramm_extension_unfolded_wo"
  "\<forall> a b. (a, middle a b) \<in> Bonk_Schramm_extension_unfolded_wo"
  "\<forall> a b. (b, middle a b) \<in> Bonk_Schramm_extension_unfolded_wo"
  "\<forall>u n. (u n, would_be_Cauchy u) \<in> Bonk_Schramm_extension_unfolded_wo"
proof -
  obtain r::"'a Bonk_Schramm_extension_unfolded rel" where r:
    "Well_order r"
    "Field r = UNIV"
    "\<And>x y. (map_aux x, map_aux y) \<in> wo_aux - Id \<Longrightarrow> (x, y) \<in> r"
  using Well_order_pullback[of wo_aux map_aux] by (metis wo_aux.WELL)

  have "(x, y) \<in> r" if "x \<in> range basepoint" "y \<in> - range basepoint" for x y
    apply (rule r(3)) using that
    apply (cases y)
      apply (auto cong del: image_cong_simp)
       apply (metis insert_is_Un map_aux.simps(2) map_aux_in_Field wo_aux.zero_smallest)
      apply (metis Diff_iff insert_is_Un wo_aux.leq_zero_imp map_aux.simps(2) middle_rel_a pair_in_Id_conv)
     apply (metis map_aux.simps(3) map_aux_in_Field wo_aux.zero_smallest)
    apply (metis Diff_iff cauchy_rel wo_aux.leq_zero_imp map_aux.simps(3) pair_in_Id_conv)
    done
  moreover have "(a, middle a b) \<in> r" for a b
    apply (rule r(3)) using middle_rel_a by auto
  moreover have "(b, middle a b) \<in> r" for a b
    apply (rule r(3)) using middle_rel_b by auto
  moreover have "(u n, would_be_Cauchy u) \<in> r" for u n
    apply (rule r(3)) using cauchy_rel by auto
  moreover have "well_order_on UNIV r"
    using r(1) r(2) by auto
  ultimately have *: "\<exists> (r::'a Bonk_Schramm_extension_unfolded rel).
      well_order_on UNIV r
      \<and> (\<forall>x \<in> range basepoint. \<forall>y \<in> - range basepoint. (x, y) \<in> r)
      \<and> (\<forall> a b. (a, middle a b) \<in> r)
      \<and> (\<forall> a b. (b, middle a b) \<in> r)
      \<and> (\<forall>u n. (u n, would_be_Cauchy u) \<in> r)"
    by blast

  show
    "well_order_on UNIV Bonk_Schramm_extension_unfolded_wo"
    "\<forall>x \<in> range basepoint. \<forall>y \<in> - range basepoint. (x, y) \<in> Bonk_Schramm_extension_unfolded_wo"
    "\<forall> a b. (a, middle a b) \<in> Bonk_Schramm_extension_unfolded_wo"
    "\<forall> a b. (b, middle a b) \<in> Bonk_Schramm_extension_unfolded_wo"
    "\<forall>u n. (u n, would_be_Cauchy u) \<in> Bonk_Schramm_extension_unfolded_wo"
  unfolding Bonk_Schramm_extension_unfolded_wo_def using someI_ex[OF *] by auto
qed

interpretation wo: wo_rel Bonk_Schramm_extension_unfolded_wo
  using well_order_on_Well_order wo_rel_def wfrec_def Bonk_Schramm_extension_unfolded_wo_props(1) by blast

text \<open>We reformulate in the interpretation \verb+wo+ the main properties of
\verb+Bonk_Schramm_extension_unfolded_wo+ that we established in Lemma~\verb+Bonk_Schramm_extension_unfolded_wo_props+\<close>

lemma Bonk_Schramm_extension_unfolded_wo_props':
  "a \<in> wo.underS (middle a b)"
  "b \<in> wo.underS (middle a b)"
  "u n \<in> wo.underS (would_be_Cauchy u)"
proof -
  have "(a, middle a b) \<in> Bonk_Schramm_extension_unfolded_wo"
    using Bonk_Schramm_extension_unfolded_wo_props(3) by auto
  then show "a \<in> wo.underS (middle a b)"
    by (metis Diff_iff middle_rel_a pair_in_Id_conv underS_I)
  have "(b, middle a b) \<in> Bonk_Schramm_extension_unfolded_wo"
    using Bonk_Schramm_extension_unfolded_wo_props(4) by auto
  then show "b \<in> wo.underS (middle a b)"
    by (metis Diff_iff middle_rel_b pair_in_Id_conv underS_I)
  have "(u n, would_be_Cauchy u) \<in> Bonk_Schramm_extension_unfolded_wo"
    using Bonk_Schramm_extension_unfolded_wo_props(5) by auto
  then show "u n \<in> wo.underS (would_be_Cauchy u)"
    by (metis Diff_iff cauchy_rel pair_in_Id_conv underS_I)
qed

text \<open>We want to define by transfinite induction a distance on \verb+'a Bonk_Schramm_extension_unfolded+,
adding one point at a time (i.e., if the distance is defined on $E$, then one wants to define it
on $E \cup \{x\}$, if $x$ is a middle or a potential Cauchy sequence, by prescribing the distance
from $x$ to all the points in $E$.

Technically, we define a family of distances, indexed by $x$, on $\{y : y \leq x\}^2$. As all
functions should be defined everywhere, this will be a family of functions on $X \times X$, indexed
by points in $X$. They will have a compatibility condition, making it possible to define a global
distance by gluing them together.

Technically, transfinite induction is implemented in Isabelle/HOL by an updating rule: a function
that associates, to a family of distances indexed by $x$, a new family of distances indexed by $x$.
The result of the transfinite induction is obtained by starting from an arbitrary object, and then
applying the updating rule infinitely many times. The characteristic property of the result of this
transfinite induction is that it is a fixed point of the updating rule, as it should.

Below, this is implemented as follows:
\begin{itemize}
\item \verb+extend_distance+ is the updating rule.
\item Its fixed point \verb+extend_distance_fp+ is by definition \verb+wo.worec extend_distance+
(it only makes sense if the udpating rule satisfies a compatibility condition
\verb+wo.adm_wo extend_distance+ saying that the update of a family, at $x$,
only depends on the value of the family
strictly below $x$.
\item Finally, the global distance \verb+extended_distance+ is taken as the
value of the fixed point above, on $x y y'$ (i.e., using the distance indexed by $x$) for any $x
\geq \max(y, y')$. For definiteness, we use $\max(y, y')$, but it does not matter as everything is
compatible.
\end{itemize}\<close>

fun extend_distance::"('a Bonk_Schramm_extension_unfolded \<Rightarrow> ('a Bonk_Schramm_extension_unfolded \<Rightarrow> 'a Bonk_Schramm_extension_unfolded \<Rightarrow> real))
                    \<Rightarrow> ('a Bonk_Schramm_extension_unfolded \<Rightarrow> ('a Bonk_Schramm_extension_unfolded \<Rightarrow> 'a Bonk_Schramm_extension_unfolded \<Rightarrow> real))"
  where
    "extend_distance f (basepoint x) = (\<lambda>y z. if y \<in> range basepoint \<and> z \<in> range basepoint then
        dist (SOME y'. y = basepoint y') (SOME z'. z = basepoint z') else 1)"
  | "extend_distance f (middle a b) = (\<lambda>y z.
      if (y \<in> wo.underS (middle a b)) \<and> (z \<in> wo.underS (middle a b)) then f (wo.max2 y z) y z
      else if (y \<in> wo.underS (middle a b)) \<and> (z = middle a b) then (f (wo.max2 a b) a b)/2 + (SUP w\<in>{z \<in> wo.underS (middle a b). f z z z = 0}. f (wo.max2 y w) y w - max (f (wo.max2 a w) a w) (f (wo.max2 b w) b w))
      else if (y = middle a b) \<and> (z \<in> wo.underS (middle a b)) then (f (wo.max2 a b) a b)/2 + (SUP w\<in>{z \<in> wo.underS (middle a b). f z z z = 0}. f (wo.max2 z w) z w - max (f (wo.max2 a w) a w) (f (wo.max2 b w) b w))
      else if (y = middle a b) \<and> (z = middle a b) \<and> (f a a a = 0) \<and> (f b b b = 0) then 0
      else 1)"
  | "extend_distance f (would_be_Cauchy u) = (\<lambda>y z.
      if (y \<in> wo.underS (would_be_Cauchy u)) \<and> (z \<in> wo.underS (would_be_Cauchy u)) then f (wo.max2 y z) y z
      else if (\<not>(\<forall>eps > (0::real). \<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. f (wo.max2 (u n) (u m)) (u n) (u m) < eps)) then 1
      else if (y \<in> wo.underS (would_be_Cauchy u)) \<and> (z = would_be_Cauchy u) then lim (\<lambda>n. f (wo.max2 (u n) y) (u n) y)
      else if (y = would_be_Cauchy u) \<and> (z \<in> wo.underS (would_be_Cauchy u)) then lim (\<lambda>n. f (wo.max2 (u n) z) (u n) z)
      else if (y = would_be_Cauchy u) \<and> (z = would_be_Cauchy u) \<and> (\<forall>n. f (u n) (u n) (u n) = 0) then 0
      else 1)"

definition "extend_distance_fp = wo.worec extend_distance"

definition "extended_distance x y = extend_distance_fp (wo.max2 x y) x y"

definition "extended_distance_set = {z. extended_distance z z = 0}"

lemma wo_adm_extend_distance:
  "wo.adm_wo extend_distance"
unfolding wo.adm_wo_def proof (auto)
  fix f g::"'a Bonk_Schramm_extension_unfolded \<Rightarrow> 'a Bonk_Schramm_extension_unfolded \<Rightarrow> 'a Bonk_Schramm_extension_unfolded \<Rightarrow> real"
  fix x::"'a Bonk_Schramm_extension_unfolded"
  assume "\<forall>y\<in>wo.underS x. f y = g y"
  then have *: "f y = g y" if "y \<in> wo.underS x" for y using that by auto
  show "extend_distance f x = extend_distance g x"
    apply (cases x)
    (* We use the basic properties of our good order (middles and sequences come after their generators,
    and the fact that initial segments are stable under max2 *)
    apply (insert Bonk_Schramm_extension_unfolded_wo_props' *)
    apply auto
    (* Deal with the case of a middle, treating separately all the ifs *)
    apply (rule ext)+
    apply (rule if_cong, simp, simp)+ apply (rule SUP_cong, fastforce, blast)
    apply (rule if_cong, simp, simp)+ apply (rule SUP_cong, fastforce, blast)
    apply (rule if_cong, simp, simp)+ apply simp
    (* Deal with the case of a sequence, treating separately all the ifs *)
    apply (rule ext)+
    apply (rule if_cong, simp, simp)+
    apply simp
    done
qed

lemma extend_distance_fp:
  "extend_distance_fp = extend_distance (extend_distance_fp)"
using wo.worec_fixpoint[OF wo_adm_extend_distance] unfolding extend_distance_fp_def.

lemma extended_distance_symmetric:
  "extended_distance x y = extended_distance y x"
proof -
  have *: "extend_distance (extend_distance_fp) x x y = extend_distance (extend_distance_fp) x y x" if "y \<in> wo.underS x" for x y
    apply (cases x)
    apply (simp add: that dist_commute)+
    by blast
  have **: "extended_distance x y = extended_distance y x" if "y \<in> wo.underS x" for x y
    unfolding extended_distance_def using that *[OF that] extend_distance_fp by simp
  consider "y \<in> wo.underS x"|"x \<in> wo.underS y"|"x = y"
    by (metis UNIV_I Bonk_Schramm_extension_unfolded_wo_props(1) that(1) underS_I well_order_on_Well_order wo.TOTALS)
  then show ?thesis
    apply (cases) using ** by auto
qed

lemma extended_distance_basepoint:
  "extended_distance (basepoint x) (basepoint y) = dist x y"
proof -
  consider "wo.max2 (basepoint x) (basepoint y) = basepoint x" | "wo.max2 (basepoint x) (basepoint y) = basepoint y"
    by (meson wo.max2_def)
  then show ?thesis
    apply cases
    unfolding extended_distance_def by (subst extend_distance_fp, simp)+
qed

lemma extended_distance_set_basepoint:
  "basepoint x \<in> extended_distance_set"
unfolding extended_distance_set_def using extended_distance_basepoint by auto

lemma extended_distance_set_middle:
  assumes "a \<in> extended_distance_set" "b \<in> extended_distance_set"
  shows "middle a b \<in> extended_distance_set"
using assms unfolding extended_distance_set_def extended_distance_def apply auto
by (metis (no_types, lifting) extend_distance_fp extend_distance.simps(2) underS_E)

lemma extended_distance_set_middle':
  assumes "middle a b \<in> extended_distance_set"
  shows "a \<in> extended_distance_set \<inter> wo.underS (middle a b)"
        "b \<in> extended_distance_set \<inter> wo.underS (middle a b)"
proof -
  have "extend_distance (extend_distance_fp) (middle a b) (middle a b) (middle a b) = 0"
    apply (subst extend_distance_fp[symmetric])
    using assms unfolding extended_distance_set_def extended_distance_def by simp
  then have "a \<in> extended_distance_set" "b \<in> extended_distance_set"
    unfolding extended_distance_set_def extended_distance_def apply auto
    by (metis zero_neq_one)+
  moreover have "a \<in> wo.underS (middle a b)" "b \<in> wo.underS (middle a b)"
    by (auto simp add: Bonk_Schramm_extension_unfolded_wo_props')
  ultimately show "a \<in> extended_distance_set \<inter> wo.underS (middle a b)"
                  "b \<in> extended_distance_set \<inter> wo.underS (middle a b)"
    by auto
qed

lemma extended_distance_middle_formula:
  assumes "x \<in> wo.underS (middle a b)"
  shows "extended_distance x (middle a b) = (extended_distance a b)/2
    + (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance x w - max (extended_distance a w) (extended_distance b w))"
unfolding extended_distance_set_def extended_distance_def
apply (subst extend_distance_fp)
apply (simp add: assms)
apply (rule SUP_cong)
apply (auto simp add: wo.max2_def)
done

lemma extended_distance_set_Cauchy:
  assumes "(would_be_Cauchy u) \<in> extended_distance_set"
  shows "u n \<in> extended_distance_set \<inter> wo.underS (would_be_Cauchy u)"
        "\<forall>eps > (0::real). \<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. extended_distance (u n) (u m) < eps"
proof -
  have *: "extend_distance (extend_distance_fp) (would_be_Cauchy u) (would_be_Cauchy u) (would_be_Cauchy u) = 0"
    apply (subst extend_distance_fp[symmetric])
    using assms unfolding extended_distance_set_def extended_distance_def by simp
  then have "u n \<in> extended_distance_set"
    unfolding extended_distance_set_def extended_distance_def apply auto
    by (metis (no_types, hide_lams) underS_notIn zero_neq_one)
  moreover have "u n \<in> wo.underS (would_be_Cauchy u)"
    by (auto simp add: Bonk_Schramm_extension_unfolded_wo_props')
  ultimately show "u n \<in> extended_distance_set \<inter> wo.underS (would_be_Cauchy u)"
    by auto
  show "\<forall>eps > (0::real). \<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. extended_distance (u n) (u m) < eps"
    using * unfolding extended_distance_set_def extended_distance_def apply auto
    by (metis (no_types, hide_lams) zero_neq_one)
qed

lemma extended_distance_triang_ineq:
  assumes "x \<in> extended_distance_set"
          "y \<in> extended_distance_set"
          "z \<in> extended_distance_set"
  shows "extended_distance x z \<le> extended_distance x y + extended_distance y z"
proof -
  (* The proof of the triangular inequality is done by induction: one should show that adding
  a middle or a Cauchy sequence does not spoil the estimates. Technically, we show that the
  triangular inequality holds on all points under $t$, for all $t$, using a transfinite induction.
  The conclusion of the lemma then follows by using for $t$ the maximum of $x$, $y$, $z$.*)
  have ineq_rec: "\<forall>x y z. x \<in> wo.under t \<inter> extended_distance_set \<longrightarrow> y \<in> wo.under t \<inter> extended_distance_set \<longrightarrow> z \<in> wo.under t \<inter> extended_distance_set
      \<longrightarrow> extended_distance x z \<le> extended_distance x y + extended_distance y z" for t
  proof (rule wo.well_order_induct[of _ t])
    fix t
    assume IH_orig: "\<forall>t2. t2 \<noteq> t \<and> (t2, t) \<in> Bonk_Schramm_extension_unfolded_wo \<longrightarrow>
               (\<forall>x y z. x \<in> wo.under t2 \<inter> extended_distance_set \<longrightarrow>
                        y \<in> wo.under t2 \<inter> extended_distance_set \<longrightarrow>
                        z \<in> wo.under t2 \<inter> extended_distance_set \<longrightarrow>
                        extended_distance x z \<le> extended_distance x y + extended_distance y z)"
    (*Reformulate the induction assumption in more convenient terms*)
    then have IH: "extended_distance x z \<le> extended_distance x y + extended_distance y z"
      if "x \<in> wo.underS t \<inter> extended_distance_set"
         "y \<in> wo.underS t \<inter> extended_distance_set"
         "z \<in> wo.underS t \<inter> extended_distance_set"
      for x y z
    proof -
      define t2 where "t2 = wo.max2 (wo.max2 x y) z"
      have "t2 \<in> wo.underS t" using that t2_def by auto
      have "x \<in> wo.under t2" "y \<in> wo.under t2" "z \<in> wo.under t2" unfolding t2_def
        by (metis UNIV_I Bonk_Schramm_extension_unfolded_wo_props(1) mem_Collect_eq under_def well_order_on_Well_order wo.TOTALS wo.max2_iff)+
      then show ?thesis using that IH_orig \<open>t2 \<in> wo.underS t\<close> underS_E by fastforce
    qed

    have pos: "extended_distance x y \<ge> 0" if "x \<in> wo.underS t \<inter> extended_distance_set" "y \<in> wo.underS t \<inter> extended_distance_set" for x y
    proof -
      have "0 = extended_distance x x" using that(1) extended_distance_set_def by auto
      also have "... \<le> extended_distance x y + extended_distance y x"
        using IH that by auto
      also have "... = 2 * extended_distance x y"
        using extended_distance_symmetric by auto
      finally show ?thesis by auto
    qed

    (* The conclusion is easy if $t$ is not in \verb+extended_distance_set+, as there is no
    additional point to consider for the triangular inequality. The interesting case is when
    $t$ is admissible, then we will argue differently depending on its type.*)
    consider "t \<notin> extended_distance_set" | "t \<in> extended_distance_set" by auto
    then show "\<forall>x y z. x \<in> wo.under t \<inter> extended_distance_set \<longrightarrow>
                  y \<in> wo.under t \<inter> extended_distance_set \<longrightarrow>
                  z \<in> wo.under t \<inter> extended_distance_set \<longrightarrow>
          extended_distance x z \<le> extended_distance x y + extended_distance y z"
    proof (cases)
      case 1
      then have "wo.under t \<inter> extended_distance_set = wo.underS t \<inter> extended_distance_set"
        apply auto
        apply (metis mem_Collect_eq underS_I under_def)
        by (simp add: underS_E under_def)
      then show ?thesis using IH by auto
    next
      case 2
      (*We assume now that $t$ is admissible.
      We will prove now the triangular inequality for points under t, in the two basic cases
      where t is either the first point in the inequality, or the middle point.
      All other cases can be reduced to this one by permuting the variables, or they are
      trivial (if several variables are equal to t, for instance).*)
      have main_ineq: "extended_distance x z \<le> extended_distance x t + extended_distance t z
                    \<and> extended_distance x t \<le> extended_distance x z + extended_distance z t"
        if "x \<in> wo.underS t \<inter> extended_distance_set"
           "z \<in> wo.underS t \<inter> extended_distance_set"
        for x z
      proof (cases t)
        (*In the case of a basepoint, the distance comes from the original distance, hence
        it satisfies the triangular inequality*)
        case A: (basepoint t')
        then have "x \<in> range basepoint" using Bonk_Schramm_extension_unfolded_wo_props(2)
          by (metis that(1) Compl_iff Int_iff range_eqI wo.max2_def wo.max2_underS'(2))
        then obtain x' where x: "x = basepoint x'" by auto
        have "z \<in> range basepoint" using Bonk_Schramm_extension_unfolded_wo_props(2) A
          by (metis that(2) Compl_iff Int_iff range_eqI wo.max2_def wo.max2_underS'(2))
        then obtain z' where z: "z = basepoint z'" by auto
        show "extended_distance x z \<le> extended_distance x t + extended_distance t z
            \<and> extended_distance x t \<le> extended_distance x z + extended_distance z t"
          unfolding x z A extended_distance_basepoint by (simp add: dist_triangle)
      next
        (*In the case of a middle, the triangular inequality follows from the specific formula
        devised by Bonk and Schramm and (not very complicated) computations. The only mild difficulty
        is that the formula is defined in terms of a supremum, so one should check that this
        supremum is taken over a bounded set. This boundedness comes from the triangular inequality
        for point strictly below $t$, i.e., our inductive assumption.*)
        case M: (middle a b)
        then have ab: "a \<in> extended_distance_set \<inter> wo.underS (middle a b)"
                      "b \<in> extended_distance_set \<inter> wo.underS (middle a b)"
          using 2 extended_distance_set_middle'[of a b] by auto
        have dxt: "extended_distance x t = (extended_distance a b)/2
          + (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
              extended_distance x w - max (extended_distance a w) (extended_distance b w))"
          using that(1) unfolding M using extended_distance_middle_formula by auto
        have dzt: "extended_distance z t = (extended_distance a b)/2
            + (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
              extended_distance z w - max (extended_distance a w) (extended_distance b w))"
          using that(2) unfolding M using extended_distance_middle_formula by auto

        have bdd: "bdd_above ((\<lambda>w. extended_distance x w - max (extended_distance a w) (extended_distance b w))` (wo.underS (middle a b) \<inter> extended_distance_set))"
          if "x \<in> wo.underS t \<inter> extended_distance_set" for x
        proof (rule bdd_aboveI2)
          fix w assume w: "w \<in> wo.underS (middle a b) \<inter> extended_distance_set"
          have "extended_distance x w \<le> extended_distance x a + extended_distance a w"
            apply (rule IH) using ab w M that(1) by auto
          also have "... \<le> extended_distance x a + max (extended_distance a w) (extended_distance b w)"
            by auto
          finally show "extended_distance x w - max (extended_distance a w) (extended_distance b w)
                        \<le> extended_distance x a"
            by auto
        qed

        have "(\<lambda>w. extended_distance x z + extended_distance z w - max (extended_distance a w) (extended_distance b w)) ` (underS Bonk_Schramm_extension_unfolded_wo (middle a b) \<inter> extended_distance_set)
            = (\<lambda>s. s + extended_distance x z)` (\<lambda>w. extended_distance z w - max (extended_distance a w) (extended_distance b w)) ` (underS Bonk_Schramm_extension_unfolded_wo (middle a b) \<inter> extended_distance_set)"
          by auto
        moreover have "bdd_above ((\<lambda>s. s + extended_distance x z)` (\<lambda>w. extended_distance z w - max (extended_distance a w) (extended_distance b w)) ` (underS Bonk_Schramm_extension_unfolded_wo (middle a b) \<inter> extended_distance_set))"
          apply (rule bdd_above_image_mono) using bdd that by (auto simp add: mono_def)
        ultimately have bdd_3: "bdd_above ((\<lambda>w. extended_distance x z + extended_distance z w - max (extended_distance a w) (extended_distance b w)) ` (underS Bonk_Schramm_extension_unfolded_wo (middle a b) \<inter> extended_distance_set))"
          by simp

        have **: "max (extended_distance a a) (extended_distance b a) = extended_distance b a"
          apply (rule max_absorb2) using pos ab extended_distance_set_def M by auto
        then have "-extended_distance a b / 2 + extended_distance x a
              = (extended_distance a b)/2 + extended_distance x a - max (extended_distance a a) (extended_distance b a)"
          unfolding extended_distance_symmetric[of a b] by auto
        also have "... \<le> extended_distance x t"
          unfolding dxt apply (simp, rule cSUP_upper, simp) using bdd that M ab by auto
        finally have D1: "-extended_distance a b / 2 + extended_distance x a \<le> extended_distance x t"
          by simp

        have **: "max (extended_distance a b) (extended_distance b b) = extended_distance a b"
          apply (rule max_absorb1) using pos ab extended_distance_set_def M by auto
        then have "-extended_distance a b / 2 + extended_distance x b
              = (extended_distance a b)/2 + extended_distance x b - max (extended_distance a b) (extended_distance b b)"
          unfolding extended_distance_symmetric[of a b] by auto
        also have "... \<le> extended_distance x t"
          unfolding dxt apply (simp, rule cSUP_upper, simp) using bdd that ab by auto
        finally have "-extended_distance a b / 2 + extended_distance x b \<le> extended_distance x t"
          by simp
        then have D2: "-extended_distance a b / 2 + max (extended_distance x a) (extended_distance x b) \<le> extended_distance x t"
          using D1 by auto

        have "extended_distance x z = (-extended_distance a b / 2 + max (extended_distance x a) (extended_distance x b)) +
                      (extended_distance a b / 2 + extended_distance x z - max (extended_distance x a) (extended_distance x b))"
          by auto
        also have "... \<le> extended_distance x t +
                      (extended_distance a b / 2 + extended_distance z x - max (extended_distance a x) (extended_distance b x))"
          using D2 extended_distance_symmetric by auto
        also have "... \<le> extended_distance x t + extended_distance z t"
          unfolding dzt apply (simp, rule cSUP_upper) using bdd that M ab by auto
        finally have I: "extended_distance x z \<le> extended_distance x t + extended_distance z t"
          using extended_distance_symmetric by auto

        have T: "underS Bonk_Schramm_extension_unfolded_wo (middle a b) \<inter> extended_distance_set \<noteq> {}"
                "mono ((+) (extended_distance x z))"
                "bij ((+) (extended_distance x z))"
          using ab(1) apply blast
          by (simp add: monoI, rule bij_betw_byWitness[of _ "\<lambda>s. s - (extended_distance x z)"], auto)
        have "extended_distance x t \<le> (extended_distance a b)/2
          + (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
              extended_distance x z + extended_distance z w - max (extended_distance a w) (extended_distance b w))"
          unfolding dxt apply (simp, rule cSUP_subset_mono)
          using M that IH bdd_3 by (auto)
        also have "... = extended_distance x z + extended_distance z t"
          unfolding dzt apply simp
          using mono_cSup_bij[of "(\<lambda>w. extended_distance z w - max (extended_distance a w) (extended_distance b w))`(wo.underS (middle a b) \<inter> extended_distance_set)" "\<lambda>s. extended_distance x z + s", OF _ _ T(2) T(3)]
          by (auto simp add: bdd [OF that(2)] ab(1) T(1) add_diff_eq image_comp)
        finally have "extended_distance x t \<le> extended_distance x z + extended_distance z t" by simp
        then show "extended_distance x z \<le> extended_distance x t + extended_distance t z
                  \<and> extended_distance x t \<le> extended_distance x z + extended_distance z t"
          using I extended_distance_symmetric by auto
      next
        (*For Cauchy sequences, the distance to the Cauchy sequence is the limit of the distances
        to terms of the sequence, hence the triangular inequality follows from the triangular inequality
        for points strictly below $t$ by passing to the limit.*)
        case C: (would_be_Cauchy u)
        then have un: "u n \<in> extended_distance_set \<inter> wo.underS (would_be_Cauchy u)" for n
          using extended_distance_set_Cauchy 2 by auto
        have lim: "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> (extended_distance y (would_be_Cauchy u))"
            if y: "y \<in> extended_distance_set \<inter> wo.underS (would_be_Cauchy u)" for y
        proof -
          have "extend_distance extend_distance_fp (wo.max2 (would_be_Cauchy u) (would_be_Cauchy u)) (would_be_Cauchy u) (would_be_Cauchy u) = 0"
            using 2 unfolding C extended_distance_set_def extended_distance_def
            using extend_distance_fp by auto
          then have cauch: "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. extend_distance_fp (wo.max2 (u n) (u m)) (u n) (u m) < e" if "e > 0" for e
            apply auto using \<open>e > 0\<close> by (metis (no_types, hide_lams) zero_neq_one)
          have "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. abs(extended_distance y (u n) - extended_distance y (u m)) < e" if "e > 0" for e
          proof -
            obtain N where *: "extend_distance_fp (wo.max2 (u n) (u m)) (u n) (u m) < e" if "n \<ge> N" "m \<ge> N" for m n
              using cauch by (meson \<open>0 < e\<close>)
            {
              fix m n assume "m \<ge> N" "n \<ge> N"
              then have e: "extended_distance (u n) (u m) < e" using * unfolding extended_distance_def by auto
              have "extended_distance y (u n) \<le> extended_distance y (u m) + extended_distance (u m) (u n)"
                using IH y un C by blast
              then have 1: "extended_distance y (u n) - extended_distance y (u m) < e"
                using e extended_distance_symmetric by auto
              have "extended_distance y (u m) \<le> extended_distance y (u n) + extended_distance (u n) (u m)"
                using IH y un C by blast
              then have "extended_distance y (u m) - extended_distance y (u n) < e"
                using e extended_distance_symmetric by auto
              then have "abs(extended_distance y (u n) - extended_distance y (u m)) < e"
                using 1 by auto
            }
            then show ?thesis by auto
          qed
          then have "convergent (\<lambda>n. extended_distance y (u n))"
            by (simp add: Cauchy_iff real_Cauchy_convergent)
          then have lim: "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> lim (\<lambda>n. extended_distance y (u n))"
            using convergent_LIMSEQ_iff by auto
          have *: "wo.max2 y (would_be_Cauchy u) = would_be_Cauchy u" "y \<noteq> would_be_Cauchy u" using y by auto
          have "extended_distance y (would_be_Cauchy u) = lim (\<lambda>n. extended_distance (u n) y)"
            unfolding extended_distance_def apply (subst extend_distance_fp) unfolding *
            using *(2) y cauch by auto
          then show "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> extended_distance y (would_be_Cauchy u)"
            using lim extended_distance_symmetric by auto
        qed
        have "extended_distance x z \<le> extended_distance x (u n) + extended_distance (u n) z" for n
          using IH un that C by auto
        moreover have "(\<lambda>n. extended_distance x (u n) + extended_distance (u n) z) \<longlonglongrightarrow> extended_distance x t + extended_distance t z"
          apply (auto intro!: tendsto_add)
          using lim that extended_distance_symmetric unfolding C by auto
        ultimately have I: "extended_distance x z \<le> extended_distance x t + extended_distance t z"
          using LIMSEQ_le_const by blast

        have "extended_distance x (u n) \<le> extended_distance x z + extended_distance z (u n)" for n
          using IH un that C by auto
        moreover have "(\<lambda>n. extended_distance x (u n)) \<longlonglongrightarrow> extended_distance x t"
          using lim that extended_distance_symmetric unfolding C by auto
        moreover have "(\<lambda>n. extended_distance x z + extended_distance z (u n)) \<longlonglongrightarrow> extended_distance x z + extended_distance z t"
          apply (auto intro!: tendsto_add)
          using lim that extended_distance_symmetric unfolding C by auto
        ultimately have "extended_distance x t \<le> extended_distance x z + extended_distance z t"
          using LIMSEQ_le by blast
        then show "extended_distance x z \<le> extended_distance x t + extended_distance t z
                  \<and> extended_distance x t \<le> extended_distance x z + extended_distance z t"
          using I by auto
      qed

      (* Now, we deduce (from the above bounds in specific cases) the general triangular inequality,
      by considering separately if each point is equal to $t$ or strictly under it.*)
      {
        fix x y z assume H: "x \<in> wo.under t \<inter> extended_distance_set"
                            "y \<in> wo.under t \<inter> extended_distance_set"
                            "z \<in> wo.under t \<inter> extended_distance_set"
        have t: "extended_distance t t = 0" "extended_distance t t \<ge> 0" using 2 extended_distance_set_def by auto
        have *: "((x \<in> wo.underS t \<inter> extended_distance_set) \<or> (x = t))
            \<and> ((y \<in> wo.underS t \<inter> extended_distance_set) \<or> (y = t))
            \<and> ((z \<in> wo.underS t \<inter> extended_distance_set) \<or> (z = t))"
          using H by (simp add: underS_def under_def)
        have "extended_distance x z \<le> extended_distance x y + extended_distance y z"
          using * apply auto
          using t main_ineq extended_distance_symmetric IH pos apply blast
          using t main_ineq extended_distance_symmetric IH pos apply blast
          using t main_ineq extended_distance_symmetric IH pos apply blast
          using t main_ineq extended_distance_symmetric IH pos apply blast
          using t main_ineq extended_distance_symmetric IH pos apply (metis * Int_commute add.commute underS_notIn)
          using t main_ineq extended_distance_symmetric IH pos apply (metis (mono_tags, lifting) "*" extended_distance_set_def mem_Collect_eq underS_notIn)
          using t by auto
      }
      then show ?thesis by auto
    qed
  qed (*End of the inductive proof*)

  define t where "t = wo.max2 (wo.max2 x y) z"
  have "x \<in> wo.under t" "y \<in> wo.under t" "z \<in> wo.under t"
    unfolding t_def
    by (metis UNIV_I Bonk_Schramm_extension_unfolded_wo_props(1) mem_Collect_eq under_def well_order_on_Well_order wo.max2_equals1 wo.max2_iff wo.max2_xx)+
  then show ?thesis using assms ineq_rec by auto
qed

text \<open>We can now show the two main properties of the construction: the middle is indeed a middle
from the metric point of view (in \verb+extended_distance_middle+), and Cauchy sequences have
a limit (the corresponding \verb+would_be_Cauchy+ point).\<close>

lemma extended_distance_pos:
  assumes "a \<in> extended_distance_set"
          "b \<in> extended_distance_set"
  shows "extended_distance a b \<ge> 0"
using assms extended_distance_set_def extended_distance_triang_ineq[of a b a]
unfolding extended_distance_symmetric[of b a] by auto

lemma extended_distance_middle:
  assumes "a \<in> extended_distance_set"
          "b \<in> extended_distance_set"
  shows "extended_distance a (middle a b) = extended_distance a b / 2"
        "extended_distance b (middle a b) = extended_distance a b / 2"
proof -
  have "0 = extended_distance a b - max (extended_distance a b) (extended_distance b b)"
    using extended_distance_pos[OF assms] assms(2) extended_distance_set_def by auto
  also have "... \<le> (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance a w - max (extended_distance a w) (extended_distance b w))"
    apply (rule cSUP_upper)
    apply (simp add: assms(2) Bonk_Schramm_extension_unfolded_wo_props'(2))
    by (rule bdd_aboveI2[of _ _ 0], auto)
  ultimately have "0 \<le> (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance a w - max (extended_distance a w) (extended_distance b w))"
    by auto
  moreover have "(SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance a w - max (extended_distance a w) (extended_distance b w)) \<le> 0"
    apply (rule cSUP_least)
    using assms(1) Bonk_Schramm_extension_unfolded_wo_props'(1) by (fastforce, auto)
  moreover have "extended_distance a (middle a b) = (extended_distance a b)/2
    + (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance a w - max (extended_distance a w) (extended_distance b w))"
    by (rule extended_distance_middle_formula, simp add: Bonk_Schramm_extension_unfolded_wo_props'(1))
  ultimately show "extended_distance a (middle a b) = (extended_distance a b)/2"
    by auto

  have "0 = extended_distance b a - max (extended_distance a a) (extended_distance b a)"
    using extended_distance_pos[OF assms] assms(1) extended_distance_set_def extended_distance_symmetric by auto
  also have "... \<le> (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance b w - max (extended_distance a w) (extended_distance b w))"
    apply (rule cSUP_upper)
    apply (simp add: assms(1) Bonk_Schramm_extension_unfolded_wo_props'(1))
    by (rule bdd_aboveI2[of _ _ 0], auto)
  ultimately have "0 \<le> (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance b w - max (extended_distance a w) (extended_distance b w))"
    by auto
  moreover have "(SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance b w - max (extended_distance a w) (extended_distance b w)) \<le> 0"
    apply (rule cSUP_least)
    using assms(1) Bonk_Schramm_extension_unfolded_wo_props'(1) by (fastforce, auto)
  moreover have "extended_distance b (middle a b) = (extended_distance a b)/2
    + (SUP w\<in>wo.underS (middle a b) \<inter> extended_distance_set.
          extended_distance b w - max (extended_distance a w) (extended_distance b w))"
    by (rule extended_distance_middle_formula, simp add: Bonk_Schramm_extension_unfolded_wo_props'(2))
  ultimately show "extended_distance b (middle a b) = (extended_distance a b)/2"
    by auto
qed

lemma extended_distance_Cauchy:
  assumes "\<And>(n::nat). u n \<in> extended_distance_set"
      and "\<forall>eps > (0::real). \<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. extended_distance (u n) (u m) < eps"
  shows "would_be_Cauchy u \<in> extended_distance_set"
        "(\<lambda>n. extended_distance (u n) (would_be_Cauchy u)) \<longlonglongrightarrow> 0"
proof -
  show 2: "would_be_Cauchy u \<in> extended_distance_set"
    unfolding extended_distance_set_def extended_distance_def apply (simp, subst extend_distance_fp)
    using assms unfolding extended_distance_set_def extended_distance_def by simp

  have lim: "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> (extended_distance y (would_be_Cauchy u))"
      if y: "y \<in> extended_distance_set \<inter> wo.underS (would_be_Cauchy u)" for y
  proof -
    have "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. abs(extended_distance y (u n) - extended_distance y (u m)) < e" if "e > 0" for e
    proof -
      obtain N where *: "extended_distance (u n) (u m) < e" if "n \<ge> N" "m \<ge> N" for m n
        using assms(2) that \<open>e > 0\<close> by meson
      {
        fix m n assume "m \<ge> N" "n \<ge> N"
        then have e: "extended_distance (u n) (u m) < e" using * by auto
        have "extended_distance y (u n) \<le> extended_distance y (u m) + extended_distance (u m) (u n)"
          using extended_distance_triang_ineq y assms(1) by blast
        then have 1: "extended_distance y (u n) - extended_distance y (u m) < e"
          using e extended_distance_symmetric by auto
        have "extended_distance y (u m) \<le> extended_distance y (u n) + extended_distance (u n) (u m)"
          using extended_distance_triang_ineq y assms(1) by blast
        then have "extended_distance y (u m) - extended_distance y (u n) < e"
          using e extended_distance_symmetric by auto
        then have "abs(extended_distance y (u n) - extended_distance y (u m)) < e"
          using 1 by auto
      }
      then show ?thesis by auto
    qed
    then have "convergent (\<lambda>n. extended_distance y (u n))"
      by (simp add: Cauchy_iff real_Cauchy_convergent)
    then have lim: "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> lim (\<lambda>n. extended_distance y (u n))"
      using convergent_LIMSEQ_iff by auto
    have *: "wo.max2 y (would_be_Cauchy u) = would_be_Cauchy u" "y \<noteq> would_be_Cauchy u" using y by auto
    have "extended_distance y (would_be_Cauchy u) = lim (\<lambda>n. extended_distance (u n) y)"
      unfolding extended_distance_def apply (subst extend_distance_fp) unfolding *
      using *(2) y assms(2) extended_distance_def by auto
    then show "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> extended_distance y (would_be_Cauchy u)"
      using lim extended_distance_symmetric by auto
  qed

  have "\<exists>N. \<forall>n \<ge> N. abs(extended_distance (u n) (would_be_Cauchy u)) < e" if "e > 0" for e
  proof -
    obtain N where *: "extended_distance (u n) (u m) < e/2" if "n \<ge> N" "m \<ge> N" for m n
      using assms(2) that \<open>e > 0\<close> by (meson half_gt_zero)
    have "abs(extended_distance (u n) (would_be_Cauchy u)) \<le> e/2" if "n \<ge> N" for n
    proof -
      have "eventually (\<lambda>m. extended_distance (u n) (u m) \<le> e/2) sequentially"
        apply (rule eventually_sequentiallyI[of N]) using *[OF \<open>n \<ge> N\<close>] less_imp_le by auto
      moreover have "(\<lambda>m. extended_distance (u n) (u m)) \<longlonglongrightarrow> extended_distance (u n) (would_be_Cauchy u)"
        apply (rule lim) using "2" extended_distance_set_Cauchy by auto
      ultimately have "extended_distance (u n) (would_be_Cauchy u) \<le> e/2"
        by (meson "*" LIMSEQ_le_const2 less_imp_le that)
      then show ?thesis using extended_distance_pos[OF assms(1)[of n] 2] by auto
    qed
    then show ?thesis using \<open>e > 0\<close> by force
  qed
  then show "(\<lambda>n. extended_distance (u n) (would_be_Cauchy u)) \<longlonglongrightarrow> 0"
    using LIMSEQ_iff by force
qed

end (* of context \verb+metric_space+ *)


subsection \<open>The Bonk Schramm extension\<close>

quotient_type (overloaded) 'a Bonk_Schramm_extension =
  "('a::metric_space) Bonk_Schramm_extension_unfolded"
  / partial: "\<lambda>x y. (x \<in> extended_distance_set \<and> y \<in> extended_distance_set \<and> extended_distance x y = 0)"
unfolding part_equivp_def proof(auto intro!: ext simp: extended_distance_set_def)
  show "\<exists>x. extended_distance x x = 0"
    using extended_distance_set_basepoint extended_distance_set_def by auto
next
  fix x y z::"'a Bonk_Schramm_extension_unfolded"
  assume H: "extended_distance x x = 0" "extended_distance y y = 0" "extended_distance z z = 0"
            "extended_distance x y = 0" "extended_distance x z = 0"
  have "extended_distance y z \<le> extended_distance y x + extended_distance x z"
    apply (rule extended_distance_triang_ineq)
    using H unfolding extended_distance_set_def by auto
  also have "... \<le> 0"
    by (auto simp add: extended_distance_symmetric H)
  finally show "extended_distance y z = 0"
    using extended_distance_pos[of y z] H unfolding extended_distance_set_def by auto
next
  fix x y z::"'a Bonk_Schramm_extension_unfolded"
  assume H: "extended_distance x x = 0" "extended_distance y y = 0" "extended_distance z z = 0"
            "extended_distance x y = 0" "extended_distance y z = 0"
  have "extended_distance x z \<le> extended_distance x y + extended_distance y z"
    apply (rule extended_distance_triang_ineq)
    using H unfolding extended_distance_set_def by auto
  also have "... \<le> 0"
    by (auto simp add: extended_distance_symmetric H)
  finally show "extended_distance x z = 0"
    using extended_distance_pos[of x z] H unfolding extended_distance_set_def by auto
qed (metis)


instantiation Bonk_Schramm_extension :: (metric_space) metric_space
begin

lift_definition dist_Bonk_Schramm_extension::"('a::metric_space) Bonk_Schramm_extension \<Rightarrow> 'a Bonk_Schramm_extension \<Rightarrow> real"
  is "\<lambda>x y. extended_distance x y"
proof -
  fix x y z t::"'a Bonk_Schramm_extension_unfolded"
  assume H: "x \<in> extended_distance_set \<and> y \<in> extended_distance_set \<and> extended_distance x y = 0"
            "z \<in> extended_distance_set \<and> t \<in> extended_distance_set \<and> extended_distance z t = 0"
  have "extended_distance x z \<le> extended_distance x y + extended_distance y t + extended_distance t z"
    using extended_distance_triang_ineq[of x y z] extended_distance_triang_ineq[of y t z] H
    by auto
  also have "... = extended_distance y t"
    using H by (auto simp add: extended_distance_symmetric)
  finally have *: "extended_distance x z \<le> extended_distance y t" by simp
  have "extended_distance y t \<le> extended_distance y x + extended_distance x z + extended_distance z t"
    using extended_distance_triang_ineq[of y x t] extended_distance_triang_ineq[of x z t] H
    by auto
  also have "... = extended_distance x z"
    using H by (auto simp add: extended_distance_symmetric)
  finally show "extended_distance x z = extended_distance y t" using * by simp
qed

text \<open>To define a metric space in the current library of Isabelle/HOL, one should also introduce
a uniformity structure and a topology, as follows (they are prescribed by the distance):\<close>

definition uniformity_Bonk_Schramm_extension::"(('a Bonk_Schramm_extension) \<times> ('a Bonk_Schramm_extension)) filter"
  where "uniformity_Bonk_Schramm_extension = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_Bonk_Schramm_extension :: "'a Bonk_Schramm_extension set \<Rightarrow> bool"
  where "open_Bonk_Schramm_extension U = (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance proof
  fix x y::"'a Bonk_Schramm_extension"
  have C: "rep_Bonk_Schramm_extension x \<in> extended_distance_set"
          "rep_Bonk_Schramm_extension y \<in> extended_distance_set"
    using Quotient3_Bonk_Schramm_extension Quotient3_rep_reflp by fastforce+
  show "(dist x y = 0) = (x = y)"
    apply (subst Quotient3_rel_rep[OF Quotient3_Bonk_Schramm_extension, symmetric])
    unfolding dist_Bonk_Schramm_extension_def using C by auto
next
  fix x y z::"'a Bonk_Schramm_extension"
  have C: "rep_Bonk_Schramm_extension x \<in> extended_distance_set"
          "rep_Bonk_Schramm_extension y \<in> extended_distance_set"
          "rep_Bonk_Schramm_extension z \<in> extended_distance_set"
    using Quotient3_Bonk_Schramm_extension Quotient3_rep_reflp by fastforce+
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_Bonk_Schramm_extension_def apply auto
    by (metis C extended_distance_symmetric extended_distance_triang_ineq)
qed (auto simp add: uniformity_Bonk_Schramm_extension_def open_Bonk_Schramm_extension_def)
end

instance Bonk_Schramm_extension :: (metric_space) complete_space
proof
  fix X::"nat \<Rightarrow> 'a Bonk_Schramm_extension" assume "Cauchy X"
  have *: "\<And>n. rep_Bonk_Schramm_extension (X n) \<in> extended_distance_set"
    using Quotient3_Bonk_Schramm_extension Quotient3_rep_reflp by fastforce
  have **: "extended_distance (rep_Bonk_Schramm_extension (X n)) (rep_Bonk_Schramm_extension (X m)) = dist (X n) (X m)" for m n
    unfolding dist_Bonk_Schramm_extension_def by auto
  define y where "y = would_be_Cauchy (\<lambda>n. rep_Bonk_Schramm_extension (X n))"
  have "y \<in> extended_distance_set"
    unfolding y_def apply (rule extended_distance_Cauchy)
    using * \<open>Cauchy X\<close> unfolding Cauchy_def **[symmetric] by auto
  define x where "x = abs_Bonk_Schramm_extension y"
  have "dist (X n) x = extended_distance (rep_Bonk_Schramm_extension (X n)) y" for n
    unfolding x_def apply (subst Quotient3_abs_rep[OF Quotient3_Bonk_Schramm_extension, symmetric])
    apply (rule dist_Bonk_Schramm_extension.abs_eq) using * \<open>y \<in> extended_distance_set\<close>
    by (auto simp add: extended_distance_set_def)
  moreover have "(\<lambda>n. extended_distance (rep_Bonk_Schramm_extension (X n)) y) \<longlonglongrightarrow> 0"
    unfolding y_def apply (rule extended_distance_Cauchy)
    using * \<open>Cauchy X\<close> unfolding Cauchy_def **[symmetric] by auto
  ultimately have *: "(\<lambda>n. dist (X n) x) \<longlonglongrightarrow> 0" by simp
  have "X \<longlonglongrightarrow> x"
    apply (rule tendstoI) using * by (auto simp add: order_tendsto_iff)
  then show "convergent X" unfolding convergent_def by auto
qed

instance Bonk_Schramm_extension :: (metric_space) geodesic_space
proof (rule complete_with_middles_imp_geodesic)
  fix x y::"'a Bonk_Schramm_extension"
  have H: "rep_Bonk_Schramm_extension x \<in> extended_distance_set"
          "rep_Bonk_Schramm_extension y \<in> extended_distance_set"
    using Quotient3_Bonk_Schramm_extension Quotient3_rep_reflp by fastforce+
  define M where "M = middle (rep_Bonk_Schramm_extension x) (rep_Bonk_Schramm_extension y)"
  then have M: "M \<in> extended_distance_set"
    using extended_distance_set_middle[OF H] by simp
  define m where "m = abs_Bonk_Schramm_extension M"

  have "dist x m = extended_distance (rep_Bonk_Schramm_extension x) M"
    apply (subst Quotient3_abs_rep[OF Quotient3_Bonk_Schramm_extension, symmetric]) unfolding m_def
    apply (rule dist_Bonk_Schramm_extension.abs_eq)
    using H M extended_distance_set_def by auto
  also have "... = extended_distance (rep_Bonk_Schramm_extension x) (rep_Bonk_Schramm_extension y) / 2"
    unfolding M_def by (rule extended_distance_middle[OF H])
  also have "... = dist x y / 2"
    unfolding dist_Bonk_Schramm_extension_def by auto
  finally have *: "dist x m = dist x y / 2" by simp

  have "dist m y = extended_distance M (rep_Bonk_Schramm_extension y)"
    apply (subst Quotient3_abs_rep[OF Quotient3_Bonk_Schramm_extension, of y, symmetric]) unfolding m_def
    apply (rule dist_Bonk_Schramm_extension.abs_eq)
    using H M extended_distance_set_def by auto
  also have "... = extended_distance (rep_Bonk_Schramm_extension x) (rep_Bonk_Schramm_extension y) / 2"
    unfolding M_def using extended_distance_middle(2)[OF H] by (simp add: extended_distance_symmetric)
  also have "... = dist x y / 2"
    unfolding dist_Bonk_Schramm_extension_def by auto
  finally have "dist m y = dist x y / 2" by simp
  then show "\<exists>m. dist x m = dist x y / 2 \<and> dist m y = dist x y / 2"
    using * by auto
qed

definition to_Bonk_Schramm_extension::"'a::metric_space \<Rightarrow> 'a Bonk_Schramm_extension"
  where "to_Bonk_Schramm_extension x = abs_Bonk_Schramm_extension (basepoint x)"

lemma to_Bonk_Schramm_extension_isometry:
  "isometry_on UNIV to_Bonk_Schramm_extension"
proof (rule isometry_onI)
  fix x y::'a
  show "dist (to_Bonk_Schramm_extension x) (to_Bonk_Schramm_extension y) = dist x y"
    unfolding to_Bonk_Schramm_extension_def apply (subst dist_Bonk_Schramm_extension.abs_eq)
    unfolding extended_distance_set_def by (auto simp add: extended_distance_basepoint)
qed


section \<open>Bonk-Schramm extension of hyperbolic spaces\<close>

subsection \<open>The Bonk-Schramm extension preserves hyperbolicity\<close>

text \<open>A central feature of the Bonk-Schramm extension is that it preserves hyperbolicity, with the
same hyperbolicity constant $\delta$, as we prove now.\<close>

lemma (in Gromov_hyperbolic_space) Bonk_Schramm_extension_unfolded_hyperbolic:
  fixes x y z t::"('a::metric_space) Bonk_Schramm_extension_unfolded"
  assumes "x \<in> extended_distance_set"
          "y \<in> extended_distance_set"
          "z \<in> extended_distance_set"
          "t \<in> extended_distance_set"
  shows "extended_distance x y + extended_distance z t \<le> max (extended_distance x z + extended_distance y t) (extended_distance x t + extended_distance y z) + 2 * deltaG(TYPE('a))"
proof -
  interpret wo: wo_rel Bonk_Schramm_extension_unfolded_wo
  using well_order_on_Well_order wo_rel_def wfrec_def metric_space_class.Bonk_Schramm_extension_unfolded_wo_props(1) by blast

  (*To prove the hyperbolicity inequality, we prove it on larger and larger sets, by induction, adding
  one point $a$ at a time. Then the result will follow readily.*)
  have ineq_rec: "\<forall>x y z t. x \<in> wo.under a \<inter> extended_distance_set \<longrightarrow> y \<in> wo.under a \<inter> extended_distance_set \<longrightarrow> z \<in> wo.under a \<inter> extended_distance_set \<longrightarrow> t \<in> wo.under a \<inter> extended_distance_set
      \<longrightarrow> extended_distance x y + extended_distance z t \<le> max (extended_distance x z + extended_distance y t) (extended_distance x t + extended_distance y z) + 2 * deltaG(TYPE('a))"
    for a::"'a Bonk_Schramm_extension_unfolded"
  proof (rule wo.well_order_induct[of _ a])
    fix a::"'a Bonk_Schramm_extension_unfolded"
    assume IH_orig: "\<forall>b. b \<noteq> a \<and> (b, a) \<in> Bonk_Schramm_extension_unfolded_wo \<longrightarrow>
               (\<forall>x y z t. x \<in> wo.under b \<inter> extended_distance_set \<longrightarrow>
                          y \<in> wo.under b \<inter> extended_distance_set \<longrightarrow>
                          z \<in> wo.under b \<inter> extended_distance_set \<longrightarrow>
                          t \<in> wo.under b \<inter> extended_distance_set \<longrightarrow>
      extended_distance x y + extended_distance z t \<le> max (extended_distance x z + extended_distance y t) (extended_distance x t + extended_distance y z) + 2 * deltaG(TYPE('a)))"
    (*Reformulate the induction assumption in more convenient terms*)
    then have IH: "extended_distance x y + extended_distance z t \<le> max (extended_distance x z + extended_distance y t) (extended_distance x t + extended_distance y z) + 2 * deltaG(TYPE('a))"
      if "x \<in> wo.underS a \<inter> extended_distance_set"
         "y \<in> wo.underS a \<inter> extended_distance_set"
         "z \<in> wo.underS a \<inter> extended_distance_set"
         "t \<in> wo.underS a \<inter> extended_distance_set"
      for x y z t
    proof -
      define b where "b = wo.max2 (wo.max2 x y) (wo.max2 z t)"
      have "b \<in> wo.underS a" using that b_def by auto
      have "x \<in> wo.under b" "y \<in> wo.under b" "z \<in> wo.under b" "t \<in> wo.under b" unfolding b_def
        apply (auto simp add: under_def)
        by (metis UNIV_I metric_space_class.Bonk_Schramm_extension_unfolded_wo_props(1) mem_Collect_eq under_def well_order_on_Well_order wo.TOTALS wo.max2_iff)+
      then show ?thesis using that IH_orig \<open>b \<in> wo.underS a\<close> underS_E by fastforce
    qed

    consider "a \<notin> extended_distance_set" | "a \<in> extended_distance_set" by auto
    then show "\<forall>x y z t. x \<in> wo.under a \<inter> extended_distance_set \<longrightarrow>
                          y \<in> wo.under a \<inter> extended_distance_set \<longrightarrow>
                          z \<in> wo.under a \<inter> extended_distance_set \<longrightarrow>
                          t \<in> wo.under a \<inter> extended_distance_set \<longrightarrow>
      extended_distance x y + extended_distance z t \<le> max (extended_distance x z + extended_distance y t) (extended_distance x t + extended_distance y z) + 2 * deltaG(TYPE('a))"
    proof (cases)
      (* If the point $a$ is not admissible for the distance, then we are not adding any point,
      and the result follows readily from the assumption hypothesis.*)
      case 1
      then have "wo.under a \<inter> extended_distance_set = wo.underS a \<inter> extended_distance_set"
        apply auto
        apply (metis mem_Collect_eq underS_I under_def)
        by (simp add: underS_E under_def)
      then show ?thesis using IH by auto
    next
      (*Now, we assume that the point $a$ is admissible. We will first check the desired
      inequality when the first point is $a$, and the other points are strictly below $a$.
      The general inequality will follow from this one by a simple reduction below*)
      case 2
      then have a: "extended_distance a a = 0" unfolding metric_space_class.extended_distance_set_def by auto
      have main_ineq: "extended_distance a y + extended_distance z t \<le> max (extended_distance a z + extended_distance y t) (extended_distance a t + extended_distance y z) + 2 * deltaG(TYPE('a))"
        if yzt: "y \<in> wo.underS a \<inter> extended_distance_set"
                "z \<in> wo.underS a \<inter> extended_distance_set"
                "t \<in> wo.underS a \<inter> extended_distance_set"
        for y z t
      proof (cases a)
        (*In the case of a basepoint, the desired inequality follows from the corresponding
        inequality in the original --hyperbolic-- space.*)
        case A: (basepoint a')
        then have "y \<in> range basepoint" using metric_space_class.Bonk_Schramm_extension_unfolded_wo_props(2)
          by (metis yzt(1) Compl_iff Int_iff range_eqI wo.max2_def wo.max2_underS'(2))
        then obtain y' where y: "y = basepoint y'" by auto
        have "z \<in> range basepoint" using metric_space_class.Bonk_Schramm_extension_unfolded_wo_props(2) A
          by (metis yzt(2) Compl_iff Int_iff range_eqI wo.max2_def wo.max2_underS'(2))
        then obtain z' where z: "z = basepoint z'" by auto
        have "t \<in> range basepoint" using metric_space_class.Bonk_Schramm_extension_unfolded_wo_props(2) A
          by (metis yzt(3) Compl_iff Int_iff range_eqI wo.max2_def wo.max2_underS'(2))
        then obtain t' where t: "t = basepoint t'" by auto
        show ?thesis
          unfolding y z t A metric_space_class.extended_distance_basepoint
          using hyperb_quad_ineq UNIV_I unfolding Gromov_hyperbolic_subset_def by auto
      next
        (*In the case of a Cauchy sequence, the desired inequality is obtained from the inequality
        for the points defining the Cauchy sequence --which holds thanks to the induction
        assumption-- by passing to the limit.*)
        case C: (would_be_Cauchy u)
        then have u: "would_be_Cauchy u \<in> extended_distance_set"
                     "u n \<in> extended_distance_set \<inter> wo.underS (would_be_Cauchy u)" for n
          using metric_space_class.extended_distance_set_Cauchy 2 by auto
        have lim: "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> (extended_distance y (would_be_Cauchy u))"
          if y: "y \<in> extended_distance_set" for y
        proof -
          have a: "abs(extended_distance y (u n) - extended_distance y (would_be_Cauchy u)) \<le> extended_distance (u n) (would_be_Cauchy u)" for n
            using u(2)[of n] 2 y metric_space_class.extended_distance_triang_ineq unfolding C
            apply (subst abs_le_iff) apply (auto simp add: algebra_simps)
            by (metis metric_space_class.extended_distance_symmetric)
          have b: "(\<lambda>n. extended_distance (u n) (would_be_Cauchy u)) \<longlonglongrightarrow> 0"
            unfolding C apply (rule metric_space_class.extended_distance_Cauchy(2))
            using metric_space_class.extended_distance_set_Cauchy[of u] C 2 by auto
          have "(\<lambda>n. abs(extended_distance y (u n) - extended_distance y (would_be_Cauchy u))) \<longlonglongrightarrow> 0"
            apply (rule tendsto_sandwich[of "\<lambda>_. 0", OF _ _ _ b]) using a by auto
          then show "(\<lambda>n. extended_distance y (u n)) \<longlonglongrightarrow> extended_distance y (would_be_Cauchy u)"
            using Lim_null tendsto_rabs_zero_cancel by blast
        qed
        have "max (extended_distance (u n) z + extended_distance y t) (extended_distance (u n) t + extended_distance y z) + 2 * deltaG(TYPE('a)) - extended_distance (u n) y - extended_distance z t \<ge> 0" for n
          using IH[of "u n" y z t] u yzt C by auto
        moreover have "(\<lambda>n. max (extended_distance (u n) z + extended_distance y t) (extended_distance (u n) t + extended_distance y z) + 2 * deltaG(TYPE('a)) - extended_distance (u n) y - extended_distance z t)
              \<longlonglongrightarrow> max (extended_distance (would_be_Cauchy u) z + extended_distance y t) (extended_distance (would_be_Cauchy u) t + extended_distance y z) + 2 * deltaG(TYPE('a)) - extended_distance (would_be_Cauchy u) y - extended_distance z t"
          apply (auto intro!: tendsto_intros)
          using lim that u by (auto simp add: metric_space_class.extended_distance_symmetric)
        ultimately have I: "max (extended_distance (would_be_Cauchy u) z + extended_distance y t) (extended_distance (would_be_Cauchy u) t + extended_distance y z) + 2 * deltaG(TYPE('a)) - extended_distance (would_be_Cauchy u) y - extended_distance z t \<ge> 0"
          using LIMSEQ_le_const by blast
        then show ?thesis unfolding C by auto
      next
        (*In the case of a middle, the desired inequality follows from the formula defining
        the distance to the middle, and simple computations, as explained by Bonk and Schramm.*)
        case M: (middle c d)
        then have cd: "c \<in> extended_distance_set \<inter> wo.underS (middle c d)"
                      "d \<in> extended_distance_set \<inter> wo.underS (middle c d)"
          using 2 metric_space_class.extended_distance_set_middle'[of c d] by auto

        have bdd: "bdd_above ((\<lambda>w. extended_distance s w - max (extended_distance c w) (extended_distance d w))` (wo.underS (middle c d) \<inter> extended_distance_set))"
          if "s \<in> extended_distance_set" for s
        proof (rule bdd_aboveI2)
          fix w assume w: "w \<in> wo.underS (middle c d) \<inter> extended_distance_set"
          have "extended_distance s w \<le> extended_distance s c + extended_distance c w"
            using w that metric_space_class.extended_distance_triang_ineq cd by auto
          also have "... \<le> extended_distance s c + max (extended_distance c w) (extended_distance d w)"
            by auto
          finally show "extended_distance s w - max (extended_distance c w) (extended_distance d w)
                       \<le> extended_distance s c"
            by auto
        qed

        have I: "extended_distance y w - max (extended_distance c w) (extended_distance d w)
              \<le> max (extended_distance y z + extended_distance t (middle c d)) (extended_distance y t + extended_distance z (middle c d)) + 2 * deltaG(TYPE('a))
                - (extended_distance c d)/2 - extended_distance z t"
          if w: "w \<in> wo.underS (middle c d) \<inter> extended_distance_set" for w
        proof -
          have J: "(extended_distance c d)/2 + extended_distance s w - max (extended_distance c w) (extended_distance d w) \<le> extended_distance s (middle c d)"
              if "s \<in> wo.underS a \<inter> extended_distance_set" for s
          proof -
            have "(extended_distance c d)/2 + extended_distance s w - max (extended_distance c w) (extended_distance d w)
                \<le> (extended_distance c d)/2
                    + (SUP w\<in>wo.underS (middle c d) \<inter> extended_distance_set. extended_distance s w - max (extended_distance c w) (extended_distance d w))"
              apply auto apply (rule cSUP_upper) using w bdd that by auto
            also have "... = extended_distance s (middle c d)"
              apply (rule metric_space_class.extended_distance_middle_formula[symmetric]) using that M by auto
            finally show ?thesis by simp
          qed
          have "(extended_distance c d)/2 + extended_distance y w - max (extended_distance c w) (extended_distance d w) + extended_distance z t
            \<le> (extended_distance c d)/2 + max (extended_distance y z + extended_distance t w) (extended_distance y t + extended_distance z w) + 2 * deltaG(TYPE('a)) - max (extended_distance c w) (extended_distance d w)"
              using IH[of y w z t] w yzt M by (auto simp add: metric_space_class.extended_distance_symmetric)
          also have "... = max (extended_distance y z + (extended_distance c d)/2 + extended_distance t w - max (extended_distance c w) (extended_distance d w))
                               (extended_distance y t + (extended_distance c d)/2 + extended_distance z w - max (extended_distance c w) (extended_distance d w))
                            + 2 * deltaG(TYPE('a))"
            by auto
          also have "... \<le> max (extended_distance y z + extended_distance t (middle c d)) (extended_distance y t + extended_distance z (middle c d)) + 2 * deltaG(TYPE('a))"
            using J[OF yzt(3)] J[OF yzt(2)] by auto
          finally show ?thesis by simp
        qed
        have *: "(SUP w\<in>wo.underS (middle c d) \<inter> extended_distance_set. extended_distance y w - max (extended_distance c w) (extended_distance d w)) \<le>
                max (extended_distance y z + extended_distance t (middle c d)) (extended_distance y t + extended_distance z (middle c d)) + 2 * deltaG(TYPE('a))
                - (extended_distance c d)/2 - extended_distance z t"
          apply (rule cSUP_least) using yzt(1) M I by auto
        have "extended_distance y (middle c d) + extended_distance z t
          = (extended_distance c d)/2 + (SUP w\<in>wo.underS (middle c d) \<inter> extended_distance_set. extended_distance y w - max (extended_distance c w) (extended_distance d w)) + extended_distance z t"
          apply simp apply (rule metric_space_class.extended_distance_middle_formula) using yzt(1) M by auto
        also have "... \<le> max (extended_distance y z + extended_distance t (middle c d)) (extended_distance y t + extended_distance z (middle c d)) + 2 * deltaG(TYPE('a))"
          using * by simp
        finally show "extended_distance a y + extended_distance z t
                \<le> max (extended_distance a z + extended_distance y t) (extended_distance a t + extended_distance y z) + 2 * deltaG(TYPE('a))"
          unfolding M by (auto simp add: metric_space_class.extended_distance_symmetric)
      qed

      (*To prove the general inequality, we consider
      separately if each point is equal to $a$ or different from $a$. If no point is equal to $a$,
      then the inequality follows from the induction assumption. If exactly one point is equal to
      $a$, we can put in first position by permuting the variables, and use the main inequality
      above.
      Finally, if at least two points are equal to $a$, then the inequality follows from the
      triangular inequality.
      This reduction is straightforward, and should be automatable, but since there are 4 variables
      it is too complicated for metis, and we have to do it by hand below.*)
      show ?thesis
      proof (auto)
        fix x y z t assume H: "x \<in> wo.under a" "x \<in> extended_distance_set"
                              "y \<in> wo.under a" "y \<in> extended_distance_set"
                              "z \<in> wo.under a" "z \<in> extended_distance_set"
                              "t \<in> wo.under a" "t \<in> extended_distance_set"
        have *: "((x \<in> wo.underS a \<inter> extended_distance_set) \<or> (x = a))
                \<and> ((y \<in> wo.underS a \<inter> extended_distance_set) \<or> (y = a))
                \<and> ((z \<in> wo.underS a \<inter> extended_distance_set) \<or> (z = a))
                \<and> ((t \<in> wo.underS a \<inter> extended_distance_set) \<or> (t = a))"
          using H by (simp add: underS_def under_def)
        have d: "2 * deltaG(TYPE('a)) \<ge> 0" by auto
        show "extended_distance x y + extended_distance z t \<le> max (extended_distance x z + extended_distance y t) (extended_distance x t + extended_distance y z) + 2 * deltaG(TYPE('a))"
          using * apply (auto simp add: metric_space_class.extended_distance_symmetric a)
          using IH[of x y z t] apply (simp add: metric_space_class.extended_distance_symmetric)
          using main_ineq[of z x y] apply (simp add: metric_space_class.extended_distance_symmetric)
          using main_ineq[of t x y] apply (simp add: metric_space_class.extended_distance_symmetric)
          using 2 metric_space_class.extended_distance_triang_ineq[of x a y] H apply (simp add: metric_space_class.extended_distance_symmetric) using d apply linarith
          using main_ineq[of x z t] apply (simp add: metric_space_class.extended_distance_symmetric)
          using d apply linarith
          using d apply linarith
          using main_ineq[of y z t] apply (simp add: metric_space_class.extended_distance_symmetric)
          using d apply linarith
          using d apply linarith
          using 2 metric_space_class.extended_distance_triang_ineq[of t a z] H apply (simp add: metric_space_class.extended_distance_symmetric) using d apply linarith
          done
      qed
    qed
  qed
  define b where "b = wo.max2 (wo.max2 x y) (wo.max2 z t)"
  have "x \<in> wo.under b" "y \<in> wo.under b" "z \<in> wo.under b" "t \<in> wo.under b" unfolding b_def
    apply (auto simp add: under_def)
    by (metis UNIV_I metric_space_class.Bonk_Schramm_extension_unfolded_wo_props(1) mem_Collect_eq under_def well_order_on_Well_order wo.TOTALS wo.max2_iff)+
  then show ?thesis using ineq_rec[of b] assms by auto
qed

lemma (in Gromov_hyperbolic_space) Bonk_Schramm_extension_hyperbolic:
  "Gromov_hyperbolic_subset (deltaG(TYPE('a))) (UNIV::('a Bonk_Schramm_extension) set)"
apply (rule Gromov_hyperbolic_subsetI, simp, transfer fixing: deltaG)
using metric_space_class.extended_distance_set_def Bonk_Schramm_extension_unfolded_hyperbolic by auto

instantiation Bonk_Schramm_extension :: (Gromov_hyperbolic_space) Gromov_hyperbolic_space_geodesic
begin
definition deltaG_Bonk_Schramm_extension::"('a Bonk_Schramm_extension) itself \<Rightarrow> real" where
  "deltaG_Bonk_Schramm_extension _ = deltaG(TYPE('a))"

instance apply standard
unfolding deltaG_Bonk_Schramm_extension_def using Bonk_Schramm_extension_hyperbolic by auto
end (* of instantiation proof *)


text \<open>Finally, it follows that the Bonk Schramm extension of a $0$-hyperbolic space
(in which it embeds isometrically) is a metric tree or, equivalently, a geodesic $0$-hyperbolic
space (the equivalence is proved at the end of \verb+Geodesic_Spaces.thy+).\<close>

instance Bonk_Schramm_extension :: (Gromov_hyperbolic_space_0) Gromov_hyperbolic_space_0_geodesic
by (standard, simp add: deltaG_Bonk_Schramm_extension_def delta0)

text \<open>It then follows that it is also a metric tree, from what we have already proved.
We write explicitly for definiteness.\<close>

instance Bonk_Schramm_extension :: (Gromov_hyperbolic_space_0) metric_tree
  by standard


subsection \<open>Applications\<close>

text \<open>We deduce that we can extend results on Gromov-hyperbolic spaces without the geodesicity assumption,
even if it is used in the proofs. These results are given for illustrative purpose mainly, as one
works most often in geodesic spaces anyway.

The following results have already been proved in hyperbolic geodesic spaces. The same results
follow in a general hyperbolic space, as everything is invariant under isometries and can thus
be pulled from the corresponding result in the Bonk Schramm extension. The straightforward proofs
only express this invariance under isometries of all the properties under consideration.\<close>

proposition (in Gromov_hyperbolic_space) lipschitz_path_close_to_geodesic':
  fixes c::"real \<Rightarrow> 'a"
  assumes "lipschitz_on M {A..B} c"
          "geodesic_segment_between G (c A) (c B)"
          "x \<in> G"
  shows "infdist x (c`{A..B}) \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (B-A)) + M"
proof -
  interpret BS: Gromov_hyperbolic_space_geodesic "dist::('a Bonk_Schramm_extension \<Rightarrow> 'a Bonk_Schramm_extension \<Rightarrow> real)" "uniformity" "open" "(\<lambda>_. deltaG(TYPE('a)))"
    apply standard using Bonk_Schramm_extension_hyperbolic by auto

  have "infdist x (c`{A..B}) = infdist (to_Bonk_Schramm_extension x) ((to_Bonk_Schramm_extension o c)`{A..B})"
    unfolding image_comp[symmetric] apply (rule isometry_preserves_infdist[symmetric, of UNIV])
    using to_Bonk_Schramm_extension_isometry by auto
  also have "... \<le> (4/ln 2) * deltaG(TYPE(('a))) * max 0 (ln (B-A)) + (1*M)"
    apply (rule BS.lipschitz_path_close_to_geodesic[of _ _ _ _ "to_Bonk_Schramm_extension`G"])
    apply (rule lipschitz_on_compose)
    using assms apply simp
    apply (meson UNIV_I isometry_on_lipschitz lipschitz_on_def to_Bonk_Schramm_extension_isometry)
    unfolding comp_def apply (rule isometry_preserves_geodesic_segment_between[of UNIV])
    using assms to_Bonk_Schramm_extension_isometry by auto
  finally show ?thesis by auto
qed

theorem (in Gromov_hyperbolic_space) Morse_Gromov_theorem':
  fixes f::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {a..b} f"
          "geodesic_segment_between G (f a) (f b)"
  shows "hausdorff_distance (f`{a..b}) G \<le> 92 * lambda\<^sup>2 * (C + deltaG(TYPE('a)))"
proof -
  interpret BS: Gromov_hyperbolic_space_geodesic "dist::('a Bonk_Schramm_extension \<Rightarrow> 'a Bonk_Schramm_extension \<Rightarrow> real)" "uniformity" "open" "(\<lambda>_. deltaG(TYPE('a)))"
    apply standard using Bonk_Schramm_extension_hyperbolic by auto
  have "hausdorff_distance (f`{a..b}) (G) = hausdorff_distance ((to_Bonk_Schramm_extension o f)`{a..b}) ((to_Bonk_Schramm_extension)`G)"
    unfolding image_comp[symmetric] apply (rule isometry_preserves_hausdorff_distance[symmetric, of UNIV])
    using to_Bonk_Schramm_extension_isometry by auto
  also have "... \<le> 92 * (lambda*1)^2 * ((C*1+0) + deltaG(TYPE('a)))"
    apply (intro BS.Morse_Gromov_theorem quasi_isometry_on_compose[where Y = UNIV])
    using assms isometry_quasi_isometry_on to_Bonk_Schramm_extension_isometry apply auto
    using isometry_preserves_geodesic_segment_between by blast
  finally show ?thesis by simp
qed

theorem (in Gromov_hyperbolic_space) Morse_Gromov_theorem2':
  fixes c d::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {A..B} c"
          "lambda C-quasi_isometry_on {A..B} d"
          "c A = d A" "c B = d B"
  shows "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 184 * lambda^2 * (C + deltaG(TYPE('a)))"
proof -
  interpret BS: Gromov_hyperbolic_space_geodesic "dist::('a Bonk_Schramm_extension \<Rightarrow> 'a Bonk_Schramm_extension \<Rightarrow> real)" "uniformity" "open" "(\<lambda>_. deltaG(TYPE('a)))"
    apply standard using Bonk_Schramm_extension_hyperbolic by auto
  have "hausdorff_distance (c`{A..B}) (d`{A..B}) = hausdorff_distance ((to_Bonk_Schramm_extension o c)`{A..B}) ((to_Bonk_Schramm_extension o d)`{A..B})"
    unfolding image_comp[symmetric] apply (rule isometry_preserves_hausdorff_distance[symmetric, of UNIV])
    using to_Bonk_Schramm_extension_isometry by auto
  also have "... \<le> 184 * (lambda*1)^2 * ((C*1+0) + deltaG(TYPE('a)))"
    apply (intro BS.Morse_Gromov_theorem2 quasi_isometry_on_compose[where Y = UNIV])
    using assms isometry_quasi_isometry_on to_Bonk_Schramm_extension_isometry by auto
  finally show ?thesis by simp
qed

lemma Gromov_hyperbolic_invariant_under_quasi_isometry_explicit':
  fixes f::"'a::geodesic_space \<Rightarrow> 'b::Gromov_hyperbolic_space"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_hyperbolic_subset (752 * lambda^3 * (C + deltaG(TYPE('b)))) (UNIV::('a set))"
proof -
  interpret BS: Gromov_hyperbolic_space_geodesic "dist::('b Bonk_Schramm_extension \<Rightarrow> 'b Bonk_Schramm_extension \<Rightarrow> real)" "uniformity" "open" "(\<lambda>_. deltaG(TYPE('b)))"
    apply standard using Bonk_Schramm_extension_hyperbolic by auto
  have A: "(lambda * 1) (C * 1 + 0)-quasi_isometry_on UNIV (to_Bonk_Schramm_extension o f)"
    by (rule quasi_isometry_on_compose[OF assms, of _ _ UNIV])
       (auto simp add: isometry_quasi_isometry_on[OF to_Bonk_Schramm_extension_isometry])
  have *: "deltaG(TYPE('b)) = deltaG(TYPE('b Bonk_Schramm_extension))"
    by (simp add: deltaG_Bonk_Schramm_extension_def)
  show ?thesis
    unfolding *
    apply (rule Gromov_hyperbolic_invariant_under_quasi_isometry_explicit[of _ _ "to_Bonk_Schramm_extension o f"])
    using A by auto
qed

theorem Gromov_hyperbolic_invariant_under_quasi_isometry':
  assumes "quasi_isometric (UNIV::('a::geodesic_space) set) (UNIV::('b::Gromov_hyperbolic_space) set)"
  shows "\<exists>delta. Gromov_hyperbolic_subset delta (UNIV::'a set)"
proof -
  obtain C lambda f where f: "lambda C-quasi_isometry_between (UNIV::'a set) (UNIV::'b set) f"
    using assms unfolding quasi_isometric_def by auto
  show ?thesis using Gromov_hyperbolic_invariant_under_quasi_isometry_explicit'[OF quasi_isometry_betweenD(1)[OF f]] by blast
qed

end (*of theory Bonk_Schramm_Extension*)
