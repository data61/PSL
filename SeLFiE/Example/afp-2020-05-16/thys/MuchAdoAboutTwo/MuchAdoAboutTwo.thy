(*  Title:       Much Ado about Two
    Author:      Sascha Böhme <boehmes@informatik.tu-muenchen.de>, 2007
    Maintainer:  Sascha Böhme <boehmes@informatik.tu-muenchen.de>
*)


section \<open>Much Ado about Two\<close>

(*<*)
theory MuchAdoAboutTwo
imports "HOL-Library.Permutation"
begin
(*>*)


text \<open>

Due to Donald E. Knuth, it is known for some time that certain sorting
functions for lists of arbitrary types can be proved correct by only showing
that they are correct for boolean lists (\cite{KnuthSortingAndSearching},
see also \cite{LogicalAbstractionsInHaskell}).
This reduction idea, i.e. reducing a proof for an arbitrary type to a proof for a fixed type with a fixed number of values, has also instances in other
fields.
Recently, in \cite{MuchAdoAboutTwo}, a similar result as Knuth's 0-1-principle
is explained for the problem of parallel prefix computation 
\cite{PrefixSumsAndTheirApplications}.
That is the task to compute, for given $x_1, \ldots, x_n$ and an associative
operation $\oplus$, the values $x_1$, $x_1 \oplus x_2$, $\ldots$,
 $x_1 \oplus x_2 \oplus \cdots \oplus x_n$.
There are several solutions which optimise this computation, and an
obvious question is to ask whether these solutions are correct.
One way to answer this question is given in \cite{MuchAdoAboutTwo}.
There, a ``0-1-2-principle'' is proved which relates an unspecified solution
of the parallel prefix computation, expressed as a function \<open>candidate\<close>,
with \<open>scanl1\<close>, a functional representation of the parallel prefix
computation. The essence proved in the mentioned paper is as follows:
If \<open>candidate\<close> and \<open>scanl1\<close> behave identical on all lists over
a type which has three elements, then \<open>candidate\<close> is semantically
equivalent to \<open>scanl1\<close>, that is, \<open>candidate\<close> is a correct solution
of the parallel prefix computation.

Although it seems that nearly nothing is known about the function
\<open>candidate\<close>, it turns out that the type of \<open>candidate\<close> already
suffices for the proof of the paper's result. The key is relational
parametricity \cite{TypesAbstractionsAndParametricPolymorphism} in the form of
a free theorem \cite{TheoremsForFree}. This, some rewriting and a few 
properties about list-processing functions thrown in allow to proof the
``0-1-2-principle''.

The paper first shows some simple properties and derives a specialisation of
the free theorem. The proof of the main theorem itself is split up in two 
parts. The first, and considerably more complicated part relates lists over a
type with three values to lists of integer lists. Here, the paper uses
several figures to demonstrate and shorten several proofs. The second part then
relates lists of integer list with lists over arbitrary types, and consists of
applying the free theorem and some rewriting. The combination of these two
parts then yields the theorem.



Th article at hand formalises the proofs given in \cite{MuchAdoAboutTwo},
which is called here ``the original paper''. Compared to that paper, there are 
several differences in this article. The major differences are listed below.
A more detailed collection follows thereafter.

\begin{itemize}
\item The original paper requires lists to be non-empty. Eventhough lists in
Isabelle may also be empty, we stick to Isabelle's list datatype instead of
declaring a new datatype, due to the huge, already existing theory about
lists in Isabelle. As a consequence, however, several modifications become
necessary.

\item The figure-based proofs of the original paper are replaced by formal
proofs. This forms a major part of this article (see Section 6).

\item Instead of integers, we restrict ourselves to natural numbers. Thus,
several conditions can be simplified since every natural number is greater
than or equal to \<open>0\<close>. This decision has no further influence on the 
proofs because they never consider negative integers.

\item Mainly due to differences between Haskell and Isabelle, certain notations
are different here compared to the original paper. List concatenation is
denoted by \<open>@\<close> instead of $++$, and in writing down intervals, we use
\<open>[0..<k + 1]\<close> instead of \<open>[0..k]\<close>. Moreover, we write \<open>f\<close>
instead of $\oplus$ and \<open>g\<close> instead of $\otimes$. Functions mapping
an element of the three-valued type to an arbitrary type are denoted by
\<open>h\<close>.

\end{itemize}

Whenever we use lemmas from already existing Isabelle theories, we qualify
them by their theory name. For example, instead of \<open>map_map\<close>, we
write \<open>List.map_map\<close> to point out that this lemma is taken from
Isabelle's list theory.



The following comparison shows all differences of this article compared to the
original paper. The items below follow the structure of the original paper
(and also this article's structure). They also highlight the challenges which
needed to be solved in formalising the original paper.

\begin{itemize}
\item Introductions of several list functions (e.g. \<open>length\<close>,
\<open>map\<close>, \<open>take\<close>) are dropped. They exist already in Isabelle's list
theory and are be considered familiar to the reader.

\item The free theorem given in Lemma 1 of the original paper is not sufficient
for later proofs, because the assumption is not appropriate in the context
of Isabelle's lists, which may also be empty. Thus, here, Lemma 1 is a
derived version of the free theorem given as Lemma 1 in the original paper,
and some additional proof-work is done.

\item Before proceeding in the original paper's way, we state and proof
additional lemmas, which are not part of Isabelle's libraries. These lemmas
are not specific to this article and may also be used in other theories.

\item Laws 1 to 8 and Lemma 2 of the original paper are explicitly proved.
Most of the proofs follow directly from existing results of Isabelle's list
theory. To proof Law 7, Law 8 and Lemma 2, more work was necessary, especially
for Law 8.

\item Lemma 3 and its proof are nearly the same here as in the original paper.
Only the additional assumptions of Lemma 1, due to Isabelle's list datatype,
have to be shown.

\item Lemma 4 is split up in several smaller lemmas, and the order of them
tries to follow the structure of the original paper's Lemma 4.

For every figure of the original paper, there is now one separate proof.
These proofs constitute the major difference in the structure of this article
compared to the original paper. 

The proof of Lemma 4 in the original paper concludes by combining the results
of the figure-based proofs to a non-trivial permutation property. These three
sentences given in the original paper are split up in five separate lemmas
and according proofs, and therefore, they as well form a major difference to
the original paper.

\item Lemma 5 is mostly identical to the version in the original paper. It has
one additional assumption required by Lemma 4. Moreover, the proof is slightly
more structured, and some steps needed a bit more argumentation than in the
original paper.

\item In principle, Proposition 1 is identical to the according proposition in
the original paper. However, to fulfill the additional requirement of Lemma 5,
an additional lemma was proved. This, however, is only necessary, because we
use Isabelle's list type which allows lists to be empty.

\item Proposition 2 contains one non-trivial step, which is proved as a
seperate lemma. Note that this is not due to any decisions of using special
datatypes, but inherent in the proof itself.  Apart from that, the proof is
identical to the original paper's proof of Proposition 2.

\item The final theorem is, as in the original paper, just a combination of
Proposition 1 and Proposition 2. Only the assumptions are extended due to
Isabelle's list datatype.

\end{itemize}


\<close>





section \<open>Basic definitions\<close>



fun foldl1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a"
where
  "foldl1 f (x # xs) = foldl f x xs"

fun scanl1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "scanl1 f xs = map (\<lambda>k. foldl1 f (take k xs))
                     [1..<length xs + 1]"


text \<open>
The original paper further relies on associative functions. Thus, we define
another predicate to be able to express this condition:
\<close>

definition
  "associative f \<equiv> (\<forall>x y z. f x (f y z) = f (f x y) z)"


text \<open>
The following constant symbols represents our unspecified function. We want to
show that this function is semantically equivalent to \<open>scanl1\<close>, provided
that the first argument is an associative function.
\<close>

consts 
  candidate :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list"


text \<open>
With the final theorem, it suffices to show that \<open>candidate\<close> behaves like
\<open>scanl1\<close> on all lists of the following type, to conclude that 
\<open>canditate\<close> is semantically equivalent to \<open>scanl1\<close>.
\<close>

datatype three = Zero | One | Two



text \<open>
Although most of the functions mentioned in the original paper already exist
in Isabelle's list theory, we still need to define two more functions:
\<close>

fun wrap :: "'a \<Rightarrow> 'a list"
where
  "wrap x = [x]"

fun ups :: "nat \<Rightarrow> nat list list"
where
  "ups n = map (\<lambda>k. [0..<k + 1]) [0..<n + 1]"





section \<open>A Free Theorem\<close>

text \<open>
The key to proof the final theorem is the following free theorem \cite{TypesAbstractionsAndParametricPolymorphism,TheoremsForFree} of \<open>candidate\<close>. 
Since there is no proof possible without specifying the underlying
(functional) language (which would be beyond the scope of this work),
this lemma is expected to hold. As a consequence, all following lemmas and also
the final theorem only hold under this provision.
\<close>

axiomatization where
  candidate_free_theorem:
    "\<And>x y. h (f x y) = g (h x) (h y) \<Longrightarrow> map h (candidate f zs) = candidate g (map h zs)"



text \<open>
In what follows in this section, the previous lemma is specialised to a lemma 
for non-empty lists. More precisely, we want to restrict the above assumption
to be applicable for non-empty lists. This is already possible without
modifications when having a list datatype which does not allow for empty lists.
However, before being able to also use Isabelle's list datatype, further
conditions on \<open>f\<close> and \<open>zs\<close> are necessary.

To prove the derived lemma, we first introduce a datatype for non-empty lists,
and we furthermore define conversion functions to map the new datatype on
Isabelle lists and back.
\<close>

datatype 'a nel 
  = NE_One 'a 
  | NE_Cons 'a "'a nel"

fun n2l :: "'a nel \<Rightarrow> 'a list"
where
  "n2l (NE_One x)     = [x]"
| "n2l (NE_Cons x xs) = x # n2l xs"

fun l2n :: "'a list \<Rightarrow> 'a nel"
where
  "l2n [x]      = NE_One x"
| "l2n (x # xs) = (case xs of []      \<Rightarrow> NE_One x
                            | (_ # _) \<Rightarrow> NE_Cons x (l2n xs))"


text \<open>
The following results relate Isabelle lists and non-empty lists:
\<close>

lemma non_empty_n2l: "n2l xs \<noteq> []"
by (cases xs, auto)


lemma n2l_l2n_id: "x \<noteq> [] \<Longrightarrow> n2l (l2n x) = x"
proof (induct x)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case by (cases xs, auto)
qed


lemma n2l_l2n_map_id:
  assumes "\<And>x. x \<in> set zs \<Longrightarrow> x \<noteq> []"
  shows "map (n2l \<circ> l2n) zs = zs"
using assms 
proof (induct zs)
  case Nil thus ?case by simp
next
  case (Cons z zs)
  hence "\<And>x. x \<in> set zs \<Longrightarrow> x \<noteq> []" using List.set_subset_Cons by auto
  with Cons have IH: "map (n2l \<circ> l2n) zs = zs" by blast

  have 
  "map (n2l \<circ> l2n) (z # zs)
   = (n2l \<circ> l2n) z # map (n2l \<circ> l2n) zs" by simp
  also have 
  "\<dots> = z # map (n2l \<circ> l2n) zs" using Cons and n2l_l2n_id by auto
  also have 
  "\<dots> = z # zs" using IH by simp
  finally show ?case .
qed


text \<open>
Based on the previous lemmas, we can state and proof a specialised version
of \<open>candidate\<close>'s free theorem, suitable for our setting as explained 
before.
\<close>

lemma Lemma_1:
  assumes A1: "\<And>(x::'a list) (y::'a list). 
                 x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> h (f x y) = g (h x) (h y)"
      and A2: "\<And>x y. x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> f x y \<noteq> []"
      and A3: "\<And>x. x \<in> set zs \<Longrightarrow> x \<noteq> []"
  shows "map h (candidate f zs) = candidate g (map h zs)"
proof -
  \<comment> \<open>We define two functions, @{text "fn :: 'a nel \<Rightarrow> 'a nel \<Rightarrow> 'a nel"} and\<close>
  \<comment> \<open>@{text "hn :: 'a nel \<Rightarrow> b"}, which wrap @{text f} and @{text h} in the\<close>
  \<comment> \<open>setting of non-empty lists.\<close>
  let ?fn = "\<lambda>x y. l2n (f (n2l x) (n2l y))"
  let ?hn = "h \<circ> n2l"

  \<comment> \<open>Our new functions fulfill the preconditions of @{text candidate}'s\<close>
  \<comment> \<open>free theorem:\<close>
  have "\<And>(x::'a nel) (y::'a nel). ?hn (?fn x y) = g (?hn x) (?hn y)"
    proof -
      fix x y
      let ?xl = "n2l (x :: 'a nel)"
      let ?yl = "n2l (y :: 'a nel)"
      have 
      "?hn (?fn x y)
       = h (n2l (l2n (f (n2l x) (n2l y))))" by simp
      also have 
      "\<dots> = h (f ?xl ?yl)" 
          using A2 [where x="?xl" and y="?yl"]
          and n2l_l2n_id [where x="f (n2l x) (n2l y)"] 
          and non_empty_n2l [where xs=x] 
          and non_empty_n2l [where xs=y] by simp
      also have 
      "\<dots> = g (h ?xl) (h ?yl)"
          using A1 and non_empty_n2l and non_empty_n2l by auto
      also have 
      "\<dots> = g (?hn x) (?hn y)" by simp
      finally show "?hn (?fn x y) = g (?hn x) (?hn y)" .
    qed
  with candidate_free_theorem [where f="?fn" and h="?hn" and g = g]
  have ne_free_theorem: 
  "map ?hn (candidate ?fn (map l2n zs)) = candidate g (map ?hn (map l2n zs))"
      by auto

  \<comment> \<open>We use @{text candidate}'s free theorem again to show the following\<close>
  \<comment> \<open>property:\<close>
  have n2l_candidate: 
    "\<And>zs. map n2l (candidate ?fn zs) = candidate f (map n2l zs)"
    proof -
      fix zs
      have "\<And>x y. n2l (?fn x y) = f (n2l x) (n2l y)"
        proof -
          fix x y
          show "n2l (?fn x y) = f (n2l x) (n2l y)"
            using n2l_l2n_id [where x="f (n2l x) (n2l y)"] 
              and A2 [where x="n2l x" and y="n2l y"]
              and non_empty_n2l [where xs=x] and non_empty_n2l [where xs=y] 
            by simp
        qed
      with candidate_free_theorem [where h=n2l and f="?fn" and g=f]
      show "map n2l (candidate ?fn zs) = candidate f (map n2l zs)" by simp
    qed

  \<comment> \<open>Now, with the previous preparations, we conclude the thesis by the\<close>
  \<comment> \<open>following rewriting:\<close>
  have 
  "map h (candidate f zs)
   = map h (candidate f (map (n2l \<circ> l2n) zs))"
      using n2l_l2n_map_id [where zs=zs] and A3 by simp
  also have 
  "\<dots> = map h (candidate f (map n2l (map l2n zs)))"
      using List.map_map [where f=n2l and g=l2n and xs=zs] by simp 
  also have 
  "\<dots>= map h (map n2l (candidate ?fn (map l2n zs)))"
      using n2l_candidate by auto
  also have 
  "\<dots> = map ?hn (candidate ?fn (map l2n zs))"
      using List.map_map by auto
  also have
  "\<dots> = candidate g (map ?hn (map l2n zs))"
      using ne_free_theorem by simp
  also have 
  "\<dots> = candidate g (map ((h \<circ> n2l) \<circ> l2n) zs)" 
      using List.map_map [where f="h \<circ> n2l" and g=l2n] by simp
  also have 
  "\<dots> = candidate g (map (h \<circ> (n2l \<circ> l2n)) zs)" 
      using Fun.o_assoc [symmetric, where f=h and g=n2l and h=l2n] by simp
  also have 
  "\<dots> = candidate g (map h (map (n2l \<circ> l2n) zs))"
      using List.map_map [where f=h and g="n2l \<circ> l2n"] by simp
  also have 
  "\<dots> = candidate g (map h zs)" 
      using n2l_l2n_map_id [where zs=zs] and A3 by auto
  finally show ?thesis .
qed





section \<open>Useful lemmas\<close>

text \<open>
In this section, we state and proof several lemmas, which neither occur in the
original paper nor in Isabelle's libraries.
\<close>

lemma upt_map_Suc:
  "k > 0 \<Longrightarrow> [0..<k + 1] = 0 # map Suc [0..<k]"
using List.upt_conv_Cons and List.map_Suc_upt by simp


lemma divide_and_conquer_induct:
  assumes A1: "P []"
      and A2: "\<And>x. P [x]"
      and A3: "\<And>xs ys. \<lbrakk> xs \<noteq> [] ; ys \<noteq> [] ; P xs ; P ys \<rbrakk> \<Longrightarrow> P (xs @ ys)"
  shows "P zs"
proof (induct zs)
  case Nil with A1 show ?case by simp
next
  case (Cons z zs) 
  hence IH: "P zs" by simp
  show ?case
  proof (cases zs)
    case Nil with A2 show ?thesis by simp
  next
    case Cons with IH and A2 and A3 [where xs="[z]" and ys=zs] 
    show ?thesis by auto
  qed
qed

lemmas divide_and_conquer 
  = divide_and_conquer_induct [case_names Nil One Partition]


lemma all_set_inter_empty_distinct:
  assumes "\<And>xs ys. js = xs @ ys \<Longrightarrow> set xs \<inter> set ys = {}"
  shows "distinct js"
using assms proof (induct js rule: divide_and_conquer)
  case Nil thus ?case by simp
next
  case One thus ?case by simp
next
  case (Partition xs ys)
  hence P: "\<And>as bs. xs @ ys = as @ bs \<Longrightarrow> set as \<inter> set bs = {}" by simp

  have "\<And>xs1 xs2. xs = xs1 @ xs2 \<Longrightarrow> set xs1 \<inter> set xs2 = {}"
    proof -
      fix xs1 xs2
      assume "xs = xs1 @ xs2"
      hence "set xs1 \<inter> set (xs2 @ ys) = {}"
        using P [where as=xs1 and bs="xs2 @ ys"] by simp
      thus "set xs1 \<inter> set xs2 = {}" 
        using List.set_append and Set.Int_Un_distrib by auto
    qed
  with Partition have distinct_xs: "distinct xs" by simp
  have "\<And>ys1 ys2. ys = ys1 @ ys2 \<Longrightarrow> set ys1 \<inter> set ys2 = {}"
    proof -
      fix ys1 ys2
      assume "ys = ys1 @ ys2"
      hence "set (xs @ ys1) \<inter> set ys2 = {}"
        using P [where as="xs @ ys1" and bs=ys2] by simp
      thus "set ys1 \<inter> set ys2 = {}" 
        using List.set_append and Set.Int_Un_distrib by auto
    qed
  with Partition have distinct_ys: "distinct ys" by simp
  from Partition and distinct_xs and distinct_ys show ?case by simp
qed



lemma partitions_sorted:
  assumes "\<And>xs ys x y. \<lbrakk> js = xs @ ys ; x \<in> set xs ; y \<in> set ys \<rbrakk> \<Longrightarrow> x \<le> y"
  shows "sorted js"
using assms proof (induct js rule: divide_and_conquer)
  case Nil thus ?case by simp
next
  case One thus ?case by simp
next
  case (Partition xs ys)
  hence P: "\<And>as bs x y. \<lbrakk> xs @ ys = as @ bs ; x \<in> set as ; y \<in> set bs\<rbrakk> \<Longrightarrow> x \<le> y"
    by simp

  have "\<And>xs1 xs2 x y. \<lbrakk> xs = xs1 @ xs2 ; x \<in> set xs1 ; y \<in> set xs2 \<rbrakk> \<Longrightarrow> x \<le> y"
    proof -
      fix xs1 xs2
      assume "xs = xs1 @ xs2"
      hence "\<And>x y. \<lbrakk> x \<in> set xs1 ; y \<in> set (xs2 @ ys) \<rbrakk> \<Longrightarrow> x \<le> y"
        using P [where as=xs1 and bs="xs2 @ ys"] by simp
      thus "\<And>x y. \<lbrakk> x \<in> set xs1 ; y \<in> set xs2 \<rbrakk> \<Longrightarrow> x \<le> y"
        using List.set_append by auto
    qed
  with Partition have sorted_xs: "sorted xs" by simp
  have "\<And>ys1 ys2 x y. \<lbrakk> ys = ys1 @ ys2 ; x \<in> set ys1 ; y \<in> set ys2 \<rbrakk> \<Longrightarrow> x \<le> y"
    proof -
      fix ys1 ys2
      assume "ys = ys1 @ ys2"
      hence "\<And>x y. \<lbrakk> x \<in> set (xs @ ys1) ; y \<in> set ys2 \<rbrakk> \<Longrightarrow> x \<le> y"
        using P [where as="xs @ ys1" and bs=ys2] by simp
      thus "\<And>x y. \<lbrakk> x \<in> set ys1 ; y \<in> set ys2 \<rbrakk> \<Longrightarrow> x \<le> y"
        using List.set_append by auto
    qed
  with Partition have sorted_ys: "sorted ys" by simp

  have "\<forall>x \<in> set xs. \<forall>y \<in> set ys. x \<le> y"
    using P [where as=xs and bs=ys] by simp
  with sorted_xs and sorted_ys show ?case using List.sorted_append by auto
qed



section \<open>Preparatory Material\<close>

text \<open>
In the original paper, the following lemmas L1 to L8 are given without a proof,
although it is hinted there that most of them follow from parametricity
properties \cite{TypesAbstractionsAndParametricPolymorphism,TheoremsForFree}.
Alternatively, most of them can be shown by induction over lists.
However, since we are using Isabelle's list datatype, we rely on already
existing results.
\<close>

lemma L1: "map g (map f xs) = map (g \<circ> f) xs"
using List.map_map by auto

lemma L2: "length (map f xs) = length xs"
using List.length_map by simp

lemma L3: "take k (map f xs) = map f (take k xs)"
using List.take_map by auto

lemma L4: "map f \<circ> wrap = wrap \<circ> f"
by (simp add: fun_eq_iff)

lemma L5: "map f (xs @ ys) = (map f xs) @ (map f ys)"
using List.map_append by simp

lemma L6: "k < length xs \<Longrightarrow> (map f xs) ! k = f (xs ! k)"
using List.nth_map by simp


lemma L7: "\<And>k. k < length xs \<Longrightarrow> map (nth xs) [0..<k + 1] = take (k + 1) xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) 
  thus ?case
  proof (cases k)
    case 0 thus ?thesis by simp
  next
    case (Suc k')
    hence "k > 0" by simp
    hence "map (nth (x # xs)) [0..<k + 1] 
           = map (nth (x # xs)) (0 # map Suc [0..<k])" 
        using upt_map_Suc by simp
    also have "\<dots> = ((x # xs) ! 0) # (map (nth (x # xs) \<circ> Suc) [0..<k])"
        using L1 by simp
    also have "\<dots> = x # map (nth xs) [0..<k]" by simp
    also have "\<dots> = x # map (nth xs) [0..<k' + 1]" using Suc by simp
    also have "\<dots> = x # take (k' + 1) xs" using Cons and Suc by simp
    also have "\<dots> = take (k + 1) (x # xs)" using Suc by simp
    finally show ?thesis .
  qed
qed


text \<open>
In Isabelle's list theory, a similar result for \<open>foldl\<close> already exists.
Therefore, it is easy to prove the following lemma for \<open>foldl1\<close>.
Note that this lemma does not occur in the original paper.
\<close>

lemma foldl1_append:
  assumes "xs \<noteq> []"
  shows "foldl1 f (xs @ ys) = foldl1 f (foldl1 f xs # ys)"
proof -
  have non_empty_list: "xs \<noteq> [] \<Longrightarrow> \<exists>y ys. xs = y # ys" by (cases xs, auto)
  with assms obtain x xs' where x_xs_def: "xs = x # xs'" by auto

  have "foldl1 f (xs @ ys) = foldl f x (xs' @ ys)" using x_xs_def by simp
  also have "\<dots> = foldl f (foldl f x xs') ys" using List.foldl_append by simp
  also have "\<dots> = foldl f (foldl1 f (x # xs')) ys" by simp
  also have "\<dots> = foldl1 f (foldl1 f xs # ys)" using x_xs_def by simp
  finally show ?thesis .
qed


text \<open>
This is a special induction scheme suitable for proving L8. It is not mentioned
in the original paper.
\<close>

lemma foldl1_induct':
  assumes "\<And>f x. P f [x]"
      and "\<And>f x y. P f [x, y]" 
      and "\<And>f x y z zs. P f (f x y # z # zs) \<Longrightarrow> P f (x # y # z # zs)"
      and "\<And>f. P f []"
  shows "P f xs"
proof (induct xs rule: List.length_induct)
  fix xs
  assume A: "\<forall>ys::'a list. length ys < length (xs::'a list) \<longrightarrow> P f ys"
  thus "P f xs"
  proof (cases xs)
    case Nil with assms show ?thesis by simp
  next
    case (Cons x1 xs1)
    hence xs1: "xs = x1 # xs1" by simp
    thus ?thesis
    proof (cases xs1)
      case Nil with assms and xs1 show ?thesis by simp
    next
      case (Cons x2 xs2)
      hence xs2: "xs1 = x2 # xs2" by simp
      thus ?thesis
      proof (cases xs2)
        case Nil with assms and xs1 and xs2 show ?thesis by simp
      next
        case (Cons x3 xs3)
        hence "xs2 = x3 # xs3" by simp
        with assms and xs1 xs2 and A show ?thesis by simp
      qed
    qed
  qed
qed
  
lemmas foldl1_induct = foldl1_induct' [case_names One Two More Nil]


lemma L8:
  assumes "associative f"
      and "xs \<noteq> []"
      and "ys \<noteq> []"
  shows "foldl1 f (xs @ ys) = f (foldl1 f xs) (foldl1 f ys)"
using assms proof (induct f ys rule: foldl1_induct)
  case (One f y)
  have 
  "foldl1 f (xs @ [y]) 
   = foldl1 f (foldl1 f xs # [y])" 
      using foldl1_append [where xs=xs] and One by simp
  also have 
  "\<dots> = f (foldl1 f xs) y" by simp
  also have 
  "\<dots> = f (foldl1 f xs) (foldl1 f [y])" by simp
  finally show ?case .
next
  case (Two f x y)
  have 
  "foldl1 f (xs @ [x, y]) 
   = foldl1 f (foldl1 f xs # [x, y])"
      using foldl1_append [where xs=xs] and Two by simp
  also have 
  "\<dots> = foldl1 f (f (foldl1 f xs) x # [y])" by simp
  also have 
  "\<dots> = f (f (foldl1 f xs) x) y" by simp
  also have 
  "\<dots> = f (foldl1 f xs) (f x y)" using Two 
      unfolding associative_def by simp
  also have 
  "\<dots> = f (foldl1 f xs) (foldl1 f [x, y])" by simp
  finally show ?case .
next
  case (More f x y z zs)
  hence IH: "foldl1 f (xs @ f x y # z # zs) 
             = f (foldl1 f xs) (foldl1 f (f x y # z # zs))" by simp

  have 
  "foldl1 f (xs @ x # y # z # zs) 
   = foldl1 f (foldl1 f xs # x # y # z # zs)"
      using foldl1_append [where xs=xs] and More by simp
  also have 
  "\<dots> = foldl1 f (f (foldl1 f xs) x # y # z # zs)" by simp
  also have 
  "\<dots> = foldl1 f (f (f (foldl1 f xs) x) y # z # zs)" by simp
  also have 
  "\<dots> = foldl1 f (f (foldl1 f xs) (f x y) # z # zs)"
      using More unfolding associative_def by simp
  also have 
  "\<dots> = foldl1 f (foldl1 f xs # f x y # z # zs)" by simp
  also have 
  "\<dots> = foldl1 f (xs @ f x y # z # zs)"
      using foldl1_append [where xs=xs] and More by simp
  also have 
  "\<dots> = f (foldl1 f xs) (foldl1 f (x # y # z # zs))"
      using IH by simp
  finally show ?case .
next
  case Nil thus ?case by simp
qed


text \<open>
The next lemma is applied in several following proofs whenever the equivalence
of two lists is shown.
\<close>

lemma Lemma_2:
  assumes "length xs = length ys"
      and "\<And>k. k < length xs \<Longrightarrow> xs ! k = ys ! k"
  shows "xs = ys"
using assms by (auto simp: List.list_eq_iff_nth_eq)



text \<open>
In the original paper, this lemma and its proof appear inside of Lemma 3.
However, this property will be useful also in later proofs and is thus 
separated.
\<close>

lemma foldl1_map:
  assumes "associative f"
      and "xs \<noteq> []"
      and "ys \<noteq> []"
  shows "foldl1 f (map h (xs @ ys)) 
         = f (foldl1 f (map h xs)) (foldl1 f (map h ys))"
proof -
  have 
  "foldl1 f (map h (xs @ ys)) 
   = foldl1 f (map h xs @ map h ys)"
      using L5 by simp
  also have 
  "\<dots> = f (foldl1 f (map h xs)) (foldl1 f (map h ys))" 
      using assms and L8 [where f=f] by auto
  finally show ?thesis .
qed


lemma Lemma_3:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and h :: "nat \<Rightarrow> 'a"
  assumes "associative f"
  shows "map (foldl1 f \<circ> map h) (candidate (@) (map wrap [0..<n+1])) 
         = candidate f (map h [0..<n+1])"
proof - 
  \<comment> \<open>The following three properties @{text P1}, @{text P2} and @{text P3}\<close>
  \<comment> \<open>are preconditions of Lemma 1.\<close>
  have P1: 
  "\<And>x y. \<lbrakk> x \<noteq> [] ; y \<noteq> [] \<rbrakk>
   \<Longrightarrow> foldl1 f (map h (x @ y)) = f (foldl1 f (map h x)) (foldl1 f (map h y))"
      using assms and foldl1_map by blast

  have P2: "\<And>x y. x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> x @ y  \<noteq> []" by auto

  have P3: "\<And>x. x \<in> set (map wrap [0..<n+1]) \<Longrightarrow> x \<noteq> []" by auto

  \<comment> \<open>The proof for the thesis is now equal to the one of the original paper:\<close>
  from Lemma_1 [where h="foldl1 f \<circ> map h" and zs="map wrap [0..<n+1]"
       and f="(@)"] and P1 P2 P3
  have 
  "map (foldl1 f \<circ> map h) (candidate (@) (map wrap [0..<n+1])) 
   = candidate f (map (foldl1 f \<circ> map h) (map wrap [0..<n+1]))"
      by auto
  also have 
  "\<dots> = candidate f (map (foldl1 f \<circ> map h \<circ> wrap) [0..<n+1])" 
      by (simp add: L1)
  also have
  "\<dots> = candidate f (map (foldl1 f \<circ> wrap \<circ> h) [0..<n+1])" 
      using L4 by (simp add: Fun.o_def)
  also have 
  "\<dots> = candidate f (map h [0..<n+1])" 
      by (simp add: Fun.o_def)
  finally show ?thesis .
qed





section \<open>Proving Proposition 1\<close>


subsection \<open>Definitions of Lemma 4\<close>

text \<open>
In the same way as in the original paper, the following two functions are 
defined:
\<close>

fun f1 :: "three \<Rightarrow> three \<Rightarrow> three"
where
  "f1 x    Zero = x"
| "f1 Zero One  = One"
| "f1 x    y    = Two"

fun f2 :: "three \<Rightarrow> three \<Rightarrow> three"
where
  "f2 x Zero = x"
| "f2 x One  = One"
| "f2 x Two  = Two"


text \<open>
Both functions are associative as is proved by case analysis:
\<close>

lemma f1_assoc: "associative f1"
unfolding associative_def proof auto
  fix x y z
  show "f1 x (f1 y z) = f1 (f1 x y) z" 
  proof (cases z)
    case Zero thus ?thesis by simp
  next
    case One 
    hence z_One: "z = One" by simp
    thus ?thesis by (cases y, simp_all, cases x, simp_all)
  next
    case Two thus ?thesis by simp
  qed
qed

lemma f2_assoc: "associative f2" 
unfolding associative_def proof auto
  fix x y z
  show "f2 x (f2 y z) = f2 (f2 x y) z" by (cases z, auto)
qed


text \<open>
Next, we define two other functions, again according to the original paper.
Note that \<open>h1\<close> has an extra parameter \<open>k\<close> which is only implicit in
the original paper.
\<close>

fun h1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> three"
where
  "h1 k i j = (if i = j then One
               else if j \<le> k then Zero
               else Two)"

fun h2 :: "nat \<Rightarrow> nat \<Rightarrow> three"
where
  "h2 i j = (if i = j then One
             else if i + 1 = j then Two
             else Zero)"



subsection \<open>Figures and Proofs\<close>

text \<open>
In the original paper, this lemma is depicted in (and proved by) Figure~2.
Therefore, it carries this unusual name here.
\<close>

lemma Figure_2: 
  assumes "i \<le> k"
  shows "foldl1 f1 (map (h1 k i) [0..<k + 1]) = One"
proof -
  let ?mr = "replicate i Zero @ [One] @ replicate (k - i) Zero"

  have P1: "map (h1 k i) [0..<k + 1] = ?mr"
    proof -
      have Q1: "length (map (h1 k i) [0..<k + 1]) = length ?mr"
        using assms by simp
      
      have Q2: "\<And>j. j < length (map (h1 k i) [0..<k + 1])
                    \<Longrightarrow> (map (h1 k i) [0..<k + 1]) ! j = ?mr ! j"
        proof -
          fix j
          assume "j < length (map (h1 k i) [0..<k + 1])"
          hence j_k: "j < k + 1" by simp
          have M1: "(map (h1 k i) [0..<k + 1]) ! i = One"
            using L6 [where f="h1 k i" and xs="[0..<k + 1]"] and assms
              and List.nth_upt [where i=0 and k=i and j="k + 1"] by simp
          have M2: "j \<noteq> i \<Longrightarrow> (map (h1 k i) [0..<k + 1]) ! j = Zero"
            using L6 [where f="h1 k i" and xs="[0..<k + 1]"] and j_k
              and List.nth_upt [where i=0 and j="k + 1"] by simp
          have R1: "?mr ! i = One"
            using List.nth_append [where xs="replicate i Zero"] by simp
          have R2: "j < i \<Longrightarrow> ?mr ! j = Zero"
            using List.nth_append [where xs="replicate i Zero"] by simp
          have R3: "j > i \<Longrightarrow> ?mr ! j = Zero"
            using List.nth_append [where xs="replicate i Zero @ [One]"]
              and j_k by simp
          
          show "(map (h1 k i) [0..<k + 1]) ! j = ?mr ! j"
          proof (cases "i = j")
            assume "i = j"
            with M1 and R1 show ?thesis by simp
          next
            assume i_ne_j: "i \<noteq> j"
            thus ?thesis
            proof (cases "i < j")
              assume "i < j"
              with M2 and R3 show ?thesis by simp
            next 
              assume "\<not>(i < j)"
              with i_ne_j have "i > j" by simp
              with M2 and R2 show ?thesis by simp
            qed
          qed
        qed
      
      from Q1 Q2 and Lemma_2 show ?thesis by blast
    qed

  have P2: "\<And>j. j > 0 \<Longrightarrow> foldl1 f1 (replicate j Zero) = Zero"
    proof -
      fix j
      assume "(j::nat) > 0"
      thus "foldl1 f1 (replicate j Zero) = Zero"
      proof (induct j)
        case 0 thus ?case by simp
      next
        case (Suc j) thus ?case by (cases j, auto)
      qed
    qed

  have P3: "\<And>j. foldl1 f1 ([One] @ replicate j Zero) = One"
    proof -
      fix j
      show "foldl1 f1 ([One] @ replicate j Zero) = One"
        using L8 [where f=f1 and xs="[One]" and ys="replicate (Suc j) Zero"] 
          and f1_assoc and P2 [where j="Suc j"] by simp
    qed
  
  have "foldl1 f1 ?mr = One"
    proof (cases i)
      case 0
      thus ?thesis using P3 by simp
    next
      case (Suc i)
      hence 
      "foldl1 f1 (replicate (Suc i) Zero @ [One] @ replicate (k - Suc i) Zero)
       = f1 (foldl1 f1 (replicate (Suc i) Zero))
            (foldl1 f1 ([One] @ replicate (k - Suc i) Zero))"
          using L8 [where xs="replicate (Suc i) Zero" 
                    and ys="[One] @ replicate (k - Suc i) Zero"] 
          and f1_assoc by simp
      also have 
      "\<dots> = One" 
          using P2 [where j="Suc i"] and P3 [where j="k - Suc i"] by simp
      finally show ?thesis using Suc by simp
    qed
  with P1 show ?thesis by simp
qed



text \<open>
In the original paper, this lemma is depicted in (and proved by) Figure~3.
Therefore, it carries this unusual name here.
\<close>

lemma Figure_3: 
  assumes "i < k"
  shows "foldl1 f2 (map (h2 i) [0..<k + 1]) = Two" 
proof -
  let ?mr = "replicate i Zero @ [One, Two] @ replicate (k - i - 1) Zero"

  have P1: "map (h2 i) [0..<k + 1] = ?mr"
    proof -
      have Q1: "length (map (h2 i) [0..<k + 1]) = length ?mr"
        using assms by simp
      
      have Q2: "\<And>j. j < length (map (h2 i) [0..<k + 1])
                    \<Longrightarrow> (map (h2 i) [0..<k + 1]) ! j = ?mr ! j"
        proof -
          fix j
          assume "j < length (map (h2 i) [0..<k + 1])"
          hence j_k: "j < k + 1" by simp
          have M1: "(map (h2 i) [0..<k + 1]) ! i = One" 
            using L6 [where xs="[0..<k + 1]" and f="h2 i" and k=i] and assms 
            and List.nth_upt [where i=0 and k=i and j="k + 1"] by simp
          have M2: "(map (h2 i) [0..<k + 1]) ! (i + 1) = Two"
            using L6 [where xs="[0..<k + 1]" and f="h2 i" and k="i + 1"] 
            and assms and List.nth_upt [where i=0 and k="i + 1" and j="k + 1"]
            by simp
          have M3: "j < i \<or> j > i + 1 \<Longrightarrow> (map (h2 i) [0..<k + 1]) ! j = Zero" 
            using L6 [where xs="[0..<k + 1]" and f="h2 i" and k=j] 
            and assms and List.nth_upt [where i=0 and k=j and j="k + 1"]
            and j_k by auto
          have R1: "j < i \<Longrightarrow> ?mr ! j = Zero" 
            using List.nth_append [where xs="replicate i Zero"] by simp
          have R2: "?mr ! i = One"
            using List.nth_append [where xs="replicate i Zero"] by simp
          have R3: "?mr ! (i + 1) = Two"
            using List.nth_append [where xs="replicate i Zero @ [One]"] by simp
          have R4: "j > i + 1 \<Longrightarrow> ?mr ! j = Zero"
            using List.nth_append [where xs="replicate i Zero @ [One,Two]"]
            and j_k by simp
          show "(map (h2 i) [0..<k + 1]) ! j = ?mr ! j"
          proof (cases "j < i")
            assume "j < i" with M3 and R1 show ?thesis by simp
          next
            assume "\<not>(j < i)"
            hence j_ge_i: "j \<ge> i" by simp
            thus ?thesis
            proof (cases "j = i")
              assume "j = i" with M1 and R2 show ?thesis by simp
            next
              assume "\<not>(j = i)"
              with j_ge_i have j_gt_i: "j > i" by simp
              thus ?thesis
              proof (cases "j = i + 1")
                assume "j = i + 1" with M2 and R3 show ?thesis by simp
              next
                assume "\<not>(j = i + 1)"
                with j_gt_i have "j > i + 1" by simp
                with M3 and R4 show ?thesis by simp
              qed
            qed
          qed
        qed
      from Q1 Q2 and Lemma_2 show ?thesis by blast
    qed
 
  have P2: "\<And>j. j > 0 \<Longrightarrow> foldl1 f2 (replicate j Zero) = Zero"
    proof -
      fix j
      assume j_0: "(j::nat) > 0"
      show "foldl1 f2 (replicate j Zero) = Zero"
      using j_0 proof (induct j)
        case 0 thus ?case by simp
      next
        case (Suc j) thus ?case by (cases j, auto)
      qed
    qed
 
  have P3: "\<And>j. foldl1 f2 ([One, Two] @ replicate j Zero) = Two"
    proof -
      fix j
      show "foldl1 f2 ([One, Two] @ replicate j Zero) = Two"
        using L8 [where f=f2 and xs="[One,Two]" 
        and ys="replicate (Suc j) Zero"] and f2_assoc and P2 [where j="Suc j"]
        by simp
    qed

  have "foldl1 f2 ?mr = Two" 
    proof (cases i)
      case 0 thus ?thesis using P3 by simp
    next
      case (Suc i)
      hence 
      "foldl1 f2 (replicate (Suc i) Zero @ [One, Two] 
                                         @ replicate (k - Suc i - 1) Zero)
       = f2 (foldl1 f2 (replicate (Suc i) Zero))
            (foldl1 f2 ([One, Two] @  replicate (k - Suc i - 1) Zero))"
          using L8 [where f=f2 and xs="replicate (Suc i) Zero" 
                    and ys="[One, Two] @ replicate (k - Suc i - 1) Zero"] 
          and f2_assoc by simp
      also have 
      "\<dots> = Two"
          using P2 [where j="Suc i"] and P3 [where j="k - Suc i - 1"] by simp
      finally show ?thesis using Suc by simp
    qed
  with P1 show ?thesis by simp
qed



text \<open>
Counterparts of the following two lemmas are shown in the proof of Lemma 4 in
the original paper. Since here, the proof of Lemma 4 is seperated in several
smaller lemmas, also these two properties are given separately.
\<close>

lemma L9:
  assumes "\<And> (f :: three \<Rightarrow> three \<Rightarrow> three) h. associative f 
             \<Longrightarrow> foldl1 f (map h js) = foldl1 f (map h [0..<k + 1])"
      and "i \<le> k"
  shows "foldl1 f1 (map (h1 k i) js) = One"
using assms and f1_assoc and Figure_2 by auto


lemma L10:
  assumes "\<And> (f :: three \<Rightarrow> three \<Rightarrow> three) h. associative f 
             \<Longrightarrow> foldl1 f (map h js) = foldl1 f (map h [0..<k + 1])"
      and "i < k"
  shows "foldl1 f2 (map (h2 i) js) = Two"
using assms and f2_assoc and Figure_3 by auto



text \<open>
In the original paper, this lemma is depicted in (and proved by) Figure~4.
Therefore, it carries this unusual name here. This lemma expresses that every
\<open>i \<le> k\<close> is contained in \<open>js\<close> at least once.
\<close>

lemma Figure_4:
  assumes "foldl1 f1 (map (h1 k i) js) = One"
      and "js \<noteq> []"
  shows "i \<in> set js" 
proof (rule ccontr)
  assume i_not_in_js: "i \<notin> set js"

  have One_not_in_map_js: "One \<notin> set (map (h1 k i) js)" 
    proof 
      assume "One \<in> set (map (h1 k i) js)" 
      hence "One \<in> (h1 k i) ` (set js)" by simp
      then obtain j where j_def: "j \<in> set js \<and> One = h1 k i j" 
        using Set.image_iff [where f="h1 k i"] by auto
      hence "i = j" by (simp split: if_splits)
      with i_not_in_js and j_def show False by simp
    qed
  
  have f1_One: "\<And>x y. x \<noteq> One \<and> y \<noteq> One \<Longrightarrow> f1 x y \<noteq> One"
    proof - 
      fix x y
      assume "x \<noteq> One \<and> y \<noteq> One"
      thus "f1 x y \<noteq> One" by (cases y, cases x, auto)
    qed
  
  have "\<And>xs. \<lbrakk> xs \<noteq> [] ; One \<notin> set xs \<rbrakk> \<Longrightarrow> foldl1 f1 xs \<noteq> One"
    proof -
      fix xs
      assume A: "(xs :: three list) \<noteq> []"
      thus "One \<notin> set xs \<Longrightarrow> foldl1 f1 xs \<noteq> One"
      proof (induct xs rule: divide_and_conquer)
        case Nil thus ?case by simp
      next
        case (One x)
        thus "foldl1 f1 [x] \<noteq> One" by simp
      next
        case (Partition xs ys)
        hence "One \<notin> set xs \<and> One \<notin> set ys" by simp
        with Partition have "foldl1 f1 xs \<noteq> One \<and> foldl1 f1 ys \<noteq> One" by simp
        with f1_One have "f1 (foldl1 f1 xs) (foldl1 f1 ys) \<noteq> One" by simp
        with L8 [symmetric, where f=f1] and f1_assoc and Partition 
        show "foldl1 f1 (xs @ ys) \<noteq> One" by auto
      qed
    qed
  with One_not_in_map_js and assms show False by auto
qed



text \<open>
In the original paper, this lemma is depicted in (and proved by) Figure~5.
Therefore, it carries this unusual name here. This lemma expresses that every
\<open>i \<le> k\<close> is contained in \<open>js\<close> at most once.
\<close>

lemma Figure_5:
  assumes "foldl1 f1 (map (h1 k i) js) = One"
      and "js = xs @ ys"
  shows "\<not>(i \<in> set xs \<and> i \<in> set ys)"
proof (rule ccontr)
  assume "\<not>\<not>(i \<in> set xs \<and> i \<in> set ys)"
  hence i_xs_ys: "i \<in> set xs \<and> i \<in> set ys" by simp

  from i_xs_ys have xs_not_empty: "xs \<noteq> []" by auto
  from i_xs_ys have ys_not_empty: "ys \<noteq> []" by auto

  have f1_Zero: "\<And>x y. x \<noteq> Zero \<or> y \<noteq> Zero \<Longrightarrow> f1 x y \<noteq> Zero"
    proof -
      fix x y 
      show "x \<noteq> Zero \<or> y \<noteq> Zero \<Longrightarrow> f1 x y \<noteq> Zero"
      by (cases y, simp_all, cases x, simp_all)
    qed

  have One_foldl1: "\<And>xs. One \<in> set xs \<Longrightarrow> foldl1 f1 xs \<noteq> Zero"
    proof -
      fix xs
      assume One_xs: "One \<in> set xs"
      thus "foldl1 f1 xs \<noteq> Zero"
      proof (induct xs rule: divide_and_conquer)
        case Nil thus ?case by simp
      next
        case One thus ?case by simp
      next
        case (Partition xs ys)
        hence "One \<in> set xs \<or> One \<in> set ys" by simp
        with Partition have "foldl1 f1 xs \<noteq> Zero \<or> foldl1 f1 ys \<noteq> Zero" by auto
        with f1_Zero have "f1 (foldl1 f1 xs) (foldl1 f1 ys) \<noteq> Zero" by simp
        thus ?case using L8 [symmetric, where f=f1] and f1_assoc and Partition
          by auto
      qed
    qed

  have f1_Two: "\<And>x y. x \<noteq> Zero \<and> y \<noteq> Zero \<Longrightarrow> f1 x y = Two"
    proof -
      fix x y 
      show "x \<noteq> Zero \<and> y \<noteq> Zero \<Longrightarrow> f1 x y = Two"
      by (cases y, simp_all, cases x, simp_all)
    qed
  
  from i_xs_ys
  have "One \<in> set (map (h1 k i) xs) \<and> One \<in> set (map (h1 k i) ys)" by simp
  hence "foldl1 f1 (map (h1 k i) xs) \<noteq> Zero 
         \<and> foldl1 f1 (map (h1 k i) ys) \<noteq> Zero"
    using One_foldl1 by simp
  hence "f1 (foldl1 f1 (map (h1 k i) xs)) (foldl1 f1 (map (h1 k i) ys)) = Two"
    using f1_Two by simp
  hence "foldl1 f1 (map (h1 k i) (xs @ ys)) = Two"
    using foldl1_map [symmetric, where h="h1 k i"] and f1_assoc 
      and xs_not_empty and ys_not_empty by auto
  with assms show False by simp
qed



text \<open>
In the original paper, this lemma is depicted in (and proved by) Figure~6.
Therefore, it carries this unusual name here. This lemma expresses that
\<open>js\<close> contains only elements of \<open>[0..<k + 1]\<close>.
\<close>

lemma Figure_6:
  assumes "\<And>i. i \<le> k \<Longrightarrow> foldl1 f1 (map (h1 k i) js) = One"
      and "i > k"
  shows "i \<notin> set js"
proof
  assume i_in_js: "i \<in> set js"

  have Two_map: "Two \<in> set (map (h1 k 0) js)"
    proof -
      have "Two = h1 k 0 i" using assms by simp
      with i_in_js show ?thesis using IntI by (auto split: if_splits)
    qed
  
  have f1_Two: "\<And>x y. x = Two \<or> y = Two \<Longrightarrow> f1 x y = Two"
    proof -
      fix x y
      show "x = Two \<or> y = Two \<Longrightarrow> f1 x y = Two" by (cases y, auto)
    qed

  have "\<And>xs. Two \<in> set xs \<Longrightarrow> foldl1 f1 xs = Two"
    proof -
      fix xs
      assume Two_xs: "Two \<in> set xs"
      thus "foldl1 f1 xs = Two" using Two_xs
      proof (induct xs rule: divide_and_conquer)
        case Nil thus ?case by simp
      next
        case One thus ?case by simp
      next
        case (Partition xs ys)
        hence "Two \<in> set xs \<or> Two \<in> set ys" by simp
        hence "foldl1 f1 xs = Two \<or> foldl1 f1 ys = Two" using Partition by auto
        with f1_Two have "f1 (foldl1 f1 xs) (foldl1 f1 ys) = Two" by simp
        thus "foldl1 f1 (xs @ ys) = Two" 
          using L8 [symmetric, where f=f1] and f1_assoc and Partition by auto
      qed
    qed

  with Two_map have "foldl1 f1 (map (h1 k 0) js) = Two" by simp
  with assms show False by auto
qed



text \<open>
In the original paper, this lemma is depicted in (and proved by) Figure~7.
Therefore, it carries this unusual name here. This lemma expresses that every
\<open>i \<le> k\<close> in \<open>js\<close> is eventually followed by \<open>i + 1\<close>.
\<close>

lemma Figure_7:
  assumes "foldl1 f2 (map (h2 i) js) = Two"
      and "js = xs @ ys"
      and "xs \<noteq> []"
      and "i = last xs"
  shows "(i + 1) \<in> set ys"
proof (rule ccontr)
  assume Suc_i_not_in_ys: "(i + 1) \<notin> set ys"

  have last_map_One: "last (map (h2 i) xs) = One"
    proof -
      have 
      "last (map (h2 i) xs) 
        = (map (h2 i) xs) ! (length (map (h2 i) xs) - 1)" 
          using List.last_conv_nth [where xs="map (h2 i) xs"] and assms by simp
      also have 
      "\<dots> = (map (h2 i) xs) ! (length xs - 1)" using L2 by simp
      also have 
      "\<dots> = h2 i (xs ! (length xs - 1))" 
          using L6 and assms by simp
      also have 
      "\<dots> = h2 i (last xs)" 
          using List.last_conv_nth [symmetric,where xs=xs] and assms by simp
      also have 
      "\<dots> = One" using assms by simp
      finally show ?thesis .
    qed
  
  have "\<And>xs. \<lbrakk>  xs \<noteq> [] ; last xs = One \<rbrakk> \<Longrightarrow> foldl1 f2 xs = One"
    proof -
      fix xs
      assume last_xs_One: "last xs = One"
      assume xs_not_empty: "xs \<noteq> []"
      hence xs_partition: "xs = butlast xs @ [last xs]" by simp
      show "foldl1 f2 xs = One"
      proof (cases "butlast xs")
        case Nil with xs_partition and last_xs_One show ?thesis by simp
      next
        case Cons
        hence butlast_not_empty: "butlast xs \<noteq> []" by simp
        
        have 
        "foldl1 f2 xs = foldl1 f2 (butlast xs @ [last xs])" 
            using xs_partition by simp
        also have 
        "\<dots> = f2 (foldl1 f2 (butlast xs)) (foldl1 f2 [last xs])" 
            using L8 [where f=f2] and f2_assoc and butlast_not_empty by simp
        also have 
        "\<dots> = One" using last_xs_One by simp
        finally show ?thesis .
      qed
    qed
  with last_map_One have foldl1_map_xs: "foldl1 f2 (map (h2 i) xs) = One" 
    using assms by simp

  have ys_not_empty: "ys \<noteq> []" using foldl1_map_xs and assms by auto

  have Two_map_ys: "Two \<notin> set (map (h2 i) ys)"
    proof
      assume "Two \<in> set (map (h2 i) ys)"
      hence "Two \<in> (h2 i) ` (set ys)" by simp
      then obtain j where j_def: "j \<in> set ys \<and> Two = h2 i j" 
        using Set.image_iff [where f="h2 i"] by auto
      hence "i + 1 = j" by (simp split: if_splits)
      with Suc_i_not_in_ys and j_def show False by simp
    qed
  
  have f2_One: "\<And>x y. x \<noteq> Two \<and> y \<noteq> Two \<Longrightarrow> f2 x y \<noteq> Two"
    proof -
      fix x y
      show "x \<noteq> Two \<and> y \<noteq> Two \<Longrightarrow> f2 x y \<noteq> Two" by (cases y, auto) 
    qed

  have "\<And>xs. \<lbrakk> xs \<noteq> [] ; Two \<notin> set xs \<rbrakk> \<Longrightarrow> foldl1 f2 xs \<noteq> Two"
    proof -
      fix xs
      assume xs_not_empty: "(xs :: three list) \<noteq> []"
      thus "Two \<notin> set xs \<Longrightarrow> foldl1 f2 xs \<noteq> Two"
      proof (induct xs rule: divide_and_conquer)
        case Nil thus ?case by simp
      next
        case One thus ?case by simp
      next
        case (Partition xs ys)
        hence "Two \<notin> set xs \<and> Two \<notin> set ys" by simp
        hence "foldl1 f2 xs \<noteq> Two \<and> foldl1 f2 ys \<noteq> Two" using Partition by simp
        hence "f2 (foldl1 f2 xs) (foldl1 f2 ys) \<noteq> Two" using f2_One by simp
        thus "foldl1 f2 (xs @ ys) \<noteq> Two" 
          using L8 [symmetric, where f=f2] and f2_assoc and Partition by simp
      qed
    qed
  with Two_map_ys have foldl1_map_ys: "foldl1 f2 (map (h2 i) ys) \<noteq> Two" 
    using ys_not_empty by simp

  from f2_One 
  have "f2 (foldl1 f2 (map (h2 i) xs)) (foldl1 f2 (map (h2 i) ys)) \<noteq> Two"
    using foldl1_map_xs and foldl1_map_ys by simp
  hence "foldl1 f2 (map (h2 i) (xs @ ys)) \<noteq> Two" 
    using foldl1_map [symmetric, where h="h2 i" and f=f2] and f2_assoc 
      and assms and ys_not_empty by simp
  with assms show False by simp
qed
  


subsection \<open>Permutations and Lemma 4\<close>

text \<open>
In the original paper, the argumentation goes as follows:
From \<open>Figure_4\<close> and \<open>Figure_5\<close> we can show that \<open>js\<close>
contains every \<open>i \<le> k\<close> exactly once, and from \<open>Figure_6\<close> we can
furthermore show that \<open>js\<close> contains no other elements. Thus, \<open>js\<close>
must be a permutation of \<open>[0..<k + 1]\<close>.

Here, however, the argumentation is different, because we want to use already
existing results. Therefore, we show first, that the sets of \<open>js\<close> and
\<open>[0..<k + 1]\<close> are equal using the results of \<open>Figure_4\<close> and
\<open>Figure_6\<close>. Second, we show that \<open>js\<close> is a distinct list, i.e. no
element occurs twice in \<open>js\<close>. Since also \<open>[0..<k + 1]\<close> is
distinct, the multisets of \<open>js\<close> and \<open>[0..<k + 1]\<close> are equal,
and therefore, both lists are permutations.
\<close>

lemma js_is_a_permutation:
  assumes A1: "\<And> (f :: three \<Rightarrow> three \<Rightarrow> three) h. associative f
                \<Longrightarrow> foldl1 f (map h js) = foldl1 f (map h [0..<k + 1])"
      and A2: "js \<noteq> []"
  shows "js <~~> [0..<k + 1]"
proof -
  from A1 and L9 have L9': 
  "\<And>i. i \<le> k \<Longrightarrow> foldl1 f1 (map (h1 k i) js) = One" by auto

  from L9' and Figure_4 and A2 have P1: "\<And>i. i \<le> k \<Longrightarrow> i \<in> set js" by auto
  from L9' and Figure_5 have P2:
    "\<And>i xs ys. \<lbrakk> i \<le> k ; js = xs @ ys \<rbrakk> \<Longrightarrow> \<not>(i \<in> set xs \<and> i \<in> set ys)" by blast
  from L9' and Figure_6 have P3: "\<And>i. i > k \<Longrightarrow> i \<notin> set js" by auto

  have set_eq: "set [0..<k + 1] = set js"
    proof
      from P1 show "set [0..<k + 1] \<subseteq> set js" by auto
    next
      show "set js \<subseteq> set [0..<k + 1]"
      proof
        fix j
        assume "j \<in> set js"
        hence "\<not>(j \<notin> set js)" by simp
        with P3 have "\<not>(j > k)" using HOL.contrapos_nn by auto
        hence "j \<le> k" by simp
        thus "j \<in> set [0..<k + 1]" by auto
      qed
    qed

  have "\<And>xs ys. js = xs @ ys \<Longrightarrow> set xs \<inter> set ys = {}"
    proof -
      fix xs ys
      assume js_xs_ys: "js = xs @ ys"
      with set_eq have i_xs_ys: "\<And>i. i \<in> set xs \<or> i \<in> set ys \<Longrightarrow> i \<le> k" by auto
      have "\<And>i. i \<le> k \<Longrightarrow> (i \<in> set xs) = (i \<notin> set ys)"
        proof
          fix i
          assume "i \<in> set xs"
          moreover assume "i \<le> k"
          ultimately show "i \<notin> set ys" using js_xs_ys and P2 by simp
        next
          fix i
          assume "i \<notin> set ys"
          moreover assume "i \<le> k"
          ultimately show "i \<in> set xs" using js_xs_ys and P2 and P1 by auto
        qed
      thus "set xs \<inter> set ys = {}" using i_xs_ys by auto
    qed
  with all_set_inter_empty_distinct have "distinct js" using A2 by auto
  with set_eq have "mset js = mset [0..<k + 1]"
    using Multiset.set_eq_iff_mset_eq_distinct 
          [where x=js and y="[0..<k + 1]"] by simp
  thus "js <~~> [0..<k + 1]" 
    using Permutation.mset_eq_perm [where xs=js and ys="[0..<k + 1]"] 
    by simp
qed



text \<open>
The result of \<open>Figure_7\<close> is too specific. Instead of having that every
\<open>i\<close> is eventually followed by \<open>i + 1\<close>, it more useful to know
that every \<open>i\<close> is followed by all \<open>i + r\<close>, where 
\<open>r > 0\<close>. This result follows easily by induction from 
\<open>Figure_7\<close>.
\<close>

lemma Figure_7_trans:
  assumes A1: "\<And>i xs ys. \<lbrakk> i < k ; js = xs @ ys ; xs \<noteq> [] ; i = last xs \<rbrakk>
                         \<Longrightarrow> (i + 1) \<in> set ys"
      and A2: "(r::nat) > 0"
      and A3: "i + r \<le> k"
      and A4: "js = xs @ ys"
      and A5: "xs \<noteq> []"
      and A6: "i = last xs"
  shows "(i + r) \<in> set ys"
using A2 A3 proof (induct r)
  case 0 thus ?case by simp
next
  case (Suc r)
  hence IH: "0 < r \<Longrightarrow> (i + r) \<in> set ys" by simp
  from Suc have i_r_k: "i + Suc r \<le> k" by simp
  show ?case
  proof (cases r)
    case 0 thus ?thesis using A1 and i_r_k and A4 and A5 and A6 by auto
  next
    case Suc 
    with IH have "(i + r) \<in> set ys" by simp
    then obtain p where p_def: "p < length ys \<and> ys ! p = i + r" 
      using List.in_set_conv_nth [where x="i + r"] by auto
    
    let ?xs = "xs @ take (p + 1) ys"
    let ?ys = "drop (p + 1) ys"

    have "i + r < k" using i_r_k by simp
    moreover have "js = ?xs @ ?ys" using A4 by simp
    moreover have "?xs \<noteq> []" using A5 by simp
    moreover have "i + r = last ?xs" 
      using p_def and List.take_Suc_conv_app_nth [where i=p and xs=ys] by simp
    ultimately have "(i + Suc r) \<in> set ?ys" using A1 [where i="i + r"] by auto
    thus "(i + Suc r) \<in> set ys" 
      using List.set_drop_subset [where xs=ys] by auto
  qed
qed



text \<open>
Since we want to use Lemma \<open>partitions_sorted\<close> to show that \<open>js\<close>
is sorted, we need yet another result which can be obtained using the
previous lemma and some further argumentation:
\<close>

lemma js_partition_order:
  assumes A1: "js <~~> [0..<k + 1]"
      and A2: "\<And>i xs ys. \<lbrakk> i < k ; js = xs @ ys ; xs \<noteq> [] ; i = last xs \<rbrakk>
                         \<Longrightarrow> (i + 1) \<in> set ys"
      and A3: "js = xs @ ys"
      and A4: "i \<in> set xs" 
      and A5: "j \<in> set ys"
  shows "i \<le> j"
proof (rule ccontr)
  assume "\<not>(i \<le> j)"
  hence i_j: "i > j" by simp

  from A5 obtain pj where pj_def: "pj < length ys \<and> ys ! pj = j" 
    using List.in_set_conv_nth [where x=j] by auto

  let ?xs = "xs @ take (pj + 1) ys"
  let ?ys = "drop (pj + 1) ys"

  let ?r = "i - j"

  from A1 and A3 have "distinct (xs @ ys)" 
    using Permutation.perm_distinct_iff [where xs="xs @ ys"] by auto
  hence xs_ys_inter_empty: "set xs \<inter> set ys = {}" by simp

  from A2 and Figure_7_trans have
  "\<And>i r xs ys. \<lbrakk> r > 0 ; i + r \<le> k ; js = xs @ ys ; xs \<noteq> [] ; i = last xs \<rbrakk>
               \<Longrightarrow> (i + r) \<in> set ys" by blast
  moreover from i_j have "?r > 0" by simp
  moreover have "j + ?r \<le> k"
    proof -
      have "i \<in> set js" using A4 and A3 by simp
      hence "i \<in> set [0..<k + 1]" 
        using A1 and Permutation.perm_set_eq by blast
      hence "i \<le> k" by auto
      thus ?thesis using i_j by simp
    qed
  moreover have "js = ?xs @ ?ys" using A3 by simp
  moreover have "?xs \<noteq> []" using A4 by auto
  moreover have "j = last (?xs)"
    using pj_def and List.take_Suc_conv_app_nth [where i=pj and xs=ys] by simp
  ultimately have "(j + ?r) \<in> set ?ys" by blast
  hence "i \<in> set ys" using i_j and List.set_drop_subset [where xs=ys] by auto
  with A4 and xs_ys_inter_empty show False by auto
qed



text \<open>
With the help of the previous lemma, we show now that \<open>js\<close> equals
\<open>[0..<k + 1]\<close>, if both lists are permutations and every \<open>i\<close> is
eventually followed by \<open>i + 1\<close> in \<open>js\<close>.
\<close>

lemma js_equals_upt_k:
  assumes A1: "js <~~> [0..<k + 1]"
      and A2: "\<And>i xs ys. \<lbrakk> i < k ; js = xs @ ys ; xs \<noteq> [] ; i = last xs \<rbrakk>
                         \<Longrightarrow> (i + 1) \<in> set ys"
  shows "js = [0..<k + 1]"
proof -
  from A1 and A2 and js_partition_order
  have "\<And>xs ys x y. \<lbrakk> js = xs @ ys ; x \<in> set xs ; y \<in> set ys \<rbrakk> \<Longrightarrow> x \<le> y"
    by blast
  hence "sorted js" using partitions_sorted by blast
  moreover have "distinct js" 
    using A1 and Permutation.perm_distinct_iff and List.distinct_upt by blast
  moreover have "sorted [0..<k + 1]"
    using List.sorted_upt by blast 
  moreover have "distinct [0..<k + 1]" by simp
  moreover have "set js = set [0..<k + 1]" 
    using A1 and Permutation.perm_set_eq by blast
  ultimately show "js = [0..<k + 1]" using List.sorted_distinct_set_unique 
    by blast
qed



text \<open>
From all the work done before, we conclude now Lemma 4:
\<close>

lemma Lemma_4:
  assumes "\<And>(f :: three \<Rightarrow> three \<Rightarrow> three) h. associative f  
             \<Longrightarrow> foldl1 f (map h js) = foldl1 f (map h [0..<k + 1])"
      and "js \<noteq> []"
  shows "js = [0..<k + 1]"
proof -
  from assms and js_is_a_permutation have "js <~~> [0..<k + 1]" by auto
  moreover 
  from assms and L10 and Figure_7
  have "\<And>i xs ys. \<lbrakk> i < k ; js = xs @ ys ; xs \<noteq> [] ; i = last xs \<rbrakk>
                  \<Longrightarrow> (i + 1) \<in> set ys" by blast
  ultimately show ?thesis using js_equals_upt_k by auto
qed



subsection \<open>Lemma 5\<close>

text \<open>
This lemma is a lifting of Lemma 4 to the overall computation of 
\<open>scanl1\<close>. Its proof follows closely the one given in the original paper.
\<close>

lemma Lemma_5:
  assumes "\<And>(f :: three \<Rightarrow> three \<Rightarrow> three) h. associative f
             \<Longrightarrow> map (foldl1 f \<circ> map h) jss = scanl1 f (map h [0..<n + 1])"
      and "\<And>js. js \<in> set jss \<Longrightarrow> js \<noteq> []"
  shows "jss = ups n"
proof -
  have P1: "length jss = length (ups n)" 
    proof -
      obtain f :: "three \<Rightarrow> three \<Rightarrow> three" where f_assoc: "associative f"
        using f1_assoc by auto

      fix h
      have 
      "length jss = length (map (foldl1 f \<circ> map h) jss)" by (simp add: L2)
      also have 
      "\<dots> = length (scanl1 f (map h [0..<n + 1]))" 
          using assms and f_assoc by simp
      also have 
      "\<dots> = length (map (\<lambda>k. foldl1 f (take (k + 1) (map h [0..<n + 1])))
                       [0..<length (map h [0..<n + 1])])" by simp
      also have 
      "\<dots> = length [0..<length (map h [0..<n + 1])]" by (simp add: L2)
      also have
      "\<dots> = length [0..<length [0..<n + 1]]" by (simp add: L2)
      also have 
      "\<dots> = length [0..<n + 1]" by simp
      also have 
      "\<dots> = length (map (\<lambda>k. [0..<k + 1]) [0..<n + 1])" by (simp add: L2)
      also have 
      "\<dots> = length (ups n)" by simp
      finally show ?thesis .
    qed

  have P2: "\<And>k. k < length jss \<Longrightarrow> jss ! k = (ups n) ! k"
    proof -
      fix k
      assume k_length_jss: "k < length jss"
      hence non_empty_jss_k: "jss ! k \<noteq> []" using assms by simp

      from k_length_jss 
      have k_length_length: "k < length [1..<length [0..<n + 1] + 1]"
        using P1 by simp
      hence k_length: "k < length [0..<n + 1]"
        using List.length_upt [where i=1 and j="length [0..<n + 1] + 1"] 
        by simp 

      have "\<And>(f :: three \<Rightarrow> three \<Rightarrow> three) h. associative f
                  \<Longrightarrow> foldl1 f (map h (jss ! k)) = foldl1 f (map h [0..<k + 1])"
        proof -
          fix f h
          assume f_assoc: "associative (f :: three \<Rightarrow> three \<Rightarrow> three)"
          have 
          "foldl1 f (map h (jss ! k))
           = (map (foldl1 f \<circ> map h) jss) ! k" 
              using L6 and k_length_jss by auto
          also have 
          "\<dots> = (scanl1 f (map h [0..<n + 1])) ! k" 
              using assms and f_assoc by simp
          also have 
          "\<dots> = (map (\<lambda>k. foldl1 f (take k (map h [0..<n + 1])))
                    [1..<length (map h [0..<n + 1]) + 1]) ! k" by simp
          also have 
          "\<dots> = (map (\<lambda>k. foldl1 f (take k (map h [0..<n + 1]))) 
                    [1..<length [0..<n + 1] + 1]) ! k" 
              by (simp add: L2)
          also have 
          "\<dots> = (\<lambda>k. foldl1 f (take k (map h [0..<n + 1])))
                  ([1..<length [0..<n + 1] + 1] ! k)"
            using L6 [where xs="[1..<length [0..<n + 1] + 1]"
              and f="(\<lambda>k. foldl1 f (take k (map h [0..<n + 1])))"] 
              and k_length_length by auto
          also have 
          "\<dots> = foldl1 f (take (k + 1) (map h [0..<n + 1]))"
              proof -
                have "[1..<length [0..<n + 1] + 1] ! k  = k + 1"
                  using List.nth_upt [where i=1 and j="length [0..<n + 1] + 1"]
                    and k_length by simp
                thus ?thesis by simp
              qed
          also have 
          "\<dots> = foldl1 f (map h (take (k + 1) [0..<n + 1]))"
              using L3 [where k="k + 1" and xs="[0..<n + 1]" and f=h] by simp
          also have "\<dots> = foldl1 f (map h [0..<k + 1])"
              using List.take_upt [where i=0 and m="k + 1" and n="n + 1"]
                and k_length by simp
          finally show 
          "foldl1 f (map h (jss ! k)) = foldl1 f (map h [0..<k + 1])" .
        qed
      with Lemma_4 and non_empty_jss_k have P3: "jss ! k = [0..<k + 1]" 
        by blast

      have 
      "(ups n) ! k 
       = (map (\<lambda>k. [0..<k + 1]) [0..<n + 1]) ! k" by simp
      also have 
      "\<dots> = (\<lambda>k. [0..<k + 1]) ([0..<n + 1] ! k)" 
          using L6 [where xs="[0..<n + 1]"] and k_length by auto
      also have 
      "\<dots> = [0..<k + 1]" 
          using List.nth_upt [where i=0 and j="n + 1"] and k_length by simp
      finally have "(ups n) ! k = [0..<k + 1]" .
      
      with P3 show "jss ! k = (ups n) ! k" by simp
    qed

  from P1 P2 and Lemma_2 show "jss = ups n" by blast
qed



subsection \<open>Proposition 1\<close>

text \<open>
In the original paper, only non-empty lists where considered, whereas here,
the used list datatype allows also for empty lists. Therefore, we need to 
exclude non-empty lists to have a similar setting as in the original paper.

In the case of Proposition 1, we need to show that every list contained in
the result of \<open>candidate (@) (map wrap [0..<n + 1])\<close> is non-empty.
The idea is to interpret empty lists by the value \<open>Zero\<close> and non-empty
lists by the value \<open>One\<close>, and to apply the assumptions.
\<close>

lemma non_empty_candidate_results:
  assumes "\<And> (f :: three \<Rightarrow> three \<Rightarrow> three) (xs :: three list). 
             \<lbrakk> associative f ; xs \<noteq> [] \<rbrakk>  \<Longrightarrow> candidate f xs = scanl1 f xs"
      and "js \<in> set (candidate (@) (map wrap [0..<n + 1]))"
  shows   "js \<noteq> []"
proof -
  \<comment> \<open>We define a mapping of lists to values of @{text three} as explained\<close>
  \<comment> \<open>above, and a function which behaves like @{text @} on values of\<close>
  \<comment> \<open>@{text three}.\<close>
  let ?h = "\<lambda>xs. case xs of [] \<Rightarrow> Zero | (_#_) \<Rightarrow> One"
  let ?g = "\<lambda>x y. if (x = One \<or> y = One) then One else Zero"
  have g_assoc: "associative ?g" unfolding associative_def by auto

  \<comment> \<open>Our defined functions fulfill the requirements of the free theorem of\<close>
  \<comment> \<open>@{text candidate}, that is:\<close>
  have req_free_theorem: "\<And>xs ys. ?h (xs @ ys) = ?g (?h xs) (?h ys)"
    proof -
      fix xs ys
      show "?h (xs @ ys) = ?g (?h xs) (?h ys)"
        by (cases xs, simp_all, cases ys, simp_all)
    qed

  \<comment> \<open>Before applying the assumptions, we show that @{text candidate}'s\<close>
  \<comment> \<open>counterpart @{text scanl1}, applied to a non-empty list, returns only\<close>
  \<comment> \<open>a repetition of the value @{text One}.\<close>
  have set_scanl1_is_One: 
    "set (scanl1 ?g (map ?h (map wrap [0..<n + 1]))) = {One}"
    proof -
      have const_One: "map (\<lambda>x. One) [0..<n + 1] = replicate (n + 1) One"
        proof (induct n)
          case 0 thus ?case by simp
        next
          case (Suc n) 
          have 
          "map (\<lambda>x. One) [0..<Suc n + 1]
           = map (\<lambda>x. One) ([0..<Suc n] @ [Suc n])" by simp
          also have 
          "\<dots> = map (\<lambda>x. One) [0..<Suc n] @ map (\<lambda>x. One) [Suc n]"
              by simp
          also have "\<dots> = replicate (Suc n) One @ replicate 1 One" 
              using Suc by simp
          also have "\<dots> = replicate (Suc n + 1) One" 
              using List.replicate_add 
                      [symmetric, where x=One and n="Suc n" and m=1]
              by simp
          finally show ?case .
        qed

      have foldl1_One: "\<And>xs. foldl1 ?g (One # xs) = One" 
        proof -
          fix xs
          show "foldl1 ?g (One # xs) = One" 
          proof (induct xs rule: measure_induct [where f=length])
            fix x
            assume "\<forall>y. length y < length (x::three list) 
                        \<longrightarrow> foldl1 ?g (One # y) = One"
            thus "foldl1 ?g (One # x) = One" by (cases x, auto)
          qed
        qed

      have 
      "scanl1 ?g (map ?h (map wrap [0..<n + 1]))
       = scanl1 ?g (map (?h \<circ> wrap) [0..<n + 1])" 
          using L1 [where g="?h" and f=wrap and xs="[0..<n + 1]"] by simp
      also have 
      "\<dots> = scanl1 ?g (map (\<lambda>x. One) [0..<n + 1])" by (simp add: Fun.o_def)
      also have 
      "\<dots> = scanl1 ?g (replicate (n + 1) One)" using const_One by auto
      also have 
      "\<dots> = map (\<lambda>k. foldl1 ?g (take k (replicate (n + 1) One)))
               [1..<length (replicate (n + 1) One) + 1]" by simp
      also have 
      "\<dots> = map (\<lambda>k. foldl1 ?g (take k (replicate (n + 1) One)))
               (map Suc [0..<length (replicate (n + 1) One)])" 
          using List.map_Suc_upt by simp
      also have 
      "\<dots> = map ((\<lambda>k. foldl1 ?g (take k (replicate (n + 1) One))) \<circ> Suc)
               [0..<length (replicate (n + 1) One)]" 
          using L1 by simp
      also have 
      "\<dots> = map (\<lambda>k. foldl1 ?g (replicate (min (k + 1) (n + 1)) One))
               [0..<n + 1]" using Fun.o_def by simp
      also have 
      "\<dots> = map (\<lambda>k. foldl1 ?g (One # replicate (min k n) One)) 
               [0..<n + 1]" by simp
      also have 
      "\<dots> = map (\<lambda>k. One) [0..<n + 1]" using foldl1_One by simp
      also have 
      "\<dots> = replicate (n + 1) One" using const_One by simp
      finally show ?thesis using List.set_replicate [where n="n + 1"] by simp
    qed

  \<comment> \<open>Thus, with the assumptions and the free theorem of candidate, we show\<close>
  \<comment> \<open>that results of @{text candidate}, after applying @{text h}, can only\<close>
  \<comment> \<open>have the value @{text One}.\<close>
  have 
  "scanl1 ?g (map ?h (map wrap [0..<n + 1])) 
   = candidate ?g (map ?h (map wrap [0..<n + 1]))" 
      using assms and g_assoc by auto
  also have 
  "\<dots> = map ?h (candidate (@) (map wrap [0..<n + 1]))"
      using candidate_free_theorem [symmetric, where f="(@)" and g="?g" 
      and h="?h" and zs="(map wrap [0..<n + 1])"] and req_free_theorem by auto
  finally have set_is_One: 
  "\<And>x. x \<in> set (map ?h (candidate (@) (map wrap [0..<n + 1])))
       \<Longrightarrow> x = One" 
      using set_scanl1_is_One by auto

  \<comment> \<open>Now, it is easy to conclude the thesis.\<close>
  from assms
  have "?h js \<in> ?h ` set (candidate (@) (map wrap [0..<n + 1]))" by auto
  with set_is_One have "?h js = One" by simp
  thus "js \<noteq> []" by auto
qed



text \<open>
Proposition 1 is very similar to the corresponding one shown in the original
paper except of a slight modification due to the choice of using Isabelle's
list datatype.

Strictly speaking, the requirement that \<open>xs\<close> must be non-empty in the
assumptions of Proposition 1 is not necessary, because only non-empty lists
are applied in the proof. However, the additional requirement eases the proof
obligations of the final theorem, i.e. this additions allows more (or easier)
applications of the final theorem.
\<close>

lemma Proposition_1:
  assumes "\<And> (f :: three \<Rightarrow> three \<Rightarrow> three) (xs :: three list). 
             \<lbrakk> associative f ; xs \<noteq> [] \<rbrakk>  \<Longrightarrow> candidate f xs = scanl1 f xs"
  shows "candidate (@) (map wrap [0..<n + 1]) = ups n"
proof -
  \<comment> \<open>This addition is necessary because we are using Isabelle's list datatype\<close>
  \<comment> \<open>which allows for empty lists.\<close>
  from assms and non_empty_candidate_results have non_empty_candidate: 
  "\<And>js. js \<in> set (candidate (@) (map wrap [0..<n + 1])) \<Longrightarrow> js \<noteq> []"
      by auto

  have "\<And>(f:: three \<Rightarrow> three \<Rightarrow> three) h. associative f
        \<Longrightarrow> map (foldl1 f \<circ> map h) (candidate (@) (map wrap [0..<n + 1])) 
           = scanl1 f (map h [0..<n + 1])" 
    proof -
      fix f h
      assume f_assoc: "associative (f :: three \<Rightarrow> three \<Rightarrow> three)"
      hence 
      "map (foldl1 f \<circ> map h) (candidate (@) (map wrap [0..<n + 1])) 
       = candidate f (map h [0..<n + 1])" using Lemma_3 by auto
      also have 
      "\<dots> = scanl1 f (map h [0..<n + 1])" 
          using assms [where xs="map h [0..<n + 1]"] and f_assoc by simp
      finally show 
      "map (foldl1 f \<circ> map h) (candidate (@) (map wrap [0..<n + 1]))
       = scanl1 f (map h [0..<n + 1])" .
    qed
  with Lemma_5 and non_empty_candidate show ?thesis by auto
qed





section \<open>Proving Proposition 2\<close>


text \<open>
Before proving Proposition 2, a non-trivial step of that proof is shown first.
In the original paper, the argumentation simply applies L7 and the definition
of \<open>map\<close> and \<open>[0..<k + 1]\<close>. However, since, L7 requires that
\<open>k\<close> must be less than \<open>length [0..<length xs]\<close> and this does
not simply follow for the bound occurrence of \<open>k\<close>, a more complicated
proof is necessary. Here, it is shown based on Lemma 2.
\<close>
      
lemma Prop_2_step_L7:
  "map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) [0..<length xs]
   = map (\<lambda>k. foldl1 g (take (k + 1) xs)) [0..<length xs]" 
proof -   
  have P1: 
  "length (map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) [0..<length xs])
   = length (map (\<lambda>k. foldl1 g (take (k + 1) xs)) [0..<length xs])" 
      by (simp add: L2)
      
  have P2: 
  "\<And>k. k < length (map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) 
                       [0..<length xs]) 
       \<Longrightarrow> (map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) [0..<length xs]) ! k
          = (map (\<lambda>k. foldl1 g (take (k + 1) xs)) [0..<length xs]) ! k"
    proof -
      fix k
      assume k_length: 
        "k < length (map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1]))
                         [0..<length xs])"
      hence k_length': "k < length xs" by (simp add: L2)
        
      have 
      "(map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) [0..<length xs]) ! k 
       = (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) ([0..<length xs] ! k)"
          using L6 and k_length by (simp add: L2)
      also have 
      "\<dots> = foldl1 g (map (nth xs) [0..<k + 1])" 
          using k_length' by (auto simp: L2)
      also have 
      "\<dots> = foldl1 g (take (k + 1) xs)" 
          using L7 [where k=k and xs=xs] and k_length' by simp
      also have 
      "\<dots> = (\<lambda>k. foldl1 g (take (k + 1) xs)) ([0..<length xs] ! k)" 
          using k_length' by (auto simp: L2)
      also have 
      "\<dots> = (map (\<lambda>k. foldl1 g (take (k + 1) xs)) [0..<length xs]) ! k" 
          using L6 [symmetric] and k_length by (simp add: L2)
      finally show
      "(map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) [0..<length xs]) ! k 
       = (map (\<lambda>k. foldl1 g (take (k + 1) xs)) [0..<length xs]) ! k" .
    qed
      
  from P1 P2 and Lemma_2 show ?thesis by blast
qed



text \<open>
Compared to the original paper, here, Proposition 2 has the additional 
assumption that \<open>xs\<close> is non-empty. The proof, however, is identical
to the the one given in the original paper, except for the non-trivial step
shown before.
\<close>

lemma Proposition_2:
  assumes A1: "\<And> n. candidate (@) (map wrap [0..<n + 1]) = ups n"
      and A2: "associative g"
      and A3: "xs \<noteq> []"
  shows "candidate g xs = scanl1 g xs"
proof -
  \<comment> \<open>First, based on Lemma 2, we show that\<close>
  \<comment> \<open>@{term "xs = map (nth xs) [0..<length xs]"}\<close>
  \<comment> \<open>by the following facts P1 and P2.\<close>

  have P1: "length xs = length (map (nth xs) [0..<length xs])" 
    proof -
      have 
      "length xs 
       = length [0..<length xs]" by simp
      also have 
      "\<dots> = length (map (nth xs) [0..<length xs])"
          using L2 [symmetric] by auto
      finally show ?thesis .
    qed

  have P2: "\<And>k. k < length xs \<Longrightarrow> xs ! k = (map (nth xs) [0..<length xs]) ! k"
    proof -
      fix k
      assume k_length_xs: "k < length xs"
      hence k_length_xs': "k < length [0..<length xs]" by simp
      have 
      "xs ! k = nth xs ([0..<length xs] ! k)" 
          using k_length_xs by simp
      also have 
      "\<dots> = (map (nth xs) [0..<length xs]) ! k" 
          using L6 [symmetric] and k_length_xs' by auto
      finally show "xs ! k = (map (nth xs) [0..<length xs]) ! k" .
    qed

  from P1 P2 and Lemma_2 have "xs = map (nth xs) [0..<length xs]" by blast
  
  \<comment> \<open>Thus, with some rewriting, we show the thesis.\<close>
  hence 
  "candidate g xs 
   = candidate g (map (nth xs) [0..<length xs])" by simp
  also have 
  "\<dots> = map (foldl1 g \<circ> map (nth xs))
           (candidate (@) (map wrap [0..<length xs]))"
      using Lemma_3 [symmetric, where h="nth xs" and n="length xs - 1"] 
      and A2 and A3 by auto
  also have 
  "\<dots> = map (foldl1 g \<circ> map (nth xs)) (ups (length xs - 1))"
      using A1 [where n="length xs - 1"] and A3 by simp
  also have 
  "\<dots> = map (foldl1 g \<circ> map (nth xs)) (map (\<lambda>k. [0..<k + 1]) [0..<length xs])"
      using A3 by simp
  also have 
  "\<dots> = map (\<lambda>k. foldl1 g (map (nth xs) [0..<k + 1])) [0..<length xs]"
      using L1 [where g="foldl1 g \<circ> map (nth xs)" and f="(\<lambda>k. [0..<k + 1])"] 
      by (simp add: Fun.o_def)
  also have 
  "\<dots> = map (\<lambda>k. foldl1 g (take (k + 1) xs)) [0..<length xs]" 
      using Prop_2_step_L7 by simp
  also have
  "\<dots> = map (\<lambda>k. foldl1 g (take k xs)) (map (\<lambda>k. k + 1) [0..<length xs])"
      by (simp add: L1)
  also have
  "\<dots> = map (\<lambda>k. foldl1 g (take k xs)) [1..<length xs + 1]"
      using List.map_Suc_upt by simp
  also have 
  "\<dots> = scanl1 g xs" by simp
  finally show ?thesis .
qed




section \<open>The Final Result\<close>

text \<open>
Finally, we the main result follows directly from Proposition 1 and 
Proposition 2.
\<close>

theorem The_0_1_2_Principle:
  assumes "\<And> (f :: three \<Rightarrow> three \<Rightarrow> three) (xs :: three list). 
             \<lbrakk> associative f ; xs \<noteq> [] \<rbrakk> \<Longrightarrow> candidate f xs = scanl1 f xs"
      and "associative g"
      and "ys \<noteq> []"
  shows "candidate g ys = scanl1 g ys"
using Proposition_1 Proposition_2 and assms by blast





text \<open>
\section*{Acknowledgments}

I thank Janis Voigtl\"ander for sharing a draft of his paper before its
publication with me.

\<close>



(*<*)
end
(*>*)

