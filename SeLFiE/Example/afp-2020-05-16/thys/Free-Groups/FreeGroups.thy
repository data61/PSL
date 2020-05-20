section \<open>The Free Group\<close>

theory "FreeGroups"
imports
   "HOL-Algebra.Group"
   Cancelation
   Generators
begin

text \<open>
Based on the work in @{theory "Free-Groups.Cancelation"}, the free group is now easily defined
over the set of fully canceled words with the corresponding operations.
\<close>

subsection \<open>Inversion\<close>

text \<open>
To define the inverse of a word, we first create a helper function that inverts
a single generator, and show that it is self-inverse.
\<close>

definition inv1 :: "'a g_i \<Rightarrow> 'a g_i"
 where "inv1 = apfst Not"

lemma inv1_inv1: "inv1 \<circ> inv1 = id"
  by (simp add: fun_eq_iff comp_def inv1_def)

lemmas inv1_inv1_simp [simp] = inv1_inv1[unfolded id_def]

lemma snd_inv1: "snd \<circ> inv1 = snd"
  by(simp add: fun_eq_iff comp_def inv1_def)

text \<open>
The inverse of a word is obtained by reversing the order of the generators and
inverting each generator using @{term inv1}. Some properties of @{term inv_fg}
are noted.
\<close>

definition inv_fg :: "'a word_g_i \<Rightarrow> 'a word_g_i"
 where "inv_fg l = rev (map inv1 l)"

lemma cancelling_inf[simp]: "canceling (inv1 a) (inv1 b) = canceling a b"
  by(simp add: canceling_def inv1_def)

lemma inv_idemp: "inv_fg (inv_fg l) = l"
  by (auto simp add:inv_fg_def rev_map)

lemma inv_fg_cancel: "normalize (l @ inv_fg l) = []"
proof(induct l rule:rev_induct)
  case Nil thus ?case
    by (auto simp add: inv_fg_def)
next
  case (snoc x xs)
  have "canceling x (inv1 x)" by (simp add:inv1_def canceling_def)
  moreover
  let ?i = "length xs"
  have "Suc ?i < length xs + 1 + 1 + length xs"
    by auto
  moreover
  have "inv_fg (xs @ [x]) = [inv1 x] @ inv_fg xs"
    by (auto simp add:inv_fg_def)
  ultimately
  have "cancels_to_1_at ?i (xs @ [x] @ (inv_fg (xs @ [x]))) (xs @ inv_fg xs)"
    by (auto simp add:cancels_to_1_at_def cancel_at_def nth_append)
  hence "cancels_to_1 (xs @ [x] @ (inv_fg (xs @ [x]))) (xs @ inv_fg xs)"
    by (auto simp add: cancels_to_1_def)
  hence "cancels_to (xs @ [x] @ (inv_fg (xs @ [x]))) (xs @ inv_fg xs)"
    by (auto simp add:cancels_to_def)
  with \<open>normalize (xs @ (inv_fg xs)) = []\<close>
  show "normalize ((xs @ [x]) @ (inv_fg (xs @ [x]))) = []"
    by auto
qed

lemma inv_fg_cancel2: "normalize (inv_fg l @ l) = []"
proof-
  have "normalize (inv_fg l @ inv_fg (inv_fg l)) = []" by (rule inv_fg_cancel)
  thus "normalize (inv_fg l @ l) = []" by (simp add: inv_idemp)
qed

lemma canceled_rev:
  assumes "canceled l"
  shows "canceled (rev l)"
proof(rule ccontr)
  assume "\<not>canceled (rev l)"
  hence "Domainp cancels_to_1 (rev l)" by (simp add: canceled_def)
  then obtain l' where "cancels_to_1 (rev l) l'" by auto
  then obtain i where "cancels_to_1_at i (rev l) l'" by (auto simp add:cancels_to_1_def)
  hence "Suc i < length (rev l)"
    and "canceling (rev l ! i) (rev l ! Suc i)"
    by (auto simp add:cancels_to_1_at_def)
  let ?x = "length l - i - 2"
  from \<open>Suc i < length (rev l)\<close>
  have "Suc ?x < length l" by auto
  moreover
  from \<open>Suc i < length (rev l)\<close>
  have "i < length l" and "length l - Suc i = Suc(length l - Suc (Suc i))" by auto
  hence "rev l ! i = l ! Suc ?x" and "rev l ! Suc i = l ! ?x"
    by (auto simp add: rev_nth map_nth)
  with \<open>canceling (rev l ! i) (rev l ! Suc i)\<close>
  have "canceling (l ! Suc ?x) (l ! ?x)" by auto
  hence "canceling (l ! ?x) (l ! Suc ?x)" by (rule cancel_sym)
  hence "canceling (l ! ?x) (l ! Suc ?x)" by simp
  ultimately
  have "cancels_to_1_at ?x l (cancel_at ?x l)" 
    by (auto simp add:cancels_to_1_at_def)
  hence "cancels_to_1 l (cancel_at ?x l)"
    by (auto simp add:cancels_to_1_def)
  hence "\<not>canceled l"
    by (auto simp add:canceled_def)
  with \<open>canceled l\<close> show False by contradiction
qed

lemma inv_fg_closure1:
  assumes "canceled l"
  shows "canceled (inv_fg l)"
unfolding inv_fg_def and inv1_def and apfst_def
proof-
  have "inj Not" by (auto intro:injI)
  moreover
  have "inj_on id (snd ` set l)" by auto
  ultimately
  have "canceled (map (map_prod Not id) l)" 
    using \<open>canceled l\<close> 
    by -(rule rename_gens_canceled)
  thus "canceled (rev (map (map_prod Not id) l))" by (rule canceled_rev)
qed

lemma inv_fg_closure2:
  "l \<in> lists (UNIV \<times> gens) \<Longrightarrow> inv_fg l \<in> lists (UNIV \<times> gens)"
  by (auto iff:lists_eq_set simp add:inv1_def inv_fg_def)

subsection \<open>The definition\<close>

text \<open>
Finally, we can define the Free Group over a set of generators, and show that it
is indeed a group.
\<close>

definition free_group :: "'a set => ((bool * 'a) list) monoid" ("\<F>\<index>")
where 
  "\<F>\<^bsub>gens\<^esub> \<equiv> \<lparr>
     carrier = {l\<in>lists (UNIV \<times> gens). canceled l },
     mult = \<lambda> x y. normalize (x @ y),
     one = []
  \<rparr>"


lemma occuring_gens_in_element:
  "x \<in> carrier \<F>\<^bsub>gens\<^esub> \<Longrightarrow> x \<in> lists (UNIV \<times> gens)"
by(auto simp add:free_group_def)

theorem free_group_is_group: "group \<F>\<^bsub>gens\<^esub>"
proof
  fix x y
  assume "x \<in> carrier \<F>\<^bsub>gens\<^esub>" hence x: "x \<in> lists (UNIV \<times> gens)" by
    (rule occuring_gens_in_element)
  assume "y \<in> carrier \<F>\<^bsub>gens\<^esub>" hence y: "y \<in> lists (UNIV \<times> gens)" by
    (rule occuring_gens_in_element)
  from x and y
  have "x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> y \<in> lists (UNIV \<times> gens)"
    by (auto intro!: normalize_preserves_generators simp add:free_group_def append_in_lists_conv)
  thus "x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> y \<in> carrier \<F>\<^bsub>gens\<^esub>"
    by (auto simp add:free_group_def)
next
  fix x y z
  have "cancels_to (x @ y) (normalize (x @ (y::'a word_g_i)))"
   and "cancels_to z (z::'a word_g_i)"
    by auto
  hence "normalize (normalize (x @ y) @ z) = normalize ((x @ y) @ z)"
    by (rule normalize_append_cancel_to[THEN sym])
  also
  have "\<dots> = normalize (x @ (y @ z))" by auto
  also
  have "cancels_to (y @ z) (normalize (y @ (z::'a word_g_i)))"
   and "cancels_to x (x::'a word_g_i)"
    by auto
  hence "normalize (x @ (y @ z)) = normalize (x @ normalize (y @ z))"
    by -(rule normalize_append_cancel_to)
  finally
  show "x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> y \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> z =
        x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> (y \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> z)"
    by (auto simp add:free_group_def)
next
  show "\<one>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> \<in> carrier \<F>\<^bsub>gens\<^esub>"
    by (auto simp add:free_group_def)
next
  fix x
  assume "x \<in> carrier \<F>\<^bsub>gens\<^esub>"
  thus "\<one>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> x = x"
    by (auto simp add:free_group_def)
next
  fix x
  assume "x \<in> carrier \<F>\<^bsub>gens\<^esub>"
  thus "x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> \<one>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> = x"
    by (auto simp add:free_group_def)
next
  show "carrier \<F>\<^bsub>gens\<^esub> \<subseteq> Units \<F>\<^bsub>gens\<^esub>"
  proof (simp add:free_group_def Units_def, rule subsetI)
    fix x :: "'a word_g_i"
    let ?x' = "inv_fg x"
    assume "x \<in> {y\<in>lists(UNIV\<times>gens). canceled y}"
    hence "?x' \<in> lists(UNIV\<times>gens) \<and> canceled ?x'"
      by (auto elim:inv_fg_closure1 simp add:inv_fg_closure2)
    moreover
    have "normalize (?x' @ x) = []"
     and "normalize (x @ ?x') = []"
      by (auto simp add:inv_fg_cancel inv_fg_cancel2)
    ultimately
    have "\<exists>y. y \<in> lists (UNIV \<times> gens) \<and>
                  canceled y \<and>
                  normalize (y @ x) = [] \<and> normalize (x @ y) = []"
      by auto
    with \<open>x \<in> {y\<in>lists(UNIV\<times>gens). canceled y}\<close>
    show "x \<in> {y \<in> lists (UNIV \<times> gens).  canceled y  \<and>
          (\<exists>x. x \<in> lists (UNIV \<times> gens) \<and>
                  canceled x \<and>
                  normalize (x @ y) = [] \<and> normalize (y @ x) = [])}"
      by auto
  qed
qed

lemma inv_is_inv_fg[simp]:
  "x \<in> carrier \<F>\<^bsub>gens\<^esub> \<Longrightarrow> inv\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> x = inv_fg x"
by (rule group.inv_equality,auto simp add:free_group_is_group,auto simp add: free_group_def inv_fg_cancel inv_fg_cancel2 inv_fg_closure1 inv_fg_closure2)


subsection \<open>The universal property\<close>

text \<open>Free Groups are important due to their universal property: Every map of
the set of generators to another group can be extended uniquely to an
homomorphism from the Free Group.\<close>

definition insert ("\<iota>")
  where "\<iota> g = [(False, g)]"

lemma insert_closed:
  "g \<in> gens \<Longrightarrow> \<iota> g \<in> carrier \<F>\<^bsub>gens\<^esub>"
  by (auto simp add:insert_def free_group_def)

definition (in group) lift_gi
  where "lift_gi f gi = (if fst gi then inv (f (snd gi)) else f (snd gi))"

lemma (in group) lift_gi_closed:
  assumes cl: "f \<in> gens \<rightarrow> carrier G"
      and "snd gi \<in> gens"
  shows "lift_gi f gi \<in> carrier G"
using assms by (auto simp add:lift_gi_def)

definition (in group) lift
  where "lift f w = m_concat (map (lift_gi f) w)"

lemma (in group) lift_nil[simp]: "lift f [] = \<one>"
 by (auto simp add:lift_def)

lemma (in group) lift_closed[simp]:
  assumes cl: "f \<in> gens \<rightarrow> carrier G"
      and "x \<in> lists (UNIV \<times> gens)"
  shows "lift f x \<in> carrier G"
proof-
  have "set (map (lift_gi f) x) \<subseteq> carrier G"
    using \<open>x \<in> lists (UNIV \<times> gens)\<close>
    by (auto simp add:lift_gi_closed[OF cl])
  thus "lift f x \<in> carrier G"
    by (auto simp add:lift_def)
qed

lemma (in group) lift_append[simp]:
  assumes cl: "f \<in> gens \<rightarrow> carrier G"
      and "x \<in> lists (UNIV \<times> gens)"
      and "y \<in> lists (UNIV \<times> gens)"
  shows "lift f (x @ y) = lift f x \<otimes> lift f y"
proof-
  from \<open>x \<in> lists (UNIV \<times> gens)\<close>
  have "set (map snd x) \<subseteq> gens" by auto
  hence "set (map (lift_gi f) x) \<subseteq> carrier G"
    by (induct x)(auto simp add:lift_gi_closed[OF cl])
  moreover
  from \<open>y \<in> lists (UNIV \<times> gens)\<close>
  have "set (map snd y) \<subseteq> gens" by auto
  hence "set (map (lift_gi f) y) \<subseteq> carrier G"
    by (induct y)(auto simp add:lift_gi_closed[OF cl])
  ultimately
  show "lift f (x @ y) = lift f x \<otimes> lift f y"
    by (auto simp add:lift_def m_assoc simp del:set_map foldr_append)
qed

lemma (in group) lift_cancels_to:
  assumes "cancels_to x y"
      and "x \<in> lists (UNIV \<times> gens)"
      and cl: "f \<in> gens \<rightarrow> carrier G"
  shows "lift f x = lift f y"
using assms
unfolding cancels_to_def
proof(induct rule:rtranclp_induct)
  case (step y z)
    from \<open>cancels_to_1\<^sup>*\<^sup>* x y\<close>
    and \<open>x \<in> lists (UNIV \<times> gens)\<close>
    have "y \<in> lists (UNIV \<times> gens)"
      by -(rule cancels_to_preserves_generators, simp add:cancels_to_def)
    hence "lift f x = lift f y"
      using step by auto
    also
    from \<open>cancels_to_1 y z\<close>
    obtain ys1 y1 y2 ys2
      where y: "y = ys1 @ y1 # y2 # ys2"
      and "z = ys1 @ ys2"
      and "canceling y1 y2"
    by (rule cancels_to_1_unfold)
    have "lift f y  = lift f (ys1 @ [y1] @ [y2] @ ys2)"
      using y by simp
    also
    from y and cl and \<open>y \<in> lists (UNIV \<times> gens)\<close>
    have "lift f (ys1 @ [y1] @ [y2] @ ys2)
        = lift f ys1 \<otimes> (lift f [y1] \<otimes> lift f [y2]) \<otimes> lift f ys2"
      by (auto intro:lift_append[OF cl] simp del: append_Cons simp add:m_assoc iff:lists_eq_set)
    also
    from cl[THEN funcset_image]
     and y and \<open>y \<in> lists (UNIV \<times> gens)\<close>
     and \<open>canceling y1 y2\<close>
    have "(lift f [y1] \<otimes> lift f [y2]) = \<one>"
      by (auto simp add:lift_def lift_gi_def canceling_def iff:lists_eq_set)
    hence "lift f ys1 \<otimes> (lift f [y1] \<otimes> lift f [y2]) \<otimes> lift f ys2
           = lift f ys1 \<otimes> \<one> \<otimes> lift f ys2"
      by simp
    also
    from y and \<open>y \<in> lists (UNIV \<times> gens)\<close>
     and cl
     have "lift f ys1 \<otimes> \<one> \<otimes> lift f ys2 = lift f (ys1 @ ys2)"
      by (auto intro:lift_append iff:lists_eq_set)
    also
    from \<open>z = ys1 @ ys2\<close>
    have "lift f (ys1 @ ys2) = lift f z" by simp
    finally show "lift f x = lift f z" .
qed auto

lemma (in group) lift_is_hom:
  assumes cl: "f \<in> gens \<rightarrow> carrier G"
  shows "lift f \<in> hom \<F>\<^bsub>gens\<^esub> G"
proof-
  {
    fix x
    assume "x \<in> carrier \<F>\<^bsub>gens\<^esub>"
    hence "x \<in> lists (UNIV \<times> gens)"
      unfolding free_group_def by simp
    hence "lift f x \<in> carrier G"
     by (induct x, auto simp add:lift_def lift_gi_closed[OF cl])
  } 
  moreover
  { fix x
    assume "x \<in> carrier \<F>\<^bsub>gens\<^esub>"
    fix y
    assume "y \<in> carrier \<F>\<^bsub>gens\<^esub>"

    from \<open>x \<in> carrier \<F>\<^bsub>gens\<^esub>\<close> and \<open>y \<in> carrier \<F>\<^bsub>gens\<^esub>\<close>
    have "x \<in> lists (UNIV \<times> gens)" and "y \<in> lists (UNIV \<times> gens)"
      by (auto simp add:free_group_def)

    have "cancels_to (x @ y) (normalize (x @ y))" by simp
    from \<open>x \<in> lists (UNIV \<times> gens)\<close> and \<open>y \<in> lists (UNIV \<times> gens)\<close>
     and lift_cancels_to[THEN sym, OF \<open>cancels_to (x @ y) (normalize (x @ y))\<close>] and cl
    have "lift f (x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> y) = lift f (x @ y)"
      by (auto simp add:free_group_def iff:lists_eq_set)
    also
    from \<open>x \<in> lists (UNIV \<times> gens)\<close> and \<open>y \<in> lists (UNIV \<times> gens)\<close> and cl
    have "lift f (x @ y) = lift f x \<otimes> lift f y"
      by simp
    finally
    have "lift f (x \<otimes>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> y) = lift f x \<otimes> lift f y" .
  }
  ultimately
  show "lift f \<in> hom \<F>\<^bsub>gens\<^esub> G"
    by auto
qed

lemma gens_span_free_group:
shows "\<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> = carrier \<F>\<^bsub>gens\<^esub>"
proof
  interpret group "\<F>\<^bsub>gens\<^esub>" by (rule free_group_is_group)
  show "\<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> \<subseteq> carrier \<F>\<^bsub>gens\<^esub>"
  by(rule gen_span_closed, auto simp add:insert_def free_group_def)

  show "carrier \<F>\<^bsub>gens\<^esub>  \<subseteq> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
  proof
    fix x
    show "x \<in> carrier \<F>\<^bsub>gens\<^esub> \<Longrightarrow> x \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
    proof(induct x)
    case Nil
      have "one \<F>\<^bsub>gens\<^esub> \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
        by simp
      thus "[] \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
        by (simp add:free_group_def)
    next
    case (Cons a x)
      from \<open>a # x \<in> carrier \<F>\<^bsub>gens\<^esub>\<close>
      have "x \<in> carrier \<F>\<^bsub>gens\<^esub>"
        by (auto intro:cons_canceled simp add:free_group_def)
      hence "x \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
        using Cons by simp
      moreover

      from \<open>a # x \<in> carrier \<F>\<^bsub>gens\<^esub>\<close>
      have "snd a \<in> gens"
        by (auto simp add:free_group_def)
      hence isa: "\<iota> (snd a) \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
        by (auto simp add:insert_def intro:gen_gens)
      have "[a] \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
      proof(cases "fst a")
        case False
          hence "[a] = \<iota> (snd a)" by (cases a, auto simp add:insert_def)
           with isa show "[a] \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>" by simp
       next
        case True
          from \<open>snd a \<in> gens\<close>
          have "\<iota> (snd a) \<in> carrier \<F>\<^bsub>gens\<^esub>" 
            by (auto simp add:free_group_def insert_def)
          with True
          have "[a] = inv\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> (\<iota> (snd a))"
            by (cases a, auto simp add:insert_def inv_fg_def inv1_def)
          moreover
          from isa
          have "inv\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub> (\<iota> (snd a)) \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
            by (auto intro:gen_inv)
          ultimately
          show "[a] \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
            by simp
      qed
      ultimately 
      have "mult \<F>\<^bsub>gens\<^esub> [a] x \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>"
        by (auto intro:gen_mult)
      with
      \<open>a # x \<in> carrier \<F>\<^bsub>gens\<^esub>\<close>
      show "a # x \<in> \<langle>\<iota> ` gens\<rangle>\<^bsub>\<F>\<^bsub>gens\<^esub>\<^esub>" by (simp add:free_group_def)
    qed
  qed
qed

lemma (in group) lift_is_unique:
  assumes "group G"
  and cl: "f \<in> gens \<rightarrow> carrier G"
  and "h \<in> hom \<F>\<^bsub>gens\<^esub> G"
  and "\<forall> g \<in> gens. h (\<iota> g) = f g"
  shows "\<forall>x \<in> carrier \<F>\<^bsub>gens\<^esub>. h x = lift f x"
unfolding gens_span_free_group[THEN sym]
proof(rule hom_unique_on_span[of "\<F>\<^bsub>gens\<^esub>" G])
  show "group \<F>\<^bsub>gens\<^esub>" by (rule free_group_is_group)
next
  show "group G" by fact
next
  show "\<iota> ` gens \<subseteq> carrier \<F>\<^bsub>gens\<^esub>"
    by(auto intro:insert_closed)
next
  show "h \<in> hom \<F>\<^bsub>gens\<^esub> G" by fact
next
  show "lift f \<in> hom \<F>\<^bsub>gens\<^esub> G" by (rule lift_is_hom[OF cl])
next
  from \<open>\<forall>g\<in> gens. h (\<iota> g) = f g\<close> and cl[THEN funcset_image]
  show "\<forall>g\<in> \<iota> ` gens. h g = lift f g"
    by(auto simp add:insert_def lift_def lift_gi_def)
qed

end
