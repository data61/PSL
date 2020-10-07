section \<open>Isomorphisms of Free Groups\<close>

theory "Isomorphisms"
imports
   UnitGroup
   "HOL-Algebra.IntRing"
   FreeGroups
   C2
   "HOL-Cardinals.Cardinal_Order_Relation"
begin

subsection \<open>The Free Group over the empty set\<close>

text \<open>The Free Group over an empty set of generators is isomorphic to the trivial
group.\<close>

lemma free_group_over_empty_set: "\<exists>h. h \<in> iso \<F>\<^bsub>{}\<^esub> unit_group"
proof(rule group.unit_group_unique)
  show "group \<F>\<^bsub>{}\<^esub>" by (rule free_group_is_group)
next
  have "carrier \<F>\<^bsub>{}::'a set\<^esub> = {[]}"
    by (auto simp add:free_group_def)
  thus "card (carrier \<F>\<^bsub>{}::'a set\<^esub>) = 1"
    by simp
qed

subsection \<open>The Free Group over one generator\<close>

text \<open>The Free Group over one generator is isomorphic to the free abelian group
over one element, also known as the integers.\<close>

abbreviation "int_group"
  where "int_group \<equiv> \<lparr> carrier = carrier \<Z>, monoid.mult = (+), one = 0::int \<rparr>"

lemma replicate_set_eq[simp]: "\<forall>x \<in> set xs. x = y \<Longrightarrow> xs = replicate (length xs) y"
  by(induct xs)auto

lemma int_group_gen_by_one: "\<langle>{1}\<rangle>\<^bsub>int_group\<^esub> = carrier int_group"
proof
  show "\<langle>{1}\<rangle>\<^bsub>int_group\<^esub> \<subseteq> carrier int_group"
    by auto
  show "carrier int_group \<subseteq> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
  proof
    interpret int: group int_group
      using int.a_group by auto
    fix x
    have plus1: "1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (auto intro:gen_span.gen_gens)
    hence "inv\<^bsub>int_group\<^esub> 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (auto intro:gen_span.gen_inv)
    moreover
    have "-1 = inv\<^bsub>int_group\<^esub> 1" 
      by (rule sym, rule int.inv_equality) simp_all
    ultimately
    have minus1: "-1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (simp)

    show "x \<in> \<langle>{1::int}\<rangle>\<^bsub>int_group\<^esub>" (*
    It does not work directly, unfortunately:
    apply(induct x rule:int_induct[of _ "0::int"])
    apply (auto simp add: int_arith_rules intro:gen_span.intros[of int_group])
    *)
    proof(induct x rule:int_induct[of _ "0::int"])
    case base
      have "\<one>\<^bsub>int_group\<^esub> \<in> \<langle>{1::int}\<rangle>\<^bsub>int_group\<^esub>"
        by (rule gen_span.gen_one)
      thus"0 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
        by simp
    next
    case (step1 i)
      from \<open>i \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>\<close> and plus1
      have "i \<otimes>\<^bsub>int_group\<^esub> 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" 
        by (rule gen_span.gen_mult)
      thus "i + 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" by simp
    next
    case (step2 i)
      from \<open>i \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>\<close> and minus1
      have "i \<otimes>\<^bsub>int_group\<^esub> -1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" 
        by (rule gen_span.gen_mult)
      thus "i - 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
        by simp
    qed
  qed
qed

lemma free_group_over_one_gen: "\<exists>h. h \<in> iso \<F>\<^bsub>{()}\<^esub> int_group"
proof-
  interpret int: group int_group 
    using int.a_group by auto
  define f :: "unit \<Rightarrow> int" where "f x = 1" for x
  have "f \<in> {()} \<rightarrow> carrier int_group"
    by auto
  hence "int.lift f \<in> hom \<F>\<^bsub>{()}\<^esub> int_group"
    by (rule int.lift_is_hom)
  then
  interpret hom: group_hom "\<F>\<^bsub>{()}\<^esub>" int_group "int.lift f"
    unfolding group_hom_def group_hom_axioms_def
    using int.a_group by(auto intro: free_group_is_group)
    
  { (* This shows injectiveness of the given map *)
    fix x
    assume "x \<in> carrier \<F>\<^bsub>{()}\<^esub>"
    hence "canceled x" by (auto simp add:free_group_def)
    assume "int.lift f x = (0::int)"
    have "x = []" 
    proof(rule ccontr)
      assume "x \<noteq> []"
      then obtain a and xs where "x = a # xs" by (cases x, auto)
      hence "length (takeWhile (\<lambda>y. y = a) x) > 0" by auto
      then obtain i where i: "length (takeWhile (\<lambda>y. y = a) x) = Suc i" 
        by (cases "length (takeWhile (\<lambda>y. y = a) x)", auto)
      have "Suc i \<ge> length x"
      proof(rule ccontr)
        assume "\<not> length x \<le> Suc i"
        hence "length (takeWhile (\<lambda>y. y = a) x) < length x" using i by simp
        hence "\<not> (\<lambda>y. y = a) (x ! length (takeWhile (\<lambda>y. y = a) x))"
          by (rule nth_length_takeWhile)
        hence "\<not> (\<lambda>y. y = a) (x ! Suc i)" using i by simp
        hence "fst (x ! Suc i) \<noteq> fst a" by (cases "x ! Suc i", cases "a", auto)
        moreover
        {
          have "takeWhile (\<lambda>y. y = a) x ! i = x ! i"
            using i by (auto intro: takeWhile_nth)
          moreover
          have "(takeWhile (\<lambda>y. y = a) x) ! i \<in> set (takeWhile (\<lambda>y. y = a) x)"
            using i by auto
          ultimately
          have "(\<lambda>y. y = a) (x ! i)"
            by (auto dest:set_takeWhileD)
        }
        hence "fst (x ! i) = fst a" by auto
        moreover
        have "snd (x ! i) = snd (x ! Suc i)" by simp
        ultimately
        have "canceling (x ! i) (x ! Suc i)" unfolding canceling_def by auto
        hence "cancels_to_1_at i x (cancel_at i x)"
          using \<open>\<not> length x \<le> Suc i\<close> unfolding cancels_to_1_at_def 
          by (auto simp add:length_takeWhile_le)
        hence "cancels_to_1 x (cancel_at i x)" unfolding cancels_to_1_def by auto
        hence "\<not> canceled x" unfolding canceled_def by auto
        thus False using \<open>canceled x\<close> by contradiction
      qed
      hence "length (takeWhile (\<lambda>y. y = a) x) = length x"
        using i[THEN sym] by (auto dest:le_antisym simp add:length_takeWhile_le)
      hence "takeWhile (\<lambda>y. y = a) x = x"
        by (subst takeWhile_eq_take, simp)
      moreover
      have "\<forall>y \<in> set (takeWhile (\<lambda>y. y = a) x). y = a"
        by (auto dest: set_takeWhileD)
      ultimately
      have "\<forall>y \<in> set x. y = a" by auto
      hence "x = replicate (length x) a" by simp
      hence "int.lift f x = int.lift f (replicate (length x) a)" by simp
      also have "... = pow int_group (int.lift_gi f a) (length x)"
        apply (induct x)
        using local.int.nat_pow_Suc local.int.nat_pow_0
         apply (auto simp: int.lift_def [simplified])
        done
      also have "... = (int.lift_gi f a) * int (length x)"
        apply (induct x)
        using local.int.nat_pow_Suc local.int.nat_pow_0
        by (auto simp: int_distrib)
      finally have "\<dots> = 0" using \<open>int.lift f x = 0\<close> by simp
      hence "nat (abs (group.lift_gi int_group f a * int (length x))) = 0" by simp
      hence "nat (abs (group.lift_gi int_group f a)) * length x = 0" by simp
      hence "nat (abs (group.lift_gi int_group f a)) = 0"
        using \<open>x \<noteq> []\<close> by auto
      moreover
      have "inv\<^bsub>int_group\<^esub> 1 = -1" 
        using int.inv_equality by auto
      hence "abs (group.lift_gi int_group f a) = 1"
      using int.is_group
        by(auto simp add: group.lift_gi_def f_def)
      ultimately
      show False by simp
    qed
  }
  hence "\<forall>x\<in>carrier \<F>\<^bsub>{()}\<^esub>. int.lift f x = \<one>\<^bsub>int_group\<^esub> \<longrightarrow> x = \<one>\<^bsub>\<F>\<^bsub>{()}\<^esub>\<^esub>"
    by (auto simp add:free_group_def)
  moreover
  {
    have "carrier \<F>\<^bsub>{()}\<^esub> = \<langle>insert`{()}\<rangle>\<^bsub>\<F>\<^bsub>{()}\<^esub>\<^esub>"
      by (rule gens_span_free_group[THEN sym])
    moreover
    have "carrier int_group = \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (rule int_group_gen_by_one[THEN sym])
    moreover
    have "int.lift f ` insert ` {()} = {1}"
      by (auto simp add: int.lift_def [simplified] insert_def f_def int.lift_gi_def [simplified])
    moreover
    have  "int.lift f ` \<langle>insert`{()}\<rangle>\<^bsub>\<F>\<^bsub>{()}\<^esub>\<^esub> = \<langle>int.lift f ` (insert `{()})\<rangle>\<^bsub>int_group\<^esub>"
      by (rule hom.hom_span, auto intro:insert_closed)
    ultimately
    have "int.lift f ` carrier \<F>\<^bsub>{()}\<^esub> = carrier int_group"
      by simp
  }
  ultimately
  have "int.lift f \<in> iso \<F>\<^bsub>{()}\<^esub> int_group"
    using \<open>int.lift f \<in> hom \<F>\<^bsub>{()}\<^esub> int_group\<close>
    using hom.hom_mult int.is_group
    by (auto intro:group_isoI simp add: free_group_is_group)
  thus ?thesis by auto
qed

subsection \<open>Free Groups over isomorphic sets of generators\<close>

text \<open>Free Groups are isomorphic if their set of generators are isomorphic.\<close>

definition lift_generator_function :: "('a \<Rightarrow> 'b) \<Rightarrow> (bool \<times> 'a) list \<Rightarrow> (bool \<times> 'b) list"
where "lift_generator_function f = map (map_prod id f)"

theorem isomorphic_free_groups:
  assumes "bij_betw f gens1 gens2"
  shows "lift_generator_function f \<in> iso \<F>\<^bsub>gens1\<^esub> \<F>\<^bsub>gens2\<^esub>"
unfolding lift_generator_function_def
proof(rule group_isoI)
  show "\<forall>x\<in>carrier \<F>\<^bsub>gens1\<^esub>.
       map (map_prod id f) x = \<one>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> \<longrightarrow> x = \<one>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub>"
    by(auto simp add:free_group_def)
next
  from \<open>bij_betw f gens1 gens2\<close> have "inj_on f gens1" by (auto simp:bij_betw_def)
  show "map (map_prod id f) ` carrier \<F>\<^bsub>gens1\<^esub> = carrier \<F>\<^bsub>gens2\<^esub>"
  proof(rule Set.set_eqI,rule iffI)
    from \<open>bij_betw f gens1 gens2\<close> have "f ` gens1 = gens2" by (auto simp:bij_betw_def)
    fix x :: "(bool \<times> 'b) list"
    assume "x \<in> image (map (map_prod id f)) (carrier \<F>\<^bsub>gens1\<^esub>)"
    then obtain y :: "(bool \<times> 'a) list" where "x = map (map_prod id f) y"
                    and "y \<in> carrier \<F>\<^bsub>gens1\<^esub>" by auto
    from \<open>y \<in> carrier \<F>\<^bsub>gens1\<^esub>\<close>
    have "canceled y" and "y \<in> lists(UNIV\<times>gens1)" by (auto simp add:free_group_def)

    from \<open>y \<in> lists (UNIV\<times>gens1)\<close>
      and \<open>x = map (map_prod id f) y\<close>
      and \<open>image f gens1 = gens2\<close>
    have "x \<in> lists (UNIV\<times>gens2)"
      by (auto iff:lists_eq_set)
    moreover

    from \<open>x = map (map_prod id f) y\<close>
     and \<open>y \<in> lists (UNIV\<times>gens1)\<close>
     and \<open>canceled y\<close>
     and \<open>inj_on f gens1\<close>
    have "canceled x"
      by (auto intro!:rename_gens_canceled subset_inj_on[OF \<open>inj_on f gens1\<close>] iff:lists_eq_set)
    ultimately
    show "x \<in> carrier \<F>\<^bsub>gens2\<^esub>" by (simp add:free_group_def)
  next
    fix x
    assume "x \<in> carrier \<F>\<^bsub>gens2\<^esub>"
    hence "canceled x" and "x \<in> lists (UNIV\<times>gens2)"
      unfolding free_group_def by auto
    define y where "y = map (map_prod id (the_inv_into gens1 f)) x"
    have "map (map_prod id f) y =
          map (map_prod id f) (map (map_prod id (the_inv_into gens1 f)) x)"
      by (simp add:y_def)
    also have "\<dots> = map (map_prod id f \<circ> map_prod id (the_inv_into gens1 f)) x"
      by simp
    also have "\<dots> = map (map_prod id (f \<circ> the_inv_into gens1 f)) x"
      by auto
    also have "\<dots> = map id x"
    proof(rule map_ext, rule impI)
      fix xa :: "bool \<times> 'b"
      assume "xa \<in> set x"
      from \<open>x \<in> lists (UNIV\<times>gens2)\<close>
      have "set (map snd x) \<subseteq> gens2"  by auto
      hence "snd ` set x \<subseteq> gens2" by (simp add: set_map)
      with \<open>xa \<in> set x\<close> have "snd xa \<in> gens2" by auto
      with \<open>bij_betw f gens1 gens2\<close> have "snd xa \<in> f`gens1"
        by (auto simp add: bij_betw_def)

      have "map_prod id (f \<circ> the_inv_into gens1 f) xa
            = map_prod id (f \<circ> the_inv_into gens1 f) (fst xa, snd xa)" by simp
      also have "\<dots> = (fst xa, f (the_inv_into gens1 f (snd xa)))"
        by (auto simp del:prod.collapse)
      also
      from \<open>snd xa \<in> image f gens1\<close> and \<open>inj_on f gens1\<close>
      have "\<dots> = (fst xa, snd xa)"
        by (auto elim:f_the_inv_into_f simp del:prod.collapse)
      also have "\<dots> = id xa" by simp
      finally show "map_prod id (f \<circ> the_inv_into gens1 f) xa = id xa".
    qed
    also have "\<dots> = x" unfolding id_def by auto
    finally have "map (map_prod id f) y = x".
    moreover
    {
      from \<open>bij_betw f gens1 gens2\<close>
      have "bij_betw (the_inv_into gens1 f) gens2 gens1" by (rule bij_betw_the_inv_into)
      hence "inj_on (the_inv_into gens1 f) gens2" by (rule bij_betw_imp_inj_on)

      with \<open>canceled x\<close>      
       and \<open>x \<in> lists (UNIV\<times>gens2)\<close>
      have "canceled y"
        by (auto intro!:rename_gens_canceled[OF subset_inj_on] simp add:y_def)
      moreover
      {
        from \<open>bij_betw (the_inv_into gens1 f) gens2 gens1\<close>
         and \<open>x\<in>lists(UNIV\<times>gens2)\<close>
        have "y \<in> lists(UNIV\<times>gens1)"
          unfolding y_def and bij_betw_def
          by (auto iff:lists_eq_set dest!:subsetD)
      }
      ultimately
      have "y \<in> carrier \<F>\<^bsub>gens1\<^esub>" by (simp add:free_group_def)
    }
    ultimately
    show "x \<in> map (map_prod id f) ` carrier \<F>\<^bsub>gens1\<^esub>" by auto
  qed
next
  from \<open>bij_betw f gens1 gens2\<close> have "inj_on f gens1" by (auto simp:bij_betw_def)
  {
  fix x
  assume "x \<in> carrier \<F>\<^bsub>gens1\<^esub>"
  fix y
  assume "y \<in> carrier \<F>\<^bsub>gens1\<^esub>"

  from \<open>x \<in> carrier \<F>\<^bsub>gens1\<^esub>\<close> and \<open>y \<in> carrier \<F>\<^bsub>gens1\<^esub>\<close>
  have "x \<in> lists(UNIV\<times>gens1)" and "y \<in> lists(UNIV\<times>gens1)"
    by (auto simp add:occuring_gens_in_element)
(*  hence "occuring_generators (x@y) \<subseteq> gens1"
    by(auto simp add:occuring_generators_def)
  with `inj_on f gens1` have "inj_on f (occuring_generators (x@y))"
    by (rule subset_inj_on) *)

  have "map (map_prod id f) (x \<otimes>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub> y)
       = map (map_prod id f) (normalize (x@y))" by (simp add:free_group_def)
  also (* from `inj_on f (occuring_generators (x@y))` *)
       from \<open>x \<in> lists(UNIV\<times>gens1)\<close> and \<open>y \<in> lists(UNIV\<times>gens1)\<close>
        and \<open>inj_on f gens1\<close>
       have "\<dots> = normalize (map (map_prod id f) (x@y))"
         by -(rule rename_gens_normalize[THEN sym],
              auto intro!: subset_inj_on[OF \<open>inj_on f gens1\<close>] iff:lists_eq_set)
  also have "\<dots> = normalize (map (map_prod id f) x @ map (map_prod id f) y)"
       by (auto)
  also have "\<dots> = map (map_prod id f) x \<otimes>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> map (map_prod id f) y"
       by (simp add:free_group_def)
  finally have "map (map_prod id f) (x \<otimes>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub> y) =
                map (map_prod id f) x \<otimes>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> map (map_prod id f) y".
  }
  thus "\<forall>x\<in>carrier \<F>\<^bsub>gens1\<^esub>.
       \<forall>y\<in>carrier \<F>\<^bsub>gens1\<^esub>.
          map (map_prod id f) (x \<otimes>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub> y) =
          map (map_prod id f) x \<otimes>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> map (map_prod id f) y"
   by auto
qed (auto intro: free_group_is_group)

subsection \<open>Bases of isomorphic free groups\<close>

text \<open>
Isomorphic free groups have bases of same cardinality. The proof is very different
for infinite bases and for finite bases.

The proof for the finite case uses the set of of homomorphisms from the free
group to the group with two elements, as suggested by Christian Sievers. The
definition of @{term hom} is not suitable for proofs about the cardinality of that
set, as its definition does not require extensionality. This is amended by the
following definition:
\<close>

definition homr
  where "homr G H = {h. h \<in> hom G H \<and> h \<in> extensional (carrier G)}"

lemma (in group_hom) restrict_hom[intro!]:
  shows "restrict h (carrier G) \<in> homr G H"
  unfolding homr_def and hom_def
  by (auto)

lemma hom_F_C2_Powerset:
  "\<exists> f. bij_betw f (Pow X) (homr (\<F>\<^bsub>X\<^esub>) C2)"
proof
  interpret F: group "\<F>\<^bsub>X\<^esub>" by (rule free_group_is_group)
  interpret C2: group C2 by (rule C2_is_group)
  let ?f = "\<lambda>S . restrict (C2.lift (\<lambda>x. x \<in> S)) (carrier \<F>\<^bsub>X\<^esub>)"
  let ?f' = "\<lambda>h . X \<inter> Collect(h \<circ> insert)"
  show "bij_betw ?f (Pow X) (homr (\<F>\<^bsub>X\<^esub>) C2)"
  proof(induct rule: bij_betwI[of ?f _ _ ?f'])
  case 1 show ?case
    proof
      fix S assume "S \<in> Pow X"
      interpret h: group_hom "\<F>\<^bsub>X\<^esub>" C2 "C2.lift (\<lambda>x. x \<in> S)"
        by unfold_locales (auto intro: C2.lift_is_hom)
      show "?f S \<in> homr \<F>\<^bsub>X\<^esub> C2"
        by (rule h.restrict_hom)
     qed
  next
  case 2 show ?case by auto next
  case (3 S) show ?case
    proof (induct rule: Set.set_eqI)
      case (1 x) show ?case
      proof(cases "x \<in> X")
      case True thus ?thesis using insert_closed[of x X]
         by (auto simp add:insert_def C2.lift_def C2.lift_gi_def)
      next case False thus ?thesis using 3 by auto
    qed
  qed
  next
  case (4 h)
    hence hom: "h \<in> hom \<F>\<^bsub>X\<^esub> C2"
      and extn: "h \<in> extensional (carrier \<F>\<^bsub>X\<^esub>)"
      unfolding homr_def by auto
    have "\<forall>x \<in> carrier \<F>\<^bsub>X\<^esub> . h x = group.lift C2 (\<lambda>z. z \<in> X & (h \<circ> FreeGroups.insert) z) x"
     by (rule C2.lift_is_unique[OF C2_is_group _ hom, of "(\<lambda>z. z \<in> X & (h \<circ> FreeGroups.insert) z)"],
             auto)
    thus ?case
    by -(rule extensionalityI[OF restrict_extensional extn], auto)
  qed
qed

lemma group_iso_betw_hom:
  assumes "group G1" and "group G2"
      and iso: "i \<in> iso G1 G2"
  shows   "\<exists> f . bij_betw f (homr G2 H) (homr G1 H)"
proof-
  interpret G2: group G2 by (rule \<open>group G2\<close>)
  let ?i' = "restrict (inv_into (carrier G1) i) (carrier G2)"
  have "inv_into (carrier G1) i \<in> iso G2 G1"
    by (simp add: \<open>group G1\<close> group.iso_set_sym iso)    
  hence iso': "?i' \<in> iso G2 G1"
    by (auto simp add:Group.iso_def hom_def G2.m_closed)
  show ?thesis
  proof(rule, induct rule: bij_betwI[of "(\<lambda>h. compose (carrier G1) h i)" _ _ "(\<lambda>h. compose (carrier G2) h ?i')"])
  case 1
    show ?case
    proof
      fix h assume "h \<in> homr G2 H"
      hence "compose (carrier G1) h i \<in> hom G1 H"
        using iso
        by (auto intro: group.hom_compose[OF \<open>group G1\<close>, of _ G2] simp add:Group.iso_def homr_def)
      thus "compose (carrier G1) h i \<in> homr G1 H"
        unfolding homr_def by simp
     qed
  next
  case 2
    show ?case
    proof
      fix h assume "h \<in> homr G1 H"
      hence "compose (carrier G2) h ?i' \<in> hom G2 H"
        using iso'
        by (auto intro: group.hom_compose[OF \<open>group G2\<close>, of _ G1] simp add:Group.iso_def homr_def)
      thus "compose (carrier G2) h ?i' \<in> homr G2 H"
        unfolding homr_def by simp
     qed
  next
  case (3 x)
    hence "compose (carrier G2) (compose (carrier G1) x i) ?i'
          = compose (carrier G2) x (compose (carrier G2) i ?i')"
      using iso iso'
      by (auto intro: compose_assoc[THEN sym]   simp add:Group.iso_def hom_def homr_def)
    also have "\<dots> = compose (carrier G2) x (\<lambda>y\<in>carrier G2. y)"
      using iso
      by (subst compose_id_inv_into, auto simp add:Group.iso_def hom_def bij_betw_def)
    also have "\<dots> = x"
      using 3
      by (auto intro:compose_Id simp add:homr_def)
    finally
    show ?case .
  next
  case (4 y)
    hence "compose (carrier G1) (compose (carrier G2) y ?i') i
          = compose (carrier G1) y (compose (carrier G1) ?i' i)"
      using iso iso'
      by (auto intro: compose_assoc[THEN sym] simp add:Group.iso_def hom_def homr_def)
    also have "\<dots> = compose (carrier G1) y (\<lambda>x\<in>carrier G1. x)"
      using iso
      by (subst compose_inv_into_id, auto simp add:Group.iso_def hom_def bij_betw_def)
    also have "\<dots> = y"
      using 4
      by (auto intro:compose_Id simp add:homr_def)
    finally
    show ?case .
  qed
qed

lemma isomorphic_free_groups_bases_finite:
  assumes iso: "i \<in> iso \<F>\<^bsub>X\<^esub> \<F>\<^bsub>Y\<^esub>"
      and finite: "finite X"
  shows "\<exists>f. bij_betw f X Y"
proof-
  obtain f
    where "bij_betw f (homr \<F>\<^bsub>Y\<^esub> C2) (homr \<F>\<^bsub>X\<^esub> C2)"
    using group_iso_betw_hom[OF free_group_is_group free_group_is_group iso]
    by auto
  moreover
  obtain g'
    where "bij_betw g' (Pow X) (homr (\<F>\<^bsub>X\<^esub>) C2)"
    using hom_F_C2_Powerset by auto
  then obtain g
    where "bij_betw g (homr (\<F>\<^bsub>X\<^esub>) C2) (Pow X)"
    by (auto intro: bij_betw_inv_into)
  moreover
  obtain h
    where "bij_betw h (Pow Y) (homr (\<F>\<^bsub>Y\<^esub>) C2)"
    using hom_F_C2_Powerset by auto
  ultimately
  have "bij_betw (g \<circ> f \<circ> h) (Pow Y) (Pow X)"
    by (auto intro: bij_betw_trans)
  hence eq_card: "card (Pow Y) = card (Pow X)"
    by (rule bij_betw_same_card)
  with finite
  have "finite (Pow Y)"
   by -(rule card_ge_0_finite, auto simp add:card_Pow)
  hence finite': "finite Y" by simp

  with eq_card finite
  have "card X = card Y"
   by (auto simp add:card_Pow)
  with finite finite'
  show ?thesis
   by (rule finite_same_card_bij)
qed

text \<open>
The proof for the infinite case is trivial once the fact that the free group
over an infinite set has the same cardinality is established.
\<close>

lemma free_group_card_infinite:
  assumes "\<not> finite X"
  shows "|X| =o |carrier \<F>\<^bsub>X\<^esub>|"
proof-
  have "inj_on insert X"
    by (rule inj_onI) (auto simp add: insert_def)
  moreover have "insert ` X \<subseteq> carrier \<F>\<^bsub>X\<^esub>"
    by (auto intro: insert_closed)
  ultimately have "\<exists>f. inj_on f X \<and> f ` X \<subseteq> carrier \<F>\<^bsub>X\<^esub>"
    by auto
  then have "|X| \<le>o |carrier \<F>\<^bsub>X\<^esub>|"
    by (simp add: card_of_ordLeq)
  moreover
  have "|carrier \<F>\<^bsub>X\<^esub>| \<le>o |lists ((UNIV::bool set)\<times>X)|"
    by (auto intro!:card_of_mono1 simp add:free_group_def)
  moreover
  have "|lists ((UNIV::bool set)\<times>X)| =o |(UNIV::bool set)\<times>X|"
    using \<open>\<not> finite X\<close>
    by (auto intro:card_of_lists_infinite dest!:finite_cartesian_productD2)
  moreover
  have  "|(UNIV::bool set)\<times>X| =o |X|"
    using \<open>\<not> finite X\<close>
    by (auto intro: card_of_Times_infinite[OF _ _ ordLess_imp_ordLeq[OF finite_ordLess_infinite2], THEN conjunct2])
  ultimately
  show "|X| =o |carrier \<F>\<^bsub>X\<^esub>|"
    by (subst ordIso_iff_ordLeq, auto intro: ord_trans)
qed

theorem isomorphic_free_groups_bases:
  assumes iso: "i \<in> iso \<F>\<^bsub>X\<^esub> \<F>\<^bsub>Y\<^esub>"
  shows "\<exists>f. bij_betw f X Y"
proof(cases "finite X")
case True
  thus ?thesis using iso by -(rule isomorphic_free_groups_bases_finite)
next
case False show ?thesis
  proof(cases "finite Y")
  case True
  from iso obtain i' where "i' \<in> iso \<F>\<^bsub>Y\<^esub> \<F>\<^bsub>X\<^esub>"
    using free_group_is_group group.iso_set_sym by blast
  with \<open>finite Y\<close>
  have "\<exists>f. bij_betw f Y X" by -(rule isomorphic_free_groups_bases_finite)
  thus "\<exists>f. bij_betw f X Y" by (auto intro: bij_betw_the_inv_into) next
case False
  from \<open>\<not> finite X\<close> have "|X| =o |carrier \<F>\<^bsub>X\<^esub>|" 
    by (rule free_group_card_infinite)
  moreover
  from \<open>\<not> finite Y\<close> have "|Y| =o |carrier \<F>\<^bsub>Y\<^esub>|" 
    by (rule free_group_card_infinite)
  moreover
  from iso have "|carrier \<F>\<^bsub>X\<^esub>| =o |carrier \<F>\<^bsub>Y\<^esub>|"
    by (auto simp add:Group.iso_def iff:card_of_ordIso[THEN sym])
  ultimately
  have "|X| =o |Y|" by (auto intro: ordIso_equivalence)
  thus ?thesis by (subst card_of_ordIso)
qed
qed

end
