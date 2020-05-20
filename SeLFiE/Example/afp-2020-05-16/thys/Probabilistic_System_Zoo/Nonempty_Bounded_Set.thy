section \<open>Nonempty Sets Strictly Bounded by an Infinite Cardinal\<close>

theory Nonempty_Bounded_Set
imports
  "HOL-Cardinals.Bounded_Set"
begin

typedef ('a, 'k) nebset ("_ set![_]" [22, 21] 21) =
  "{A :: 'a set. A \<noteq> {} \<and> |A| <o natLeq +c |UNIV :: 'k set|}"
  morphisms set_nebset Abs_nebset
  apply (rule exI[of _ "{undefined}"], simp)
  apply (rule Cfinite_ordLess_Cinfinite)
  apply (auto simp: cfinite_def cinfinite_csum natLeq_cinfinite Card_order_csum)
  done

setup_lifting type_definition_nebset

lift_definition map_nebset ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a set!['k] \<Rightarrow> 'b set!['k]" is image
  using card_of_image ordLeq_ordLess_trans by blast

lift_definition rel_nebset ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set!['k] \<Rightarrow> 'b set!['k] \<Rightarrow> bool" is rel_set .

lift_definition nebinsert :: "'a \<Rightarrow> 'a set!['k] \<Rightarrow> 'a set!['k]" is "insert"
  using infinite_card_of_insert ordIso_ordLess_trans Field_card_of Field_natLeq UNIV_Plus_UNIV
   csum_def finite_Plus_UNIV_iff finite_insert finite_ordLess_infinite2 infinite_UNIV_nat
   insert_not_empty by metis

lift_definition nebsingleton :: "'a \<Rightarrow> 'a set!['k]" is "\<lambda>a. {a}"
  apply simp
  apply (rule Cfinite_ordLess_Cinfinite)
  apply (auto simp: cfinite_def cinfinite_csum natLeq_cinfinite Card_order_csum)
  done

lemma set_nebset_to_set_nebset: "A \<noteq> {} \<Longrightarrow> |A| <o natLeq +c |UNIV :: 'k set| \<Longrightarrow>
  set_nebset (the_inv set_nebset A :: 'a set!['k]) = A"
  apply (rule f_the_inv_into_f[unfolded inj_on_def])
  apply (simp add: set_nebset_inject range_eqI Abs_nebset_inverse[symmetric])
  apply (rule range_eqI Abs_nebset_inverse[symmetric] CollectI)+
  apply blast
  done

lemma rel_nebset_aux_infinite:
  fixes a :: "'a set!['k]" and b :: "'b set!['k]"
  shows "(\<forall>t \<in> set_nebset a. \<exists>u \<in> set_nebset b. R t u) \<and> (\<forall>u \<in> set_nebset b. \<exists>t \<in> set_nebset a. R t u) \<longleftrightarrow>
   ((BNF_Def.Grp {a. set_nebset a \<subseteq> {(a, b). R a b}} (map_nebset fst))\<inverse>\<inverse> OO
    BNF_Def.Grp {a. set_nebset a \<subseteq> {(a, b). R a b}} (map_nebset snd)) a b" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  define R' :: "('a \<times> 'b) set!['k]"
    where "R' = the_inv set_nebset (Collect (case_prod R) \<inter> (set_nebset a \<times> set_nebset b))"
    (is "_ = the_inv set_nebset ?L'")
  from \<open>?L\<close> have "?L' \<noteq> {}" by transfer auto
  moreover
  have "|?L'| <o natLeq +c |UNIV :: 'k set|"
    unfolding csum_def Field_natLeq
    by (intro ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower2]]
      card_of_Times_ordLess_infinite)
      (simp, (transfer, simp add: csum_def Field_natLeq)+)
  ultimately have *: "set_nebset R' = ?L'" unfolding R'_def by (intro set_nebset_to_set_nebset)
  show ?R unfolding Grp_def relcompp.simps conversep.simps
  proof (intro CollectI case_prodI exI[of _ a] exI[of _ b] exI[of _ R'] conjI refl)
    from * show "a = map_nebset fst R'" using conjunct1[OF \<open>?L\<close>]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
    from * show "b = map_nebset snd R'" using conjunct2[OF \<open>?L\<close>]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
  qed (auto simp add: *)
next
  assume ?R thus ?L unfolding Grp_def relcompp.simps conversep.simps
    by transfer force
qed

bnf "'a set!['k]"
  map: map_nebset
  sets: set_nebset
  bd: "natLeq +c |UNIV :: 'k set|"
  rel: rel_nebset
proof -
  show "map_nebset id = id" by (rule ext, transfer) simp
next
  fix f g
  show "map_nebset (f o g) = map_nebset f o map_nebset g" by (rule ext, transfer) auto
next
  fix X f g
  assume "\<And>z. z \<in> set_nebset X \<Longrightarrow> f z = g z"
  then show "map_nebset f X = map_nebset g X" by transfer force
next
  fix f
  show "set_nebset \<circ> map_nebset f = (`) f \<circ> set_nebset" by (rule ext, transfer) auto
next
  fix X :: "'a set!['k]"
  show "|set_nebset X| \<le>o natLeq +c |UNIV :: 'k set|"
    by transfer (blast dest: ordLess_imp_ordLeq)
next
  fix R S
  show "rel_nebset R OO rel_nebset S \<le> rel_nebset (R OO S)"
    by (rule predicate2I, transfer) (auto simp: rel_set_OO[symmetric])
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "rel_nebset R = ((\<lambda>x y. \<exists>z. set_nebset z \<subseteq> {(x, y). R x y} \<and>
    map_nebset fst z = x \<and> map_nebset snd z = y) :: 'a set!['k] \<Rightarrow> 'b set!['k] \<Rightarrow> bool)"
    by (simp add: rel_nebset_def map_fun_def o_def rel_set_def
      rel_nebset_aux_infinite[unfolded OO_Grp_alt])
qed (simp_all add: card_order_csum natLeq_card_order cinfinite_csum natLeq_cinfinite)

lemma map_nebset_nebinsert[simp]: "map_nebset f (nebinsert x X) = nebinsert (f x) (map_nebset f X)"
  by transfer auto

lemma map_nebset_nebsingleton: "map_nebset f (nebsingleton x) = nebsingleton (f x)"
  by transfer auto

lemma nebsingleton_inj[simp]: "nebsingleton x = nebsingleton y \<longleftrightarrow> x = y"
  by transfer auto

lemma rel_nebsingleton[simp]:
  "rel_nebset R (nebsingleton x1) (nebsingleton x2) = R x1 x2"
  by transfer (auto simp: rel_set_def)

lemma rel_nebset_nebsingleton[simp]:
  "rel_nebset R (nebsingleton x1) X = (\<forall>x2\<in>set_nebset X. R x1 x2)"
  "rel_nebset R X (nebsingleton x2) = (\<forall>x1\<in>set_nebset X. R x1 x2)"
  by (transfer, force simp add: rel_set_def)+

lemma rel_nebset_False[simp]: "rel_nebset (\<lambda>x y. False) x y = False"
  by transfer (auto simp: rel_set_def)

lemmas set_nebset_nebsingleton[simp] = nebsingleton.rep_eq

lemma nebinsert_absorb[simp]: "nebinsert a (nebinsert a x) = nebinsert a x"
  by transfer simp

lift_definition bset_of_nebset :: "'a set!['k] \<Rightarrow> 'a set['k]" is "\<lambda>X. X" by (rule conjunct2)

lemma rel_bset_bset_of_nebset[simp]:
  "rel_bset R (bset_of_nebset X) (bset_of_nebset Y) = rel_nebset R X Y"
  by transfer (rule refl)

lemma rel_nebset_conj[simp]:
  "rel_nebset (\<lambda>x y. P \<and> Q x y) x y \<longleftrightarrow> P \<and> rel_nebset Q x y"
  "rel_nebset (\<lambda>x y. Q x y \<and> P) x y \<longleftrightarrow> P \<and> rel_nebset Q x y"
  by (transfer, auto simp: rel_set_def)+

lemma set_bset_empty[simp]: "set_bset X = {} \<longleftrightarrow> X = bempty"
  by transfer simp

(* FIXME for ONDRA*)
(*
declare nebset.rel_eq[relator_eq]
declare nebset.rel_mono[relator_mono]
declare nebset.rel_compp[symmetric, relator_distr]
declare nebset.rel_transfer[transfer_rule]

lemma nebset_quot_map[quot_map]: "Quotient R Abs Rep T \<Longrightarrow>
  Quotient (rel_nebset R) (map_nebset Abs) (map_nebset Rep) (rel_nebset T)"
  unfolding Quotient_alt_def5 nebset.rel_Grp[of UNIV, simplified, symmetric]
    nebset.rel_conversep[symmetric] nebset.rel_compp[symmetric]
    by (auto elim: nebset.rel_mono_strong)

lemma set_relator_eq_onp [relator_eq_onp]:
  "rel_nebset (eq_onp P) = eq_onp (\<lambda>A. Ball (set_nebset A) P)"
  unfolding fun_eq_iff eq_onp_def by transfer (auto simp: rel_set_def)
*)

end
