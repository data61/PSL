(*  Title:       MonoidalFunctor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Monoidal Functor"

text_raw\<open>
\label{monoidal-functor-chap}
\<close>

theory MonoidalFunctor
imports MonoidalCategory
begin

    text \<open>
      A monoidal functor is a functor @{term F} between monoidal categories @{term C}
      and @{term D} that preserves the monoidal structure up to isomorphism.
      The traditional definition assumes a monoidal functor to be equipped with
      two natural isomorphisms, a natural isomorphism @{term \<phi>} that expresses the preservation
      of tensor product and a natural isomorphism @{term \<psi>} that expresses the preservation
      of the unit object.  These natural isomorphisms are subject to coherence conditions;
      the condition for @{term \<phi>} involving the associator and the conditions for @{term \<psi>}
      involving the unitors.  However, as pointed out in \cite{Etingof15} (Section 2.4),
      it is not necessary to take the natural isomorphism @{term \<psi>} as given,
      since the mere assumption that @{term "F \<I>\<^sub>C"} is isomorphic to @{term "\<I>\<^sub>D"}
      is sufficient for there to be a canonical definition of @{term \<psi>} from which the
      coherence conditions can be derived.  This leads to a more economical definition
      of monoidal functor, which is the one we adopt here.
\<close>

  locale monoidal_functor =
    C: monoidal_category C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C +
    D: monoidal_category D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D +
    "functor" C D F +
    CC: product_category C C +
    DD: product_category D D +
    FF: product_functor C C D D F F +
    FoT\<^sub>C: composite_functor C.CC.comp C D T\<^sub>C F +
    T\<^sub>DoFF: composite_functor C.CC.comp D.CC.comp D FF.map T\<^sub>D +
    \<phi>: natural_isomorphism C.CC.comp D T\<^sub>DoFF.map FoT\<^sub>C.map \<phi>
  for C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and T\<^sub>C :: "'c * 'c \<Rightarrow> 'c"
  and \<alpha>\<^sub>C :: "'c * 'c * 'c \<Rightarrow> 'c"
  and \<iota>\<^sub>C :: "'c"
  and D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and T\<^sub>D :: "'d * 'd \<Rightarrow> 'd"
  and \<alpha>\<^sub>D :: "'d * 'd * 'd \<Rightarrow> 'd"
  and \<iota>\<^sub>D :: "'d"
  and F :: "'c \<Rightarrow> 'd"
  and \<phi> :: "'c * 'c \<Rightarrow> 'd" +
  assumes preserves_unity: "D.isomorphic D.unity (F C.unity)"
  and assoc_coherence:
      "\<lbrakk> C.ide a; C.ide b; C.ide c \<rbrakk> \<Longrightarrow>
         F (\<alpha>\<^sub>C (a, b, c)) \<cdot>\<^sub>D \<phi> (T\<^sub>C (a, b), c) \<cdot>\<^sub>D T\<^sub>D (\<phi> (a, b), F c)
           = \<phi> (a, T\<^sub>C (b, c)) \<cdot>\<^sub>D T\<^sub>D (F a, \<phi> (b, c)) \<cdot>\<^sub>D \<alpha>\<^sub>D (F a, F b, F c)"
  begin

    notation C.tensor                     (infixr "\<otimes>\<^sub>C" 53)
    and C.unity                           ("\<I>\<^sub>C")
    and C.lunit                           ("\<l>\<^sub>C[_]")
    and C.runit                           ("\<r>\<^sub>C[_]")
    and C.assoc                           ("\<a>\<^sub>C[_, _, _]")
    and D.tensor                          (infixr "\<otimes>\<^sub>D" 53)
    and D.unity                           ("\<I>\<^sub>D")
    and D.lunit                           ("\<l>\<^sub>D[_]")
    and D.runit                           ("\<r>\<^sub>D[_]")
    and D.assoc                           ("\<a>\<^sub>D[_, _, _]")

    lemma \<phi>_in_hom:
    assumes "C.ide a" and "C.ide b"
    shows "\<guillemotleft>\<phi> (a, b) : F a \<otimes>\<^sub>D F b \<rightarrow>\<^sub>D F (a \<otimes>\<^sub>C b)\<guillemotright>"
      using assms by auto

    text \<open>
      We wish to exhibit a canonical definition of an isomorphism
      @{term "\<psi> \<in> D.hom \<I>\<^sub>D (F \<I>\<^sub>C)"} that satisfies certain coherence conditions that
      involve the left and right unitors.  In \cite{Etingof15}, the isomorphism @{term \<psi>}
      is defined by the equation @{term "\<l>\<^sub>D[F \<I>\<^sub>C] = F \<l>\<^sub>C[\<I>\<^sub>C] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F \<I>\<^sub>C)"},
      which suffices for the definition because the functor \<open>- \<otimes>\<^sub>D F \<I>\<^sub>C\<close> is fully faithful.
      It is then asserted (Proposition 2.4.3) that the coherence condition
      @{term "\<l>\<^sub>D[F a] = F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F a)"} is satisfied for any object @{term a}
      of \<open>C\<close>, as well as the corresponding condition for the right unitor.
      However, the proof is left as an exercise (Exercise 2.4.4).
      The organization of the presentation suggests that that one should derive the
      general coherence condition from the special case
      @{term "\<l>\<^sub>D[F \<I>\<^sub>C] = F \<l>\<^sub>C[\<I>\<^sub>C] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F \<I>\<^sub>C)"} used as the definition of @{term \<psi>}.
      However, I did not see how to do it that way, so I used a different approach.
      The isomorphism @{term "\<iota>\<^sub>D' \<equiv> F \<iota>\<^sub>C \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, \<I>\<^sub>C)"} serves as an alternative unit for the
      monoidal category \<open>D\<close>.  There is consequently a unique isomorphism that maps
      @{term "\<iota>\<^sub>D"} to @{term "\<iota>\<^sub>D'"}.  We define @{term \<psi>} to be this isomorphism and then use
      the definition to establish the desired coherence conditions.
\<close>

    abbreviation \<iota>\<^sub>1
    where "\<iota>\<^sub>1 \<equiv> F \<iota>\<^sub>C \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, \<I>\<^sub>C)"

    lemma \<iota>\<^sub>1_in_hom:
    shows "\<guillemotleft>\<iota>\<^sub>1 : F \<I>\<^sub>C \<otimes>\<^sub>D F \<I>\<^sub>C \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright>"
      using C.\<iota>_in_hom by (intro D.in_homI, auto)

    lemma \<iota>\<^sub>1_is_iso:
    shows "D.iso \<iota>\<^sub>1"
      using C.\<iota>_is_iso C.\<iota>_in_hom \<phi>_in_hom D.isos_compose by auto

    interpretation D: monoidal_category_with_alternate_unit D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D \<iota>\<^sub>1
    proof -
      have 1: "\<exists>\<psi>. \<guillemotleft>\<psi> : F \<I>\<^sub>C \<rightarrow>\<^sub>D \<I>\<^sub>D\<guillemotright> \<and> D.iso \<psi>"
      proof -
        obtain \<psi>' where \<psi>': "\<guillemotleft>\<psi>' : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<psi>'"
          using preserves_unity by auto
        have "\<guillemotleft>D.inv \<psi>' : F \<I>\<^sub>C \<rightarrow>\<^sub>D \<I>\<^sub>D\<guillemotright> \<and> D.iso (D.inv \<psi>')"
          using \<psi>' D.iso_inv_iso by simp
        thus ?thesis by auto
      qed
      obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : F \<I>\<^sub>C \<rightarrow>\<^sub>D \<I>\<^sub>D\<guillemotright> \<and> D.iso \<psi>"
        using 1 by blast
      interpret L: equivalence_functor D D "\<lambda>f. (D.cod \<iota>\<^sub>1) \<otimes>\<^sub>D f"
      proof -
        interpret L: "functor" D D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f"
          using D.T.fixing_ide_gives_functor_1 by simp
        interpret L: endofunctor D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f" ..
        interpret \<psi>x: natural_transformation D D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f" "\<lambda>f. \<I>\<^sub>D \<otimes>\<^sub>D f" "\<lambda>f. \<psi> \<otimes>\<^sub>D f"
          using \<psi> D.T.fixing_arr_gives_natural_transformation_1 [of \<psi>] by auto
        interpret \<psi>x: natural_isomorphism D D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f" "\<lambda>f. \<I>\<^sub>D \<otimes>\<^sub>D f" "\<lambda>f. \<psi> \<otimes>\<^sub>D f"
          apply unfold_locales using \<psi> D.tensor_preserves_iso by simp
        interpret \<ll>\<^sub>Do\<psi>x: vertical_composite D D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f" "\<lambda>f. \<I>\<^sub>D \<otimes>\<^sub>D f" D.map
                                           "\<lambda>f. \<psi> \<otimes>\<^sub>D f" D.\<ll> ..
        interpret \<ll>\<^sub>Do\<psi>x: natural_isomorphism D D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f" D.map \<ll>\<^sub>Do\<psi>x.map
          using \<psi>x.natural_isomorphism_axioms D.\<ll>.natural_isomorphism_axioms
                natural_isomorphisms_compose by blast
        interpret L: equivalence_functor D D "\<lambda>f. (F \<I>\<^sub>C) \<otimes>\<^sub>D f"
          using L.isomorphic_to_identity_is_equivalence \<ll>\<^sub>Do\<psi>x.natural_isomorphism_axioms
          by simp
        show "equivalence_functor D D (\<lambda>f. (D.cod \<iota>\<^sub>1) \<otimes>\<^sub>D f)"
          using L.equivalence_functor_axioms C.\<iota>_in_hom by auto
      qed
      interpret R: equivalence_functor D D "\<lambda>f. T\<^sub>D (f, D.cod \<iota>\<^sub>1)"
      proof -
        interpret R: "functor" D D "\<lambda>f. T\<^sub>D (f, F \<I>\<^sub>C)"
          using D.T.fixing_ide_gives_functor_2 by simp
        interpret R: endofunctor D "\<lambda>f. T\<^sub>D (f, F \<I>\<^sub>C)" ..
        interpret x\<psi>: natural_transformation D D "\<lambda>f. f \<otimes>\<^sub>D (F \<I>\<^sub>C)" "\<lambda>f. f \<otimes>\<^sub>D \<I>\<^sub>D" "\<lambda>f. f \<otimes>\<^sub>D \<psi>"
          using \<psi> D.T.fixing_arr_gives_natural_transformation_2 [of \<psi>] by auto
        interpret x\<psi>: natural_isomorphism D D "\<lambda>f. f \<otimes>\<^sub>D (F \<I>\<^sub>C)" "\<lambda>f. f \<otimes>\<^sub>D \<I>\<^sub>D" "\<lambda>f. f \<otimes>\<^sub>D \<psi>"
          using \<psi> D.tensor_preserves_iso by (unfold_locales, simp)
        interpret \<rho>\<^sub>Dox\<psi>: vertical_composite D D "\<lambda>f. f \<otimes>\<^sub>D (F \<I>\<^sub>C)" "\<lambda>f. f \<otimes>\<^sub>D \<I>\<^sub>D" D.map
                                                "\<lambda>f. f \<otimes>\<^sub>D \<psi>" D.\<rho> ..
        interpret \<rho>\<^sub>Dox\<psi>: natural_isomorphism D D "\<lambda>f. f \<otimes>\<^sub>D (F \<I>\<^sub>C)" D.map \<rho>\<^sub>Dox\<psi>.map
          using x\<psi>.natural_isomorphism_axioms D.\<rho>.natural_isomorphism_axioms
                natural_isomorphisms_compose by blast
        interpret R: equivalence_functor D D "\<lambda>f. f \<otimes>\<^sub>D (F \<I>\<^sub>C)"
          using R.isomorphic_to_identity_is_equivalence \<rho>\<^sub>Dox\<psi>.natural_isomorphism_axioms
          by simp
        show "equivalence_functor D D (\<lambda>f. f \<otimes>\<^sub>D (D.cod \<iota>\<^sub>1))"
          using R.equivalence_functor_axioms C.\<iota>_in_hom by auto
      qed
      show "monoidal_category_with_alternate_unit D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D \<iota>\<^sub>1"
        using D.pentagon C.\<iota>_is_iso C.\<iota>_in_hom preserves_hom \<iota>\<^sub>1_is_iso \<iota>\<^sub>1_in_hom
        by (unfold_locales, auto)
    qed

    no_notation D.tensor   (infixr "\<otimes>\<^sub>D" 53)
    notation D.C\<^sub>1.tensor   (infixr "\<otimes>\<^sub>D" 53)   (* equal to D.tensor *)
    no_notation D.assoc    ("\<a>\<^sub>D[_, _, _]")
    notation D.C\<^sub>1.assoc    ("\<a>\<^sub>D[_, _, _]")      (* equal to D.assoc *)
    no_notation D.assoc'   ("\<a>\<^sub>D\<^sup>-\<^sup>1[_, _, _]")
    notation D.C\<^sub>1.assoc'   ("\<a>\<^sub>D\<^sup>-\<^sup>1[_, _, _]")   (* equal to D.assoc' *)
    notation D.C\<^sub>1.unity    ("\<I>\<^sub>1")
    notation D.C\<^sub>1.lunit    ("\<l>\<^sub>1[_]")
    notation D.C\<^sub>1.runit    ("\<r>\<^sub>1[_]")

    lemma \<I>\<^sub>1_char [simp]:
    shows "\<I>\<^sub>1 = F \<I>\<^sub>C"
      using D.C\<^sub>1.unity_def \<iota>\<^sub>1_in_hom by auto

    definition \<psi>
    where "\<psi> \<equiv> THE \<psi>. \<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)"

    lemma \<psi>_char:
    shows "\<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright>" and "D.iso \<psi>" and "\<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)"
    and "\<exists>!\<psi>. \<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)"
    proof -
      show "\<exists>!\<psi>. \<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)"
        using D.unit_unique_upto_unique_iso \<iota>\<^sub>1_in_hom D.C\<^sub>1.\<iota>_in_hom
        by (elim D.in_homE, auto)
      hence 1: "\<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)"
        unfolding \<psi>_def
        using theI' [of "\<lambda>\<psi>. \<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)"]
          by fast
      show "\<guillemotleft>\<psi> : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright>" using 1 by simp
      show "D.iso \<psi>" using 1 by simp
      show "\<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi>)" using 1 by simp
    qed

    lemma \<psi>_eqI:
    assumes "\<guillemotleft>f: \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright>" and "D.iso f" and "f \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (f \<otimes>\<^sub>D f)"
    shows "f = \<psi>"
      using assms \<psi>_def \<psi>_char
            the1_equality [of "\<lambda>f. \<guillemotleft>f: \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso f \<and> f \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (f \<otimes>\<^sub>D f)" f]
      by simp

    lemma lunit_coherence1:
    assumes "C.ide a"
    shows "\<l>\<^sub>1[F a] \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F a) = \<l>\<^sub>D[F a]"
    proof -
      have "D.par (\<l>\<^sub>1[F a] \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F a)) \<l>\<^sub>D[F a]"
        using assms D.C\<^sub>1.lunit_in_hom D.tensor_in_hom D.lunit_in_hom \<psi>_char(1) C.\<iota>_in_hom
        by auto
      text \<open>
        The upper left triangle in the following diagram commutes.
\<close>
      text \<open>
\newcommand\xIc{{\cal I}}
\newcommand\xId{{\cal I}}
\newcommand\xac[3]{{\scriptsize \<open>\<a>\<close>}[{#1},{#2},{#3}]}
\newcommand\xad[3]{{\scriptsize \<open>\<a>\<close>}[{#1},{#2},{#3}]}
\newcommand\xlc[1]{{\scriptsize \<open>\<l>\<close>}[{#1}]}
\newcommand\xld[1]{{\scriptsize \<open>\<l>\<close>}[{#1}]}
\newcommand\xldp[1]{{\scriptsize \<open>\<l>\<close>}_1[{#1}]}
$$\xymatrix{
  {\xId\otimes F a}
     \ar[rrr]^{\psi\otimes F a}
  & & &
  {F\xIc\otimes F a}
  \\
  &
  {\xId\otimes(F\xIc \otimes F a)}
     \ar[ul]_{\xId\otimes\xldp{F a}}
     \ar[ddr]^{\psi\otimes(F\xIc\otimes F a)}
  \\ \\
  &
  {\xId\otimes(\xId \otimes F a)}
     \ar[r]_{\psi\otimes(\psi\otimes F a)}
     \ar[uuul]^{\xId\otimes\xld{F a}}
     \ar[uu]_{\xId\otimes(\psi\otimes F a)}
  &
  {F\xIc\otimes (F\xIc\otimes F a)}
     \ar[uuur]^{F\xIc\otimes\xldp{F a}}
  \\ \\
  {(\xId\otimes\xId)\otimes F a}
     \ar[uuuuu]^{\iota\otimes F a}
     \ar[uur]_{\xad{\xId}{\xId}{F a}}
     \ar[rrr]^{(\psi\otimes\psi)\otimes F a}
  & & &
  {(F\xIc\otimes F\xIc)\otimes F a}
     \ar[uuuuu]_{\iota_1\otimes F a}
     \ar[uul]^{\xad{F\xIc}{F\xIc}{F a}}
}$$
\<close>
      moreover have "(\<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>1[F a]) \<cdot>\<^sub>D (\<I>\<^sub>D \<otimes>\<^sub>D \<psi> \<otimes>\<^sub>D F a) = \<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>D[F a]"
      proof -
        have "(\<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>1[F a]) \<cdot>\<^sub>D (\<I>\<^sub>D \<otimes>\<^sub>D \<psi> \<otimes>\<^sub>D F a)
                = (\<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>1[F a]) \<cdot>\<^sub>D (D.inv \<psi> \<otimes>\<^sub>D F \<I>\<^sub>C \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi> \<otimes>\<^sub>D F a)"
          using assms \<psi>_char(1-2) D.interchange [of "D.inv \<psi>"] D.comp_cod_arr
                D.inv_is_inverse D.comp_inv_arr
          by (elim D.in_homE, simp)
        also have "... = (D.inv \<psi> \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D \<psi> \<otimes>\<^sub>D F a)"
        proof -
          have "(\<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>1[F a]) \<cdot>\<^sub>D (D.inv \<psi> \<otimes>\<^sub>D F \<I>\<^sub>C \<otimes>\<^sub>D F a) =
                (D.inv \<psi> \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a])"
            using assms \<psi>_char(1-2) D.interchange [of "\<I>\<^sub>D"] D.interchange [of "D.inv \<psi>"]
                  D.comp_arr_dom D.comp_cod_arr
            by (elim D.in_homE, auto)
          thus ?thesis
            using assms \<psi>_char(1-2) D.inv_in_hom
                  D.comp_permute [of "\<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>1[F a]" "D.inv \<psi> \<otimes>\<^sub>D F \<I>\<^sub>C \<otimes>\<^sub>D F a"
                                     "D.inv \<psi> \<otimes>\<^sub>D F a" "F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]"]
            by (elim D.in_homE, auto)
        qed
        also have "... = (D.inv \<psi> \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (\<iota>\<^sub>1 \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a] \<cdot>\<^sub>D
                         (\<psi> \<otimes>\<^sub>D \<psi> \<otimes>\<^sub>D F a)"
          using assms \<psi>_char(1-2) D.C\<^sub>1.lunit_char(2) D.comp_assoc by auto
        also have "... = ((D.inv \<psi> \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (\<iota>\<^sub>1 \<otimes>\<^sub>D F a) \<cdot>\<^sub>D ((\<psi> \<otimes>\<^sub>D \<psi>) \<otimes>\<^sub>D F a)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[\<I>\<^sub>D, \<I>\<^sub>D, F a]"
          using assms \<psi>_char(1-2) D.assoc'_naturality [of \<psi> \<psi> "F a"] D.comp_assoc by auto
        also have "... = (\<iota>\<^sub>D \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[\<I>\<^sub>D, \<I>\<^sub>D, F a]"
        proof -
          have "(D.inv \<psi> \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (\<iota>\<^sub>1 \<otimes>\<^sub>D F a) \<cdot>\<^sub>D ((\<psi> \<otimes>\<^sub>D \<psi>) \<otimes>\<^sub>D F a) = \<iota>\<^sub>D \<otimes>\<^sub>D F a"
          proof -
            have "(D.inv \<psi> \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (\<iota>\<^sub>1 \<otimes>\<^sub>D F a) \<cdot>\<^sub>D ((\<psi> \<otimes>\<^sub>D \<psi>) \<otimes>\<^sub>D F a) =
                  D.inv \<psi> \<cdot>\<^sub>D \<psi> \<cdot>\<^sub>D \<iota>\<^sub>D \<otimes>\<^sub>D F a"
              using assms \<psi>_char(1-3) D.\<iota>_in_hom \<iota>\<^sub>1_in_hom D.interchange
              by (elim D.in_homE, auto)
            also have "... = \<iota>\<^sub>D \<otimes>\<^sub>D F a"
              using assms \<psi>_char(1-2) D.inv_is_inverse D.comp_inv_arr D.comp_cod_arr
                    D.comp_reduce D.\<iota>_in_hom
              by (elim D.in_homE, auto)
            finally show ?thesis by blast
          qed
          thus ?thesis by simp
        qed
        also have "... = \<I>\<^sub>D \<otimes>\<^sub>D \<l>\<^sub>D[F a]"
          using assms D.lunit_char by simp
        finally show ?thesis by blast
      qed
      ultimately show ?thesis
        using D.L.is_faithful [of "\<l>\<^sub>1[F a] \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F a)" "\<l>\<^sub>D[F a]"] D.\<iota>_in_hom by force
    qed

    lemma lunit_coherence2:
    assumes "C.ide a"
    shows "F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) = \<l>\<^sub>1[F a]"
    proof -
      text \<open>
        We show that the lower left triangle in the following diagram commutes.
\<close>
      text \<open>
\newcommand\xIc{{\cal I}}
\newcommand\xId{{\cal I}}
\newcommand\xac[3]{{\scriptsize \<open>\<a>\<close>}[{#1},{#2},{#3}]}
\newcommand\xad[3]{{\scriptsize \<open>\<a>\<close>}[{#1},{#2},{#3}]}
\newcommand\xlc[1]{{\scriptsize \<open>\<l>\<close>}[{#1}]}
\newcommand\xld[1]{{\scriptsize \<open>\<l>\<close>}[{#1}]}
\newcommand\xldp[1]{{\scriptsize \<open>\<l>\<close>}_1[{#1}]}
$$\xymatrix{
  {(F\xIc\otimes F\xIc)\otimes F a}
      \ar[rrrrr]^{\phi(\xIc,\xIc)\otimes F a}
      \ar[ddd]_{\xad{F\xIc}{F\xIc}{Fa}}
      \ar[dddrr]^{\iota_1\otimes F a}
  &&&&&{F(\xIc\otimes\xIc)\otimes F a}
      \ar[ddd]^{\phi(\xIc\otimes\xIc, a)}
      \ar[dddlll]_{F\iota\otimes F a}
  \\ \\ \\
  {F\xIc\otimes(F\xIc\otimes F a)}
      \ar[ddd]_{F\xIc\otimes\phi(\xIc, a)}
      \ar[rr]_{F\xIc\otimes\xldp{Fa}}
  &&{F\xIc\otimes F a}
      \ar[r]_{\phi(\xIc, a)}
  &{F(\xIc\otimes a)}
  &&{F((\xIc\otimes\xIc)\otimes a)}
      \ar[ddd]^{F\xac{\xIc}{\xIc}{a}}
      \ar[ll]^{F(\iota\otimes a)}
  \\ \\ \\
  {F\xIc\otimes F (\xIc\otimes a)}
      \ar[rrrrr]_{\phi(\xIc, \xIc\otimes a)}
      \ar[uuurr]_{F\xIc\otimes F\xlc{a}}
  &&&&&{F(\xIc\otimes (\xIc \otimes a))}
      \ar[uuull]^{F(\xIc\otimes\xlc{a})}
}$$
\<close>
      have "(F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D (F \<I>\<^sub>C \<otimes>\<^sub>D \<phi> (\<I>\<^sub>C, a)) = F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]"
      proof -
        have "(F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D (F \<I>\<^sub>C \<otimes>\<^sub>D \<phi> (\<I>\<^sub>C, a))
                = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C, a] \<cdot>\<^sub>D
                  \<phi> (\<I>\<^sub>C \<otimes>\<^sub>C \<I>\<^sub>C, a) \<cdot>\<^sub>D (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
        proof -
          have "D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C, a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C \<otimes>\<^sub>C \<I>\<^sub>C, a) \<cdot>\<^sub>D
                       (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a)
                   = (F \<I>\<^sub>C \<otimes>\<^sub>D \<phi> (\<I>\<^sub>C, a)) \<cdot>\<^sub>D \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
            using assms \<phi>_in_hom assoc_coherence D.invert_side_of_triangle(1) by simp
          hence "F \<I>\<^sub>C \<otimes>\<^sub>D \<phi> (\<I>\<^sub>C, a)
                    = (D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C, a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C \<otimes>\<^sub>C \<I>\<^sub>C, a) \<cdot>\<^sub>D
                      (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a)) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
            using assms \<phi>_in_hom D.invert_side_of_triangle(2) by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         (D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D F (\<iota>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         \<phi> (\<I>\<^sub>C \<otimes>\<^sub>C \<I>\<^sub>C, a) \<cdot>\<^sub>D (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
        proof -
          have 1: "F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a]) = F (\<iota>\<^sub>C \<otimes>\<^sub>C a) \<cdot>\<^sub>D D.inv (F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C, a])"
            using assms C.lunit_char(1-2) C.\<iota>_in_hom preserves_inv by auto
          hence "F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C, a] = D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D F (\<iota>\<^sub>C \<otimes>\<^sub>C a)"
          proof -
            have "F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C, a] \<cdot>\<^sub>D D.inv (F (\<iota>\<^sub>C \<otimes>\<^sub>C a))
                    = D.inv (F (\<iota>\<^sub>C \<otimes>\<^sub>C a) \<cdot>\<^sub>D D.inv (F \<a>\<^sub>C[\<I>\<^sub>C, \<I>\<^sub>C ,a]))"
              using assms 1 preserves_iso C.ide_is_iso C.\<iota>_is_iso C.ide_unity C.iso_assoc
                    C.iso_lunit C.tensor_preserves_iso D.inv_comp D.inv_inv
                    D.iso_inv_iso D.iso_is_arr
              by metis
            thus ?thesis
              using assms 1 preserves_iso C.ide_is_iso C.\<iota>_is_iso C.ide_unity C.iso_assoc
                    C.iso_lunit C.tensor_preserves_iso D.inv_comp D.inv_inv
                    D.iso_inv_iso D.iso_is_arr D.invert_side_of_triangle(2)
              by metis
          qed
         thus ?thesis by argo
        qed
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D (F (\<iota>\<^sub>C \<otimes>\<^sub>C a) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C \<otimes>\<^sub>C \<I>\<^sub>C, a)) \<cdot>\<^sub>D
                         (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
          using D.comp_assoc by auto
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D (\<phi> (\<I>\<^sub>C, a) \<cdot>\<^sub>D (F \<iota>\<^sub>C \<otimes>\<^sub>D F a)) \<cdot>\<^sub>D
                         (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
          using assms \<phi>.naturality [of "(\<iota>\<^sub>C, a)"] C.\<iota>_in_hom by auto
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) \<cdot>\<^sub>D
                         ((F \<iota>\<^sub>C \<otimes>\<^sub>D F a) \<cdot>\<^sub>D (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C) \<otimes>\<^sub>D F a)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
          using D.comp_assoc by auto
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) \<cdot>\<^sub>D (\<iota>\<^sub>1 \<otimes>\<^sub>D F a) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
          using assms D.interchange C.\<iota>_in_hom by auto
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D
                         D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) \<cdot>\<^sub>D
                         ((F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]) \<cdot>\<^sub>D \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F \<I>\<^sub>C, F \<I>\<^sub>C, F a]"
        proof -
          have "(\<iota>\<^sub>1 \<otimes>\<^sub>D F a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F \<I>\<^sub>C, F \<I>\<^sub>C, F a] = F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]"
            using assms D.C\<^sub>1.lunit_char [of "F a"] by auto
          thus ?thesis
            using assms D.inv_is_inverse \<iota>\<^sub>1_in_hom \<phi>_in_hom D.invert_side_of_triangle(2)
            by simp
        qed
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D
                         (D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)) \<cdot>\<^sub>D
                         (F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a])"
          using assms D.comp_arr_dom [of "F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]"] D.comp_assoc by auto
        also have "... = (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D (F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a])"
        proof -
          have "D.inv (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a])
                   = D.inv (D.inv (\<phi> (\<I>\<^sub>C, a)) \<cdot>\<^sub>D F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a]) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a))"
            using assms \<phi>.naturality [of "(\<I>\<^sub>C, \<l>\<^sub>C[a])"] D.invert_side_of_triangle(1) by simp
          also have "... = D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)"
            using assms D.inv_comp D.iso_inv_iso D.inv_is_inverse D.isos_compose D.comp_assoc
            by simp
          finally have "D.inv (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a])
                          = D.inv (\<phi> (\<I>\<^sub>C, \<I>\<^sub>C \<otimes>\<^sub>C a)) \<cdot>\<^sub>D D.inv (F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])) \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)"
            by blast
          thus ?thesis by argo
        qed
        also have "... = ((F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a]) \<cdot>\<^sub>D D.inv (F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a])) \<cdot>\<^sub>D (F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a])"
          using assms D.tensor_preserves_iso D.comp_assoc by simp
        also have "... = F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]"
          using assms D.tensor_preserves_iso D.comp_arr_inv D.inv_is_inverse D.comp_cod_arr
                D.interchange
          by simp
        finally show ?thesis by blast
      qed
      hence "F \<I>\<^sub>C \<otimes>\<^sub>D F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) = F \<I>\<^sub>C \<otimes>\<^sub>D \<l>\<^sub>1[F a]"
        using assms \<phi>_in_hom D.interchange by simp
      moreover have "D.par (F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)) \<l>\<^sub>1[F a]"
        using assms \<phi>_in_hom by simp
      ultimately show ?thesis
        using D.C\<^sub>1.L.is_faithful [of "F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)" "\<l>\<^sub>1[F a]"] D.C\<^sub>1.unity_def by simp
    qed

    text \<open>
      Combining the two previous lemmas yields the coherence result we seek.
      This is the condition that is traditionally taken as part of the definition
      of monoidal functor.
\<close>

    lemma lunit_coherence:
    assumes "C.ide a"
    shows "\<l>\<^sub>D[F a] = F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F a)"
    proof -
      have "\<l>\<^sub>D[F a] \<cdot>\<^sub>D D.inv (\<psi> \<otimes>\<^sub>D F a) = \<l>\<^sub>1[F a]"
        using assms lunit_coherence1 \<psi>_char(2)
              D.invert_side_of_triangle(2) [of "\<l>\<^sub>D[F a]" "\<l>\<^sub>1[F a]" "\<psi> \<otimes>\<^sub>D F a"]
        by auto
      also have "... = F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)"
        using assms lunit_coherence2 by simp
      finally have "\<l>\<^sub>D[F a] \<cdot>\<^sub>D D.inv (\<psi> \<otimes>\<^sub>D F a) = F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)"
        by blast
      hence "\<l>\<^sub>D[F a] = (F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)) \<cdot>\<^sub>D (\<psi> \<otimes>\<^sub>D F a)"
        using assms \<psi>_char(2) D.iso_inv_iso \<phi>_in_hom
              D.invert_side_of_triangle(2) [of "F \<l>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (\<I>\<^sub>C, a)" "\<l>\<^sub>D[F a]" "D.inv (\<psi> \<otimes>\<^sub>D F a)"]
        by simp
      thus ?thesis
        using assms \<psi>_char(1) D.comp_assoc by auto
    qed

    text \<open>
      We now want to obtain the corresponding result for the right unitor.
      To avoid a repetition of what would amount to essentially the same tedious diagram chases
      that were carried out above, we instead show here that @{term F} becomes a monoidal functor
      from the opposite of \<open>C\<close> to the opposite of \<open>D\<close>,
      with @{term "\<lambda>f. \<phi> (snd f, fst f)"} as the structure map.
      The fact that in the opposite monoidal categories the left and right unitors are exchanged
      then permits us to obtain the result for the right unitor from the result already proved
      for the left unitor.
\<close>

    interpretation C': opposite_monoidal_category C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C ..
    interpretation D': opposite_monoidal_category D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D ..
    interpretation T\<^sub>D'oFF: composite_functor C.CC.comp D.CC.comp D FF.map D'.T ..
    interpretation FoT\<^sub>C': composite_functor C.CC.comp C D C'.T F ..
    interpretation \<phi>': natural_transformation C.CC.comp D T\<^sub>D'oFF.map FoT\<^sub>C'.map
                                              "\<lambda>f. \<phi> (snd f, fst f)"
      using \<phi>.is_natural_1 \<phi>.is_natural_2 \<phi>.is_extensional by (unfold_locales, auto)
    interpretation \<phi>': natural_isomorphism C.CC.comp D T\<^sub>D'oFF.map FoT\<^sub>C'.map
                                           "\<lambda>f. \<phi> (snd f, fst f)"
      by (unfold_locales, simp)
    interpretation F': monoidal_functor C C'.T C'.\<alpha> \<iota>\<^sub>C D D'.T D'.\<alpha> \<iota>\<^sub>D F "\<lambda>f. \<phi> (snd f, fst f)"
      using preserves_unity apply (unfold_locales; simp)
    proof -
      fix a b c
      assume a: "C.ide a" and b: "C.ide b" and c: "C.ide c"
      have "(\<phi> (c \<otimes>\<^sub>C b, a) \<cdot>\<^sub>D (\<phi> (c, b) \<otimes>\<^sub>D F a)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F c, F b, F a] =
            F (C.assoc' c b a) \<cdot>\<^sub>D \<phi> (c, b \<otimes>\<^sub>C a) \<cdot>\<^sub>D (F c \<otimes>\<^sub>D \<phi> (b, a))"
      proof -
        have "D.seq (F \<a>\<^sub>C[c, b, a]) (\<phi> (c \<otimes>\<^sub>C b, a) \<cdot>\<^sub>D (\<phi> (c, b) \<otimes>\<^sub>D F a))"
          using a b c \<phi>_in_hom by simp
        moreover have "D.seq (\<phi> (c, b \<otimes>\<^sub>C a) \<cdot>\<^sub>D (F c \<otimes>\<^sub>D \<phi> (b, a))) \<a>\<^sub>D[F c, F b, F a]"
          using a b c \<phi>_in_hom by simp
        moreover have
             "F \<a>\<^sub>C[c, b, a] \<cdot>\<^sub>D \<phi> (c \<otimes>\<^sub>C b, a) \<cdot>\<^sub>D (\<phi> (c, b) \<otimes>\<^sub>D F a) =
              (\<phi> (c, b \<otimes>\<^sub>C a) \<cdot>\<^sub>D (F c \<otimes>\<^sub>D \<phi> (b, a))) \<cdot>\<^sub>D \<a>\<^sub>D[F c, F b, F a]"
          using a b c assoc_coherence D.comp_assoc by simp
        moreover have "D.iso (F \<a>\<^sub>C[c,b,a])"
          using a b c by simp
        moreover have "D.iso \<a>\<^sub>D[F c, F b, F a]"
          using a b c by simp
        moreover have "D.inv (F \<a>\<^sub>C[c,b,a]) = F (C.assoc' c b a)"
          using a b c preserves_inv by simp
        ultimately show ?thesis
          using D.invert_opposite_sides_of_square by simp
      qed
      thus "F (C.assoc' c b a) \<cdot>\<^sub>D \<phi> (c, b \<otimes>\<^sub>C a) \<cdot>\<^sub>D (F c \<otimes>\<^sub>D \<phi> (b, a)) =
            \<phi> (c \<otimes>\<^sub>C b, a) \<cdot>\<^sub>D (\<phi> (c, b) \<otimes>\<^sub>D F a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F c, F b, F a]"
        using D.comp_assoc by simp
    qed

    lemma induces_monoidal_functor_between_opposites:
    shows "monoidal_functor C C'.T C'.\<alpha> \<iota>\<^sub>C D D'.T D'.\<alpha> \<iota>\<^sub>D F (\<lambda>f. \<phi> (snd f, fst f))"
      ..

    lemma runit_coherence:
    assumes "C.ide a"
    shows "\<r>\<^sub>D[F a] = F \<r>\<^sub>C[a] \<cdot>\<^sub>D \<phi> (a, \<I>\<^sub>C) \<cdot>\<^sub>D (F a \<otimes>\<^sub>D \<psi>)"
    proof -
      have "C'.lunit a = \<r>\<^sub>C[a]"
        using assms C'.lunit_simp by simp
      moreover have "D'.lunit (F a) = \<r>\<^sub>D[F a]"
        using assms D'.lunit_simp by simp
      moreover have "F'.\<psi> = \<psi>"
      proof (intro \<psi>_eqI)
        show "\<guillemotleft>F'.\<psi> : D'.unity \<rightarrow>\<^sub>D F C'.unity\<guillemotright>" using F'.\<psi>_char(1) by simp
        show "D.iso F'.\<psi>" using F'.\<psi>_char(2) by simp
        show "F'.\<psi> \<cdot>\<^sub>D \<iota>\<^sub>D = \<iota>\<^sub>1 \<cdot>\<^sub>D (F'.\<psi> \<otimes>\<^sub>D F'.\<psi>)" using F'.\<psi>_char(3) by simp
      qed
      moreover have "D'.lunit (F a) = F (C'.lunit a) \<cdot>\<^sub>D \<phi> (a, C'.unity) \<cdot>\<^sub>D (F a \<otimes>\<^sub>D F'.\<psi>)"
        using assms F'.lunit_coherence by simp
      ultimately show ?thesis by simp
    qed

  end

  section "Strict Monoidal Functor"

  text \<open>
    A strict monoidal functor preserves the monoidal structure ``on the nose''.
\<close>

  locale strict_monoidal_functor =
    C: monoidal_category C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C +
    D: monoidal_category D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D +
    "functor" C D F
  for C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and T\<^sub>C :: "'c * 'c \<Rightarrow> 'c"
  and \<alpha>\<^sub>C :: "'c * 'c * 'c \<Rightarrow> 'c"
  and \<iota>\<^sub>C :: "'c"
  and D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and T\<^sub>D :: "'d * 'd \<Rightarrow> 'd"
  and \<alpha>\<^sub>D :: "'d * 'd * 'd \<Rightarrow> 'd"
  and \<iota>\<^sub>D :: "'d"
  and F :: "'c \<Rightarrow> 'd" +
  assumes strictly_preserves_\<iota>: "F \<iota>\<^sub>C = \<iota>\<^sub>D"
  and strictly_preserves_T: "\<lbrakk> C.arr f; C.arr g \<rbrakk> \<Longrightarrow> F (T\<^sub>C (f, g)) = T\<^sub>D (F f, F g)"
  and strictly_preserves_\<alpha>_ide: "\<lbrakk> C.ide a; C.ide b; C.ide c \<rbrakk> \<Longrightarrow>
                                   F (\<alpha>\<^sub>C (a, b, c)) = \<alpha>\<^sub>D (F a, F b, F c)"
  begin

    notation C.tensor                  (infixr "\<otimes>\<^sub>C" 53)
    and C.unity                        ("\<I>\<^sub>C")
    and C.lunit                        ("\<l>\<^sub>C[_]")
    and C.runit                        ("\<r>\<^sub>C[_]")
    and C.assoc                        ("\<a>\<^sub>C[_, _, _]")
    and D.tensor                       (infixr "\<otimes>\<^sub>D" 53)
    and D.unity                        ("\<I>\<^sub>D")
    and D.lunit                        ("\<l>\<^sub>D[_]")
    and D.runit                        ("\<r>\<^sub>D[_]")
    and D.assoc                        ("\<a>\<^sub>D[_, _, _]")

    lemma strictly_preserves_tensor:
    assumes "C.arr f" and "C.arr g"
    shows "F (f \<otimes>\<^sub>C g) = F f \<otimes>\<^sub>D F g"
      using assms strictly_preserves_T by blast

    lemma strictly_preserves_\<alpha>:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "F (\<alpha>\<^sub>C (f, g, h)) = \<alpha>\<^sub>D (F f, F g, F h)"
    proof -
      have "F (\<alpha>\<^sub>C (f, g, h)) = F ((f \<otimes>\<^sub>C g \<otimes>\<^sub>C h) \<cdot>\<^sub>C \<alpha>\<^sub>C (C.dom f, C.dom g, C.dom h))"
        using assms C.\<alpha>.is_natural_1 [of "(f, g, h)"] C.T.ToCT_simp by force
      also have "... = (F f \<otimes>\<^sub>D F g \<otimes>\<^sub>D F h) \<cdot>\<^sub>D \<alpha>\<^sub>D (D.dom (F f), D.dom (F g), D.dom (F h))"
        using assms strictly_preserves_\<alpha>_ide strictly_preserves_tensor by simp
      also have "... = \<alpha>\<^sub>D (F f, F g, F h)"
        using assms D.\<alpha>.is_natural_1 [of "(F f, F g, F h)"] by simp
      finally show ?thesis by blast
    qed

    lemma strictly_preserves_unity:
    shows "F \<I>\<^sub>C = \<I>\<^sub>D"
      using C.\<iota>_in_hom strictly_preserves_\<iota> C.unity_def D.unity_def by auto

    lemma strictly_preserves_assoc:
    assumes "C.arr a" and "C.arr b" and "C.arr c"
    shows "F \<a>\<^sub>C[a, b, c] = \<a>\<^sub>D[F a, F b, F c] "
      using assms strictly_preserves_\<alpha> by simp

    lemma strictly_preserves_lunit:
    assumes "C.ide a"
    shows "F \<l>\<^sub>C[a] = \<l>\<^sub>D[F a]"
    proof -
      let ?P = "\<lambda>f. f \<in> C.hom (\<I>\<^sub>C \<otimes>\<^sub>C a) a \<and> \<I>\<^sub>C \<otimes>\<^sub>C f = (\<iota>\<^sub>C \<otimes>\<^sub>C a) \<cdot>\<^sub>C C.assoc' \<I>\<^sub>C \<I>\<^sub>C a"
      let ?Q = "\<lambda>f. f \<in> D.hom (\<I>\<^sub>D \<otimes>\<^sub>D F a) (F a) \<and>
                    \<I>\<^sub>D \<otimes>\<^sub>D f = (\<iota>\<^sub>D \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.assoc' \<I>\<^sub>D \<I>\<^sub>D (F a)"
      have 1: "?P \<l>\<^sub>C[a]" using assms C.lunit_char by simp
      hence "?Q (F \<l>\<^sub>C[a])"
      proof -
        have "F \<l>\<^sub>C[a] \<in> D.hom (\<I>\<^sub>D \<otimes>\<^sub>D F a) (F a)"
          using assms 1 strictly_preserves_unity strictly_preserves_tensor by auto
        moreover have
            "F ((\<iota>\<^sub>C \<otimes>\<^sub>C a) \<cdot>\<^sub>C C.assoc' \<I>\<^sub>C \<I>\<^sub>C a) = (\<iota>\<^sub>D \<otimes>\<^sub>D F a) \<cdot>\<^sub>D D.assoc' \<I>\<^sub>D \<I>\<^sub>D (F a)"
          using assms 1 strictly_preserves_\<iota> strictly_preserves_assoc strictly_preserves_unity
                strictly_preserves_tensor preserves_inv C.\<iota>_in_hom
          by auto
        moreover have "\<I>\<^sub>D \<otimes>\<^sub>D F \<l>\<^sub>C[a] = F (\<I>\<^sub>C \<otimes>\<^sub>C \<l>\<^sub>C[a])"
          using assms strictly_preserves_unity strictly_preserves_tensor by simp
        ultimately show ?thesis
          using assms C.lunit_char(2) by simp
      qed
      thus ?thesis using assms D.lunit_eqI by simp
    qed

    lemma strictly_preserves_runit:
    assumes "C.ide a"
    shows "F \<r>\<^sub>C[a] = \<r>\<^sub>D[F a]"
    proof -
      let ?P = "\<lambda>f. f \<in> C.hom (a \<otimes>\<^sub>C \<I>\<^sub>C) a \<and> f \<otimes>\<^sub>C \<I>\<^sub>C = (a \<otimes>\<^sub>C \<iota>\<^sub>C) \<cdot>\<^sub>C C.assoc a \<I>\<^sub>C \<I>\<^sub>C"
      let ?Q = "\<lambda>f. f \<in> D.hom (F a \<otimes>\<^sub>D \<I>\<^sub>D) (F a) \<and>
                    f \<otimes>\<^sub>D \<I>\<^sub>D = (F a \<otimes>\<^sub>D \<iota>\<^sub>D) \<cdot>\<^sub>D D.assoc (F a) \<I>\<^sub>D \<I>\<^sub>D"
      have 1: "?P \<r>\<^sub>C[a]" using assms C.runit_char by simp
      hence "?Q (F \<r>\<^sub>C[a])"
      proof -
        have "F \<r>\<^sub>C[a] \<in> D.hom (F a \<otimes>\<^sub>D \<I>\<^sub>D) (F a)"
          using assms 1 strictly_preserves_unity strictly_preserves_tensor by auto
        moreover have "F ((a \<otimes>\<^sub>C \<iota>\<^sub>C) \<cdot>\<^sub>C C.assoc a \<I>\<^sub>C \<I>\<^sub>C)
                         = (F a \<otimes>\<^sub>D \<iota>\<^sub>D) \<cdot>\<^sub>D D.assoc (F a) \<I>\<^sub>D \<I>\<^sub>D"
          using assms 1 strictly_preserves_\<iota> strictly_preserves_assoc strictly_preserves_unity
                strictly_preserves_tensor preserves_inv C.\<iota>_in_hom
          by auto
        moreover have "F \<r>\<^sub>C[a] \<otimes>\<^sub>D \<I>\<^sub>D = F (\<r>\<^sub>C[a] \<otimes>\<^sub>C \<I>\<^sub>C)"
          using assms strictly_preserves_unity strictly_preserves_tensor by simp
        ultimately show ?thesis
          using assms C.runit_char(2) by simp
      qed
      thus ?thesis using assms D.runit_eqI by simp
    qed

    text \<open>
      The following are used to simplify the expression of the sublocale relationship between
      @{locale strict_monoidal_functor} and @{locale monoidal_functor}, as the definition of
      the latter mentions the structure map @{term \<phi>}.  For a strict monoidal functor,
      this is an identity transformation.
\<close>

    interpretation FF: product_functor C C D D F F ..
    interpretation FoT\<^sub>C: composite_functor C.CC.comp C D T\<^sub>C F ..
    interpretation T\<^sub>DoFF: composite_functor C.CC.comp D.CC.comp D FF.map T\<^sub>D ..

    lemma structure_is_trivial:
    shows "T\<^sub>DoFF.map = FoT\<^sub>C.map"
    proof
      fix x
      have "C.CC.arr x \<Longrightarrow> T\<^sub>DoFF.map x = FoT\<^sub>C.map x"
      proof -
        assume x: "C.CC.arr x"
        have "T\<^sub>DoFF.map x = F (fst x) \<otimes>\<^sub>D F (snd x)"
          using x by simp
        also have "... = FoT\<^sub>C.map x"
          using x strictly_preserves_tensor [of "fst x" "snd x"] by simp
        finally show "T\<^sub>DoFF.map x = FoT\<^sub>C.map x" by simp
      qed
      moreover have "\<not> C.CC.arr x \<Longrightarrow> T\<^sub>DoFF.map x = FoT\<^sub>C.map x"
        using T\<^sub>DoFF.is_extensional FoT\<^sub>C.is_extensional by simp
      ultimately show "T\<^sub>DoFF.map x = FoT\<^sub>C.map x" by blast
    qed

    abbreviation \<phi> where "\<phi> \<equiv> T\<^sub>DoFF.map"

    lemma structure_is_natural_isomorphism:
    shows "natural_isomorphism C.CC.comp D T\<^sub>DoFF.map FoT\<^sub>C.map \<phi>"
      using T\<^sub>DoFF.natural_isomorphism_axioms structure_is_trivial by force

  end

  text \<open>
    A strict monoidal functor is a monoidal functor.
\<close>

  sublocale strict_monoidal_functor \<subseteq> monoidal_functor C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D F \<phi>
  proof -
    interpret FF: product_functor C C D D F F ..
    interpret FoT\<^sub>C: composite_functor C.CC.comp C D T\<^sub>C F ..
    interpret T\<^sub>DoFF: composite_functor C.CC.comp D.CC.comp D FF.map T\<^sub>D ..
    interpret \<phi>: natural_isomorphism C.CC.comp D T\<^sub>DoFF.map FoT\<^sub>C.map \<phi>
      using structure_is_natural_isomorphism by simp
    show "monoidal_functor C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D F \<phi>"
    proof
      show "D.isomorphic \<I>\<^sub>D (F \<I>\<^sub>C)"
      proof (unfold D.isomorphic_def)
        have "\<guillemotleft>\<I>\<^sub>D : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso \<I>\<^sub>D"
          using strictly_preserves_unity by auto
        thus "\<exists>f. \<guillemotleft>f : \<I>\<^sub>D \<rightarrow>\<^sub>D F \<I>\<^sub>C\<guillemotright> \<and> D.iso f" by blast
      qed
      fix a b c
      assume a: "C.ide a"
      assume b: "C.ide b"
      assume c: "C.ide c"
      show "F \<a>\<^sub>C[a, b, c] \<cdot>\<^sub>D \<phi> (a \<otimes>\<^sub>C b, c) \<cdot>\<^sub>D (\<phi> (a, b) \<otimes>\<^sub>D F c) =
            \<phi> (a, b \<otimes>\<^sub>C c) \<cdot>\<^sub>D (F a \<otimes>\<^sub>D \<phi> (b, c)) \<cdot>\<^sub>D \<a>\<^sub>D[F a, F b, F c]"
        using a b c strictly_preserves_tensor strictly_preserves_assoc
              D.comp_arr_dom D.comp_cod_arr
        by simp
    qed
  qed

  lemma strict_monoidal_functors_compose:
  assumes "strict_monoidal_functor B T\<^sub>B \<alpha>\<^sub>B \<iota>\<^sub>B C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C F"
  and "strict_monoidal_functor C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D G"
  shows "strict_monoidal_functor B T\<^sub>B \<alpha>\<^sub>B \<iota>\<^sub>B D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D (G o F)"
  proof -
    interpret F: strict_monoidal_functor B T\<^sub>B \<alpha>\<^sub>B \<iota>\<^sub>B C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C F
      using assms(1) by auto
    interpret G: strict_monoidal_functor C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D G
      using assms(2) by auto
    interpret GoF: composite_functor B C D F G ..
    show ?thesis
      using F.strictly_preserves_T F.strictly_preserves_\<iota> F.strictly_preserves_\<alpha>
            G.strictly_preserves_T G.strictly_preserves_\<iota> G.strictly_preserves_\<alpha>
      by (unfold_locales, simp_all)
  qed

  text \<open>
    An equivalence of monoidal categories is a monoidal functor whose underlying
    ordinary functor is also part of an ordinary equivalence of categories.
\<close>

  locale equivalence_of_monoidal_categories =
    C: monoidal_category C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C +
    D: monoidal_category D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D +
    equivalence_of_categories C D F G \<eta> \<epsilon> +
    monoidal_functor D T\<^sub>D \<alpha>\<^sub>D \<iota>\<^sub>D C T\<^sub>C \<alpha>\<^sub>C \<iota>\<^sub>C F \<phi>
  for C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and T\<^sub>C :: "'c * 'c \<Rightarrow> 'c"
  and \<alpha>\<^sub>C :: "'c * 'c * 'c \<Rightarrow> 'c"
  and \<iota>\<^sub>C :: "'c"
  and D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and T\<^sub>D :: "'d * 'd \<Rightarrow> 'd"
  and \<alpha>\<^sub>D :: "'d * 'd * 'd \<Rightarrow> 'd"
  and \<iota>\<^sub>D :: "'d"
  and F :: "'d \<Rightarrow> 'c"
  and \<phi> :: "'d * 'd \<Rightarrow> 'c"
  and \<iota> :: 'c
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"

end
