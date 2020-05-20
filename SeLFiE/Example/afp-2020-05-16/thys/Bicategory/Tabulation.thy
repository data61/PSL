(*  Title:       Tabulation
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Tabulations"

theory Tabulation
imports CanonicalIsos InternalAdjunction
begin

  text \<open>
    A ``tabulation'' is a kind of bicategorical limit that associates with a 1-cell \<open>r\<close>
    a triple \<open>(f, \<rho>, g)\<close>, where \<open>f\<close> and \<open>g\<close> are 1-cells having a common source,
    and \<open>\<rho>\<close> is a $2$-cell from \<open>g\<close> to \<open>r \<cdot> f\<close>, such that a certain biuniversal property
    is satisfied.
    The notion was introduced in a study of bicategories of spans and relations by
    Carboni, Kasangian, and Street \cite{carboni-et-al} (hereinafter, ``CKS''),
    who named it after a related,
    but different notion previously used by Freyd in his study of the algebra of relations.
    One can find motivation for the concept of tabulation by considering the problem of
    trying to find some kind of universal way of factoring a 1-cell \<open>r\<close>, up to isomorphism,
    as the composition \<open>g \<cdot> f\<^sup>*\<close> of a map \<open>g\<close> and the right adjoint \<open>f\<^sup>*\<close> of a map \<open>f\<close>.
    In order to be able to express this as a bicategorical limit, CKS consider,
    instead of an isomorphism \<open>\<guillemotleft>\<phi> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>\<close>, its transpose
    \<open>\<rho> : g \<Rightarrow> r \<star> f\<close> under the adjunction \<open>f \<stileturn> f\<^sup>*\<close>.
  \<close>

  subsection "Definition of Tabulation"

  text \<open>
    The following locale sets forth the ``signature'' of the data involved in a tabulation,
    and establishes some basic facts.
$$\xymatrix{
  & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f} \xtwocell[ddd]{}\omit{^\rho}
  \ar[ddl] _{g}
  \ar[ddr] ^{f}
  \\
  \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll] ^{r}
  \\
  &
}$$
  \<close>

  locale tabulation_data =
    bicategory +
  fixes r :: 'a
    and \<rho> :: 'a
    and f :: 'a
    and g :: 'a
  assumes ide_base: "ide r"
  and ide_leg0: "ide f"
  and tab_in_vhom': "\<guillemotleft>\<rho> : g \<Rightarrow> r \<star> f\<guillemotright>"
  begin

    lemma base_in_hom [intro]:
    shows "\<guillemotleft>r : src r \<rightarrow> trg r\<guillemotright>" and "\<guillemotleft>r : r \<Rightarrow> r\<guillemotright>"
      using ide_base by auto

    lemma base_simps [simp]:
    shows "ide r" and "arr r"
    and "dom r = r" and "cod r = r"
      using ide_base by auto

    lemma tab_in_hom [intro]:
    shows "\<guillemotleft>\<rho> : src f \<rightarrow> trg r\<guillemotright>" and "\<guillemotleft>\<rho> : g \<Rightarrow> r \<star> f\<guillemotright>"
      using tab_in_vhom' src_dom [of \<rho>] trg_dom [of \<rho>] base_in_hom apply auto
      by (metis arrI hcomp_simps(1) hcomp_simps(2) in_hhomI not_arr_null
          src.is_extensional src.preserves_hom vconn_implies_hpar(1)
          vconn_implies_hpar(2) vconn_implies_hpar(3) vconn_implies_hpar(4))

    lemma ide_leg1:
    shows "ide g"
      using tab_in_hom by auto

    lemma leg1_in_hom [intro]:
    shows "\<guillemotleft>g : src f \<rightarrow> trg r\<guillemotright>" and "\<guillemotleft>g : g \<Rightarrow> g\<guillemotright>"
      using ide_leg1 apply auto
      using tab_in_hom ide_dom [of \<rho>]
      apply (elim conjE in_homE) by auto

    lemma leg1_simps [simp]:
    shows "ide g" and "arr g"
    and "src g = src f" and "trg g = trg r"
    and "dom g = g"and "cod g = g"
      using ide_leg1 leg1_in_hom by auto

    lemma tab_simps [simp]:
    shows "arr \<rho>" and "src \<rho> = src f" and "trg \<rho> = trg r"
    and "dom \<rho> = g" and "cod \<rho> = r \<star> f"
      using tab_in_hom by auto

    lemma leg0_in_hom [intro]:
    shows "\<guillemotleft>f : src f \<rightarrow> src r\<guillemotright>" and "\<guillemotleft>f : f \<Rightarrow> f\<guillemotright>"
      using ide_leg0 apply auto
      using tab_in_hom ide_cod [of \<rho>] hseq_char [of r f]
      apply (elim conjE in_homE) by auto

    lemma leg0_simps [simp]:
    shows "ide f" and "arr f"
    and "trg f = src r"
    and "dom f = f" and "cod f = f"
      using ide_leg0 leg0_in_hom by auto

    text \<open>
      The following function, which composes \<open>\<rho>\<close> with a 2-cell \<open>\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>\<close> to obtain
      a 2-cell \<open>\<guillemotleft>(r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) : g \<star> w \<Rightarrow> r \<star> u\<guillemotright>"\<close>,
      occurs frequently in the sequel.
    \<close>

    abbreviation (input) composite_cell
    where "composite_cell w \<theta> \<equiv> (r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w)"

    lemma composite_cell_in_hom:
    assumes "ide w" and "\<guillemotleft>w : src u \<rightarrow> src f\<guillemotright>" and "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>"
    shows "\<guillemotleft>composite_cell w \<theta> : g \<star> w \<Rightarrow> r \<star> u\<guillemotright>"
    proof (intro comp_in_homI)
      show "\<guillemotleft>\<rho> \<star> w : g \<star> w \<Rightarrow> (r \<star> f) \<star> w\<guillemotright>"
        using assms tab_in_hom
        apply (elim conjE in_hhomE in_homE)
        by (intro hcomp_in_vhom, auto)
      show "\<guillemotleft>\<a>[r, f, w] : (r \<star> f) \<star> w \<Rightarrow> r \<star> f \<star> w\<guillemotright>"
        using assms ide_base ide_leg0 tab_in_hom by fastforce
      show "\<guillemotleft>r \<star> \<theta> : r \<star> f \<star> w \<Rightarrow> r \<star> u\<guillemotright>"
        using assms ide_base ide_leg0 tab_in_hom by fastforce
    qed

    text \<open>
      We define some abbreviations for various combinations of conditions that occur in the
      hypotheses and conclusions of the tabulation axioms.
    \<close>

    abbreviation (input) uw\<theta>\<omega>
    where "uw\<theta>\<omega> u w \<theta> \<omega> \<equiv> ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright>"

    abbreviation (input) uw\<theta>\<omega>\<nu>
    where "uw\<theta>\<omega>\<nu> u w \<theta> \<omega> \<nu> \<equiv>
           ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
             (r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu> = \<omega>"

    abbreviation (input) uw\<theta>w'\<theta>'\<beta>
    where "uw\<theta>w'\<theta>'\<beta> u w \<theta> w' \<theta>' \<beta> \<equiv>
               ide u \<and> ide w \<and> ide w' \<and>
               \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright> \<and>
               (r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) = (r \<star> \<theta>') \<cdot> \<a>[r, f, w'] \<cdot> (\<rho> \<star> w') \<cdot> \<beta>"

  end

  text \<open>
    CKS define two notions of tabulation.
    The first, which they call simply ``tabulation'', is restricted to triples \<open>(f, \<rho>, g)\<close>
    where the ``input leg'' \<open>f\<close> is a map, and assumes only a weak form of the biuniversal
    property that only applies to \<open>(u, \<omega>, v)\<close> for which u is a map.
    The second notion, which they call ``wide tabulation'', concerns arbitrary \<open>(f, \<rho>, g)\<close>,
    and assumes a strong form of the biuniversal property that applies to all \<open>(u, \<omega>, v)\<close>.
    On its face, neither notion implies the other: ``tabulation'' has the stronger assumption
    that \<open>f\<close> is a map, but requires a weaker biuniversal property, and ``wide tabulation''
    omits the assumption on \<open>f\<close>, but requires a stronger biuniversal property.
    CKS Proposition 1(c) states that if \<open>(f, \<rho>, g)\<close> is a wide tabulation,
    then \<open>f\<close> is automatically a map.  This is in fact true, but it took me a long time to
    reconstruct the details of the proof.
   
    CKS' definition of ``bicategory of spans'' uses their notion ``tabulation'',
    presumably because it is only applied in situations where maps are involved and it is more
    desirable to have axioms that involve a weaker biuniversal property rather than a stronger one.
    However I am more interested in ``wide tabulation'', as it is in some sense the nicer notion,
    and since I have had to establish various kinds of preservation results that I don't want
    to repeat for both tabulation and wide tabulation, I am using wide tabulation everywhere,
    calling it simply ``tabulation''.  The fact that the ``input leg'' of a tabulation must
    be a map is an essential ingredient throughout.
   
    I have attempted to follow CKS variable naming conventions as much as possible in this
    development to avoid confusion when comparing with their paper, even though these are
    sometimes at odds with what I have been using elsewhere in this document.
  \<close>

  locale tabulation =
    tabulation_data +
  assumes T1: "\<And>u \<omega>.
                 \<lbrakk> ide u; \<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright> \<rbrakk> \<Longrightarrow>
                 \<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                         composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
      and T2: "\<And>u w w' \<theta> \<theta>' \<beta>.
                 \<lbrakk> ide w; ide w'; \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>;
                   composite_cell w \<theta> = composite_cell w' \<theta>' \<cdot> \<beta> \<rbrakk> \<Longrightarrow>
                 \<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"

  text \<open>
$$
\textbf{T1:}\qquad\qquad
\xy/u67pt/
\xymatrix{
  & {\scriptstyle{{\rm src}~\omega}}
  \xlowertwocell[ddddl]{}_{{\rm dom}~\omega\hspace{20pt}}{^\nu}
  \xuppertwocell[ddddr]{}^{u}{^\theta}
  \ar@ {.>}[dd]^{w}
  \\
  \\
  & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f} \xtwocell[ddd]{}\omit{^\rho}
  \ar[ddl] _{g}
  \ar[ddr] ^{f}
  \\
  \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll] ^{r}
  \\
  &
}
\endxy
\;\;=\;\;
\xy/u33pt/
\xymatrix{
  & \scriptstyle{{\rm src}~\omega} \xtwocell[ddd]{}\omit{^\omega}
  \ar[ddl] _{{\rm dom}~\omega}
  \ar[ddr] ^{u}
  \\
  \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll] ^{r}
  \\
  &
}
\endxy
$$
  \<close>

  text \<open>
    The following definition includes the additional axiom \<open>T0\<close>, which states that
    the ``input leg'' \<open>f\<close> is a map.
  \<close>

  locale tabulation_data_with_T0 =
    tabulation_data +
    T0: map_in_bicategory V H \<a> \<i> src trg f
  begin

    abbreviation \<eta> where "\<eta> \<equiv> T0.\<eta>"
    abbreviation \<epsilon> where "\<epsilon> \<equiv> T0.\<epsilon>"

    text \<open>
      If \<open>\<guillemotleft>\<rho> : g \<Rightarrow> r \<star> f\<guillemotright>\<close> is a 2-cell and \<open>f\<close> is a map, then \<open>\<guillemotleft>T0.trnr\<^sub>\<epsilon> r \<rho> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>\<close>,
      where \<open>T0.trnr\<^sub>\<epsilon> r \<rho>\<close> is the adjoint transpose of \<open>\<rho>\<close>.
      We will show (CKS Proposition 1(d)) that if \<open>\<rho>\<close> is a tabulation,
      then \<open>\<psi> = T0.trnr\<^sub>\<epsilon> r \<rho>\<close> is an isomorphism.  However, regardless of whether \<open>\<rho>\<close> is a
      tabulation, the mapping \<open>\<rho> \<mapsto> \<psi>\<close> is injective, and we can recover \<open>\<rho>\<close> by the formula:
      \<open>\<rho> = (\<psi> \<star> f) \<cdot> T0.trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)\<close>.  The proof requires only \<open>T0\<close> and the ``syntactic''
      properties of the tabulation data, and in particular does not require the tabulation
      conditions \<open>T1\<close> and \<open>T2\<close>.  In case \<open>\<rho>\<close> is in fact a tabulation, then this formula can
      be interpreted as expressing that \<open>\<rho>\<close> is obtained by transposing the identity
      \<open>\<guillemotleft>g \<star> f\<^sup>* : g \<star> f\<^sup>* \<Rightarrow> g \<star> f\<^sup>*\<guillemotright>\<close> to obtain a 2-cell \<open>\<guillemotleft>T0.trnr\<^sub>\<eta> g (g \<star> f\<^sup>*) : g \<Rightarrow> (g \<star> f\<^sup>*) \<star> f\<guillemotright>\<close>
      (which may be regarded as the canonical tabulation of \<open>g \<star> f\<^sup>*\<close>), and then composing
      with the isomorphism \<open>\<guillemotleft>\<psi> \<star> f : (g \<star> f\<^sup>*) \<star> f \<Rightarrow> r \<star> f\<guillemotright>\<close> to obtain a tabulation of \<open>r\<close>.
      This fact will end up being very important in establishing the characterization of
      bicategories of spans.  Strangely, CKS doesn't make any explicit mention of it.
    \<close>

    lemma rep_in_hom [intro]:
    shows "\<guillemotleft>T0.trnr\<^sub>\<epsilon> r \<rho> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>"
    proof (unfold T0.trnr\<^sub>\<epsilon>_def, intro comp_in_homI)
      show "\<guillemotleft>\<rho> \<star> f\<^sup>* : g \<star> f\<^sup>* \<Rightarrow> (r \<star> f) \<star> f\<^sup>*\<guillemotright>"
        using tab_in_hom T0.antipar(1) by auto
      show "\<guillemotleft>\<a>[r, f, f\<^sup>*] : (r \<star> f) \<star> f\<^sup>* \<Rightarrow> r \<star> f \<star> f\<^sup>*\<guillemotright>"
        using T0.antipar(1-2) by auto
      show "\<guillemotleft>r \<star> \<epsilon> : r \<star> f \<star> f\<^sup>* \<Rightarrow> r \<star> src r\<guillemotright>"
        using T0.antipar by auto
      show "\<guillemotleft>\<r>[r] : r \<star> src r \<Rightarrow> r\<guillemotright>"
        by auto
    qed

    lemma \<rho>_in_terms_of_rep:
    shows "\<rho> = (T0.trnr\<^sub>\<epsilon> r \<rho> \<star> f) \<cdot> T0.trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)"
    proof -
      have "(T0.trnr\<^sub>\<epsilon> r \<rho> \<star> f) \<cdot> T0.trnr\<^sub>\<eta> g (g \<star> f\<^sup>*) =
            (\<r>[r] \<cdot> composite_cell f\<^sup>* \<epsilon> \<star> f) \<cdot> ((g \<star> f\<^sup>*) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] \<cdot> (g \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
        unfolding T0.trnr\<^sub>\<epsilon>_def T0.trnr\<^sub>\<eta>_def by simp
      text \<open>
$$
\xy/u67pt/
\xymatrix{
  & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f}
  \ar[ddl]_{g} \ar[ddr]^{f} \xtwocell[ddd]{}\omit{^\rho}
  &
  \\
  \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll]^{r}
  \\
  & &
}
\endxy
\;\;=\;\;
\xy/u133pt/
\xymatrix{
  & & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f} \ar[dd]
  \xtwocell[dddddddl]{}\omit{^\rho}
  \xlowertwocell[ddddll]{}_{g}{^{\hspace{20pt}{\rm r}^{-1}[g]}}
  \xuppertwocell[ddddrr]{}^{f}{\omit} & &
  \xtwocell[dddddddlll]{}\omit{^\epsilon}
  \xtwocell[ddddll]{}\omit{^\eta}
  \\
  & \\
  & & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f} \ar[dd]^{f} \ar[ddll]_{g}
  & \\
  & & & \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll]^{r}
  & &
  \scriptstyle{{\rm src}~r} \ar[ll] \ar[uull]_{f^\ast}
  \xuppertwocell[llll]{}^{r}<20>{^{\hspace{20pt}{\rm r}[r]}}
  \\
  & & \\
  & & \\
  & & & & \\
}
\endxy
$$
      \<close>
      also have "... = (\<r>[r] \<cdot> composite_cell f\<^sup>* \<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] \<cdot> (g \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
      proof -
        have "((g \<star> f\<^sup>*) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] = \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f]"
          using comp_cod_arr T0.antipar by simp
        thus ?thesis
          using comp_assoc by metis
      qed
      also have "... = (\<r>[r] \<star> f) \<cdot> (composite_cell f\<^sup>* \<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] \<cdot> (g \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
        using comp_assoc T0.antipar whisker_right [of "f" "\<r>[r]" "composite_cell f\<^sup>* \<epsilon>"]
        by fastforce
      also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<star> f) \<cdot> ((\<rho> \<star> f\<^sup>*) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] \<cdot>
                         (g \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
        using T0.antipar whisker_right [of "f" "(r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*]" "\<rho> \<star> f\<^sup>*"] comp_assoc
        by fastforce
      also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[r, f, f\<^sup>*] \<star> f) \<cdot>
                         ((\<rho> \<star> f\<^sup>*) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] \<cdot> (g \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
        using T0.antipar whisker_right [of "f" "r \<star> \<epsilon>" "\<a>[r, f, f\<^sup>*]"] comp_assoc by fastforce
      also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[r, f, f\<^sup>*] \<star> f) \<cdot>
                         \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] \<cdot> (\<rho> \<star> f\<^sup>* \<star> f) \<cdot> (g \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
      proof -
        have "((\<rho> \<star> f\<^sup>*) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sup>*, f] = \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] \<cdot> (\<rho> \<star> f\<^sup>* \<star> f)"
          using assoc'_naturality [of \<rho> "f\<^sup>*" "f"] T0.antipar by simp
        thus ?thesis
          using comp_assoc by metis
      qed
      also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot>
                         (\<a>[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] \<cdot>
                         ((r \<star> f) \<star> \<eta>) \<cdot> (\<rho> \<star> src (f)) \<cdot> \<r>\<^sup>-\<^sup>1[g]"
      proof -
        have "(\<rho> \<star> f\<^sup>* \<star> f) \<cdot> (g \<star> \<eta>) = ((r \<star> f) \<star> \<eta>) \<cdot> (\<rho> \<star> src (f))"
          using comp_arr_dom comp_cod_arr T0.antipar interchange [of \<rho> "g" "f\<^sup>* \<star> f" \<eta>]
                interchange [of "r \<star> f" \<rho> \<eta> "src (f)"]
          by auto
        thus ?thesis
          using comp_assoc by metis
      qed
      also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] \<cdot>
                         ((r \<star> f) \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f] \<cdot> \<rho>"
        using runit'_naturality [of \<rho>] by simp
      also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot>
                         \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f] \<cdot>
                         ((r \<star> f) \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f] \<cdot> \<rho>"
      proof - 
        have "(\<a>[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] =
              \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f]"
        proof -
          have "\<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] =
                (\<a>\<^sup>-\<^sup>1[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f]"
            using pentagon' [of r "f" "f\<^sup>*" "f"] T0.antipar iso_inv_iso iso_assoc comp_assoc
              invert_side_of_triangle(2)
                [of "((\<a>\<^sup>-\<^sup>1[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f])"
                    "\<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f]" "\<a>\<^sup>-\<^sup>1[r, f, f\<^sup>* \<star> f]"]
            by fastforce
          hence "(\<a>[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sup>*, f] =
                 ((\<a>[r, f, f\<^sup>*] \<star> f) \<cdot> (\<a>\<^sup>-\<^sup>1[r, f, f\<^sup>*] \<star> f)) \<cdot>
                   \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f]"
            using comp_assoc by simp
          also have "... = \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f]"
          proof -
            have "(\<a>[r, f, f\<^sup>*] \<star> f) \<cdot> (\<a>\<^sup>-\<^sup>1[r, f, f\<^sup>*] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] =
                  ((r \<star> f \<star> f\<^sup>*) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f]"
              using comp_cod_arr comp_assoc iso_assoc comp_arr_inv T0.antipar
                    whisker_right [of "f" "\<a>[r, f, f\<^sup>*]" "\<a>\<^sup>-\<^sup>1[r, f, f\<^sup>*]"] comp_assoc_assoc'
              by simp
            also have "... = \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f]"
              using comp_cod_arr T0.antipar by auto
            finally show ?thesis
              using comp_assoc by metis
          qed
          finally show ?thesis by blast
        qed
        thus ?thesis
          using comp_assoc by metis
      qed
      also have "... = (\<r>[r] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> \<epsilon> \<star> f) \<cdot>
                         (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> (r \<star> f \<star> \<eta>) \<cdot> \<a>[r, f, src (f)] \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f] \<cdot> \<rho>"
      proof -
        have "((r \<star> \<epsilon>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sup>*, f] = \<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> \<epsilon> \<star> f)"
          using assoc'_naturality [of r \<epsilon> "f"] by auto
        moreover have "\<a>[r, f, f\<^sup>* \<star> f] \<cdot> ((r \<star> f) \<star> \<eta>) = (r \<star> f \<star> \<eta>) \<cdot> \<a>[r, f, src (f)]"
          using assoc_naturality [of r "f" \<eta>] T0.antipar by auto
        ultimately show ?thesis
          using comp_assoc by metis
      qed
      also have "... = (\<r>[r] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> (\<epsilon> \<star> f) \<cdot>
                         \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<cdot> (f \<star> \<eta>)) \<cdot> \<a>[r, f, src (f)] \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f] \<cdot> \<rho>"
      proof -
        have "seq \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] (f \<star> \<eta>)"
          using T0.antipar by force
        moreover have "seq (\<epsilon> \<star> f) (\<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<cdot> (f \<star> \<eta>))"
          using T0.antipar by fastforce
        ultimately have "(r \<star> \<epsilon> \<star> f) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]) \<cdot> (r \<star> f \<star> \<eta>) =
                         r \<star> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<cdot> (f \<star> \<eta>)"
          using T0.antipar whisker_left [of r "\<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f]" "f \<star> \<eta>"]
                whisker_left [of r "\<epsilon> \<star> f" "\<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<cdot> (f \<star> \<eta>)"]
          by auto
        thus ?thesis
          using comp_assoc by metis
      qed
      also have "... = (\<r>[r] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) \<cdot>
                         \<a>[r, f, src (f)] \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f] \<cdot> \<rho>"
        using T0.triangle_left by simp
      also have "... = ((\<r>[r] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> \<l>\<^sup>-\<^sup>1[f])) \<cdot>
                         ((r \<star> \<r>[f]) \<cdot> \<a>[r, f, src (f)] \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f]) \<cdot> \<rho>"
        using whisker_left [of r "\<l>\<^sup>-\<^sup>1[f]" "\<r>[f]"] comp_assoc by simp
      also have "... = ((r \<star> \<l>[f]) \<cdot> (r \<star> \<l>\<^sup>-\<^sup>1[f])) \<cdot> (\<r>[r \<star> f] \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f]) \<cdot> \<rho>"
        using triangle' [of r "f"] runit_hcomp [of r "f"] comp_assoc by simp
      also have "... = \<rho>"
      proof -
        have "(r \<star> \<l>[f]) \<cdot> (r \<star> \<l>\<^sup>-\<^sup>1[f]) = r \<star> f"
          using iso_lunit comp_arr_inv' whisker_left [of r "\<l>[f]" "\<l>\<^sup>-\<^sup>1[f]"] by simp
        moreover have "(\<r>[r \<star> f] \<cdot> \<r>\<^sup>-\<^sup>1[r \<star> f]) = r \<star> f"
          using iso_runit inv_is_inverse comp_arr_inv' by auto
        ultimately show ?thesis
          using comp_cod_arr by simp
      qed
      finally show ?thesis by simp
    qed

  end

  text \<open>
    The following corresponds to what CKS call ``tabulation''; it supposes axiom \<open>T0\<close>,
    but involves weaker versions of \<open>T1\<close> and \<open>T2\<close>.  I am calling it ``narrow tabulation''.
  \<close>

  locale narrow_tabulation =
    tabulation_data_with_T0 +
  assumes T1: "\<And>u \<omega>.
                  \<lbrakk> is_left_adjoint u; \<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright> \<rbrakk> \<Longrightarrow>
                  \<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                          composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
      and T2: "\<And>u w w' \<theta> \<theta>' \<beta>.
                  \<lbrakk> is_left_adjoint u; ide w; ide w';
                    \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>;
                    composite_cell w \<theta> = composite_cell w' \<theta>' \<cdot> \<beta> \<rbrakk> \<Longrightarrow>
                  \<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"

  text \<open>
    The next few locales are used to bundle up some routine consequences of
    the situations described by the hypotheses and conclusions of the tabulation axioms,
    so we don't have to keep deriving them over and over again in each context,
    and also so as to keep the simplification rules oriented consistently with each other.
  \<close>

  locale uw\<theta> =
    tabulation_data +
  fixes u :: 'a
  and w :: 'a
  and \<theta> :: 'a
  assumes uw\<theta>: "ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>"
  begin

    lemma ide_u:
    shows "ide u"
      using uw\<theta> by force

    lemma u_in_hom [intro]:
    shows "\<guillemotleft>u : src u \<rightarrow> src r\<guillemotright>"
      using uw\<theta> ide_u ide_cod [of \<theta>] hseq_char [of f w]
      apply (intro in_hhomI, simp_all)
      by (metis arr_dom in_homE leg0_simps(3) trg_hcomp vconn_implies_hpar(4))

    lemma u_simps [simp]:
    shows "ide u" and "arr u"
    and "trg u = src r"
    and "dom u = u" and "cod u = u"
      using ide_u u_in_hom by auto

    lemma ide_w:
    shows "ide w"
      using uw\<theta> by auto

    lemma w_in_hom [intro]:
    shows "\<guillemotleft>w : src u \<rightarrow> src f\<guillemotright>" and "\<guillemotleft>w : w \<Rightarrow> w\<guillemotright>"
    proof -
      show "\<guillemotleft>w : w \<Rightarrow> w\<guillemotright>"
        using ide_w by auto
      show "\<guillemotleft>w : src u \<rightarrow> src f\<guillemotright>"
      proof
        show "arr w" using ide_w by simp
        show "src w = src u"
          using uw\<theta> ide_dom [of \<theta>] hseq_char [of f w]
          by (metis arr_dom in_homE src_cod src_dom hcomp_simps(1))
        show "trg w = src f"
          using uw\<theta> ide_dom [of \<theta>] hseq_char [of f w]
          by (metis arr_dom in_homE)
      qed
    qed

    lemma w_simps [simp]:
    shows "ide w" and "arr w"
    and "src w = src u" and "trg w = src f"
    and "dom w = w" and "cod w = w"
      using ide_w w_in_hom by auto

    lemma \<theta>_in_hom [intro]:
    shows "\<guillemotleft>\<theta> : src u \<rightarrow> src r\<guillemotright>" and "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>"
    proof -
      show "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>"
        using uw\<theta> by simp
      show "\<guillemotleft>\<theta> : src u \<rightarrow> src r\<guillemotright>"
        using uw\<theta> src_dom trg_dom hcomp_simps(1-2) by fastforce
    qed

    lemma \<theta>_simps [simp]:
    shows "arr \<theta>" and "src \<theta> = src u" and "trg \<theta> = src r"
    and "dom \<theta> = f \<star> w" and "cod \<theta> = u"
      using \<theta>_in_hom by auto

  end

  locale uw\<theta>\<omega> =
    uw\<theta> +
  fixes \<omega> :: 'a
  assumes uw\<theta>\<omega>: "uw\<theta>\<omega> u w \<theta> \<omega>"
  begin

    lemma \<omega>_in_hom [intro]:
    shows "\<guillemotleft>\<omega> : src w \<rightarrow> trg r\<guillemotright>" and "\<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright>"
    proof -
      show "\<guillemotleft>\<omega> : src w \<rightarrow> trg r\<guillemotright>"
        using uw\<theta>\<omega> src_cod [of \<omega>] trg_cod [of \<omega>]
        apply (elim conjE in_homE)
        by simp
      show "\<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright>"
        using uw\<theta>\<omega> by auto
    qed

    lemma \<omega>_simps [simp]:
    shows "arr \<omega>" and "src \<omega> = src w" and "trg \<omega> = trg r"
    and "cod \<omega> = r \<star> u"
      using \<omega>_in_hom by auto

  end

  locale uw\<theta>\<omega>\<nu> =
    uw\<theta> +
  fixes \<omega> :: 'a
  and \<nu> :: 'a
  assumes uw\<theta>\<omega>\<nu>: "uw\<theta>\<omega>\<nu> u w \<theta> \<omega> \<nu>"
  begin

    lemma \<nu>_in_hom [intro]:
    shows "\<guillemotleft>\<nu> : src u \<rightarrow> trg r\<guillemotright>" and "\<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright>"
    proof -
      show "\<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright>"
        using uw\<theta>\<omega>\<nu> by auto
      show "\<guillemotleft>\<nu> : src u \<rightarrow> trg r\<guillemotright>"
      proof
        show 1: "arr \<nu>"
          using uw\<theta>\<omega>\<nu> by auto
        show "src \<nu> = src u"
        proof -
          have "src \<nu> = src (cod \<nu>)"
            using 1 uw\<theta>\<omega>\<nu> src_cod [of \<nu>] by simp
          also have "... = src u"
            using uw\<theta>\<omega>\<nu> by auto
          finally show ?thesis by simp
        qed
        show "trg \<nu> = trg r"
        proof -
          have "trg \<nu> = trg (cod \<nu>)"
            using 1 uw\<theta>\<omega>\<nu> src_cod [of \<nu>] by simp
          also have "... = trg r"
            using uw\<theta>\<omega>\<nu> by auto
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma \<nu>_simps [simp]:
    shows "iso \<nu>" and "arr \<nu>" and "src \<nu> = src u" and "trg \<nu> = trg r"
    and "cod \<nu> = g \<star> w"
      using uw\<theta>\<omega>\<nu> \<nu>_in_hom by auto

    sublocale uw\<theta>\<omega>
    proof (unfold_locales, intro conjI)
      show "ide w"
        using uw\<theta>\<omega>\<nu> by simp
      show "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>"
        using uw\<theta>\<omega>\<nu> by simp
      have "\<guillemotleft>(r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu> : dom \<nu> \<Rightarrow> r \<star> u\<guillemotright>"
        using ide_base ide_leg0 ide_w by fastforce
      thus "\<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright>"
        using uw\<theta>\<omega>\<nu> by auto
    qed

  end


  locale uw\<theta>w'\<theta>' =
    tabulation_data V H \<a> \<iota> src trg r \<rho> f g +
    uw\<theta>: uw\<theta> V H \<a> \<iota> src trg r \<rho> f g u w \<theta> +
    uw'\<theta>': uw\<theta> V H \<a> \<iota> src trg r \<rho> f g u w' \<theta>'
  for V :: "'a comp"                 (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"          (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"     ("\<a>[_, _, _]")
  and \<iota> :: "'a \<Rightarrow> 'a"                 ("\<i>[_]")
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a"
  and r :: 'a
  and \<rho> :: 'a
  and f :: 'a
  and g :: 'a
  and u :: 'a
  and w :: 'a
  and \<theta> :: 'a
  and w' :: 'a
  and \<theta>' :: 'a
   
  locale uw\<theta>w'\<theta>'\<gamma> =
    uw\<theta>w'\<theta>' +
  fixes \<gamma> :: 'a
  assumes \<gamma>_in_vhom: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright>"
  and "\<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
  begin

    lemma \<gamma>_in_hom [intro]:
    shows "\<guillemotleft>\<gamma> : src u \<rightarrow> src f\<guillemotright>" and "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright>"
    proof -
      show "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright>"
        using \<gamma>_in_vhom by simp
      show "\<guillemotleft>\<gamma> : src u \<rightarrow> src f\<guillemotright>"
      proof
        show "arr \<gamma>"
          using \<gamma>_in_vhom by auto
        show "src \<gamma> = src u"
          using \<gamma>_in_vhom src_dom [of \<gamma>]
          apply (elim in_homE) by simp
        show "trg \<gamma> = src f"
          using \<gamma>_in_vhom trg_dom [of \<gamma>]
          apply (elim in_homE) by simp
      qed
    qed

    lemma \<gamma>_simps [simp]:
    shows "arr \<gamma>" 
    and "src \<gamma> = src u" and "trg \<gamma> = src f"
    and "dom \<gamma> = w" and "cod \<gamma> = w'"
      using \<gamma>_in_hom by auto

  end

  locale uw\<theta>w'\<theta>'\<beta> =
    uw\<theta>w'\<theta>' +
  fixes \<beta> :: 'a
  assumes uw\<theta>w'\<theta>'\<beta>: "uw\<theta>w'\<theta>'\<beta> u w \<theta> w' \<theta>' \<beta>"
  begin

    lemma \<beta>_in_hom [intro]:
    shows "\<guillemotleft>\<beta> : src u \<rightarrow> trg r\<guillemotright>" and "\<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>"
    proof -
      show "\<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>"
        using uw\<theta>w'\<theta>'\<beta> by auto
      show "\<guillemotleft>\<beta> : src u \<rightarrow> trg r\<guillemotright>"
        using uw\<theta>w'\<theta>'\<beta> src_dom [of \<beta>] trg_dom [of \<beta>] hseq_char [of g w]
        apply (elim conjE in_homE) by auto
    qed

    lemma \<beta>_simps [simp]:
    shows "arr \<beta>" and "src \<beta> = src u" and "trg \<beta> = trg r"
    and "dom \<beta> = g \<star> w" and "cod \<beta> = g \<star> w'"
      using \<beta>_in_hom by auto

  end

  subsection "Tabulations yield Factorizations"

  text \<open>
    If \<open>(f, \<rho>, g)\<close> is a (wide) tabulation, then \<open>f\<close> is automatically a map;
    this is CKS Proposition 1(c).
    The proof sketch provided by CKS is only three lines long, and for a long time I
    was only able to prove one of the two triangle identities.
    Finally, after gaining a lot of experience with the definitions I saw how to prove
    the other.
    CKS say nothing about the extra step that seems to be required.
  \<close>

  context tabulation
  begin

    text \<open>
      The following is used in order to allow us to apply the coherence theorem
      to shortcut proofs of equations between canonical arrows.
    \<close>

    interpretation E: self_evaluation_map V H \<a> \<i> src trg ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    lemma satisfies_T0:
    shows "is_left_adjoint f"
    proof -
      text \<open>
        The difficulty is filling in details left out by CKS, and accounting for the
        fact that they have suppressed unitors and associators everywhere.
        In addition, their typography generally uses only parentheses, with no explicit
        operation symbols to distinguish between horizontal and vertical composition.
        In some cases, for example the statement of T2 in the definition of tabulation,
        this makes it difficult for someone not very experienced with the definitions to
        reconstruct the correct formulas.
      \<close>
      text \<open>
        CKS say to first apply \<open>T1\<close> with \<open>u = src r\<close>, \<open>v = r\<close>, and \<open>\<rho>' = r\<close>.
        However, \<open>\<guillemotleft>r : r \<Rightarrow> r\<guillemotright>\<close>, not \<open>\<guillemotleft>r : r \<Rightarrow> r \<star> src r\<guillemotright>\<close>, so we have to take \<open>\<rho>' = \<r>\<^sup>-\<^sup>1[r]\<close>.
      \<close>
      obtain f\<^sub>a \<epsilon> \<nu>
      where f\<^sub>a: "ide f\<^sub>a \<and> \<guillemotleft>\<epsilon> : f \<star> f\<^sub>a \<Rightarrow> src r\<guillemotright> \<and> \<guillemotleft>\<nu> : r \<Rightarrow> g \<star> f\<^sub>a\<guillemotright> \<and> iso \<nu> \<and>
                 composite_cell f\<^sub>a \<epsilon> \<cdot> \<nu> = \<r>\<^sup>-\<^sup>1[r]"
        using T1 [of "src r" "\<r>\<^sup>-\<^sup>1[r]"] runit'_in_hom [of r] ide_base comp_assoc by auto
      have f\<^sub>a': "composite_cell f\<^sub>a \<epsilon> \<cdot> \<nu> = \<r>\<^sup>-\<^sup>1[r]"
        using f\<^sub>a by simp
      have f\<^sub>a: "ide f\<^sub>a \<and> \<guillemotleft>\<epsilon> : f \<star> f\<^sub>a \<Rightarrow> src r\<guillemotright> \<and> \<guillemotleft>\<nu> : r \<Rightarrow> g \<star> f\<^sub>a\<guillemotright> \<and> iso \<nu>"
        using f\<^sub>a by simp
      have 1: "src f\<^sub>a = trg f"
        using f\<^sub>a f\<^sub>a' comp_assoc
        by (metis ide_base leg0_simps(3) runit'_simps(1) seqE src_hcomp vconn_implies_hpar(1)
            vseq_implies_hpar(1))
      have 2: "trg f\<^sub>a = src g"
        using f\<^sub>a by force
      have \<epsilon>: "\<guillemotleft>\<epsilon> : f \<star> f\<^sub>a \<Rightarrow> trg f\<guillemotright> \<and> \<guillemotleft>\<epsilon> : trg f \<rightarrow> trg f\<guillemotright> \<and>
               arr \<epsilon> \<and> src \<epsilon> = trg f \<and> trg \<epsilon> = trg f \<and> dom \<epsilon> = f \<star> f\<^sub>a \<and> cod \<epsilon> = trg f"
        using f\<^sub>a src_cod [of \<epsilon>] trg_cod [of \<epsilon>] 1 2 by fastforce
      have \<nu>: "\<guillemotleft>\<nu> : r \<Rightarrow> g \<star> f\<^sub>a\<guillemotright> \<and> \<guillemotleft>\<nu> : trg f \<rightarrow> trg g\<guillemotright> \<and>
               arr \<nu> \<and> src \<nu> = trg f \<and> trg \<nu> = trg g \<and> dom \<nu> = r \<and> cod \<nu> = g \<star> f\<^sub>a"
        using f\<^sub>a by force
      text \<open>
        Next, CKS say to apply \<open>T2\<close> with \<open>w = trg f\<^sub>a = src f\<close>, \<open>w' = f\<^sub>a \<star> f\<close>, \<open>u = f\<close>,
        to obtain the unit and the adjunction conditions, but they don't say explicitly
        what to use for \<open>\<theta>\<close>, \<open>\<theta>'\<close>, and \<open>\<beta>\<close>.
        We need \<open>\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>\<close> and \<open>\<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>\<close>;
        \emph{i.e.}~\<open>\<guillemotleft>\<theta> : f \<star> trg f\<^sub>a \<Rightarrow> f\<guillemotright>\<close> and \<open>\<guillemotleft>\<theta>' : f \<star> f\<^sub>a \<star> f \<Rightarrow> f\<guillemotright>\<close>.
        Evidently, we may take \<open>\<theta> = \<rho>[f]\<close> and \<open>\<theta>' = \<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]\<close>.

        What should be taken for \<open>\<beta>\<close>?  Reconstructing this is a little bit more difficult.
        \<open>T2\<close> requires \<open>\<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>\<close>, hence \<open>\<guillemotleft>\<beta> : g \<star> trg f\<^sub>a \<Rightarrow> g \<star> f\<^sub>a \<star> f\<guillemotright>\<close>.
        We have the isomorphism \<open>\<guillemotleft>\<nu> : r \<Rightarrow> g \<star> f\<^sub>a\<guillemotright>\<close> from \<open>T1\<close>.  Also \<open>\<guillemotleft>\<rho> : g \<Rightarrow> r \<star> f\<guillemotright>\<close>.
        So \<open>\<guillemotleft>\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g] : g \<star> trg f\<^sub>a \<Rightarrow> g \<star> f\<^sub>a \<star> f\<guillemotright>\<close>,
        suggesting that we take \<open>\<beta> = \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g]\<close>.
        Now, to apply \<open>T2\<close> we need to satisfy the equation:
        \[
           \<open>(r \<star> \<theta>) \<cdot> \<a>[r, f, trg f\<^sub>a] \<cdot> (\<rho> \<star> trg f\<^sub>a ) =
           (r \<star> \<theta>') \<cdot> \<a>[r, f, f\<^sub>a \<star> f] \<cdot> (\<rho> \<star> f\<^sub>a \<star> f) \<cdot> \<beta>\<close>;
        \]
        that is, with our choice of \<open>\<theta>\<close>, \<open>\<theta>'\<close>, and \<open>\<beta>\<close>:

        \<open>(r \<star> \<r>[f]) \<cdot> \<a>[r, f, trg f\<^sub>a] \<cdot> (\<rho> \<star> trg f\<^sub>a ) =
         (r \<star> \<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]) \<cdot> \<a>[r, f, f\<^sub>a \<star> f] \<cdot> (\<rho> \<cdot> (f\<^sub>a \<star> f)) \<cdot>
               \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g]\<close>.

        It is not too difficult to get the idea of showing that the left-hand side
        is equal to \<open>\<rho> \<cdot> \<r>[g]\<close> (note that \<open>trg f\<^sub>a = src f = src g]\<close> and \<open>trg f = src r\<close>),
        so we should also try to prove that the right-hand side is equal to this as well.
        What we have to work with is the equation:
        \[
           \<open>\<r>\<^sup>-\<^sup>1[r] = (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sub>a] \<cdot> (\<rho> \<star> f\<^sub>a ) \<cdot> \<nu>\<close>.
        \]
        After some pondering, I realized that to apply this to the right-hand side of the
        equation to be shown requires that we re-associate everything to the left,
        so that f stands alone on the right.
      \<close>
      let ?\<beta> = "\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g]"
      let ?\<theta> = "\<r>[f]"
      let ?\<theta>' = "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]"
      have \<beta>: "\<guillemotleft>?\<beta> : g \<star> src g \<Rightarrow> g \<star> f\<^sub>a \<star> f\<guillemotright> \<and> \<guillemotleft>?\<beta> : src f \<rightarrow> trg g\<guillemotright> \<and>
               src ?\<beta> = src g \<and> trg ?\<beta> = trg g \<and> dom ?\<beta> = g \<star> src g \<and> cod ?\<beta> = g \<star> f\<^sub>a \<star> f"
      proof -
        have 3: "\<guillemotleft>?\<beta> : g \<star> src g \<Rightarrow> g \<star> f\<^sub>a \<star> f\<guillemotright>"
          using f\<^sub>a 1 2 by fastforce
        moreover have "\<guillemotleft>?\<beta> : src f \<rightarrow> trg g\<guillemotright>"
          using 1 2 3 f\<^sub>a by auto
        ultimately show ?thesis
          by (auto simp add: in_hhom_def)
      qed
      have \<theta>': "\<guillemotleft>?\<theta>' : f \<star> f\<^sub>a \<star> f \<Rightarrow> f\<guillemotright>"
        using f\<^sub>a 1 2 \<epsilon> by fastforce
      have A: "composite_cell (trg f\<^sub>a) \<r>[f] = composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> ?\<beta>"
      proof -
        have "composite_cell (trg f\<^sub>a) \<r>[f] = \<rho> \<cdot> \<r>[g]"
          using 2 runit_hcomp runit_naturality [of \<rho>] comp_assoc by simp
        also have "... = composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> ?\<beta>"
        proof -
          have "composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> ?\<beta> =
                (composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> \<a>[g, f\<^sub>a, f]) \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g]"
            using comp_assoc by simp
          also have "... = \<rho> \<cdot> \<r>[g]"
          proof -
            have "(composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> \<a>[g, f\<^sub>a, f]) \<cdot> (\<nu> \<star> f) = r \<star> f"
            proof -
              have "(composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> \<a>[g, f\<^sub>a, f]) \<cdot> (\<nu> \<star> f) =
                    \<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sub>a] \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> \<nu> \<star> f"
              proof -
                have "(composite_cell (f\<^sub>a \<star> f) ?\<theta>' \<cdot> \<a>[g, f\<^sub>a, f]) \<cdot> (\<nu> \<star> f) =
                      (r \<star> \<l>[f]) \<cdot> (r \<star> \<epsilon> \<star> f) \<cdot>
                        composite_cell (f\<^sub>a \<star> f) \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f))"
                  using f\<^sub>a 1 2 \<epsilon> whisker_left comp_assoc by auto
                also have "... = (\<r>[r] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> \<epsilon> \<star> f) \<cdot>
                                   composite_cell (f\<^sub>a \<star> f) \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f))"
                  using f\<^sub>a 1 2 comp_assoc by (simp add: triangle')
                also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sub>a, f] \<cdot>
                                   composite_cell (f\<^sub>a \<star> f) \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f))"
                proof -
                  have "\<a>\<^sup>-\<^sup>1[r, src r, f] \<cdot> (r \<star> \<epsilon> \<star> f) = ((r \<star> \<epsilon>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sub>a, f]"
                    using f\<^sub>a \<epsilon> assoc'_naturality [of r \<epsilon> f] by auto
                  thus ?thesis
                    using comp_assoc by metis
                qed
                also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot>
                                   (\<a>[r, f, f\<^sub>a] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sub>a, f] \<cdot> (\<rho> \<star> f\<^sub>a \<star> f) \<cdot>
                                     \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f)"
                proof -
                  have "(\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sub>a, f] \<cdot>
                          composite_cell (f\<^sub>a \<star> f) \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f)) =
                        (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot>
                          (\<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sub>a, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]) \<cdot> \<a>[r, f, f\<^sub>a \<star> f]) \<cdot>
                            (\<rho> \<star> f\<^sub>a \<star> f) \<cdot> \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f)"
                    by (simp add: comp_assoc)
                  also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot>
                                     ((\<a>[r, f, f\<^sub>a] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sub>a, f]) \<cdot>
                                       (\<rho> \<star> f\<^sub>a \<star> f) \<cdot> \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f)"
                  proof -
                    have "\<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sub>a, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]) \<cdot> \<a>[r, f, f\<^sub>a \<star> f] =
                            (\<a>[r, f, f\<^sub>a] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sub>a, f]"
                    proof -
                      (* No need to calculate manually, apply the coherence theorem. *)
                      have "\<a>\<^sup>-\<^sup>1[r, f \<star> f\<^sub>a, f] \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]) \<cdot> \<a>[r, f, f\<^sub>a \<star> f] =
                            \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>r\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^sub>a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sub>a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                              \<^bold>\<a>\<^bold>[\<^bold>\<langle>r\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sub>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]\<rbrace>"
                        using f\<^sub>a 1 2 \<a>'_def \<alpha>_def assoc'_eq_inv_assoc by auto
                      also have "... = \<lbrace>(\<^bold>\<a>\<^bold>[\<^bold>\<langle>r\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sub>a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sub>a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]\<rbrace>"
                        using f\<^sub>a 1 2 by (intro E.eval_eqI, auto)
                      also have "... = (\<a>[r, f, f\<^sub>a] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sub>a, f]"
                        using f\<^sub>a 1 2 \<a>'_def \<alpha>_def assoc'_eq_inv_assoc by auto
                      finally show ?thesis by blast
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[r, f, f\<^sub>a] \<star> f) \<cdot>
                                     \<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sub>a, f] \<cdot> (\<rho> \<star> f\<^sub>a \<star> f) \<cdot> \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f)"
                    by (simp add: comp_assoc)
                  finally show ?thesis by blast
                qed
                also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot>
                                   (\<a>[r, f, f\<^sub>a] \<star> f) \<cdot> ((\<rho> \<star> f\<^sub>a) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sub>a, f] \<cdot>
                                     \<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f)"
                proof -
                  have "\<a>\<^sup>-\<^sup>1[r \<star> f, f\<^sub>a, f] \<cdot> (\<rho> \<star> f\<^sub>a \<star> f) = ((\<rho> \<star> f\<^sub>a) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sub>a, f]"
                    using f\<^sub>a 1 2 assoc'_naturality [of \<rho> f\<^sub>a f] by auto
                  thus ?thesis
                    by (metis comp_assoc)
                qed
                also have "... = (\<r>[r] \<star> f) \<cdot> ((r \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[r, f, f\<^sub>a] \<star> f) \<cdot>
                                 ((\<rho> \<star> f\<^sub>a) \<star> f) \<cdot> (\<nu> \<star> f)"
                proof -
                  have "\<a>\<^sup>-\<^sup>1[g, f\<^sub>a, f] \<cdot> \<a>[g, f\<^sub>a, f] = (g \<star> f\<^sub>a) \<star> f"
                    using f\<^sub>a 1 2 comp_assoc_assoc' by auto
                  moreover have "((g \<star> f\<^sub>a) \<star> f) \<cdot> (\<nu> \<star> f) = \<nu> \<star> f"
                    by (simp add: \<nu> comp_cod_arr)
                  ultimately show ?thesis
                    using comp_assoc by metis
                qed
                also have "... = (\<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sub>a] \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> \<nu>) \<star> f"
                proof -
                  have "arr (\<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sub>a] \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> \<nu>)"
                    using f\<^sub>a' comp_assoc by auto
                  thus ?thesis
                    using whisker_right by fastforce
                qed
                finally show ?thesis by blast
              qed
              also have "... = (\<r>[r] \<cdot> \<r>\<^sup>-\<^sup>1[r]) \<star> f"
                using f\<^sub>a' comp_assoc by simp
              also have "... = r \<star> f"
                using ide_base by (simp add: comp_arr_inv')
              finally show ?thesis by blast
            qed
            thus ?thesis
              using ide_leg0 ide_leg1 tab_in_hom comp_cod_arr comp_assoc tab_simps(5) arrI
              by metis
          qed
          finally show ?thesis by argo
        qed
        finally show ?thesis by argo
      qed
      obtain \<eta> where \<eta>: "\<guillemotleft>\<eta> : trg f\<^sub>a \<Rightarrow> f\<^sub>a \<star> f\<guillemotright> \<and> ?\<beta> = g \<star> \<eta> \<and>
                         (\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]) \<cdot> (f \<star> \<eta>) = \<r>[f]"
        using \<beta> \<theta>' A 1 2 f\<^sub>a runit_in_hom ide_leg0 ide_hcomp src.preserves_ide
              T2 [of "trg f\<^sub>a" "f\<^sub>a \<star> f" "\<r>[f]" f "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]" ?\<beta>] comp_assoc
              leg1_simps(3)
        by metis
      have \<eta>': "?\<beta> = g \<star> \<eta> \<and> (\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f]) \<cdot> (f \<star> \<eta>) = \<r>[f]"
        using \<eta> by simp
      have \<eta>: "\<guillemotleft>\<eta> : trg f\<^sub>a \<Rightarrow> f\<^sub>a \<star> f\<guillemotright> \<and> \<guillemotleft>\<eta> : src f \<rightarrow> src f\<guillemotright> \<and>
               arr \<eta> \<and> src \<eta> = src f \<and> trg \<eta> = src f \<and> dom \<eta> = trg f\<^sub>a \<and> cod \<eta> = f\<^sub>a \<star> f"
        using \<eta> \<beta> 2 by force

      have "adjunction_in_bicategory V H \<a> \<i> src trg f f\<^sub>a \<eta> \<epsilon>"
      proof
        show "ide f" using ide_leg0 by simp
        show "ide f\<^sub>a" using f\<^sub>a by blast
        show \<eta>_in_hom: "\<guillemotleft>\<eta> : src f \<Rightarrow> f\<^sub>a \<star> f\<guillemotright>"
          using \<eta> 2 by simp
        show \<epsilon>_in_hom: "\<guillemotleft>\<epsilon> : f \<star> f\<^sub>a \<Rightarrow> src f\<^sub>a\<guillemotright>"
          using f\<^sub>a 1 by simp
        show *: "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
          using ide_leg0 iso_lunit invert_side_of_triangle(1) \<eta>' comp_assoc by auto

        text \<open>
           We have proved one of the triangle identities; now we have to show the other.
           This part, not mentioned by CKS, took me a while to discover.
           Apply \<open>T2\<close> again, this time with the following:
           \[\begin{array}{l}
              \<open>w = src f \<star> f\<^sub>a\<close>,\\
              \<open>\<theta> = (\<epsilon> \<star> \<epsilon>) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a)\<close>,\\
              \<open>w' = f\<^sub>a \<star> trg\<close>,\\
              \<open>\<theta>' = \<epsilon> \<star> trg f\<close>,\\
              \<open>\<beta> = g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]\<close>
           \end{array}\]
           Then the conditions for \<open>\<gamma>\<close> are satisfied by both
           \<open>\<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]\<close> and \<open>(f\<^sub>a \<star> \<epsilon>) \<cdot> \<a>[f\<^sub>a, f, f\<^sub>a] \<cdot> (\<eta> \<star> f\<^sub>a)\<close> so they are equal,
           as required.
        \<close>
        show "(f\<^sub>a \<star> \<epsilon>) \<cdot> \<a>[f\<^sub>a, f, f\<^sub>a] \<cdot> (\<eta> \<star> f\<^sub>a) = \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]"
        proof -
          let ?u = "trg f \<star> trg f"
          let ?w = "src f \<star> f\<^sub>a"
          let ?w' = "f\<^sub>a \<star> trg f"
          let ?\<theta> = "(\<epsilon> \<star> \<epsilon>) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a)"
          let ?\<theta>' = "(\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, trg f]"
          let ?\<beta> = "g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]"
          let ?\<gamma> = "\<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]"
          let ?\<gamma>' = "(f\<^sub>a \<star> \<epsilon>) \<cdot> \<a>[f\<^sub>a, f, f\<^sub>a] \<cdot> (\<eta> \<star> f\<^sub>a)"
          have \<theta>_eq': "?\<theta> = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
          proof -
            have "?\<theta> = (trg f \<star> \<epsilon>) \<cdot> (\<epsilon> \<star> f \<star> f\<^sub>a) \<cdot>
                         (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a])) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a)"
              using interchange [of "trg f" \<epsilon> \<epsilon> "f \<star> f\<^sub>a"] comp_arr_dom comp_cod_arr comp_assoc
              by (simp add: \<epsilon>)
            also have "... = (trg f \<star> \<epsilon>) \<cdot> (\<epsilon> \<star> f \<star> f\<^sub>a) \<cdot>
                               (\<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]) \<cdot>
                               (f \<star> \<eta> \<star> f\<^sub>a)"
            proof -
              have "\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) =
                    \<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]"
              proof -
                have "(\<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> ((\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a])) \<cdot>
                        (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]) =
                      \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]"
                  using 1 2 \<open>ide f\<^sub>a\<close> ide_leg0 iso_inv_iso iso_assoc
                        invert_side_of_triangle(1)
                          [of "((\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]) \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a])"
                              "\<a>\<^sup>-\<^sup>1[f \<star> f\<^sub>a, f, f\<^sub>a]" "\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]"]
                       pentagon' comp_assoc by auto
                hence "(\<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> ((\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a])) =
                       \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a])"
                  using 1 2 \<open>ide f\<^sub>a\<close> iso_inv_iso
                        invert_side_of_triangle(2)
                          [of "\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]" "\<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> ((\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a])"
                              "f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]"]
                  by auto
                thus ?thesis
                  using comp_assoc by simp
              qed
              thus ?thesis by simp
            qed
            also have "... = (trg f \<star> \<epsilon>) \<cdot> ((\<epsilon> \<star> f \<star> f\<^sub>a) \<cdot> \<a>[f \<star> f\<^sub>a, f, f\<^sub>a]) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot>
                               \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a] \<cdot> (f \<star> \<eta> \<star> f\<^sub>a)"
              using comp_assoc by simp
            also have "... = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot>
                               ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (f \<star> \<eta>) \<star> f\<^sub>a) \<cdot>
                               \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
            proof -
              have "((\<epsilon> \<star> f \<star> f\<^sub>a) \<cdot> \<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot>
                      \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a) =
                    (\<a>[trg f, f, f\<^sub>a] \<cdot> ((\<epsilon> \<star> f) \<star> f\<^sub>a)) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot>
                      ((f \<star> \<eta>) \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using assoc_naturality [of \<epsilon> f f\<^sub>a] assoc'_naturality [of f \<eta> f\<^sub>a]
                by (simp add: 2 \<epsilon> \<eta> \<open>ide f\<^sub>a\<close> comp_assoc)
              also have "... = \<a>[trg f, f, f\<^sub>a] \<cdot>
                                 (((\<epsilon> \<star> f) \<star> f\<^sub>a) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> ((f \<star> \<eta>) \<star> f\<^sub>a)) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using comp_assoc by simp
              also have "... = \<a>[trg f, f, f\<^sub>a] \<cdot>
                                 ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (f \<star> \<eta>) \<star> f\<^sub>a) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using \<eta>' comp_assoc whisker_right \<open>ide f\<^sub>a\<close> comp_null(2) ide_leg0 ext
                      runit_simps(1)
                by metis
              finally show ?thesis
                using comp_assoc by simp
            qed
            also have "... = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
              using * by simp
            finally show ?thesis by simp
          qed
          have \<theta>_eq: "?\<theta> = (\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, src f\<^sub>a] \<cdot> (f \<star> ?\<gamma>)"
          proof -
            have "?\<theta> = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
              using \<theta>_eq' by simp
            also have "... =
                       (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<star> f\<^sub>a) \<cdot> (\<r>[f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
              using \<open>ide f\<^sub>a\<close> whisker_right comp_assoc by auto
            also have "... = (trg f \<star> \<epsilon>) \<cdot> ((\<a>[trg f, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[trg f, f, f\<^sub>a]) \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> f\<^sub>a])) \<cdot>
                               (f \<star> \<l>[f\<^sub>a])"
               using 2 \<open>ide f\<^sub>a\<close> lunit_hcomp [of f f\<^sub>a] invert_side_of_triangle(2) triangle'
                     comp_assoc
               by auto
            also have "... = (trg f \<star> \<epsilon>) \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> f\<^sub>a] \<cdot> (f \<star> \<l>[f\<^sub>a])"
              using f\<^sub>a 2 comp_cod_arr iso_assoc comp_arr_inv lunit_hcomp(2) lunit_hcomp(4)
                    ide_leg0 leg1_simps(3)
              by metis
            also have "... = \<l>\<^sup>-\<^sup>1[trg f] \<cdot> \<epsilon> \<cdot> (f \<star> \<l>[f\<^sub>a])"
              using \<epsilon> lunit'_naturality comp_assoc by metis
            also have "... = \<r>\<^sup>-\<^sup>1[trg f] \<cdot> \<epsilon> \<cdot> (f \<star> \<l>[f\<^sub>a])"
              using unitor_coincidence by simp
            also have "... = (\<epsilon> \<star> trg f) \<cdot> \<r>\<^sup>-\<^sup>1[f \<star> f\<^sub>a] \<cdot> (f \<star> \<l>[f\<^sub>a])"
              using \<epsilon> runit'_naturality comp_assoc by metis
            also have "... = (\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, src f\<^sub>a] \<cdot> (f \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a]) \<cdot> (f \<star> \<l>[f\<^sub>a])"
              using 2 \<open>ide f\<^sub>a\<close> runit_hcomp(2) comp_assoc by auto
            also have "... = (\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, src f\<^sub>a] \<cdot> (f \<star> ?\<gamma>)"
              using 2 \<open>ide f\<^sub>a\<close> whisker_left by simp
            finally show ?thesis by simp
          qed
          have \<theta>: "\<guillemotleft>?\<theta> : f \<star> ?w \<Rightarrow> ?u\<guillemotright>"
            using 1 2 \<open>ide f\<^sub>a\<close> \<eta>_in_hom \<epsilon> by fastforce
          have \<theta>': "\<guillemotleft>?\<theta>' : f \<star> ?w' \<Rightarrow> ?u\<guillemotright>"
            using f\<^sub>a 1 2 \<epsilon> by auto
          have ww': "ide ?w \<and> ide ?w'"
            by (simp add: 1 2 \<open>ide f\<^sub>a\<close>)
          have "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : ?w \<Rightarrow> ?w'\<guillemotright> \<and> ?\<beta> = g \<star> \<gamma> \<and> ?\<theta> = ?\<theta>' \<cdot> (f \<star> \<gamma>)"
          proof -
            have "\<guillemotleft>?\<beta> : g \<star> ?w \<Rightarrow> g \<star> ?w'\<guillemotright>"
              using \<open>ide f\<^sub>a\<close> 1 2 by auto
            moreover have "composite_cell ?w ?\<theta> = composite_cell ?w' ?\<theta>' \<cdot> ?\<beta>"
            proof -
              have "composite_cell ?w' ?\<theta>' \<cdot> ?\<beta> =
                    composite_cell ?w ((\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, src f\<^sub>a] \<cdot> (f \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]))"
              proof -
                have "\<a>[r, f, f\<^sub>a \<star> trg f] \<cdot> (\<rho> \<star> f\<^sub>a \<star> trg f) \<cdot> (g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]) =
                      composite_cell ?w (f \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a])"
                proof -
                  have "\<a>[r, f, f\<^sub>a \<star> trg f] \<cdot> (\<rho> \<star> f\<^sub>a \<star> trg f) \<cdot> (g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]) =
                        (\<a>[r, f, f\<^sub>a \<star> trg f] \<cdot> ((r \<star> f) \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a])) \<cdot> (\<rho> \<star> src f \<star> f\<^sub>a)"
                  proof -
                    have "(\<rho> \<star> f\<^sub>a \<star> trg f) \<cdot> (g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]) = \<rho> \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]"
                      using interchange [of \<rho> g "f\<^sub>a \<star> trg f" "\<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]"]
                            comp_arr_dom comp_cod_arr 1 2 \<open>ide f\<^sub>a\<close>
                      by simp
                    also have "... = ((r \<star> f) \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]) \<cdot> (\<rho> \<star> src f \<star> f\<^sub>a)"
                    proof -
                      have "seq (f\<^sub>a \<star> trg f) (\<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a])"
                        using f\<^sub>a 1 2 ww' by auto
                      thus ?thesis
                        using interchange comp_arr_dom comp_cod_arr 1 2 \<open>ide f\<^sub>a\<close>
                        by (metis ww' comp_ide_arr dom_comp leg1_simps(3)
                                  lunit_simps(4) tab_simps(1) tab_simps(5))
                    qed
                    finally show ?thesis
                      using comp_assoc by simp
                  qed
                  also have "... = composite_cell ?w (f \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a])"
                    using assoc_naturality [of r f "\<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]"] 1 2 \<open>ide f\<^sub>a\<close> comp_assoc by simp
                  finally show ?thesis by simp
                qed
                hence "composite_cell ?w' ?\<theta>' \<cdot> ?\<beta> =
                       ((r \<star> (\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, trg f]) \<cdot> (r \<star> f \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a])) \<cdot>
                         \<a>[r, f, src f \<star> f\<^sub>a] \<cdot> (\<rho> \<star> src f \<star> f\<^sub>a)"
                  using comp_assoc by simp
                also have 
                  "... = composite_cell ?w (((\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, trg f]) \<cdot> (f \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]))"
                  using whisker_left 1 2 \<open>ide f\<^sub>a\<close> ide_base
                  by (metis \<open>\<guillemotleft>(\<epsilon> \<star> \<epsilon>) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a) :
                               f \<star> src f \<star> f\<^sub>a \<Rightarrow> trg f \<star> trg f\<guillemotright>\<close>
                      \<theta>_eq arrI comp_assoc)
                finally show ?thesis
                  using comp_assoc by (simp add: "1")
              qed
              also have "... = composite_cell ?w ?\<theta>"
                using \<theta>_eq by simp
              finally show ?thesis by simp
            qed
            ultimately show ?thesis
              using ww' \<theta> \<theta>' T2 [of ?w ?w' ?\<theta> ?u ?\<theta>' ?\<beta>] comp_assoc by metis
          qed
          moreover have "\<guillemotleft>?\<gamma> : ?w \<Rightarrow> ?w'\<guillemotright> \<and> ?\<beta> = g \<star> ?\<gamma> \<and> ?\<theta> = ?\<theta>' \<cdot> (f \<star> ?\<gamma>)"
            using 1 2 \<open>ide f\<^sub>a\<close> \<theta>_eq comp_assoc by auto
          moreover have "\<guillemotleft>?\<gamma>' : ?w \<Rightarrow> ?w'\<guillemotright> \<and> ?\<beta> = g \<star> ?\<gamma>' \<and> ?\<theta> = ?\<theta>' \<cdot> (f \<star> ?\<gamma>')"
          proof (intro conjI)
            show "\<guillemotleft>?\<gamma>' : ?w \<Rightarrow> ?w'\<guillemotright>"
              using 1 2 f\<^sub>a \<eta>_in_hom \<epsilon>_in_hom by fastforce
            show "?\<beta> = g \<star> ?\<gamma>'"
         text \<open>
           This equation is not immediate.
           To show it, we have to recall the properties from the construction of \<open>\<epsilon>\<close> and \<open>\<eta>\<close>.
           Use the property of \<open>\<eta>\<close> to replace \<open>g \<star> \<eta> \<star> f\<^sub>a\<close> by a 2-cell involving
           \<open>\<epsilon>\<close>, \<open>\<rho>\<close>, and \<open>\<nu>\<close>.
           Use the property \<open>(r \<star> \<epsilon>) \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> \<nu> = \<r>[r]\<close> from the construction of \<open>\<epsilon>\<close> to
           eliminate \<open>\<epsilon>\<close> and \<open>\<rho>\<close> in favor of inv \<open>\<nu>\<close> and canonical isomorphisms.
           Cancelling \<open>\<nu>\<close> and inv \<open>\<nu>\<close> leaves the canonical 2-cell \<open>g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a] \<cdot> \<l>[f\<^sub>a]\<close>.
            \<close>
            proof -
              have "g \<star> ?\<gamma>' = (g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot> (g \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (g \<star> \<eta> \<star> f\<^sub>a)"
                using 1 2 \<open>ide f\<^sub>a\<close> \<epsilon> \<eta> whisker_left
                by (metis \<open>\<guillemotleft>?\<gamma>' : ?w \<Rightarrow> ?w'\<guillemotright>\<close> arrI ide_leg1 seqE)
              also have "... = (g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot> (g \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (g \<star> \<eta> \<star> f\<^sub>a) \<cdot>
                                 \<a>[g, src f, f\<^sub>a] \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> \<eta> comp_arr_dom hseq_char comp_assoc_assoc'
                by simp
              also have "... = (g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot> (g \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> ((g \<star> \<eta> \<star> f\<^sub>a) \<cdot>
                                 \<a>[g, src f, f\<^sub>a]) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using comp_assoc by simp
              also have "... = (g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot> (g \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot>
                                 (\<a>[g, f\<^sub>a \<star> f, f\<^sub>a] \<cdot> ((g \<star> \<eta>) \<star> f\<^sub>a)) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> \<epsilon> \<eta> assoc_naturality [of g \<eta> f\<^sub>a] by simp
              also have "... = (g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot> (g \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> \<a>[g, f\<^sub>a \<star> f, f\<^sub>a] \<cdot>
                                 (\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using \<eta>' comp_assoc by simp
              also have "... = (g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot>
                                 ((g \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> \<a>[g, f\<^sub>a \<star> f, f\<^sub>a] \<cdot> (\<a>[g, f\<^sub>a, f] \<star> f\<^sub>a)) \<cdot>
                                 ((\<nu> \<star> f) \<star> f\<^sub>a) \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
              proof -
                have "\<a>[g, f\<^sub>a, f] \<cdot> (\<nu> \<star> f) \<cdot> \<rho> \<cdot> \<r>[g] \<star> f\<^sub>a =
                      (\<a>[g, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> ((\<nu> \<star> f) \<star> f\<^sub>a) \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> (\<r>[g] \<star> f\<^sub>a)"
                  using 1 2 \<open>ide f\<^sub>a\<close> \<beta> \<epsilon> \<eta> whisker_right by (metis arrI seqE)
                thus ?thesis
                  using comp_assoc by simp
              qed
              also have "... = ((g \<star> f\<^sub>a \<star> \<epsilon>) \<cdot>
                                 \<a>[g, f\<^sub>a, f \<star> f\<^sub>a]) \<cdot> (\<a>[g \<star> f\<^sub>a, f, f\<^sub>a] \<cdot>
                                 ((\<nu> \<star> f) \<star> f\<^sub>a)) \<cdot> (\<rho> \<star> f\<^sub>a) \<cdot> (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> pentagon comp_assoc by simp
              also have "... = (\<a>[g, f\<^sub>a, trg f] \<cdot> ((g \<star> f\<^sub>a) \<star> \<epsilon>)) \<cdot>
                               ((\<nu> \<star> f \<star> f\<^sub>a) \<cdot> \<a>[r, f, f\<^sub>a]) \<cdot>
                               (\<rho> \<star> f\<^sub>a) \<cdot> (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> assoc_naturality [of g f\<^sub>a \<epsilon>] assoc_naturality [of \<nu> f f\<^sub>a]
                by (simp add: \<epsilon> \<nu>)
              also have "... = \<a>[g, f\<^sub>a, trg f] \<cdot> (((g \<star> f\<^sub>a) \<star> \<epsilon>) \<cdot> (\<nu> \<star> f \<star> f\<^sub>a)) \<cdot> \<a>[r, f, f\<^sub>a] \<cdot>
                               (\<rho> \<star> f\<^sub>a) \<cdot> (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> assoc_naturality [of g f\<^sub>a \<epsilon>] assoc_naturality [of \<nu> f f\<^sub>a]
                      comp_assoc
                by simp
              also have "... = \<a>[g, f\<^sub>a, trg f] \<cdot> (\<nu> \<star> trg f) \<cdot>
                                 composite_cell f\<^sub>a \<epsilon> \<cdot>
                                 (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
              proof -
                have "((g \<star> f\<^sub>a) \<star> \<epsilon>) \<cdot> (\<nu> \<star> f \<star> f\<^sub>a) = \<nu> \<star> \<epsilon>"
                  using 1 2 \<open>ide f\<^sub>a\<close> \<nu> \<epsilon> interchange [of "g \<star> f\<^sub>a" \<nu> \<epsilon> "f \<star> f\<^sub>a"]
                        comp_arr_dom comp_cod_arr
                  by simp
                also have "... = (\<nu> \<star> trg f) \<cdot> (r \<star> \<epsilon>)"
                  using \<open>ide f\<^sub>a\<close> \<nu> \<epsilon> interchange [of \<nu> r "trg f" \<epsilon>] comp_arr_dom comp_cod_arr
                  by simp
                finally show ?thesis
                  using comp_assoc by simp
              qed
              also have "... = \<a>[g, f\<^sub>a, trg f] \<cdot> ((((\<nu> \<star> trg f) \<cdot> \<r>\<^sup>-\<^sup>1[r]) \<cdot> inv \<nu>) \<cdot> (\<r>[g] \<star> f\<^sub>a)) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using ide_base f\<^sub>a' comp_assoc f\<^sub>a runit'_simps(1) invert_side_of_triangle(2)
                      comp_assoc
                by presburger
              also have "... = \<a>[g, f\<^sub>a, trg f] \<cdot> \<r>\<^sup>-\<^sup>1[g \<star> f\<^sub>a] \<cdot> (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
              proof -
                have "((\<nu> \<star> trg f) \<cdot> \<r>\<^sup>-\<^sup>1[r]) \<cdot> inv \<nu> = \<r>\<^sup>-\<^sup>1[g \<star> f\<^sub>a]"
                  using 1 2 \<open>ide f\<^sub>a\<close> \<nu> ide_base runit'_naturality [of \<nu>] comp_arr_dom
                  by (metis f\<^sub>a ide_compE inv_is_inverse inverse_arrowsE comp_assoc
                      runit'_simps(1) runit'_simps(4))
                thus ?thesis
                  using comp_assoc by simp
              qed
              also have "... = ((\<a>[g, f\<^sub>a, trg f] \<cdot> \<a>\<^sup>-\<^sup>1[g, f\<^sub>a, src f\<^sub>a]) \<cdot>
                                 (g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a])) \<cdot> (\<r>[g] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[g, src f, f\<^sub>a]"
                using f\<^sub>a "2" runit_hcomp \<open>ide f\<^sub>a\<close> comp_assoc by simp
              also have "... = (g \<star> \<r>\<^sup>-\<^sup>1[f\<^sub>a]) \<cdot> (g \<star> \<l>[f\<^sub>a])"
                using 1 2 comp_cod_arr \<open>ide f\<^sub>a\<close> comp_assoc_assoc' triangle' by simp
              also have "... = ?\<beta>"
                using 2 \<open>ide f\<^sub>a\<close> whisker_left by simp
              finally show ?thesis by simp
            qed
            show "?\<theta> = ?\<theta>' \<cdot> (f \<star> ?\<gamma>')"
            proof -
              have "((\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, trg f]) \<cdot> (f \<star> (f\<^sub>a \<star> \<epsilon>) \<cdot> \<a>[f\<^sub>a, f, f\<^sub>a] \<cdot> (\<eta> \<star> f\<^sub>a)) =
                    ((\<epsilon> \<star> trg f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, trg f]) \<cdot> (f \<star> f\<^sub>a \<star> \<epsilon>) \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a)"
                using 1 2 \<open>ide f\<^sub>a\<close> \<epsilon> \<eta> whisker_left
                by (metis \<open>\<guillemotleft>(f\<^sub>a \<star> \<epsilon>) \<cdot> \<a>[f\<^sub>a, f, f\<^sub>a] \<cdot> (\<eta> \<star> f\<^sub>a) : src f \<star> f\<^sub>a \<Rightarrow> f\<^sub>a \<star> trg f\<guillemotright>\<close>
                    arrI ide_leg0 seqE)
              also have
                "... = (\<epsilon> \<star> trg f) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, trg f] \<cdot> (f \<star> f\<^sub>a \<star> \<epsilon>)) \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot> (f \<star> \<eta> \<star> f\<^sub>a)"
                using comp_assoc by simp
              also have "... = ((\<epsilon> \<star> trg f) \<cdot> ((f \<star> f\<^sub>a) \<star> \<epsilon>)) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) \<cdot>
                                 (f \<star> \<eta> \<star> f\<^sub>a)"
                using 1 2 \<open>ide f\<^sub>a\<close> \<epsilon> assoc'_naturality [of f f\<^sub>a \<epsilon>] comp_assoc by simp
              also have "... = (trg f \<star> \<epsilon>) \<cdot> (\<epsilon> \<star> f \<star> f\<^sub>a) \<cdot>
                                 (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a])) \<cdot>
                                 (f \<star> \<eta> \<star> f\<^sub>a)"
                using 1 2 \<open>ide f\<^sub>a\<close> \<epsilon> interchange [of \<epsilon> "f \<star> f\<^sub>a" "trg f" \<epsilon>]
                       interchange [of "trg f" \<epsilon> \<epsilon> "f \<star> f\<^sub>a"] comp_arr_dom comp_cod_arr comp_assoc
                by simp
              also have "... = (trg f \<star> \<epsilon>) \<cdot> ((\<epsilon> \<star> f \<star> f\<^sub>a) \<cdot>
                                 (\<a>[f \<star> f\<^sub>a, f, f\<^sub>a]) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]) \<cdot>
                                 (f \<star> \<eta> \<star> f\<^sub>a))"
              proof -
                have "\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a] \<cdot> (f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]) =
                      \<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]"
                proof -
                  have A: "(\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a] \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]) =
                           \<a>\<^sup>-\<^sup>1[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]"
                    using 1 2 \<open>ide f\<^sub>a\<close> pentagon' comp_assoc by fastforce
                  hence B: "\<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a] \<cdot>
                              (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]) =
                            \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]"
                    using A 1 2 \<open>ide f\<^sub>a\<close> iso_inv_iso
                          invert_side_of_triangle(1)
                            [of "(\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a] \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a])"
                                "\<a>\<^sup>-\<^sup>1[f \<star> f\<^sub>a, f, f\<^sub>a]" "\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]"]
                    by auto
                  show ?thesis
                  proof -
                    have C: "iso (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a])"
                      using 1 2 \<open>ide f\<^sub>a\<close> iso_inv_iso by simp
                    moreover have "inv (f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]) = f \<star> \<a>[f\<^sub>a, f, f\<^sub>a]"
                       using C 1 2 inv_hcomp [of f "\<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]"]
                             \<open>ide f\<^sub>a\<close> iso_assoc' assoc'_eq_inv_assoc
                       by fastforce
                    ultimately show ?thesis
                      using B 1 2 \<open>ide f\<^sub>a\<close> comp_assoc
                            invert_side_of_triangle(2)
                              [of "\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f \<star> f\<^sub>a]"
                                  "\<a>[f \<star> f\<^sub>a, f, f\<^sub>a] \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a \<star> f, f\<^sub>a]"
                                  "f \<star> \<a>\<^sup>-\<^sup>1[f\<^sub>a, f, f\<^sub>a]"]
                      by simp
                  qed
                qed
                thus ?thesis
                  using comp_assoc by simp
              qed
              also have "... = (trg f \<star> \<epsilon>) \<cdot> (\<a>[trg f, f, f\<^sub>a] \<cdot>
                                 ((\<epsilon> \<star> f) \<star> f\<^sub>a)) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> ((f \<star> \<eta>) \<star> f\<^sub>a) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> \<open>ide f\<close> \<eta> \<epsilon> assoc_naturality [of \<epsilon> f f\<^sub>a]
                      assoc'_naturality [of f \<eta> f\<^sub>a] comp_assoc
                by simp
              also have "... = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot>
                                 (((\<epsilon> \<star> f) \<star> f\<^sub>a) \<cdot> (\<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<star> f\<^sub>a) \<cdot> ((f \<star> \<eta>) \<star> f\<^sub>a)) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using comp_assoc by simp
              also have "... = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot>
                                 ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sub>a, f] \<cdot> (f \<star> \<eta>) \<star> f\<^sub>a) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using 1 2 \<open>ide f\<^sub>a\<close> \<open>ide f\<close> \<eta> \<epsilon> whisker_right
                by (metis (full_types) * \<theta> \<theta>_eq' arrI hseqE seqE)
              also have "... = (trg f \<star> \<epsilon>) \<cdot> \<a>[trg f, f, f\<^sub>a] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> f\<^sub>a) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, f\<^sub>a]"
                using * by simp
              also have "... = ?\<theta>"
                using \<theta>_eq' by simp
              finally show ?thesis by simp
            qed
          qed
          ultimately show "?\<gamma>' = ?\<gamma>" by blast
        qed
      qed
      thus ?thesis
        using adjoint_pair_def by auto
    qed

    sublocale tabulation_data_with_T0
      using satisfies_T0 by (unfold_locales, simp)
    sublocale narrow_tabulation
      using adjoint_pair_antipar(1) T1 T2
      by (unfold_locales, auto)

  end

  text \<open>
    A tabulation \<open>(f, \<rho>, g)\<close> of \<open>r\<close> yields an isomorphism \<open>\<guillemotleft>\<psi> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>\<close>
    via adjoint transpose.
    The proof requires \<open>T0\<close>, in order to obtain \<open>\<psi>\<close> as the transpose of \<open>\<guillemotleft>\<rho> : g \<Rightarrow> r \<star> f\<guillemotright>\<close>.
    However, it uses only the weaker versions of \<open>T1\<close> and \<open>T2\<close>.
  \<close>

  context narrow_tabulation
  begin

    interpretation E: self_evaluation_map V H \<a> \<i> src trg ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    text \<open>
      The following is CKS Proposition 1(d), with the statement refined to incorporate
      the canonical isomorphisms that they omit.
      Note that we can easily show using \<open>T1\<close> that there is some 1-cell \<open>f\<^sub>a\<close> and isomorphism \<open>\<psi>\<close>
      such that \<open>\<guillemotleft>\<psi> : f \<star> f\<^sub>a \<Rightarrow> r\<guillemotright>\<close> (this was already part of the proof that a tabulation
      satisfies \<open>T0\<close>).  The more difficult content in the present result is that we may
      actually take \<open>f\<^sub>a\<close> to be the left adjoint \<open>f\<^sup>*\<close> of \<open>f\<close>.
    \<close>

    lemma yields_isomorphic_representation:
    shows "\<guillemotleft>T0.trnr\<^sub>\<epsilon> r \<rho> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>" and "iso (T0.trnr\<^sub>\<epsilon> r \<rho>)"
    proof -
      text \<open>
        As stated in CKS, the first step of the proof is:
        \begin{quotation}
          ``Apply \<open>T1\<close> with \<open>X = A\<close>, \<open>u = 1\<^sub>A\<close>, \<open>v = r\<close>, \<open>\<omega> = 1\<^sub>R\<close>, to obtain \<open>f'\<close>, \<open>\<theta>': ff' \<Rightarrow> 1\<^sub>A\<close>,
          \<open>\<nu> : r \<simeq> g f'\<close> with \<open>1\<^sub>R = (r\<theta>')(\<rho>f')\<nu>\<close>.''
        \end{quotation}
        In our nomenclature: \<open>X = trg f\<close>, \<open>u = trg f\<close>, \<open>v = r\<close>, but \<open>\<omega> = src f\<close>
        does not make any sense, since we need \<open>\<guillemotleft>\<omega> : v \<Rightarrow> r \<star> u\<guillemotright>\<close>.  We have to take \<open>\<omega> = \<r>\<^sup>-\<^sup>1[r]\<close>.
        It is not clear whether this is a typo, or whether it is a consequence of CKS having
        suppressed all canonical isomorphisms (unitors, in this case).  The resulting equation
        obtained via T1 is:
        \[
          \<open>\<r>\<^sup>-\<^sup>1[r] = (r \<star> \<theta>') \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu>\<close>,
        \]
        which has \<open>\<r>\<^sup>-\<^sup>1[r]\<close> on the left-hand side, rather than \<open>1\<^sub>R\<close>, as in CKS.
        Also, we have inserted the omitted associativity.
      \<close>

      obtain w \<theta>' \<nu> where w\<theta>'\<nu>: "ide w \<and> \<guillemotleft>\<theta>' : f \<star> w \<Rightarrow> src r\<guillemotright> \<and> \<guillemotleft>\<nu> : r \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                                 composite_cell w \<theta>' \<cdot> \<nu> = \<r>\<^sup>-\<^sup>1[r]"
        using ide_base obj_is_self_adjoint T1 [of "src r" "\<r>\<^sup>-\<^sup>1[r]"] comp_assoc by auto

      interpret uw\<theta>\<omega>\<nu> V H \<a> \<i> src trg r \<rho> f g \<open>src r\<close> w \<theta>' \<open>\<r>\<^sup>-\<^sup>1[r]\<close> \<nu>
        using ide_base tab_in_hom w\<theta>'\<nu> comp_assoc by (unfold_locales, auto)

      text \<open>
        CKS now say:
        \begin{quotation}
          ``Apply \<open>T2\<close> with \<open>u = 1\<^sub>A\<close>, \<open>w = f\<^sup>*\<close>, \<open>w' = f'\<close>, \<open>\<theta> = \<epsilon>: ff\<^sup>* \<Rightarrow> 1\<close>, \<open>\<theta>': ff' \<Rightarrow> 1\<close>,
          \<open>\<beta> = \<nu>(r\<epsilon>)(\<rho>f\<^sup>*)\<close> to obtain \<open>\<gamma> : f\<^sup>* \<Rightarrow> f'\<close> with \<open>g\<gamma> = \<nu>(r\<epsilon>)(\<rho>f\<^sup>*)\<epsilon> = \<theta>'(f\<gamma>).\<close>''
        \end{quotation}
        The last equation is mysterious, but upon consideration one eventually realizes
        that it is definitely a typo, and what is meant is ``\<open>g\<gamma> = \<nu>(r\<epsilon>)(\<rho>f\<^sup>*)\<close>, \<open>\<epsilon> = \<theta>'(f\<gamma>)\<close>''.

        So, we take \<open>u = trg f\<close>, \<open>w = f\<^sup>*\<close>, \<open>w' = w\<close>, \<open>\<theta>'\<close> as obtained from \<open>T1\<close>, \<open>\<theta> = \<epsilon>\<close>,
        and \<open>\<beta> = \<nu> \<cdot> \<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot> (\<rho> \<star> f\<^sup>*)\<close>.
        (CKS mention neither the unitor term \<open>\<r>[r]\<close> nor the associativity \<open>\<a>[r, f, f\<^sup>*]\<close>
        which are required for the expression for \<open>\<beta>\<close> to make sense.)
      \<close>

      let ?\<psi> = "\<r>[r] \<cdot> composite_cell f\<^sup>* \<epsilon>"
      show \<psi>_in_hom: "\<guillemotleft>T0.trnr\<^sub>\<epsilon> r \<rho> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>"
        using ide_base T0.trnr\<^sub>\<epsilon>_def rep_in_hom by simp
      have A: "\<guillemotleft>\<nu> \<cdot> ?\<psi> : g \<star> f\<^sup>* \<Rightarrow> g \<star> w\<guillemotright>"
        using ide_base T0.antipar hseq_char T0.trnr\<^sub>\<epsilon>_def rep_in_hom w\<theta>'\<nu>
        apply (intro comp_in_homI') by auto
      have B: "composite_cell f\<^sup>* \<epsilon> = composite_cell w \<theta>' \<cdot> \<nu> \<cdot> ?\<psi>"
          using ide_base T0.antipar w\<theta>'\<nu> comp_assoc
          by (metis A arrI invert_side_of_triangle(1) iso_runit)

      obtain \<gamma> where \<gamma>: "\<guillemotleft>\<gamma> : f\<^sup>* \<Rightarrow> w\<guillemotright> \<and> \<nu> \<cdot> ?\<psi> = g \<star> \<gamma> \<and> \<epsilon> = \<theta>' \<cdot> (f \<star> \<gamma>)"
        using A B T0.counit_in_hom obj_is_self_adjoint T0.antipar comp_assoc
              T2 [of "trg f" "f\<^sup>*" w \<epsilon> \<theta>' "\<nu> \<cdot> \<r>[r] \<cdot> composite_cell f\<^sup>* \<epsilon>"]
        by auto
      have trg_\<gamma>_eq: "trg \<gamma> = trg w"
        using \<gamma> by fastforce

      text \<open>
        CKS say:
        \begin{quotation}
          ``The last equation implies \<open>\<gamma>: f\<^sup>* \<Rightarrow> f'\<close> is a split monic (coretraction), while
          the calculation:
          \begin{eqnarray*}
             \<open>(g\<gamma>)(gf\<^sup>*\<theta>')(g\<eta>f')\<close> &\<open>=\<close>& \<open>\<nu>(r\<epsilon>)(\<rho>f\<^sup>*)(gf\<^sup>*\<theta>')(g\<eta>f')\<close>\\
                                 &\<open>=\<close>& \<open>\<nu>(r\<epsilon>)(rff\<^sup>*\<theta>')(\<rho>f\<^sup>*ff')(g\<eta>f')\<close>\\
                                 &\<open>=\<close>& \<open>\<nu>(r\<theta>')(r\<epsilon>ff')(rf\<eta>f')(\<rho>f')\<close>\\
                                 &\<open>=\<close>& \<open>\<nu>(r\<theta>')(\<rho>f') = 1\<^sub>g\<^sub>f\<^sub>'\<close>,
          \end{eqnarray*}
          shows that \<open>g\<gamma>\<close> is a split epic.  So \<open>g\<gamma> = \<nu>(r\<epsilon>)(\<rho>f\<^sup>*): gf\<^sup>* \<Rightarrow> gf'\<close> is invertible.
          So \<open>(r\<epsilon>)(\<rho>f\<^sup>*) = \<nu>\<^sup>-\<^sup>1(g\<gamma>)\<close> is invertible.''
        \end{quotation}
        We carry out the indicated calculations, inserting where required the canonical
        isomorphisms omitted by CKS.  It is perhaps amusing to compare the four-line sketch
        given by CKS with the formalization below, but note that we have carried out the
        proof in full, with no hand waving about units or associativities.
      \<close>

      have "section (g \<star> \<gamma>)"
      proof
        have "(g \<star> \<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w] \<cdot> (\<eta> \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[w]) \<cdot> (g \<star> \<gamma>) = g \<star> f\<^sup>*"
        proof -
          have "(\<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w] \<cdot> (\<eta> \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[w]) \<cdot> \<gamma> = f\<^sup>*"
          proof -
            have "(\<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w] \<cdot> (\<eta> \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[w]) \<cdot> \<gamma> =
                  (\<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w] \<cdot> (\<eta> \<star> w)) \<cdot> \<l>\<^sup>-\<^sup>1[w] \<cdot> \<gamma>"
              using comp_assoc by auto
            also have "... = (\<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w]) \<cdot> ((\<eta> \<star> w) \<cdot> (trg w \<star> \<gamma>)) \<cdot> \<l>\<^sup>-\<^sup>1[f\<^sup>*]"
              using \<gamma> trg_\<gamma>_eq lunit'_naturality [of \<gamma>] comp_assoc by auto
            also have "... = \<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> (\<a>[f\<^sup>*, f, w] \<cdot> ((f\<^sup>* \<star> f) \<star> \<gamma>)) \<cdot> (\<eta> \<star> f\<^sup>*) \<cdot> \<l>\<^sup>-\<^sup>1[f\<^sup>*]"
            proof -
              have "(\<eta> \<star> w) \<cdot> (trg w \<star> \<gamma>) = \<eta> \<star> \<gamma>"
                using A \<gamma> interchange comp_arr_dom comp_cod_arr
                by (metis T0.unit_simps(1-2) comp_ide_arr seqI' uw\<theta> w_in_hom(2) w_simps(4))
              also have "... = ((f\<^sup>* \<star> f) \<star> \<gamma>) \<cdot> (\<eta> \<star> f\<^sup>*)"
                using \<gamma> interchange comp_arr_dom comp_cod_arr T0.antipar T0.unit_simps(1,3)
                      in_homE
                by metis
              finally show ?thesis
                using comp_assoc by simp
            qed
            also have "... = \<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> ((f\<^sup>* \<star> f \<star> \<gamma>) \<cdot> \<a>[f\<^sup>*, f, f\<^sup>*]) \<cdot> (\<eta> \<star> f\<^sup>*) \<cdot> \<l>\<^sup>-\<^sup>1[f\<^sup>*]"
              using \<gamma> assoc_naturality [of "f\<^sup>*" f \<gamma>] trg_\<gamma>_eq T0.antipar by auto
            also have "... = \<r>[f\<^sup>*] \<cdot> ((f\<^sup>* \<star> \<epsilon>) \<cdot> \<a>[f\<^sup>*, f, f\<^sup>*] \<cdot> (\<eta> \<star> f\<^sup>*)) \<cdot> \<l>\<^sup>-\<^sup>1[f\<^sup>*]"
              using \<gamma> whisker_left trg_\<gamma>_eq T0.antipar comp_assoc by auto
            also have "... =  \<r>[f\<^sup>*] \<cdot> (\<r>\<^sup>-\<^sup>1[f\<^sup>*] \<cdot> \<l>[f\<^sup>*]) \<cdot> \<l>\<^sup>-\<^sup>1[f\<^sup>*]"
              using T0.triangle_right by simp
            also have "... = f\<^sup>*"
              using comp_assoc by (simp add: comp_arr_dom comp_arr_inv')
            finally show ?thesis by blast
          qed
          thus ?thesis
            using \<gamma> whisker_left [of g "\<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w] \<cdot> (\<eta> \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[w]" \<gamma>]
                  T0.antipar
            by simp
        qed
        thus "ide ((g \<star> \<r>[f\<^sup>*] \<cdot> (f\<^sup>* \<star> \<theta>') \<cdot> \<a>[f\<^sup>*, f, w] \<cdot> (\<eta> \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[w]) \<cdot> (g \<star> \<gamma>))"
          using T0.antipar by simp
      qed
      moreover have "retraction (g \<star> \<gamma>)"
      proof
        have "\<guillemotleft>(g \<star> \<gamma>) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]) :
                 g \<star> w \<Rightarrow> g \<star> w\<guillemotright>"
          using \<gamma> T0.antipar hseq_char by force
        hence **: "arr ((g \<star> \<gamma>) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                        (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]))"
          by auto
        show "ide ((g \<star> \<gamma>) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                    (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]))"
        proof -
          have "((g \<star> \<gamma>) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                  (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])) =
                g \<star> w"
          proof -
            have "((g \<star> \<gamma>) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                    (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])) =
                  \<nu> \<cdot> \<r>[r] \<cdot> ((r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<a>[src f\<^sup>*, f, w]) \<cdot>
                    (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                       (\<rho> \<star> trg w \<star> w)) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
            proof -
              have "(g \<star> \<gamma>) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                      (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]) =
                    (\<nu> \<cdot> \<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot> (\<rho> \<star> f\<^sup>*)) \<cdot>
                      (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                      (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
                using \<gamma> by auto
              also have "... =
                         \<nu> \<cdot> \<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot>
                           ((\<rho> \<star> f\<^sup>*) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>')) \<cdot>
                             (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
                using comp_assoc by simp
              also have "... = \<nu> \<cdot> \<r>[r] \<cdot> (r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot>
                                 (((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> ((r \<star> f) \<star> f\<^sup>* \<star> \<theta>') \<cdot> (\<rho> \<star> f\<^sup>* \<star> f \<star> w)) \<cdot>
                                   (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (g \<star> \<eta> \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<rho> \<star> f\<^sup>*) \<cdot> (g \<star> \<r>[f\<^sup>*]) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>') =
                      ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> (\<rho> \<star> f\<^sup>* \<star> src f\<^sup>*) \<cdot> (g \<star> f\<^sup>* \<star> \<theta>')"
                proof -
                  have "(\<rho> \<star> f\<^sup>*) \<cdot> (g \<star> \<r>[f\<^sup>*]) = ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> (\<rho> \<star> f\<^sup>* \<star> src f\<^sup>*)"
                    using tab_in_hom comp_arr_dom comp_cod_arr T0.antipar(1) interchange
                  by (metis T0.ide_right in_homE runit_simps(1,4-5))
                    thus ?thesis
                    by (metis comp_assoc)
                qed
                also have "... = ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> (\<rho> \<star> f\<^sup>* \<star> \<theta>')"
                  using comp_arr_dom comp_cod_arr T0.antipar
                        interchange [of \<rho> g "f\<^sup>* \<star> src f\<^sup>*" "f\<^sup>* \<star> \<theta>'"]
                  by simp
                also have "... = ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> ((r \<star> f) \<star> f\<^sup>* \<star> \<theta>') \<cdot> (\<rho> \<star> f\<^sup>* \<star> f \<star> w)"
                  using comp_arr_dom comp_cod_arr T0.antipar
                        interchange [of "r \<star> f" \<rho> "f\<^sup>* \<star> \<theta>'" "f\<^sup>* \<star> f \<star> w"]
                  by simp
                finally show ?thesis by simp
              qed
              also have "... = 
                         \<nu> \<cdot> \<r>[r] \<cdot>
                           ((r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot> ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> ((r \<star> f) \<star> f\<^sup>* \<star> \<theta>')) \<cdot>
                           ((\<rho> \<star> f\<^sup>* \<star> f \<star> w) \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (g \<star> \<eta> \<star> w)) \<cdot>
                            (g \<star> \<l>\<^sup>-\<^sup>1[w])"
                using comp_assoc by simp
              also have "... = \<nu> \<cdot> \<r>[r] \<cdot>
                                 ((r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<epsilon> \<star> f \<star> w) \<cdot>
                                 (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]) \<cdot>
                                 (((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> ((r \<star> f) \<star> \<eta> \<star> w) \<cdot> (\<rho> \<star> trg w \<star> w)) \<cdot>
                                 (g \<star> \<l>\<^sup>-\<^sup>1[w])"
              proof -
                have 1: "(r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot> ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> ((r \<star> f) \<star> f\<^sup>* \<star> \<theta>') =
                           (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<epsilon> \<star> f \<star> w) \<cdot>
                           (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                proof -
                  have "(r \<star> \<epsilon>) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot> ((r \<star> f) \<star> \<r>[f\<^sup>*]) \<cdot> ((r \<star> f) \<star> f\<^sup>* \<star> \<theta>') =
                        (r \<star> \<epsilon>) \<cdot> (r \<star> f \<star> \<r>[f\<^sup>*]) \<cdot> \<a>[r, f, f\<^sup>* \<star> src f\<^sup>*] \<cdot> ((r \<star> f) \<star> f\<^sup>* \<star> \<theta>')"
                  proof -
                    have "\<a>[r, f, f\<^sup>*] \<cdot> ((r \<star> f) \<star> \<r>[f\<^sup>*]) = (r \<star> f \<star> \<r>[f\<^sup>*]) \<cdot> \<a>[r, f, f\<^sup>* \<star> src f\<^sup>*]"
                      using assoc_naturality [of r f "\<r>[f\<^sup>*]"] T0.antipar by auto
                    thus ?thesis
                      using comp_assoc by metis
                  qed
                  also have "... = (r \<star> \<epsilon>) \<cdot> (r \<star> f \<star> \<r>[f\<^sup>*]) \<cdot> (r \<star> f \<star> f\<^sup>* \<star> \<theta>') \<cdot>
                                     \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                    using assoc_naturality [of r f "f\<^sup>* \<star> \<theta>'"] T0.antipar by fastforce
                  also have "... = (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*]) \<cdot>
                                   (r \<star> f \<star> f\<^sup>* \<star> \<theta>') \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                  proof -
                    have "(r \<star> \<epsilon>) \<cdot> (r \<star> f \<star> \<r>[f\<^sup>*]) =
                          (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*])"
                    proof -
                      have "(r \<star> \<epsilon>) \<cdot> (r \<star> f \<star> \<r>[f\<^sup>*]) = r \<star> (\<epsilon> \<cdot> (f \<star> \<r>[f\<^sup>*]))"
                        using whisker_left T0.antipar by simp
                      also have "... =
                                 (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*])"
                      proof -
                        have "\<epsilon> \<cdot> (f \<star> \<r>[f\<^sup>*]) = \<r>[src f\<^sup>*] \<cdot> (\<epsilon> \<star> src f\<^sup>*) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*]"
                          using ide_leg0 T0.antipar runit_hcomp invert_side_of_triangle(2)
                                runit_naturality comp_assoc
                          by (metis (no_types, lifting) T0.counit_simps(1-4) T0.ide_right)
                        thus ?thesis
                          using whisker_left T0.antipar by simp
                      qed
                      finally show ?thesis by simp
                    qed
                    thus ?thesis using comp_assoc by metis
                  qed
                  also have "... =
                             (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot>
                               ((r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*]) \<cdot> (r \<star> f \<star> f\<^sup>* \<star> \<theta>')) \<cdot>
                                 \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                         using comp_assoc by simp
                  also have "... = (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot>
                                     ((r \<star> (f \<star> f\<^sup>*) \<star> \<theta>') \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w])) \<cdot>
                                       \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                  proof -
                    have "(r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*]) \<cdot> (r \<star> f \<star> f\<^sup>* \<star> \<theta>') =
                          (r \<star> (f \<star> f\<^sup>*) \<star> \<theta>') \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w])"
                    proof -
                      have "(r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*]) \<cdot> (r \<star> f \<star> f\<^sup>* \<star> \<theta>') =
                            r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, src f\<^sup>*] \<cdot> (f \<star> f\<^sup>* \<star> \<theta>')"
                        using whisker_left T0.antipar by simp
                      also have "... = r \<star> ((f \<star> f\<^sup>*) \<star> \<theta>') \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]"
                        using assoc'_naturality [of f "f\<^sup>*" \<theta>'] T0.antipar by auto
                      also have "... = (r \<star> (f \<star> f\<^sup>*) \<star> \<theta>') \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w])"
                        using whisker_left T0.antipar by auto
                      finally show ?thesis by simp
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> (f \<star> f\<^sup>*) \<star> \<theta>') \<cdot>
                                     (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                    using comp_assoc by simp
                  also have "... = 
                             (r \<star> \<r>[src f\<^sup>*]) \<cdot> ((r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> (f \<star> f\<^sup>*) \<star> \<theta>')) \<cdot>
                               (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                    using comp_assoc by simp
                  also have "... = (r \<star> \<r>[src f\<^sup>*]) \<cdot> ((r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<epsilon> \<star> f \<star> w)) \<cdot>
                                     (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                  proof -
                    have "(r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> (f \<star> f\<^sup>*) \<star> \<theta>') =
                          (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<epsilon> \<star> f \<star> w)"
                    proof -
                      have "(r \<star> \<epsilon> \<star> src f\<^sup>*) \<cdot> (r \<star> (f \<star> f\<^sup>*) \<star> \<theta>') =
                            r \<star> (\<epsilon> \<star> src f\<^sup>*) \<cdot> ((f \<star> f\<^sup>*) \<star> \<theta>')"
                        using whisker_left T0.antipar by simp
                      also have "... = r \<star> \<epsilon> \<star> \<theta>'"
                        using interchange [of \<epsilon> "f \<star> f\<^sup>*" "src f\<^sup>*" \<theta>']
                              T0.antipar comp_arr_dom comp_cod_arr
                        by auto
                      also have "... = r \<star> (src f\<^sup>* \<star> \<theta>') \<cdot> (\<epsilon> \<star> f \<star> w)"
                        using interchange [of "src f\<^sup>*" \<epsilon> \<theta>' "f \<star> w"]
                              T0.antipar comp_arr_dom comp_cod_arr
                        by auto
                      also have "... = (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<epsilon> \<star> f \<star> w)"
                        using whisker_left T0.antipar by simp
                      finally show ?thesis by blast
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = (r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<epsilon> \<star> f \<star> w) \<cdot>
                                     (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]"
                    using comp_assoc by simp
                  finally show ?thesis by simp
                qed
                have 2: "(\<rho> \<star> f\<^sup>* \<star> f \<star> w) \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (g \<star> \<eta> \<star> w) =
                           ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> ((r \<star> f) \<star> \<eta> \<star> w) \<cdot> (\<rho> \<star> trg w \<star> w)"
                proof -
                  have "(\<rho> \<star> f\<^sup>* \<star> f \<star> w) \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (g \<star> \<eta> \<star> w) =
                        ((\<rho> \<star> f\<^sup>* \<star> f \<star> w) \<cdot> (g \<star> \<a>[f\<^sup>*, f, w])) \<cdot> (g \<star> \<eta> \<star> w)"
                    using comp_assoc by simp
                  also have "... = (((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (\<rho> \<star> (f\<^sup>* \<star> f) \<star> w)) \<cdot> (g \<star> \<eta> \<star> w)"
                  proof -
                    have "(\<rho> \<star> f\<^sup>* \<star> f \<star> w) \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) =
                          ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (\<rho> \<star> (f\<^sup>* \<star> f) \<star> w)"
                    proof -
                      have "(\<rho> \<star> f\<^sup>* \<star> f \<star> w) \<cdot> (g \<star> \<a>[f\<^sup>*, f, w]) =
                            \<rho> \<cdot> g \<star> (f\<^sup>* \<star> f \<star> w) \<cdot> \<a>[f\<^sup>*, f, w]"
                        using interchange T0.antipar by auto
                      also have "... = \<rho> \<star> \<a>[f\<^sup>*, f, w]"
                        using comp_arr_dom comp_cod_arr T0.antipar by auto
                      also have "... = (r \<star> f) \<cdot> \<rho> \<star> \<a>[f\<^sup>*, f, w] \<cdot> ((f\<^sup>* \<star> f) \<star> w)"
                        using comp_arr_dom comp_cod_arr T0.antipar by auto
                      also have "... = ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (\<rho> \<star> (f\<^sup>* \<star> f) \<star> w)"
                        using interchange T0.antipar by auto
                      finally show ?thesis by blast
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> (\<rho> \<star> (f\<^sup>* \<star> f) \<star> w) \<cdot> (g \<star> \<eta> \<star> w)"
                    using comp_assoc by simp
                  also have "... = ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot> ((r \<star> f) \<star> \<eta> \<star> w) \<cdot> (\<rho> \<star> trg w \<star> w)"
                  proof -
                    have "(\<rho> \<star> (f\<^sup>* \<star> f) \<star> w) \<cdot> (g \<star> \<eta> \<star> w) = ((r \<star> f) \<star> \<eta> \<star> w) \<cdot> (\<rho> \<star> trg w \<star> w)"
                    proof -
                      have "(\<rho> \<star> (f\<^sup>* \<star> f) \<star> w) \<cdot> (g \<star> \<eta> \<star> w) = \<rho> \<cdot> g \<star> (f\<^sup>* \<star> f) \<cdot> \<eta> \<star> w \<cdot> w"
                      proof -
                        have "\<guillemotleft>g \<star> \<eta> \<star> w : g \<star> trg w \<star> w \<Rightarrow> g \<star> (f\<^sup>* \<star> f) \<star> w\<guillemotright>"
                          by (intro hcomp_in_vhom, auto)
                        thus ?thesis
                          using interchange whisker_right T0.antipar by auto
                      qed
                      also have "... = (r \<star> f) \<cdot> \<rho> \<star> \<eta> \<cdot> trg w \<star> w \<cdot> w"
                        using comp_arr_dom comp_cod_arr by auto
                      also have "... = ((r \<star> f) \<star> \<eta> \<star> w) \<cdot> (\<rho> \<star> trg w \<star> w)"
                        using interchange [of "r \<star> f" \<rho> "\<eta> \<star> w" "trg w \<star> w"]
                              interchange [of \<eta> "trg w" w w]
                              comp_arr_dom comp_cod_arr T0.unit_in_hom
                        by auto
                      finally show ?thesis by simp
                    qed
                    thus ?thesis by simp
                  qed
                  finally show ?thesis by simp
                qed
                show ?thesis
                  using 1 2 by simp
              qed
              also have "... =
                         \<nu> \<cdot> \<r>[r] \<cdot>
                           ((r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>') \<cdot>
                              ((r \<star> \<a>[src r, f, w]) \<cdot> (r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f \<star> f\<^sup>*, f, w])) \<cdot>
                            (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot> \<a>[r, f, f\<^sup>* \<star> f \<star> w]) \<cdot>
                          (((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                              (\<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot> (r \<star> \<a>[f, f\<^sup>* \<star> f, w]) \<cdot>
                                (r \<star> (f \<star> \<eta>) \<star> w) \<cdot>
                               (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w]) \<cdot>
                            (\<rho> \<star> trg w \<star> w)) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
              proof -
                have 3: "r \<star> \<epsilon> \<star> f \<star> w =
                         (r \<star> \<a>[src r, f, w]) \<cdot> (r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f \<star> f\<^sup>*, f, w])"
                proof -
                  have "r \<star> \<epsilon> \<star> f \<star> w =
                        ((r \<star> \<a>[src r, f, w]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[src r, f, w])) \<cdot> (r \<star> \<epsilon> \<star> f \<star> w)"
                    using T0.antipar whisker_left [of r "\<a>[src r, f, w]" "\<a>\<^sup>-\<^sup>1[src r, f, w]"]
                          comp_cod_arr comp_assoc_assoc'
                    by simp
                 also have "... = (r \<star> \<a>[src r, f, w]) \<cdot> (r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot>
                                     (r \<star> \<a>\<^sup>-\<^sup>1[f \<star> f\<^sup>*, f, w])"
                    using assoc'_naturality [of \<epsilon> f w]
                          whisker_left [of r "\<a>\<^sup>-\<^sup>1[src r, f, w]" "\<epsilon> \<star> f \<star> w"]
                          whisker_left comp_assoc T0.antipar
                    by simp
                  finally show ?thesis
                    using T0.antipar by simp
                qed
                have 4: "(r \<star> f) \<star> \<eta> \<star> w =
                         \<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot> (r \<star> \<a>[f, f\<^sup>* \<star> f, w]) \<cdot>
                           (r \<star> (f \<star> \<eta>) \<star> w) \<cdot>
                             (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w]"
                proof -
                  have "(r \<star> f) \<star> \<eta> \<star> w =
                        (\<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot>
                          ((r \<star> \<a>[f, f\<^sup>* \<star> f, w]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>* \<star> f, w])) \<cdot>
                            \<a>[r, f, (f\<^sup>* \<star> f) \<star> w]) \<cdot>
                              ((r \<star> f) \<star> \<eta> \<star> w)"
                  proof -
                    have "ide r" by simp
                    moreover have "seq \<a>[f, f\<^sup>* \<star> f, w] \<a>\<^sup>-\<^sup>1[f, f\<^sup>* \<star> f, w]"
                      using T0.antipar comp_cod_arr ide_base by simp
                    ultimately have "(r \<star> \<a>[f, f\<^sup>* \<star> f, w]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>* \<star> f, w]) =
                                     r \<star> \<a>[f, f\<^sup>* \<star> f, w] \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sup>* \<star> f, w]"
                      using whisker_left by metis
                    thus ?thesis
                      using T0.antipar comp_cod_arr comp_assoc_assoc' by simp
                  qed
                  also have "... =
                             \<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot>
                               (r \<star> \<a>[f, f\<^sup>* \<star> f, w]) \<cdot> ((r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>* \<star> f, w]) \<cdot>
                                 (r \<star> f \<star> \<eta> \<star> w)) \<cdot>
                                   \<a>[r, f, trg w \<star> w]"
                    using assoc_naturality [of r f "\<eta> \<star> w"] comp_assoc by fastforce
                  also have "... =
                             \<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot>
                               (r \<star> \<a>[f, f\<^sup>* \<star> f, w]) \<cdot> (r \<star> (f \<star> \<eta>) \<star> w) \<cdot>
                                 (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                                   \<a>[r, f, trg w \<star> w]"
                    using assoc'_naturality [of f \<eta> w] T0.antipar comp_assoc
                          whisker_left [of r "\<a>\<^sup>-\<^sup>1[f, f\<^sup>* \<star> f, w]" "f \<star> \<eta> \<star> w"]
                          whisker_left [of r "(f \<star> \<eta>) \<star> w" "\<a>\<^sup>-\<^sup>1[f, trg w, w]"]
                    by simp
                  finally show ?thesis by blast
                qed
                show ?thesis
                  using 3 4 T0.antipar by simp
              qed
              also have "... = \<nu> \<cdot> \<r>[r] \<cdot> ((r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>') \<cdot>
                                (r \<star> \<a>[src r, f, w]) \<cdot>
                                  ((r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot>
                                    ((r \<star> \<a>\<^sup>-\<^sup>1[f \<star> f\<^sup>*, f, w]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot>
                                     \<a>[r, f, f\<^sup>* \<star> f \<star> w] \<cdot> ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                                     \<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot> (r \<star> \<a>[f, f\<^sup>* \<star> f, w])) \<cdot>
                                  (r \<star> (f \<star> \<eta>) \<star> w)) \<cdot>
                                    (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                                      (\<rho> \<star> trg w \<star> w)) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
                using comp_assoc T0.antipar by auto
              also have "... = \<nu> \<cdot> \<r>[r] \<cdot> ((r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>') \<cdot>
                                (r \<star> \<a>[src r, f, w]) \<cdot>
                                  ((r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<star> w) \<cdot>
                                    (r \<star> (f \<star> \<eta>) \<star> w)) \<cdot>
                                  (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                                    (\<rho> \<star> trg w \<star> w)) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
              proof -
                have "(r \<star> \<a>\<^sup>-\<^sup>1[f \<star> f\<^sup>*, f, w]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot>
                        \<a>[r, f, f\<^sup>* \<star> f \<star> w] \<cdot> ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                          \<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot> (r \<star> \<a>[f, f\<^sup>* \<star> f, w]) =
                      r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<star> w"
                proof -
                  text \<open>We can compress the reasoning about the associativities using coherence.\<close>
                  have "(r \<star> \<a>\<^sup>-\<^sup>1[f \<star> f\<^sup>*, f, w]) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f \<star> w]) \<cdot>
                          \<a>[r, f, f\<^sup>* \<star> f \<star> w] \<cdot> ((r \<star> f) \<star> \<a>[f\<^sup>*, f, w]) \<cdot>
                            \<a>\<^sup>-\<^sup>1[r, f, (f\<^sup>* \<star> f) \<star> w] \<cdot> (r \<star> \<a>[f, f\<^sup>* \<star> f, w]) =
                          \<lbrace>(\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^sup>*\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot> (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sup>*\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                            \<^bold>\<a>\<^bold>[\<^bold>\<langle>r\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sup>*\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> ((\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^sup>*\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                              \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>r\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, (\<^bold>\<langle>f\<^sup>*\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sup>*\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>])\<rbrace>"
                    using T0.antipar \<a>'_def \<alpha>_def assoc'_eq_inv_assoc by auto
                  also have "... = \<lbrace>\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^sup>*\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>\<rbrace>"
                    using T0.antipar by (intro E.eval_eqI, auto)
                  also have "... = r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<star> w"
                    using T0.antipar \<a>'_def \<alpha>_def assoc'_eq_inv_assoc by simp
                  finally show ?thesis
                    by simp
                qed
                thus ?thesis by simp
              qed
              also have "... = \<nu> \<cdot> \<r>[r] \<cdot> ((r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>') \<cdot>
                                  (r \<star> \<a>[src r, f, w]) \<cdot>
                                (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot>
                                  (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                                    (\<rho> \<star> trg w \<star> w)) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
              proof -
                have "(r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<star> w) \<cdot> (r \<star> (f \<star> \<eta>) \<star> w) =
                      r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w"
                proof -
                  have "(r \<star> (\<epsilon> \<star> f) \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<star> w) \<cdot> (r \<star> (f \<star> \<eta>) \<star> w) =
                        r \<star> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, f\<^sup>*, f] \<cdot> (f \<star> \<eta>) \<star> w"
                    using whisker_left whisker_right T0.antipar by simp
                  also have "... = r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w"
                    using T0.triangle_left by simp
                  finally show ?thesis by blast
                qed
                thus ?thesis by simp
              qed
              also have "... = \<nu> \<cdot> \<r>[r] \<cdot> ((r \<star> \<r>[src f\<^sup>*]) \<cdot> (r \<star> src f\<^sup>* \<star> \<theta>') \<cdot> (r \<star> \<a>[src f\<^sup>*, f, w]) \<cdot>
                                (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot>
                                  (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                                    (\<rho> \<star> trg w \<star> w)) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w])"
                using T0.antipar by simp
              finally show ?thesis by simp
            qed
            also have "... = \<nu> \<cdot> \<r>[r] \<cdot>
                               ((r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>')) \<cdot>
                                 (r \<star> \<a>[src r, f, w]) \<cdot> (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot>
                                   (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                                    ((\<rho> \<star> trg w \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]))"
              using comp_assoc T0.antipar by simp
            also have "... = \<nu> \<cdot> \<r>[r] \<cdot>
                               ((r \<star> \<theta>') \<cdot> (r \<star> \<l>[f \<star> w])) \<cdot>
                                 (r \<star> \<a>[src r, f, w]) \<cdot> (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot>
                                   (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot> \<a>[r, f, trg w \<star> w] \<cdot>
                                    (((r \<star> f) \<star> \<l>\<^sup>-\<^sup>1[w]) \<cdot> (\<rho> \<star> w))"
            proof -
              have "(r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>') = (r \<star> \<theta>') \<cdot> (r \<star> \<l>[f \<star> w])"
              proof -
                have "(r \<star> \<r>[src r]) \<cdot> (r \<star> src r \<star> \<theta>') = r \<star> \<r>[src r] \<cdot> (src r \<star> \<theta>')"
                  using whisker_left by simp
                also have "... = r \<star> \<theta>' \<cdot> \<l>[f \<star> w]"
                  using lunit_naturality [of \<theta>'] unitor_coincidence by simp
                also have "... = (r \<star> \<theta>') \<cdot> (r \<star> \<l>[f \<star> w])"
                  using whisker_left by simp
                finally show ?thesis by simp
              qed
              moreover have "(\<rho> \<star> trg w \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]) = ((r \<star> f) \<star> \<l>\<^sup>-\<^sup>1[w]) \<cdot> (\<rho> \<star> w)"
              proof -
                have "(\<rho> \<star> trg w \<star> w) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[w]) = \<rho> \<cdot> g \<star> (trg w \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[w]"
                  using interchange by simp
                also have "... = \<rho> \<star> \<l>\<^sup>-\<^sup>1[w]"
                  using comp_arr_dom comp_cod_arr by simp
                also have "... = (r \<star> f) \<cdot> \<rho> \<star> \<l>\<^sup>-\<^sup>1[w] \<cdot> w"
                  using comp_arr_dom comp_cod_arr by simp
                also have "... = ((r \<star> f) \<star> \<l>\<^sup>-\<^sup>1[w]) \<cdot> (\<rho> \<star> w)"
                  using interchange by simp
                finally show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            qed
            also have "... = \<nu> \<cdot> \<r>[r] \<cdot> (r \<star> \<theta>') \<cdot>
                              ((r \<star> \<l>[f \<star> w]) \<cdot> (r \<star> \<a>[src r, f, w]) \<cdot>
                                 (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                                    \<a>[r, f, trg w \<star> w] \<cdot> ((r \<star> f) \<star> \<l>\<^sup>-\<^sup>1[w])) \<cdot>
                                (\<rho> \<star> w)"
              using comp_assoc by simp
            also have "... = \<nu> \<cdot> \<r>[r] \<cdot> (r \<star> \<theta>') \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w)"
            proof -
              have "((r \<star> \<l>[f \<star> w]) \<cdot> (r \<star> \<a>[src r, f, w]) \<cdot>
                      (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                        \<a>[r, f, trg w \<star> w] \<cdot> ((r \<star> f) \<star> \<l>\<^sup>-\<^sup>1[w])) =
                    \<a>[r, f, w]"
              proof -
                have "((r \<star> \<l>[f \<star> w]) \<cdot> (r \<star> \<a>[src r, f, w]) \<cdot>
                        (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                          \<a>[r, f, trg w \<star> w] \<cdot> ((r \<star> f) \<star> \<l>\<^sup>-\<^sup>1[w])) =
                      ((r \<star> (\<l>[f] \<star> w) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, f, w]) \<cdot> (r \<star> \<a>[src r, f, w]) \<cdot>
                         (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                           (r \<star> f \<star> \<l>\<^sup>-\<^sup>1[w])) \<cdot> \<a>[r, f, w]"
                  using comp_assoc assoc_naturality [of r f "\<l>\<^sup>-\<^sup>1[w]"] lunit_hcomp by simp
                also have "... = \<a>[r, f, w]"
                proof -
                  have "(r \<star> (\<l>[f] \<star> w) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, f, w]) \<cdot> (r \<star> \<a>[src r, f, w]) \<cdot>
                          (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                            (r \<star> f \<star> \<l>\<^sup>-\<^sup>1[w]) =
                        r \<star> f \<star> w"
                  proof -
                    text \<open>Again, get a little more mileage out of coherence.\<close>
                    have "(r \<star> (\<l>[f] \<star> w) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, f, w]) \<cdot> (r \<star> \<a>[src r, f, w]) \<cdot>
                            (r \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, trg w, w]) \<cdot>
                              (r \<star> f \<star> \<l>\<^sup>-\<^sup>1[w]) =
                          \<lbrace>(\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<l>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[E.Trg \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                               (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[E.Src \<^bold>\<langle>r\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                             (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> \<^bold>\<r>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>) \<^bold>\<cdot> (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, E.Trg \<^bold>\<langle>w\<^bold>\<rangle>, \<^bold>\<langle>w\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                               (\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>w\<^bold>\<rangle>\<^bold>])\<rbrace>"
                        using \<ll>_ide_simp \<rr>_ide_simp \<a>'_def \<alpha>_def assoc'_eq_inv_assoc by simp
                    also have "... = \<lbrace>\<^bold>\<langle>r\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>w\<^bold>\<rangle>\<rbrace>"
                      by (intro E.eval_eqI, auto)
                    also have "... = r \<star> f \<star> w"
                      by simp
                    finally show ?thesis by blast
                  qed
                  thus ?thesis
                    using comp_cod_arr
                    by (metis assoc_is_natural_1 base_simps(2-3) leg0_simps(2-4)
                        w_simps(2) w_simps(4) w_simps(5))
                qed
                finally show ?thesis by blast
              qed
              thus ?thesis by simp
            qed
            also have "... = \<nu> \<cdot> \<r>[r] \<cdot> \<r>\<^sup>-\<^sup>1[r] \<cdot> inv \<nu>"
            proof -
              have "\<r>\<^sup>-\<^sup>1[r] \<cdot> inv \<nu> = (r \<star> \<theta>') \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w)"
                using ** w\<theta>'\<nu> ide_base ide_leg0 tab_in_hom invert_side_of_triangle(2) comp_arr_dom
                      T0.antipar comp_assoc runit'_simps(1)
                by metis
              thus ?thesis by simp
            qed
            also have "... = g \<star> w"
              using ** w\<theta>'\<nu> ide_base comp_arr_inv'
              by (metis calculation in_homE invert_side_of_triangle(1) iso_runit iso_runit')
            finally show ?thesis by simp
          qed
          thus ?thesis by simp
        qed
      qed
      ultimately have 1: "iso (g \<star> \<gamma>)"
        using iso_iff_section_and_retraction by simp
      have "iso (inv (\<nu> \<cdot> \<r>[r]) \<cdot> (g \<star> \<gamma>))"
      proof -
        have "iso (inv (\<nu> \<cdot> \<r>[r]))"
          using w\<theta>'\<nu> \<gamma> iso_runit
          by (elim conjE in_homE, intro iso_inv_iso isos_compose, auto)
        thus ?thesis
          using 1 w\<theta>'\<nu> \<gamma> trg_\<gamma>_eq isos_compose iso_inv_iso
          by (elim conjE in_homE, auto)
      qed
      moreover have "inv (\<nu> \<cdot> \<r>[r]) \<cdot> (g \<star> \<gamma>) = composite_cell f\<^sup>* \<epsilon>"
      proof -
        have "inv (\<nu> \<cdot> \<r>[r]) \<cdot> (g \<star> \<gamma>) = inv (\<nu> \<cdot> \<r>[r]) \<cdot> \<nu> \<cdot> \<r>[r] \<cdot> composite_cell f\<^sup>* \<epsilon>"
          using \<gamma> by auto
        also have "... = ((inv (\<nu> \<cdot> \<r>[r]) \<cdot> (\<nu> \<cdot> \<r>[r])) \<cdot> (r \<star> \<epsilon>)) \<cdot> \<a>[r, f, f\<^sup>*] \<cdot> (\<rho> \<star> f\<^sup>*)"
            using w\<theta>'\<nu> iso_inv_iso comp_assoc by auto
        also have "... = composite_cell f\<^sup>* \<epsilon>"
        proof -
          have "dom \<nu> = r"
            using w\<theta>'\<nu> by auto
          thus ?thesis
            using iso_runit w\<theta>'\<nu> isos_compose comp_cod_arr whisker_left [of r "src r" \<epsilon>]
                  iso_inv_iso comp_inv_arr inv_is_inverse
            by auto
        qed
        finally show ?thesis by blast
      qed
      ultimately have "iso (composite_cell f\<^sup>* \<epsilon>)" by simp
      thus "iso (T0.trnr\<^sub>\<epsilon> r \<rho>)"
        using T0.trnr\<^sub>\<epsilon>_def ide_base runit_in_hom iso_runit isos_compose
        by (metis A arrI seqE)
    qed

    text \<open>
      It is convenient to have a simpler version of the previous result for when we do
      not care about the details of the isomorphism.
    \<close>

    lemma yields_isomorphic_representation':
    obtains \<psi> where "\<guillemotleft>\<psi> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>" and "iso \<psi>"
      using yields_isomorphic_representation adjoint_pair_def by simp

  end

  text \<open>
    It is natural to ask whether if \<open>\<guillemotleft>\<psi> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>\<close> is an isomorphism
    then \<open>\<rho> = (\<psi> \<star> f) \<cdot> T0.trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)\<close> is a tabulation of \<open>r\<close>.
    This is not true without additional conditions on \<open>f\<close> and \<open>g\<close>
    (\emph{cf.}~the comments following CKS Proposition 6).
    So only rather special isomorphisms \<open>\<guillemotleft>\<psi> : g \<star> f\<^sup>* \<Rightarrow> r\<guillemotright>\<close> result from tabulations of \<open>r\<close>.
  \<close>

  subsection "Tabulation of a Right Adjoint"

  text \<open>
    Here we obtain a tabulation of the right adjoint of a map.  This is CKS Proposition 1(e).
    It was somewhat difficult to find the correct way to insert the unitors
    that CKS omit.  At first I thought I could only prove this under the assumption
    that the bicategory is normal, but later I saw how to do it in the general case.
  \<close>

  context adjunction_in_bicategory
  begin

    lemma tabulation_of_right_adjoint:
    shows "tabulation V H \<a> \<i> src trg g \<eta> f (src f)"
    proof -
      interpret T: tabulation_data V H \<a> \<i> src trg g \<eta> f \<open>src f\<close>
        using unit_in_hom antipar by (unfold_locales, simp_all)
      show ?thesis
      proof
        show T1: "\<And>u \<omega>. \<lbrakk> ide u; \<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> g \<star> u\<guillemotright> \<rbrakk> \<Longrightarrow>
                         \<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> src f \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                                 T.composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
        proof -
          fix u v \<omega>
          assume u: "ide u"
          assume \<omega>: "\<guillemotleft>\<omega> : v \<Rightarrow> g \<star> u\<guillemotright>"
          have v: "ide v"
            using \<omega> by auto
          have 1: "src g = trg u"
            using \<omega> by (metis arr_cod in_homE not_arr_null seq_if_composable)
          have 2: "src f = trg v"
            using \<omega> 1 u ide_right antipar(1) vconn_implies_hpar(4) by force
          text \<open>It seems clear that we need to take \<open>w = v\<close> and \<open>\<nu> = \<l>\<^sup>-\<^sup>1[v]\<close>. \<close>
          let ?w = v
          let ?\<nu> = "\<l>\<^sup>-\<^sup>1[v]"
          have \<nu>: "\<guillemotleft>?\<nu> : v \<Rightarrow> src f \<star> ?w\<guillemotright> \<and> iso ?\<nu>"
            using v 2 iso_lunit' by auto
          text \<open>
            We need \<open>\<theta>\<close>, defined to satisfy \<open>\<guillemotleft>\<theta> : f \<star> v \<Rightarrow> u\<guillemotright>\<close> and
            \<open>\<omega> = (v \<star> \<theta>) \<cdot> \<a>[v, f, v] \<cdot> (\<eta> \<star> w) \<cdot> \<l>\<^sup>-\<^sup>1[v]\<close>.
            We have \<open>\<guillemotleft>\<omega> : v \<Rightarrow> g \<star> u\<guillemotright>\<close>, so we can get arrow \<open>\<guillemotleft>\<theta> : f \<star> v \<Rightarrow> u\<guillemotright>\<close> by adjoint transpose.
            Note that this uses adjoint transpose on the \emph{left}, rather than on the right.
          \<close>
          let ?\<theta> = "trnl\<^sub>\<epsilon> u \<omega>"
          have \<theta>: "\<guillemotleft>?\<theta> : f \<star> ?w \<Rightarrow> u\<guillemotright>"
            using u v antipar 1 2 \<omega> adjoint_transpose_left(2) [of u v] by auto
          text \<open>
            Now, \<open>trnl\<^sub>\<eta> v \<theta> \<equiv> (g \<star> \<theta>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v]\<close>, which suggests that
            we ought to have \<open>\<omega> = trnl\<^sub>\<eta> v \<theta>\<close> and \<open>\<nu> = \<l>\<^sup>-\<^sup>1[v]\<close>;
          \<close>
          have "T.composite_cell ?w ?\<theta> \<cdot> ?\<nu> = \<omega>"
            using u v \<omega> 1 2 adjoint_transpose_left(4) [of u v \<omega>] trnl\<^sub>\<eta>_def comp_assoc by simp
          thus "\<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : v \<Rightarrow> src f \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                        T.composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
            using v \<theta> \<nu> antipar comp_assoc by blast
        qed
        show T2: "\<And>u w w' \<theta> \<theta>' \<beta>.
                    \<lbrakk> ide w; ide w'; \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>;
                      \<guillemotleft>\<beta> : src f \<star> w \<Rightarrow> src f \<star> w'\<guillemotright>;
                     T.composite_cell w \<theta> = T.composite_cell w' \<theta>' \<cdot> \<beta> \<rbrakk> \<Longrightarrow>
                    \<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
        proof -
          fix u w w' \<theta> \<theta>' \<beta>
          assume w: "ide w"
          assume w': "ide w'"
          assume \<theta>: "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>"
          assume \<theta>': "\<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>"
          assume \<beta>: "\<guillemotleft>\<beta> : src f \<star> w \<Rightarrow> src f \<star> w'\<guillemotright>"
          assume E: "T.composite_cell w \<theta> = T.composite_cell w' \<theta>' \<cdot> \<beta>"
          interpret T: uw\<theta>w'\<theta>'\<beta> V H \<a> \<i> src trg g \<eta> f \<open>src f\<close> u w \<theta> w' \<theta>' \<beta>
            using w w' \<theta> \<theta>' \<beta> E comp_assoc by (unfold_locales, auto)
          have 2: "src f = trg \<beta>"
            using antipar by simp
          show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
          proof -
            text \<open>
              The requirement \<open>\<beta> = src f \<star> \<gamma>\<close> means we have to essentially invert \<open>\<lambda>\<gamma>. src f \<star> \<gamma>\<close>
              to obtain \<open>\<gamma>\<close>.  CKS say only: ``the strong form of \<open>T2\<close> is clear since \<open>g = 1\<close>"
              (here by ``\<open>g\<close>'' they are referring to \<open>dom \<eta>\<close>, the ``output leg'' of the span in
              the tabulation).  This would mean that we would have to take \<open>\<gamma> = \<beta>\<close>, which doesn't
              work for a general bicategory (we don't necessarily have \<open>src f \<star> \<gamma> = \<gamma>\<close>).
              For a general bicategory, we have to take \<open>\<gamma> = \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w]\<close>.
            \<close>
            let ?\<gamma> = "\<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w]"
            have \<gamma>: "\<guillemotleft>?\<gamma> : w \<Rightarrow> w'\<guillemotright>"
              using \<beta> by simp
            have 3: "\<beta> = src f \<star> ?\<gamma>"
            proof -
              have "\<beta> = \<l>\<^sup>-\<^sup>1[w'] \<cdot> ?\<gamma> \<cdot> \<l>[w]"
                using \<beta> iso_lunit
                by (simp add: comp_arr_dom invert_side_of_triangle(1) comp_assoc)
              also have "... = \<l>\<^sup>-\<^sup>1[w'] \<cdot> \<l>[w'] \<cdot> (src f \<star> ?\<gamma>)"
                using \<gamma> lunit_naturality
                by (metis T.uw\<theta>.w_simps(4) in_homE trg_dom)
              also have "... = (\<l>\<^sup>-\<^sup>1[w'] \<cdot> \<l>[w']) \<cdot> (src f \<star> ?\<gamma>)"
                using comp_assoc by simp
              also have "... = src f \<star> ?\<gamma>"
                using \<gamma> iso_lunit comp_inv_arr comp_cod_arr
                by (metis T.\<beta>_simps(1) calculation comp_ide_arr inv_is_inverse inverse_arrowsE w')
              finally show ?thesis by simp
            qed
            have "\<theta> = \<theta>' \<cdot> (f \<star> ?\<gamma>)"
            proof -
              have "\<theta> = trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> w \<theta>)"
                using \<theta> adjoint_transpose_left(3) [of u w \<theta>] by simp
              also have "... = trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> w' \<theta>' \<cdot> \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w])"
              proof -
                have "trnl\<^sub>\<eta> w \<theta> = trnl\<^sub>\<eta> w' \<theta>' \<cdot> \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w]"
                proof -
                  have "trnl\<^sub>\<eta> w \<theta> \<cdot> \<l>[w] = (T.composite_cell w \<theta> \<cdot> \<l>\<^sup>-\<^sup>1[w]) \<cdot> \<l>[w]"
                    unfolding trnl\<^sub>\<eta>_def using comp_assoc by simp
                  also have "... = T.composite_cell w \<theta> \<cdot> (\<l>\<^sup>-\<^sup>1[w] \<cdot> \<l>[w])"
                    using comp_assoc by simp
                  also have 4: "... = T.composite_cell w \<theta>"
                    using comp_arr_dom by (simp add: comp_inv_arr')
                  also have "... = T.composite_cell w' \<theta>' \<cdot> \<beta>"
                    using E by simp
                  also have "... = (T.composite_cell w' \<theta>' \<cdot> \<l>\<^sup>-\<^sup>1[w']) \<cdot> \<l>[w'] \<cdot> \<beta>"
                  proof -
                    have "(\<l>\<^sup>-\<^sup>1[w'] \<cdot> \<l>[w']) \<cdot> \<beta> = \<beta>"
                      using iso_lunit \<beta> comp_cod_arr comp_assoc comp_inv_arr' by simp
                    thus ?thesis
                      using comp_assoc by simp
                  qed
                  also have "... = trnl\<^sub>\<eta> w' \<theta>' \<cdot> \<l>[w'] \<cdot> \<beta>"
                    unfolding trnl\<^sub>\<eta>_def using comp_assoc by simp
                  finally have "trnl\<^sub>\<eta> w \<theta> \<cdot> \<l>[w] = trnl\<^sub>\<eta> w' \<theta>' \<cdot> \<l>[w'] \<cdot> \<beta>"
                    by simp
                  thus ?thesis
                    using \<beta> 4 invert_side_of_triangle(2) adjoint_transpose_left iso_lunit
                          trnl\<^sub>\<eta>_def comp_assoc
                    by metis
                qed
                thus ?thesis by simp
              qed
              also have "... = \<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> trnl\<^sub>\<eta> w' \<theta>' \<cdot> \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w])"
                using trnl\<^sub>\<epsilon>_def by simp
              also have
                "... = \<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> trnl\<^sub>\<eta> w' \<theta>') \<cdot> (f \<star> \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w])"
                using ide_left ide_right w w' 2 \<beta> \<theta> antipar trnl\<^sub>\<epsilon>_def adjoint_transpose_left
                      whisker_left
                by (metis T.uw\<theta>.\<theta>_simps(1) calculation hseqE seqE)
              also have
                "... = (\<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> trnl\<^sub>\<eta> w' \<theta>')) \<cdot> (f \<star> \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w])"
                using comp_assoc by simp
              also have "... = trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> w' \<theta>') \<cdot> (f \<star> \<l>[w'] \<cdot> \<beta> \<cdot> \<l>\<^sup>-\<^sup>1[w])"
                unfolding trnl\<^sub>\<epsilon>_def by simp
              also have "... = \<theta>' \<cdot> (f \<star> ?\<gamma>)"
                using \<theta>' adjoint_transpose_left(3) by auto
              finally show ?thesis by simp
            qed
            hence "\<exists>\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
              using \<gamma> 3 hcomp_obj_arr by blast
            moreover have "\<And>\<gamma> \<gamma>'. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>) \<and>
                                   \<guillemotleft>\<gamma>' : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma>' \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>') \<Longrightarrow> \<gamma> = \<gamma>'"
            proof -
              fix \<gamma> \<gamma>'
              assume \<gamma>\<gamma>': "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>) \<and>
                           \<guillemotleft>\<gamma>' : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = src f \<star> \<gamma>' \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>')"
              show "\<gamma> = \<gamma>'"
                using \<gamma>\<gamma>' vconn_implies_hpar(2) L.is_faithful [of \<gamma> \<gamma>'] by force
            qed
            ultimately show ?thesis by blast
          qed
        qed
      qed
    qed

  end

  subsection "Preservation by Isomorphisms"

  text \<open>
    Next, we show that tabulations are preserved under composition on all three sides by
    isomorphisms.  This is something that we would expect to hold if ``tabulation'' is a
    properly bicategorical notion.
  \<close>

  context tabulation
  begin

    text \<open>
      Tabulations are preserved under composition of an isomorphism with the ``input leg''.
    \<close>

    lemma preserved_by_input_iso:
    assumes "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>"
    shows "tabulation V H \<a> \<i> src trg r ((r \<star> \<phi>) \<cdot> \<rho>) f' g"
    proof -
      interpret T': tabulation_data V H \<a> \<i> src trg r \<open>(r \<star> \<phi>) \<cdot> \<rho>\<close> f'
        using assms(1) tab_in_hom
        apply unfold_locales
          apply auto
        by force
      show ?thesis
      proof
        show "\<And>u \<omega>. \<lbrakk> ide u; \<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright> \<rbrakk> \<Longrightarrow>
               \<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and>
                       iso \<nu> \<and> T'.composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
        proof -
          fix u \<omega>
          assume u: "ide u" and \<omega>: "\<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright>"
          obtain w \<theta> \<nu> where w\<theta>\<nu>: "ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and>
                                   iso \<nu> \<and> composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
            using u \<omega> T1 by blast
          interpret T1: uw\<theta>\<omega>\<nu> V H \<a> \<i> src trg r \<rho> f g u w \<theta> \<omega> \<nu>
            using w\<theta>\<nu> comp_assoc by (unfold_locales, auto)
          have 1: "\<guillemotleft>inv \<phi> \<star> w : f' \<star> w \<Rightarrow> f \<star> w\<guillemotright>"
            using assms by (intro hcomp_in_vhom, auto)
          have "ide w \<and> \<guillemotleft>\<theta> \<cdot> (inv \<phi> \<star> w) : f' \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                T'.composite_cell w (\<theta> \<cdot> (inv \<phi> \<star> w)) \<cdot> \<nu> = \<omega>"
            using w\<theta>\<nu> 1
            apply (intro conjI)
                apply auto[4]
          proof -
            show "T'.composite_cell w (\<theta> \<cdot> (inv \<phi> \<star> w)) \<cdot> \<nu> = \<omega>"
            proof -
              have "T'.composite_cell w (\<theta> \<cdot> (inv \<phi> \<star> w)) \<cdot> \<nu> =
                    (r \<star> \<theta>) \<cdot> ((r \<star> inv \<phi> \<star> w) \<cdot> \<a>[r, f', w]) \<cdot> ((r \<star> \<phi>) \<cdot> \<rho> \<star> w) \<cdot> \<nu>"
                using assms(1) 1 whisker_left [of r \<theta> "inv \<phi> \<star> w"] comp_assoc by auto
              also have "... = (r \<star> \<theta>) \<cdot> (\<a>[r, f, w] \<cdot> ((r \<star> inv \<phi>) \<star> w)) \<cdot> ((r \<star> \<phi>) \<cdot> \<rho> \<star> w) \<cdot> \<nu>"
                using assms assoc_naturality [of r "inv \<phi>" w]
                by (metis 1 T'.tab_simps(1) base_simps(3) base_simps(4) T1.w_simps(5-6)
                    cod_inv dom_inv hseqE in_homE seqE trg_inv)
              also have "... = (r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> ((((r \<star> inv \<phi>) \<star> w) \<cdot> ((r \<star> \<phi>) \<star> w)) \<cdot> (\<rho> \<star> w)) \<cdot> \<nu>"
                using whisker_right [of w "r \<star> \<phi>" \<rho>] comp_assoc T1.ide_w vseq_implies_hpar(1)
                by auto
              also have "... = composite_cell w \<theta> \<cdot> \<nu>"
              proof -
                have "(((r \<star> inv \<phi>) \<star> w) \<cdot> ((r \<star> \<phi>) \<star> w)) \<cdot> (\<rho> \<star> w) = \<rho> \<star> w"
                proof -
                  have "\<guillemotleft>r \<star> \<phi> : r \<star> f \<Rightarrow> r \<star> f'\<guillemotright>"
                    using assms(1) by (intro hcomp_in_vhom, auto)
                  moreover have "\<guillemotleft>r \<star> inv \<phi> : r \<star> f' \<Rightarrow> r \<star> f\<guillemotright>"
                    using assms by (intro hcomp_in_vhom, auto)
                  ultimately show ?thesis
                    using comp_cod_arr
                    by (metis T1.w_in_hom(2) tab_simps(1) tab_simps(5) assms(1-2) comp_inv_arr'
                              in_homE leg0_simps(2) interchange base_in_hom(2) seqI')
                qed
                thus ?thesis
                  using comp_assoc by simp
              qed
              also have "... = \<omega>"
                using w\<theta>\<nu> by simp
              finally show ?thesis by simp
            qed
          qed
          thus "\<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                        T'.composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
            by blast
        qed
        show "\<And>u w w' \<theta> \<theta>' \<beta>. \<lbrakk> ide w; ide w'; \<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<theta>' : f' \<star> w' \<Rightarrow> u\<guillemotright>;
                                \<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>;
                                T'.composite_cell w \<theta> = T'.composite_cell w' \<theta>' \<cdot> \<beta> \<rbrakk> \<Longrightarrow>
                  \<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>)"
        proof -
          fix u w w' \<theta> \<theta>' \<beta>
          assume w: "ide w" and w': "ide w'"
          and \<theta>: "\<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> u\<guillemotright>" and \<theta>': "\<guillemotleft>\<theta>' : f' \<star> w' \<Rightarrow> u\<guillemotright>"
          and \<beta>: "\<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>"
          and eq: "T'.composite_cell w \<theta> = T'.composite_cell w' \<theta>' \<cdot> \<beta>"
          interpret uw\<theta>w'\<theta>'\<beta> V H \<a> \<i> src trg r \<open>(r \<star> \<phi>) \<cdot> \<rho>\<close> f' g u w \<theta> w' \<theta>' \<beta>
            using w w' \<theta> \<theta>' \<beta> eq comp_assoc by (unfold_locales, auto)
          show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>)"
          proof -
            have \<phi>_w: "\<guillemotleft>\<phi> \<star> w : f \<star> w \<Rightarrow> f' \<star> w\<guillemotright>"
              using assms(1) by (intro hcomp_in_vhom, auto)
            have \<phi>_w': "\<guillemotleft>\<phi> \<star> w' : f \<star> w' \<Rightarrow> f' \<star> w'\<guillemotright>"
              using assms(1) by (intro hcomp_in_vhom, auto)
            have "\<guillemotleft>\<theta> \<cdot> (\<phi> \<star> w) : f \<star> w \<Rightarrow> u\<guillemotright>"
              using \<theta> assms(1) by fastforce
            moreover have "\<guillemotleft>\<theta>' \<cdot> (\<phi> \<star> w') : f \<star> w' \<Rightarrow> u\<guillemotright>"
              using \<theta>' assms(1) by fastforce
            moreover have "composite_cell w (\<theta> \<cdot> (\<phi> \<star> w)) = composite_cell w' (\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> \<beta>"
            proof -
              have "composite_cell w (\<theta> \<cdot> (\<phi> \<star> w)) =
                    (r \<star> \<theta>) \<cdot> ((r \<star> \<phi> \<star> w) \<cdot> \<a>[r, f, w]) \<cdot> (\<rho> \<star> w)"
                using assms(2) \<phi>_w \<theta> whisker_left comp_assoc by auto
              also have "... = (r \<star> \<theta>) \<cdot> \<a>[r, f', w] \<cdot> ((r \<star> \<phi>) \<star> w) \<cdot> (\<rho> \<star> w)"
                using assms(1) assoc_naturality [of r \<phi> w] comp_assoc
                by (metis \<phi>_w T'.tab_simps(1) base_simps(3) base_simps(4) hseq_char
                    in_homE seqE uw\<theta>.w_simps(5) uw\<theta>.w_simps(6))
              also have "... = T'.composite_cell w \<theta>"
                using assms(2) w whisker_right [of w] by simp
              also have "... = T'.composite_cell w' \<theta>' \<cdot> \<beta>"
                using eq by simp
              also have "... = (r \<star> \<theta>') \<cdot> (\<a>[r, f', w'] \<cdot> ((r \<star> \<phi>) \<star> w')) \<cdot> (\<rho> \<star> w') \<cdot> \<beta>"
                using assms(2) w' whisker_right [of w'] comp_assoc by simp
              also have "... = ((r \<star> \<theta>') \<cdot> (r \<star> \<phi> \<star> w')) \<cdot> \<a>[r, f, w'] \<cdot> (\<rho> \<star> w') \<cdot> \<beta>"
                using assms(1) assoc_naturality [of r \<phi> w'] comp_assoc
                by (metis \<phi>_w' T'.tab_simps(1) base_simps(3) base_simps(4) hseqE in_homE seqE
                    uw'\<theta>'.w_simps(5) uw'\<theta>'.w_simps(6))
              also have "... = composite_cell w' (\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> \<beta>"
                using assms(2) whisker_left [of r] \<open>\<guillemotleft>\<theta>' \<cdot> (\<phi> \<star> w') : f \<star> w' \<Rightarrow> u\<guillemotright>\<close> comp_assoc
                by auto
              finally show ?thesis by simp
            qed
            ultimately have *: "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and>
                                     \<theta> \<cdot> (\<phi> \<star> w) = (\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> (f \<star> \<gamma>)"
              using w w' \<beta> T2 by auto
            show ?thesis
            proof -
              have **: "\<And>\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<Longrightarrow> \<theta>' \<cdot> (\<phi> \<star> w') \<cdot> (f \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w) = \<theta>' \<cdot> (f' \<star> \<gamma>)"
              proof -
                fix \<gamma>
                assume \<gamma>: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright>"
                have "\<theta>' \<cdot> (\<phi> \<star> w') \<cdot> (f \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w) = \<theta>' \<cdot> (\<phi> \<star> w') \<cdot> (f \<cdot> inv \<phi> \<star> \<gamma> \<cdot> w)"
                  using \<gamma> assms(1-2) interchange
                  by (metis arr_inv cod_inv in_homE leg0_simps(2) leg0_simps(4) uw\<theta>.w_in_hom(2)
                      seqI)
                also have "... = \<theta>' \<cdot> (\<phi> \<cdot> f \<cdot> inv \<phi> \<star> w' \<cdot> \<gamma> \<cdot> w)"
                  using assms(1-2) interchange
                  by (metis \<gamma> arr_inv cod_inv comp_arr_dom comp_cod_arr in_homE seqI)
                also have "... = \<theta>' \<cdot> (f' \<star> \<gamma>)"
                proof -
                  have "\<phi> \<cdot> f \<cdot> inv \<phi> = f'"
                    using assms(1-2) comp_cod_arr comp_arr_inv' by auto
                  moreover have "w' \<cdot> \<gamma> \<cdot> w = \<gamma>"
                    using \<gamma> comp_arr_dom comp_cod_arr by auto
                  ultimately show ?thesis by simp
                qed
                finally show "\<theta>' \<cdot> (\<phi> \<star> w') \<cdot> (f \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w) = \<theta>' \<cdot> (f' \<star> \<gamma>)" by simp
              qed
              obtain \<gamma> where \<gamma>: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and>
                                 \<theta> \<cdot> (\<phi> \<star> w) = (\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> (f \<star> \<gamma>)"
                using * by blast
              have "\<theta> = \<theta>' \<cdot> (\<phi> \<star> w') \<cdot> (f \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w)"
              proof -
                have "seq (\<theta>' \<cdot> (\<phi> \<star> w')) (f \<star> \<gamma>)"
                  using assms(2) \<phi>_w \<phi>_w' \<gamma> \<beta> \<theta>
                  apply (intro seqI)
                          apply auto
                  by (metis seqE seqI')
                thus ?thesis
                  using assms \<phi>_w \<gamma> comp_assoc invert_side_of_triangle(2) iso_hcomp
                  by (metis hcomp_in_vhomE ide_is_iso inv_hcomp inv_ide w)
              qed
              hence "\<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>)"
                using \<gamma> ** by simp
              hence "\<exists>\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>)"
                using \<gamma> by auto
              moreover have "\<And>\<gamma> \<gamma>'. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>) \<and>
                                    \<guillemotleft>\<gamma>' : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma>' \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>')
                                        \<Longrightarrow> \<gamma> = \<gamma>'"
              proof -
                fix \<gamma> \<gamma>'
                assume A: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>) \<and>
                           \<guillemotleft>\<gamma>' : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma>' \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>')"
                have "\<theta> \<cdot> (\<phi> \<star> w) = (\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> (f \<star> \<gamma>)"
                proof -
                  have "\<theta> = ((\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> (f \<star> \<gamma>)) \<cdot> (inv \<phi> \<star> w)"
                    using A ** comp_assoc by simp
                  thus ?thesis
                    using assms(1-2) A iso_inv_iso
                    by (metis comp_arr_dom comp_cod_arr in_homE comp_assoc interchange)
                qed
                moreover have "\<theta> \<cdot> (\<phi> \<star> w) = (\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> (f \<star> \<gamma>')"
                proof -
                  have "\<theta> = ((\<theta>' \<cdot> (\<phi> \<star> w')) \<cdot> (f \<star> \<gamma>')) \<cdot> (inv \<phi> \<star> w)"
                    using A ** comp_assoc by auto
                  thus ?thesis
                    using assms(1-2) A iso_inv_iso
                    by (metis comp_arr_dom comp_cod_arr in_homE comp_assoc interchange)
                qed
               ultimately show "\<gamma> = \<gamma>'"
                  using A * by blast
              qed
              ultimately show "\<exists>!\<gamma>.  \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f' \<star> \<gamma>)"
                by metis
            qed
          qed
        qed
      qed
    qed

    text \<open>
      Similarly, tabulations are preserved under composition of an isomorphism with
      the ``output leg''.
    \<close>

    lemma preserved_by_output_iso:
    assumes "\<guillemotleft>\<phi> : g' \<Rightarrow> g\<guillemotright>" and "iso \<phi>"
    shows "tabulation V H \<a> \<i> src trg r (\<rho> \<cdot> \<phi>) f g'"
    proof -
      have \<tau>\<phi>: "\<guillemotleft>\<rho> \<cdot> \<phi> : g' \<Rightarrow> r \<star> f\<guillemotright>"
        using assms by auto
      interpret T': tabulation_data V H \<a> \<i> src trg r \<open>\<rho> \<cdot> \<phi>\<close> f g'
        using assms(2) \<tau>\<phi> by (unfold_locales, auto)
      have \<phi>_in_hhom: "\<guillemotleft>\<phi> : src f \<rightarrow> trg r\<guillemotright>"
        using assms src_cod [of \<phi>] trg_cod [of \<phi>]
        by (elim in_homE, simp)
      show ?thesis
      proof
        fix u \<omega>
        assume u: "ide u" and \<omega>: "\<guillemotleft>\<omega> : dom \<omega> \<Rightarrow> r \<star> u\<guillemotright>"
        show "\<exists>w \<theta> \<nu>'. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu>' : dom \<omega> \<Rightarrow> g' \<star> w\<guillemotright> \<and> iso \<nu>' \<and>
                       T'.composite_cell w \<theta> \<cdot> \<nu>' = \<omega>"
        proof -
          obtain w \<theta> \<nu> where w\<theta>\<nu>: "ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega> \<Rightarrow> g \<star> w\<guillemotright> \<and>
                                   iso \<nu> \<and> composite_cell w \<theta> \<cdot> \<nu> = \<omega>"
            using u \<omega> T1 [of u \<omega>] by auto
          interpret uw\<theta>\<omega>\<nu>: uw\<theta>\<omega>\<nu> V H \<a> \<i> src trg r \<rho> f g u w \<theta> \<omega> \<nu>
            using w\<theta>\<nu> comp_assoc by (unfold_locales, auto)
          let ?\<nu>' = "(inv \<phi> \<star> w) \<cdot> \<nu>"
          have \<nu>': "\<guillemotleft>?\<nu>' : dom \<omega> \<Rightarrow> g' \<star> w\<guillemotright>"
            using assms \<phi>_in_hhom uw\<theta>\<omega>\<nu>.\<nu>_in_hom
            by (intro comp_in_homI, auto)
          moreover have "iso ?\<nu>'"
            using assms \<nu>' w\<theta>\<nu> \<phi>_in_hhom iso_inv_iso
            by (intro iso_hcomp isos_compose, auto)
          moreover have "T'.composite_cell w \<theta> \<cdot> ?\<nu>' = \<omega>"
          proof -
            have "composite_cell w \<theta> \<cdot> ((\<phi> \<star> w) \<cdot> ?\<nu>') = \<omega>"
            proof -
              have "(\<phi> \<star> w) \<cdot> ?\<nu>' = \<nu>"
                using assms \<nu>' \<phi>_in_hhom whisker_right comp_cod_arr comp_assoc
                by (metis comp_arr_inv' in_homE leg1_simps(2) uw\<theta>\<omega>\<nu>.uw\<theta>\<omega>\<nu>)
              thus ?thesis
                using w\<theta>\<nu> by simp
            qed
            moreover have "(\<rho> \<cdot> \<phi> \<star> w) \<cdot> ?\<nu>' = (\<rho> \<star> w) \<cdot> ((\<phi> \<star> w) \<cdot> ?\<nu>')"
              using assms \<phi>_in_hhom whisker_right comp_assoc by simp
            ultimately show ?thesis
              using comp_assoc by simp
          qed
          ultimately show ?thesis
            using w\<theta>\<nu> by blast
        qed
        next
        fix u w w' \<theta> \<theta>' \<beta>'
        assume w: "ide w" and w': "ide w'"
        and \<theta>: "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>" and \<theta>': "\<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>"
        and \<beta>': "\<guillemotleft>\<beta>' : g' \<star> w \<Rightarrow> g' \<star> w'\<guillemotright>"
        and eq': "T'.composite_cell w \<theta> = T'.composite_cell w' \<theta>' \<cdot> \<beta>'"
        interpret uw\<theta>w'\<theta>'\<beta>: uw\<theta>w'\<theta>'\<beta> V H \<a> \<i> src trg r \<open>\<rho> \<cdot> \<phi>\<close> f g' u w \<theta> w' \<theta>' \<beta>'
          using assms w w' \<theta> \<theta>' \<beta>' eq' comp_assoc by (unfold_locales, auto)
        let ?\<beta> = "(\<phi> \<star> w') \<cdot> \<beta>' \<cdot> (inv \<phi> \<star> w)"
        have \<beta>: "\<guillemotleft>?\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>"
          using assms \<phi>_in_hhom \<beta>'
          by (intro comp_in_homI hcomp_in_vhom, auto)
        have eq: "composite_cell w \<theta> = composite_cell w' \<theta>' \<cdot> ((\<phi> \<star> w') \<cdot> \<beta>' \<cdot> (inv \<phi> \<star> w))"
        proof -
          have "composite_cell w \<theta> = (r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> ((\<rho> \<star> w) \<cdot> (\<phi> \<star> w)) \<cdot> (inv \<phi> \<star> w)"
          proof -
            have "\<rho> \<star> w = (\<rho> \<star> w) \<cdot> (\<phi> \<star> w) \<cdot> (inv \<phi> \<star> w)"
              using assms w \<phi>_in_hhom whisker_right comp_arr_dom comp_arr_inv'
              by (metis tab_simps(1) tab_simps(4) in_homE leg1_simps(2))
            thus ?thesis
              using comp_assoc by simp
          qed
          also have "... = T'.composite_cell w \<theta> \<cdot> (inv \<phi> \<star> w)"
            using assms \<phi>_in_hhom whisker_right comp_assoc by simp
          also have "... = T'.composite_cell w' \<theta>' \<cdot> (\<beta>' \<cdot> (inv \<phi> \<star> w))"
            using eq' comp_assoc by simp
          also have "... = composite_cell w' \<theta>' \<cdot> ((\<phi> \<star> w') \<cdot> \<beta>' \<cdot> (inv \<phi> \<star> w))"
            using assms \<phi>_in_hhom whisker_right comp_assoc by simp
          finally show ?thesis by simp
        qed
        show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
        proof -
          obtain \<gamma> where \<gamma>: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> ?\<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
            using assms w w' \<theta> \<theta>' \<beta> eq \<phi>_in_hhom T2 [of w w' \<theta> u \<theta>' ?\<beta>] by auto
          have "\<beta>' = g' \<star> \<gamma>"
          proof -
            have "g \<star> \<gamma> = (\<phi> \<star> w') \<cdot> \<beta>' \<cdot> (inv \<phi> \<star> w)"
              using \<gamma> by simp
            hence "(inv \<phi> \<star> w') \<cdot> (g \<star> \<gamma>) = \<beta>' \<cdot> (inv \<phi> \<star> w)"
              using assms w' \<beta> \<phi>_in_hhom invert_side_of_triangle arrI iso_hcomp
                    hseqE ide_is_iso inv_hcomp inv_ide seqE
              by metis
            hence "\<beta>' = (inv \<phi> \<star> w') \<cdot> (g \<star> \<gamma>) \<cdot> (\<phi> \<star> w)"
              using assms w \<beta> \<phi>_in_hhom invert_side_of_triangle comp_assoc seqE
              by (metis comp_arr_dom in_homE local.uw\<theta>w'\<theta>'\<beta>.\<beta>_simps(4) whisker_right)
            also have "... = (inv \<phi> \<star> w') \<cdot> (\<phi> \<star> \<gamma>)"
              using assms \<phi>_in_hhom \<gamma> interchange comp_arr_dom comp_cod_arr
              by (metis in_homE)
            also have "... = g' \<star> \<gamma>"
              using assms \<phi>_in_hhom \<gamma> interchange comp_inv_arr inv_is_inverse comp_cod_arr
              by (metis arr_dom calculation in_homE)
            finally show ?thesis by simp
          qed
          hence "\<exists>\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
            using \<beta> \<gamma> by auto
          moreover have "\<And>\<gamma> \<gamma>'. \<lbrakk> \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>);
                                  \<guillemotleft>\<gamma>' : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma>' \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>') \<rbrakk> \<Longrightarrow> \<gamma> = \<gamma>'"
          proof -
            have *: "\<And>\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<Longrightarrow> (\<phi> \<star> w') \<cdot> (g' \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w) = g \<star> \<gamma>"
            proof -
              fix \<gamma>
              assume \<gamma>: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright>"
              have "(\<phi> \<star> w') \<cdot> (g' \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w) = (\<phi> \<star> w') \<cdot> (inv \<phi> \<star> \<gamma>)"
                using assms \<phi>_in_hhom \<gamma> interchange comp_arr_dom comp_cod_arr
                by (metis arr_dom comp_inv_arr' in_homE invert_side_of_triangle(2))
              also have "... = g \<star> \<gamma>"
                using assms \<phi>_in_hhom interchange comp_arr_inv inv_is_inverse comp_cod_arr
                by (metis \<gamma> comp_arr_inv' in_homE leg1_simps(2))
              finally show "(\<phi> \<star> w') \<cdot> (g' \<star> \<gamma>) \<cdot> (inv \<phi> \<star> w) = g \<star> \<gamma>" by blast
            qed
            fix \<gamma> \<gamma>'
            assume \<gamma>: "\<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
            and \<gamma>': "\<guillemotleft>\<gamma>' : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma>' \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>')"
            show "\<gamma> = \<gamma>'"
              using w w' \<theta> \<theta>' \<beta> \<gamma> \<gamma>' eq * T2 by metis
          qed
          ultimately show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta>' = g' \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)" by blast
        qed
      qed
    qed

    text \<open>
      Finally, tabulations are preserved by composition with an isomorphism on the ``base''.
    \<close>

    lemma is_preserved_by_base_iso:
    assumes "\<guillemotleft>\<phi> : r \<Rightarrow> r'\<guillemotright>" and "iso \<phi>"
    shows "tabulation V H \<a> \<i> src trg r' ((\<phi> \<star> f) \<cdot> \<rho>) f g"
    proof -
      have \<phi>f: "\<guillemotleft>\<phi> \<star> f : r \<star> f \<Rightarrow> r' \<star> f\<guillemotright>"
        using assms ide_leg0 by auto
      interpret T: tabulation_data V H \<a> \<i> src trg r' \<open>(\<phi> \<star> f) \<cdot> \<rho>\<close> f
      proof
        show ide_r': "ide r'" using assms by auto
        show "ide f" using ide_leg0 by auto
        show "\<guillemotleft>(\<phi> \<star> f) \<cdot> \<rho> : g \<Rightarrow> r' \<star> f\<guillemotright>"
          using tab_in_hom \<phi>f by force
      qed
      show ?thesis
      proof
        have *: "\<And>u v w \<theta> \<nu>. \<lbrakk> ide u; ide v; ide w; \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<nu> : v \<Rightarrow> g \<star> w\<guillemotright> \<rbrakk> \<Longrightarrow>
                                ((\<phi> \<star> u) \<cdot> (r \<star> \<theta>)) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu> =
                                T.composite_cell w \<theta> \<cdot> \<nu>"
        proof -
          fix u v w \<theta> \<nu>
          assume u: "ide u" and v: "ide v" and w: "ide w"
          and \<theta>: "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>" and \<nu>: "\<guillemotleft>\<nu> : v \<Rightarrow> g \<star> w\<guillemotright>"
          have fw: "hseq f w"
            using \<theta> ide_dom [of \<theta>] by fastforce
          have r\<theta>: "hseq r \<theta>"
            using \<theta> ide_base ide_dom [of \<theta>] trg_dom [of \<theta>]
            using arrI fw vconn_implies_hpar(2) by auto
          have "((\<phi> \<star> u) \<cdot> (r \<star> \<theta>)) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu> =
                ((r' \<star> \<theta>) \<cdot> (\<phi> \<star> f \<star> w)) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu>"
            using assms u w ide_base ide_leg0 \<theta> interchange comp_arr_dom comp_cod_arr
            by (metis r\<theta> hseq_char in_homE)
          also have "... = (r' \<star> \<theta>) \<cdot> ((\<phi> \<star> f \<star> w) \<cdot> \<a>[r, f, w]) \<cdot> (\<rho> \<star> w) \<cdot> \<nu>"
            using comp_assoc by simp
          also have "... = (r' \<star> \<theta>) \<cdot> \<a>[r', f, w] \<cdot> (((\<phi> \<star> f) \<star> w) \<cdot> (\<rho> \<star> w)) \<cdot> \<nu>"
          proof -
            have "(\<phi> \<star> f \<star> w) \<cdot> \<a>[r, f, w] = \<a>[r', f, w] \<cdot> ((\<phi> \<star> f) \<star> w)"
              using assms ide_leg0 w assoc_naturality [of \<phi> f w] fw by fastforce
            thus ?thesis
              using comp_assoc by simp
          qed
          also have "... = T.composite_cell w \<theta> \<cdot> \<nu>"
            using assms ide_leg0 whisker_right fw T.tab_in_hom arrI w comp_assoc by auto
          finally show "((\<phi> \<star> u) \<cdot> (r \<star> \<theta>)) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu> = T.composite_cell w \<theta> \<cdot> \<nu>"
            by simp
        qed
        show "\<And>u \<omega>'. \<lbrakk> ide u; \<guillemotleft>\<omega>' : dom \<omega>' \<Rightarrow> r' \<star> u\<guillemotright> \<rbrakk> \<Longrightarrow>
                 \<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : dom \<omega>' \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                         T.composite_cell w \<theta> \<cdot> \<nu> = \<omega>'"
        proof -
          fix u v \<omega>'
          assume u: "ide u" and \<omega>': "\<guillemotleft>\<omega>' : v \<Rightarrow> r' \<star> u\<guillemotright>"
          have \<omega>: "\<guillemotleft>(inv \<phi> \<star> u) \<cdot> \<omega>' : v \<Rightarrow> r \<star> u\<guillemotright>"
          proof
            show "\<guillemotleft>\<omega>' : v \<Rightarrow> r' \<star> u\<guillemotright>" by fact
            show "\<guillemotleft>inv \<phi> \<star> u : r' \<star> u \<Rightarrow> r \<star> u\<guillemotright>"
            proof -
              have "ide (r' \<star> u)"
                using \<omega>' ide_cod by fastforce
              hence "hseq r' u" by simp
              thus ?thesis
                using assms u by auto
            qed
          qed
          have \<phi>u: "hseq \<phi> u"
            using assms \<omega> hseqI
            by (metis arrI ide_is_iso iso_hcomp iso_is_arr seqE seq_if_composable
                src_inv u)
          obtain w \<theta> \<nu> where w\<theta>\<nu>: "ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : v \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                                   composite_cell w \<theta> \<cdot> \<nu> = (inv \<phi> \<star> u) \<cdot> \<omega>'"
            using u \<omega> T1 [of u "(inv \<phi> \<star> u) \<cdot> \<omega>'"] \<phi>f in_homE seqI' by auto

          interpret uw\<theta>\<omega>\<nu> V H \<a> \<i> src trg r \<rho> f g u w \<theta> \<open>(inv \<phi> \<star> u) \<cdot> \<omega>'\<close> \<nu>
            using w\<theta>\<nu> \<omega> comp_assoc by (unfold_locales, auto)

          have "ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : v \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                T.composite_cell w \<theta> \<cdot> \<nu> = \<omega>'"
          proof -
            have "\<omega>' = ((\<phi> \<star> u) \<cdot> (r \<star> \<theta>)) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu>"
            proof -
              have "seq (r \<star> \<theta>) (\<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> \<nu>)" by fastforce
              moreover have "iso (inv \<phi> \<star> u)"
                using assms u iso_hcomp iso_inv_iso \<phi>u by auto
              moreover have "inv (inv \<phi> \<star> u) = \<phi> \<star> u"
                using assms u iso_hcomp iso_inv_iso \<phi>u by auto
              ultimately show ?thesis
                using invert_side_of_triangle(1) w\<theta>\<nu> comp_assoc by metis
            qed
            also have "... = T.composite_cell w \<theta> \<cdot> \<nu>"
              using u w\<theta>\<nu> * [of u v w \<theta> \<nu>] by force
            finally have "\<omega>' = T.composite_cell w \<theta> \<cdot> \<nu>" by simp
            thus ?thesis
              using w\<theta>\<nu> by simp
          qed
          thus "\<exists>w \<theta> \<nu>. ide w \<and> \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright> \<and> \<guillemotleft>\<nu> : v \<Rightarrow> g \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                        T.composite_cell w \<theta> \<cdot> \<nu> = \<omega>'"
            by blast
        qed
        show "\<And>u w w' \<theta> \<theta>' \<beta>. \<lbrakk> ide w; ide w'; \<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>; \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>;
                                 \<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>; 
                                 T.composite_cell w \<theta> = T.composite_cell w' \<theta>' \<cdot> \<beta> \<rbrakk> \<Longrightarrow>
                 \<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
        proof -
          fix u w w' \<theta> \<theta>' \<beta>
          assume w: "ide w" and w': "ide w'"
          and \<theta>: "\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> u\<guillemotright>" and \<theta>': "\<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> u\<guillemotright>"
          and \<beta>: "\<guillemotleft>\<beta> : g \<star> w \<Rightarrow> g \<star> w'\<guillemotright>"
          and eq': "T.composite_cell w \<theta> = T.composite_cell w' \<theta>' \<cdot> \<beta>"
          interpret T: uw\<theta>w'\<theta>'\<beta> V H \<a> \<i> src trg r' \<open>(\<phi> \<star> f) \<cdot> \<rho>\<close> f g u w \<theta> w' \<theta>' \<beta>
            using w w' \<theta> \<theta>' \<beta> eq' comp_assoc
            by (unfold_locales, auto)
          have eq: "composite_cell w \<theta> = composite_cell w' \<theta>' \<cdot> \<beta>"
          proof -
            have "(\<phi> \<star> u) \<cdot> composite_cell w \<theta> = (\<phi> \<star> u) \<cdot> composite_cell w' \<theta>' \<cdot> \<beta>"
            proof -
              have "(\<phi> \<star> u) \<cdot> composite_cell w \<theta> =
                    ((\<phi> \<star> u) \<cdot> (r \<star> \<theta>)) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w) \<cdot> (g \<star> w)"
              proof -
                have "\<guillemotleft>\<rho> \<star> w : g \<star> w \<Rightarrow> (r \<star> f) \<star> w\<guillemotright>"
                  using w by auto
                thus ?thesis
                  using comp_arr_dom comp_assoc by auto
              qed
              also have "... = T.composite_cell w \<theta> \<cdot> (g \<star> w)"
                using * [of u "g \<star> w" w \<theta> "g \<star> w"] by fastforce
              also have "... = T.composite_cell w \<theta>"
              proof -
                have "\<guillemotleft>(\<phi> \<star> f) \<cdot> \<rho> \<star> w : g \<star> w \<Rightarrow> (r' \<star> f) \<star> w\<guillemotright>"
                  using assms by fastforce
                thus ?thesis
                  using comp_arr_dom comp_assoc by auto
              qed
              also have "... = T.composite_cell w' \<theta>' \<cdot> \<beta>"
                using eq' by simp
              also have "... = ((\<phi> \<star> u) \<cdot> (r \<star> \<theta>')) \<cdot> \<a>[r, f, w'] \<cdot> (\<rho> \<star> w') \<cdot> \<beta>"
                using * [of u "g \<star> w" w' \<theta>' \<beta>] by fastforce
              finally show ?thesis
                using comp_assoc by simp
            qed
            moreover have "iso (\<phi> \<star> u)"
              using assms by auto
            moreover have "seq (\<phi> \<star> u) ((r \<star> \<theta>) \<cdot> \<a>[r, f, w] \<cdot> (\<rho> \<star> w))"
            proof -
              have "\<guillemotleft>\<phi> \<star> u : r \<star> u \<Rightarrow> r' \<star> u\<guillemotright>"
                using assms by (intro hcomp_in_vhom, auto)
              thus ?thesis
                using composite_cell_in_hom [of w u \<theta>] by auto
            qed
            moreover have "seq (\<phi> \<star> u) (composite_cell w' \<theta>' \<cdot> \<beta>)"
              using assms ide_leg0 w w' \<theta> \<theta>' \<beta> calculation(1) calculation(3) by auto
            ultimately show ?thesis
              using monoE section_is_mono iso_is_section by metis
          qed
          show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow> w'\<guillemotright> \<and> \<beta> = g \<star> \<gamma> \<and> \<theta> = \<theta>' \<cdot> (f \<star> \<gamma>)"
            using w w' \<theta> \<theta>' \<beta> eq T2 by simp
        qed
      qed
    qed

  end

  subsection "Canonical Tabulations"

  text \<open>
    If the 1-cell \<open>g \<star> f\<^sup>*\<close> has any tabulation \<open>(f, \<rho>, g)\<close>, then it has the canonical
    tabulation obtained as the adjoint transpose of (the identity on) \<open>g \<star> f\<^sup>*\<close>.
  \<close>

  context map_in_bicategory
  begin

    lemma canonical_tabulation:
    assumes "ide g" and "src f = src g"
    and "\<exists>\<rho>. tabulation V H \<a> \<i> src trg (g \<star> f\<^sup>*) \<rho> f g"
    shows "tabulation V H \<a> \<i> src trg (g \<star> f\<^sup>*) (trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)) f g"
    proof -
      have 1: "ide (g \<star> f\<^sup>*)"
        using assms(1-2) ide_right antipar by simp
      obtain \<rho> where \<rho>: "tabulation V H \<a> \<i> src trg (g \<star> f\<^sup>*) \<rho> f g"
        using assms(3) by auto
      interpret \<rho>: tabulation V H \<a> \<i> src trg \<open>g \<star> f\<^sup>*\<close> \<rho> f g
        using \<rho> by auto
      let ?\<psi> = "trnr\<^sub>\<epsilon> (g \<star> f\<^sup>*) \<rho>"
      have 3: "\<guillemotleft>?\<psi> : g \<star> f\<^sup>* \<Rightarrow> g \<star> f\<^sup>*\<guillemotright> \<and> iso ?\<psi>"
        using \<rho>.yields_isomorphic_representation by blast
      hence "tabulation (\<cdot>) (\<star>) \<a> \<i> src trg (g \<star> f\<^sup>*) ((inv ?\<psi> \<star> f) \<cdot> \<rho>) f g"
        using \<rho>.is_preserved_by_base_iso [of "inv ?\<psi>" "g \<star> f\<^sup>*"] iso_inv_iso by simp
      moreover have "(inv ?\<psi> \<star> f) \<cdot> \<rho> = trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)"
      proof -
        have "(inv ?\<psi> \<star> f) \<cdot> \<rho> = ((inv ?\<psi> \<star> f) \<cdot> (?\<psi> \<star> f)) \<cdot> trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)"
          using \<rho>.\<rho>_in_terms_of_rep comp_assoc by simp
        also have "... = ((g \<star> f\<^sup>*) \<star> f) \<cdot> trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)"
        proof -
          have "src (inv ?\<psi>) = trg f"
            using 3 antipar
            by (metis \<rho>.leg0_simps(3) \<rho>.base_in_hom(2) seqI' src_inv vseq_implies_hpar(1))
          hence "(inv ?\<psi> \<star> f) \<cdot> (?\<psi> \<star> f) = (g \<star> f\<^sup>*) \<star> f"
            using 3 whisker_right [of f "inv ?\<psi>" ?\<psi>] inv_is_inverse comp_inv_arr by auto
          thus ?thesis
            using comp_cod_arr by simp
        qed
        also have "... = trnr\<^sub>\<eta> g (g \<star> f\<^sup>*)"
        proof -
          have "src (g \<star> f\<^sup>*) = trg f" by simp
          moreover have "ide g" by simp
          ultimately have "\<guillemotleft>trnr\<^sub>\<eta> g (g \<star> f\<^sup>*) : g \<Rightarrow> (g \<star> f\<^sup>*) \<star> f\<guillemotright>"
            using 1 adjoint_transpose_right(1) ide_in_hom antipar by blast
          thus ?thesis
            using comp_cod_arr by blast
        qed
        finally show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed

  end

  subsection "Uniqueness of Tabulations"

  text \<open>
    We now intend to show that a tabulation of \<open>r\<close> is ``unique up to equivalence'',
    which is a property that any proper bicategorical limit should have.
    What do we mean by this, exactly?
    If we have two tabulations \<open>(f, \<rho>)\<close> and \<open>(f', \<rho>')\<close> of the same 1-cell \<open>r\<close>, then this
    induces \<open>\<guillemotleft>w : src f' \<rightarrow> src f\<guillemotright>\<close>, \<open>\<guillemotleft>w' : src f \<rightarrow> src f'\<guillemotright>\<close>, \<open>\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> f'\<guillemotright>\<close>, and
    \<open>\<guillemotleft>\<theta> : f \<star> w \<Rightarrow> f'\<guillemotright>\<close>, such that \<open>\<rho>'\<close> is recovered up to isomorphism \<open>\<guillemotleft>\<nu> : g' \<Rightarrow> g \<star> w\<guillemotright>\<close>
    from \<open>(w, \<theta>)\<close> by composition with \<open>\<rho>\<close> and \<open>\<rho>\<close> is recovered up to isomorphism
    \<open>\<guillemotleft>\<nu>' : g \<Rightarrow> g' \<star> w'\<guillemotright>\<close> from \<open>(w', \<theta>')\<close> by composition with \<open>\<rho>'\<close>.
    This means that we obtain isomorphisms \<open>\<guillemotleft>(\<nu>' \<star> w') \<cdot> \<nu> : g' \<Rightarrow> g' \<star> w' \<star> w\<guillemotright>\<close> and
    \<open>\<guillemotleft>(\<nu> \<star> w') \<cdot> \<nu>' : g \<Rightarrow> g \<star> w \<star> w'\<guillemotright>\<close>.
    These isomorphisms then induce, via \<open>T2\<close>, unique 2-cells from \<open>src f'\<close> to \<open>w' \<star> w\<close>
    and from \<open>src f\<close> to \<open>w \<star> w'\<close>, which must be isomorphisms, thus showing \<open>w\<close> and \<open>w'\<close> are
    equivalence maps.
  \<close>

  context tabulation
  begin

    text \<open>
      We will need the following technical lemma.
    \<close>

    lemma apex_equivalence_lemma:
    assumes "\<guillemotleft>\<rho>' : g' \<Rightarrow> r \<star> f'\<guillemotright>"
    and "ide w \<and> \<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> f\<guillemotright> \<and> \<guillemotleft>\<nu> : g \<Rightarrow> g' \<star> w\<guillemotright> \<and> iso \<nu> \<and>
         (r \<star> \<theta>) \<cdot> \<a>[r, f', w] \<cdot> (\<rho>' \<star> w) \<cdot> \<nu> = \<rho>"
    and "ide w' \<and> \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> f'\<guillemotright> \<and> \<guillemotleft>\<nu>' : g' \<Rightarrow> g \<star> w'\<guillemotright> \<and> iso \<nu>' \<and>
         (r \<star> \<theta>') \<cdot> \<a>[r, f, w'] \<cdot> (\<rho> \<star> w') \<cdot> \<nu>' = \<rho>'"
    shows "\<exists>\<phi>. \<guillemotleft>\<phi> : src f \<Rightarrow> w' \<star> w\<guillemotright> \<and> iso \<phi>"
    proof -
      interpret T': uw\<theta>\<omega>\<nu> V H \<a> \<i> src trg r \<rho> f g f' w' \<theta>' \<rho>' \<nu>'
        using assms(1,3) apply unfold_locales by auto
      interpret T: tabulation_data V H \<a> \<i> src trg r \<rho>' f' g'
        using assms(1,2) apply unfold_locales by auto
      interpret T: uw\<theta>\<omega>\<nu> V H \<a> \<i> src trg r \<rho>' f' g' f w \<theta> \<rho> \<nu>
        using assms(1,2) apply unfold_locales by auto

      (* These next simps are very important. *)
      have dom_\<nu> [simp]: "dom \<nu> = dom \<rho>"
        using assms(2) by auto
      have dom_\<nu>' [simp]: "dom \<nu>' = dom \<rho>'"
        using assms(3) by auto

      let ?\<nu>'\<nu> = "\<a>[dom \<rho>, w', w] \<cdot> (\<nu>' \<star> w) \<cdot> \<nu>"
      have \<nu>'\<nu>: "\<guillemotleft>?\<nu>'\<nu> : dom \<rho> \<Rightarrow> dom \<rho> \<star> w' \<star> w\<guillemotright>"
        by fastforce
      have "\<guillemotleft>\<nu> : src \<rho> \<rightarrow> trg r\<guillemotright>" by simp
      let ?\<theta>\<theta>' = "\<theta> \<cdot> (\<theta>' \<star> w) \<cdot> \<a>\<^sup>-\<^sup>1[f, w', w]"
      have \<theta>\<theta>': "\<guillemotleft>?\<theta>\<theta>' : f \<star> w' \<star> w \<Rightarrow> f\<guillemotright>"
        by fastforce
      have iso_\<nu>'\<nu>_r: "iso (?\<nu>'\<nu> \<cdot> \<r>[g])"
        using iso_runit \<nu>'\<nu>
        apply (intro isos_compose) by auto

      have eq: "composite_cell (src f) \<r>[f] = composite_cell (w' \<star> w) ?\<theta>\<theta>' \<cdot> (?\<nu>'\<nu> \<cdot> \<r>[g])"
      proof -
        have "composite_cell (w' \<star> w) ?\<theta>\<theta>' \<cdot> (?\<nu>'\<nu> \<cdot> \<r>[g]) =
              ((r \<star> \<theta>) \<cdot> (r \<star> \<theta>' \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, w', w])) \<cdot>
                \<a>[r, f, w' \<star> w] \<cdot> ((\<rho> \<star> w' \<star> w) \<cdot> \<a>[g, w', w]) \<cdot> (\<nu>' \<star> w) \<cdot> \<nu> \<cdot> \<r>[g]"
          using whisker_left comp_assoc by simp
        also have "... = ((r \<star> \<theta>) \<cdot> (r \<star> \<theta>' \<star> w) \<cdot> (r \<star> \<a>\<^sup>-\<^sup>1[f, w', w])) \<cdot>
                           \<a>[r, f, w' \<star> w] \<cdot> (\<a>[r \<star> f, w', w] \<cdot>
                           ((\<rho> \<star> w') \<star> w)) \<cdot> (\<nu>' \<star> w) \<cdot> \<nu> \<cdot> \<r>[g]"
          using assoc_naturality [of \<rho> w' w] by simp
        also have "... = (r \<star> \<theta>) \<cdot> (r \<star> \<theta>' \<star> w) \<cdot>
                           ((r \<star> \<a>\<^sup>-\<^sup>1[f, w', w]) \<cdot> \<a>[r, f, w' \<star> w] \<cdot> \<a>[r \<star> f, w', w]) \<cdot>
                           ((\<rho> \<star> w') \<star> w) \<cdot> (\<nu>' \<star> w) \<cdot> \<nu> \<cdot> \<r>[g]"
          using comp_assoc by simp
        also have "... = (r \<star> \<theta>) \<cdot> ((r \<star> \<theta>' \<star> w) \<cdot> \<a>[r, f \<star> w', w]) \<cdot>
                           (\<a>[r, f, w'] \<star> w) \<cdot>
                           ((\<rho> \<star> w') \<star> w) \<cdot> (\<nu>' \<star> w) \<cdot> \<nu> \<cdot> \<r>[g]"
        proof -
          have "seq \<a>[r, f, w' \<star> w] \<a>[r \<star> f, w', w]" by simp
          moreover have "inv (r \<star> \<a>[f, w', w]) = r \<star> \<a>\<^sup>-\<^sup>1[f, w', w]"
            by simp
          moreover have "(r \<star> \<a>[f, w', w]) \<cdot> \<a>[r, f \<star> w', w] \<cdot> (\<a>[r, f, w'] \<star> w) =
                \<a>[r, f, w' \<star> w] \<cdot> \<a>[r \<star> f, w', w]"
            using pentagon by simp
          ultimately have "(r \<star> \<a>\<^sup>-\<^sup>1[f, w', w]) \<cdot> \<a>[r, f, w' \<star> w] \<cdot> \<a>[r \<star> f, w', w] =
                           \<a>[r, f \<star> w', w] \<cdot> (\<a>[r, f, w'] \<star> w)"
            using iso_assoc [of f w' w] iso_hcomp
                  invert_side_of_triangle(1)
                    [of "\<a>[r, f, w' \<star> w] \<cdot> \<a>[r \<star> f, w', w]" "r \<star> \<a>[f, w', w]"
                        "\<a>[r, f \<star> w', w] \<cdot> (\<a>[r, f, w'] \<star> w)"]
            by simp
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = (r \<star> \<theta>) \<cdot> \<a>[r, f', w] \<cdot>
                           (((r \<star> \<theta>') \<star> w) \<cdot> (\<a>[r, f, w'] \<star> w) \<cdot> ((\<rho> \<star> w') \<star> w)) \<cdot>
                           (\<nu>' \<star> w) \<cdot> \<nu> \<cdot> \<r>[g]"
        proof -
          have "(r \<star> \<theta>' \<star> w) \<cdot> \<a>[r, f \<star> w', w] = \<a>[r, f', w] \<cdot> ((r \<star> \<theta>') \<star> w)"
            using assoc_naturality [of r \<theta>' w] by simp
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = (r \<star> \<theta>) \<cdot> \<a>[r, f', w] \<cdot> (composite_cell w' \<theta>' \<star> w) \<cdot> (\<nu>' \<star> w) \<cdot> \<nu> \<cdot> \<r>[g]"
          using whisker_right
          by (metis T'.uw\<theta>\<omega> T'.w_in_hom(1) composite_cell_in_hom T'.\<theta>_simps(2) T'.ide_w
              T.ide_w arrI seqE)
        also have "... = (r \<star> \<theta>) \<cdot> \<a>[r, f', w] \<cdot> ((\<rho>' \<cdot> inv \<nu>' \<star> w) \<cdot> (\<nu>' \<star> w)) \<cdot> \<nu> \<cdot> \<r>[g]"
        proof -
          have "composite_cell w' \<theta>' = \<rho>' \<cdot> inv \<nu>'"
            using assms invert_side_of_triangle(2) T.tab_simps(1) comp_assoc by presburger
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = (T.composite_cell w \<theta> \<cdot> \<nu>) \<cdot> \<r>[g]"
          using whisker_right [of w "\<rho>' \<cdot> inv \<nu>'" \<nu>'] dom_\<nu>' comp_assoc comp_inv_arr'
                comp_arr_dom
          by simp
        also have "... = \<rho> \<cdot> \<r>[g]"
          using assms(2) comp_assoc by simp
        also have "... = composite_cell (src f) \<r>[f]"
          using comp_assoc runit_hcomp runit_naturality [of \<rho>] by simp
        finally show ?thesis by simp
      qed
      have eq': "(r \<star> \<r>[f]) \<cdot> \<a>[r, f, src f] \<cdot> (\<rho> \<star> src f) \<cdot> (inv (?\<nu>'\<nu> \<cdot> \<r>[g])) =
                 composite_cell (w' \<star> w) ?\<theta>\<theta>'"
      proof -
        have 1: "composite_cell (src f) \<r>[f] = (composite_cell (w' \<star> w) ?\<theta>\<theta>') \<cdot> ?\<nu>'\<nu> \<cdot> \<r>[g]"
          using eq comp_assoc by simp
        have "composite_cell (src f) \<r>[f] \<cdot> (inv (?\<nu>'\<nu> \<cdot> \<r>[g])) = composite_cell (w' \<star> w) ?\<theta>\<theta>'"
        proof -
          have "seq (r \<star> \<r>[f]) (\<a>[r, f, src f] \<cdot> (\<rho> \<star> src f))"
            by fastforce
          thus ?thesis
            using iso_\<nu>'\<nu>_r 1 invert_side_of_triangle(2) by simp
        qed
        thus ?thesis
          using comp_assoc by simp
      qed

      have \<nu>'\<nu>_r: "\<guillemotleft>?\<nu>'\<nu> \<cdot> \<r>[g] : g \<star> src f \<Rightarrow> g \<star> w' \<star> w\<guillemotright>"
          by force
      have inv_\<nu>'\<nu>_r: "\<guillemotleft>inv (?\<nu>'\<nu> \<cdot> \<r>[g]) : g \<star> w' \<star> w \<Rightarrow> g \<star> src f\<guillemotright>"
        using \<nu>'\<nu> iso_\<nu>'\<nu>_r by auto

      let ?P = "\<lambda>\<gamma>. \<guillemotleft>\<gamma> : src f \<Rightarrow> w' \<star> w\<guillemotright> \<and> ?\<nu>'\<nu> \<cdot> \<r>[g] = dom \<rho> \<star> \<gamma> \<and> \<r>[f] = ?\<theta>\<theta>' \<cdot> (f \<star> \<gamma>)"
      let ?\<gamma> = "THE \<gamma>. ?P \<gamma>"
      have "?P ?\<gamma>"
      proof -
        have "\<exists>!\<gamma>. ?P \<gamma>"
          using \<nu>'\<nu>_r \<theta>\<theta>' eq T2 [of "src f" "w' \<star> w" "\<r>[f]" f ?\<theta>\<theta>' "?\<nu>'\<nu> \<cdot> \<r>[g]"] by simp
        thus ?thesis
          using the1_equality [of ?P] by blast
      qed
      hence \<gamma>: "\<guillemotleft>?\<gamma> : src f \<rightarrow> src f\<guillemotright> \<and> ?P ?\<gamma>"
        using src_dom trg_dom by fastforce

      let ?P' = "\<lambda>\<gamma>. \<guillemotleft>\<gamma> : w' \<star> w \<Rightarrow> src f\<guillemotright> \<and> inv (?\<nu>'\<nu> \<cdot> \<r>[g]) = g \<star> \<gamma> \<and> ?\<theta>\<theta>' = \<r>[f] \<cdot> (f \<star> \<gamma>)"
      let ?\<gamma>' = "THE \<gamma>. ?P' \<gamma>"
      have "?P' ?\<gamma>'"
      proof -
        have "\<exists>!\<gamma>. ?P' \<gamma>"
          using inv_\<nu>'\<nu>_r \<theta>\<theta>' eq'
                T2 [of "w' \<star> w" "src f" "\<theta> \<cdot> (\<theta>' \<star> w) \<cdot> \<a>\<^sup>-\<^sup>1[f, w', w]" f] comp_assoc
          by simp
        thus ?thesis
          using the1_equality [of ?P'] by blast
      qed
      hence \<gamma>': "\<guillemotleft>?\<gamma>' : src f \<rightarrow> src f\<guillemotright> \<and> ?P' ?\<gamma>'"
        using src_dom trg_dom by fastforce

      have "inverse_arrows ?\<gamma> ?\<gamma>'"
      proof
        let ?Q = "\<lambda>\<gamma>. \<guillemotleft>\<gamma> : src f \<Rightarrow> src f\<guillemotright> \<and> dom \<rho> \<star> src f = g \<star> \<gamma> \<and> \<r>[f] = \<r>[f] \<cdot> (f \<star> \<gamma>)"
        have "\<exists>!\<gamma>. ?Q \<gamma>"
        proof -
          have "ide (src f)" by simp
          moreover have "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>" by simp
          moreover have "\<guillemotleft>dom \<rho> \<star> src f : g \<star> src f \<Rightarrow> g \<star> src f\<guillemotright>" by auto
          moreover have "(\<rho> \<star> src f) \<cdot> (dom \<rho> \<star> src f) = \<rho> \<star> src f"
          proof -
            have "(\<rho> \<star> src \<rho>) \<cdot> (dom \<rho> \<star> src (dom \<rho>)) = \<rho> \<star> src \<rho>"
              using R.is_natural_1 arr_dom tab_simps(1) by presburger
            thus ?thesis
              by simp
          qed
          ultimately show ?thesis
            using comp_arr_dom T2 [of "src f" "src f" "\<r>[f]" f "\<r>[f]" "dom \<rho> \<star> src f"]
                  comp_assoc
            by metis
        qed
        moreover have "?Q (src f)"
          using comp_arr_dom by auto
        moreover have "?Q (?\<gamma>' \<cdot> ?\<gamma>)"
        proof (intro conjI)
          show "\<guillemotleft>?\<gamma>' \<cdot> ?\<gamma> : src f \<Rightarrow> src f\<guillemotright>"
            using \<gamma> \<gamma>' by auto
          show "dom \<rho> \<star> src f = g \<star> ?\<gamma>' \<cdot> ?\<gamma>"
          proof -
            have "g \<star> ?\<gamma>' \<cdot> ?\<gamma> = (g \<star> ?\<gamma>') \<cdot> (g \<star> ?\<gamma>)"
              using \<gamma> \<gamma>' whisker_left by fastforce
            also have "... = inv (?\<nu>'\<nu> \<cdot> \<r>[g]) \<cdot> (?\<nu>'\<nu> \<cdot> \<r>[g])"
              using \<gamma> \<gamma>' by simp
            also have "... = dom \<rho> \<star> src f"
              using \<nu>'\<nu> iso_\<nu>'\<nu>_r comp_inv_arr inv_is_inverse by auto
            finally show ?thesis by simp
          qed
          show "\<r>[f] = \<r>[f] \<cdot> (f \<star> ?\<gamma>' \<cdot> ?\<gamma>)"
          proof -
            have "\<r>[f] \<cdot> (f \<star> ?\<gamma>' \<cdot> ?\<gamma>) = \<r>[f] \<cdot> (f \<star> ?\<gamma>') \<cdot> (f \<star> ?\<gamma>)"
              using \<gamma> \<gamma>' whisker_left by fastforce
            also have "... = (\<r>[f] \<cdot> (f \<star> ?\<gamma>')) \<cdot> (f \<star> ?\<gamma>)"
              using comp_assoc by simp
            also have "... = \<r>[f]"
              using \<gamma> \<gamma>' by simp
            finally show ?thesis by simp
          qed
        qed
        ultimately have "?\<gamma>' \<cdot> ?\<gamma> = src f" by blast
        thus "ide (?\<gamma>' \<cdot> ?\<gamma>)" by simp

        let ?Q' = "\<lambda>\<gamma>. \<guillemotleft>\<gamma> : w' \<star> w \<Rightarrow> w' \<star> w\<guillemotright> \<and> g \<star> w' \<star> w = g \<star> \<gamma> \<and> ?\<theta>\<theta>' = ?\<theta>\<theta>' \<cdot> (f \<star> \<gamma>)"
        have "\<exists>!\<gamma>. ?Q' \<gamma>"
        proof -
          have "ide (w' \<star> w)" by simp
          moreover have "\<guillemotleft>?\<theta>\<theta>' : f \<star> w' \<star> w \<Rightarrow> f\<guillemotright>"
            using \<theta>\<theta>' by simp
          moreover have "\<guillemotleft>g \<star> w' \<star> w : g \<star> w' \<star> w \<Rightarrow> g \<star> w' \<star> w\<guillemotright>"
            by auto
          moreover have
            "composite_cell (w' \<star> w) ?\<theta>\<theta>' = composite_cell (w' \<star> w) ?\<theta>\<theta>' \<cdot> (g \<star> w' \<star> w)"
          proof -
            have "\<guillemotleft>\<rho> \<star> w' \<star> w : g \<star> w' \<star> w \<Rightarrow> (r \<star> f) \<star> w' \<star> w\<guillemotright>"
              by (intro hcomp_in_vhom, auto)
            hence "(\<rho> \<star> w' \<star> w) \<cdot> (g \<star> w' \<star> w) = \<rho> \<star> w' \<star> w"
              using comp_arr_dom by auto
            thus ?thesis
              using comp_assoc by simp
          qed
          ultimately show ?thesis
            using T2 by presburger
        qed
        moreover have "?Q' (w' \<star> w)"
          using \<theta>\<theta>' comp_arr_dom by auto
        moreover have "?Q' (?\<gamma> \<cdot> ?\<gamma>')"
        proof (intro conjI)
          show "\<guillemotleft>?\<gamma> \<cdot> ?\<gamma>' : w' \<star> w \<Rightarrow> w' \<star> w\<guillemotright>"
            using \<gamma> \<gamma>' by auto
          show "g \<star> w' \<star> w = g \<star> ?\<gamma> \<cdot> ?\<gamma>'"
          proof -
            have "g \<star> ?\<gamma> \<cdot> ?\<gamma>' = (g \<star> ?\<gamma>) \<cdot> (g \<star> ?\<gamma>')"
              using \<gamma> \<gamma>' whisker_left by fastforce
            also have "... = (?\<nu>'\<nu> \<cdot> \<r>[g]) \<cdot> inv (?\<nu>'\<nu> \<cdot> \<r>[g])"
              using \<gamma> \<gamma>' by simp
            also have "... = g \<star> w' \<star> w"
              using \<nu>'\<nu> iso_\<nu>'\<nu>_r comp_arr_inv inv_is_inverse by auto
            finally show ?thesis by simp
          qed
          show "?\<theta>\<theta>' = ?\<theta>\<theta>' \<cdot> (f \<star> ?\<gamma> \<cdot> ?\<gamma>')"
          proof -
            have "?\<theta>\<theta>' \<cdot> (f \<star> ?\<gamma> \<cdot> ?\<gamma>') = ?\<theta>\<theta>' \<cdot> (f \<star> ?\<gamma>) \<cdot> (f \<star> ?\<gamma>')"
              using \<gamma> \<gamma>' whisker_left by fastforce
            also have "... = (?\<theta>\<theta>' \<cdot> (f \<star> ?\<gamma>)) \<cdot> (f \<star> ?\<gamma>')"
              using comp_assoc by simp
            also have "... = ?\<theta>\<theta>'"
              using \<gamma> \<gamma>' by simp
            finally show ?thesis by simp
          qed
        qed
        ultimately have "?\<gamma> \<cdot> ?\<gamma>' = w' \<star> w" by blast
        thus "ide (?\<gamma> \<cdot> ?\<gamma>')" by simp
      qed
      hence "\<guillemotleft>?\<gamma> : src f \<Rightarrow> w' \<star> w\<guillemotright> \<and> iso ?\<gamma>"
        using \<gamma> by auto
      thus ?thesis by auto
    qed

    text \<open>
      Now we can show that, given two tabulations of the same 1-cell,
      there is an equivalence map between the apexes that extends to a transformation
      of one tabulation into the other.
    \<close>

    lemma apex_unique_up_to_equivalence:
    assumes "tabulation V H \<a> \<i> src trg r \<rho>' f' g'"
    shows "\<exists>w w' \<phi> \<psi> \<theta> \<nu> \<theta>' \<nu>'.
             equivalence_in_bicategory V H \<a> \<i> src trg w' w \<psi> \<phi> \<and>
             \<guillemotleft>w : src f \<rightarrow> src f'\<guillemotright> \<and> \<guillemotleft>w' : src f' \<rightarrow> src f\<guillemotright> \<and>
             \<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> f\<guillemotright> \<and> \<guillemotleft>\<nu> : g \<Rightarrow> g' \<star> w\<guillemotright> \<and> iso \<nu> \<and>
             \<rho> = (r \<star> \<theta>) \<cdot> \<a>[r, f', w] \<cdot> (\<rho>' \<star> w) \<cdot> \<nu> \<and>
             \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> f'\<guillemotright> \<and> \<guillemotleft>\<nu>' : g' \<Rightarrow> g \<star> w'\<guillemotright> \<and> iso \<nu>' \<and>
             \<rho>' = (r \<star> \<theta>') \<cdot> \<a>[r, f, w'] \<cdot> (\<rho> \<star> w') \<cdot> \<nu>'"
    proof -
      interpret T': tabulation V H \<a> \<i> src trg r \<rho>' f' g'
        using assms by auto
      obtain w \<theta> \<nu>
      where w\<theta>\<nu>: "ide w \<and> \<guillemotleft>\<theta> : f' \<star> w \<Rightarrow> f\<guillemotright> \<and> \<guillemotleft>\<nu> : g \<Rightarrow> g' \<star> w\<guillemotright> \<and> iso \<nu> \<and>
                  \<rho> = T'.composite_cell w \<theta> \<cdot> \<nu>"
        using T'.T1 [of f \<rho>] ide_leg0 tab_in_hom by auto
      obtain w' \<theta>' \<nu>'
      where w'\<theta>'\<nu>': "ide w' \<and> \<guillemotleft>\<theta>' : f \<star> w' \<Rightarrow> f'\<guillemotright> \<and> \<guillemotleft>\<nu>' : g' \<Rightarrow> g \<star> w'\<guillemotright> \<and> iso \<nu>' \<and>
                     \<rho>' = composite_cell w' \<theta>' \<cdot> \<nu>'"
        using T1 [of f' \<rho>'] T'.ide_leg0 T'.tab_in_hom by auto
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : src f \<Rightarrow> w' \<star> w\<guillemotright> \<and> iso \<phi>"
        using w\<theta>\<nu> w'\<theta>'\<nu>' apex_equivalence_lemma T'.tab_in_hom comp_assoc by metis
      obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : src f' \<Rightarrow> w \<star> w'\<guillemotright> \<and> iso \<psi>"
        using w\<theta>\<nu> w'\<theta>'\<nu>' T'.apex_equivalence_lemma tab_in_hom comp_assoc by metis
      have 1: "src f = src w"
        using \<phi> src_dom [of \<phi>] hcomp_simps(1) [of w' w]
        by (metis arr_cod in_homE leg0_simps(2) src_hcomp src_src vconn_implies_hpar(3))
      have 2: "src f' = src w'"
        using \<psi> src_dom [of \<psi>] hcomp_simps(1) [of w w']
        by (metis T'.leg0_simps(2) arr_cod in_homE src_hcomp src_src vconn_implies_hpar(3))
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg w' w \<psi> \<open>inv \<phi>\<close>
        using \<phi> \<psi> 1 2 w\<theta>\<nu> w'\<theta>'\<nu>' iso_inv_iso
        apply unfold_locales by auto
      have "\<guillemotleft>w : src f \<rightarrow> src f'\<guillemotright>"
        using \<psi> w\<theta>\<nu> 1 2 trg_cod hcomp_simps(2) E.antipar(1) by simp
      moreover have "\<guillemotleft>w' : src f' \<rightarrow> src f\<guillemotright>"
        using \<phi> w'\<theta>'\<nu>' 1 2 E.antipar(2) by simp
      ultimately show ?thesis
        using E.equivalence_in_bicategory_axioms w\<theta>\<nu> w'\<theta>'\<nu>' comp_assoc by metis
    qed

  end

  subsection "`Tabulation' is Bicategorical"

  text \<open>
    In this section we show that ``tabulation'' is a truly bicategorical notion,
    in the sense that tabulations are preserved and reflected by equivalence pseudofunctors.
    The proofs given here is are elementary proofs from first principles.
    It should also be possible to give a proof based on birepresentations,
    but for this to actually save work it would first be necessary to carry out a general
    development of birepresentations and bicategorical limits, and I have chosen not to
    attempt this here.
  \<close>

  (*
   * TODO: The fully_faithful_and_essentially_surjective_functor locale should have arguments in
   * same order as functor, faithful_functor, etc.
   * The equivalence_functor definition can reverse the arguments for consistency
   * with the definition of adjoint equivalence.
   *)

  context equivalence_pseudofunctor
  begin

    lemma preserves_tabulation:
    assumes "tabulation (\<cdot>\<^sub>C) (\<star>\<^sub>C) \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> f g"
    shows "tabulation (\<cdot>\<^sub>D) (\<star>\<^sub>D) \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F r) (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>) (F f) (F g)"
    proof -
      let ?\<rho>' = "D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>"
      interpret T: tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> f
        using assms by auto
      interpret T': tabulation_data V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F r\<close> ?\<rho>' \<open>F f\<close> \<open>F g\<close>
        using \<Phi>_in_hom \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char
        apply unfold_locales
          apply auto
        by (intro D.comp_in_homI, auto)
      interpret T': tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F r\<close> ?\<rho>' \<open>F f\<close> \<open>F g\<close>
      text \<open>
        How bad can it be to just show this directly from first principles?
        It is worse than it at first seems, once you start filling in the details!
      \<close>
      proof
        fix u' \<omega>'
        assume u': "D.ide u'"
        assume \<omega>': "\<guillemotleft>\<omega>' : D.dom \<omega>' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D u'\<guillemotright>"
        show "\<exists>w' \<theta>' \<nu>'. D.ide w' \<and> \<guillemotleft>\<theta>' : F f \<star>\<^sub>D w' \<Rightarrow>\<^sub>D u'\<guillemotright> \<and>
                         \<guillemotleft>\<nu>' : D.dom \<omega>' \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w'\<guillemotright> \<and> D.iso \<nu>' \<and>
                         T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<nu>' = \<omega>'"
        proof -
          text \<open>
            First, obtain \<open>\<omega>\<close> in \<open>C\<close> such that \<open>F \<omega>\<close> is related to \<open>\<omega>'\<close> by an equivalence in \<open>D\<close>.
          \<close>
          define v' where "v' = D.dom \<omega>'"
          have v': "D.ide v'"
            using assms v'_def D.ide_dom \<omega>' by blast
          have \<omega>': "\<guillemotleft>\<omega>' : v' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D u'\<guillemotright>"
            using v'_def \<omega>' by simp
          define a' where "a' = src\<^sub>D \<omega>'"

          have [simp]: "src\<^sub>D u' = a'"
            using a'_def \<omega>'
            by (metis D.arr_cod D.ide_char D.in_homE D.src.preserves_cod D.src_dom
                D.src_hcomp v')
          have [simp]: "trg\<^sub>D u' = src\<^sub>D (F r)"
            using \<omega>'
            by (metis D.cod_trg D.in_homE D.not_arr_null D.seq_if_composable D.trg.is_extensional
                D.trg.preserves_arr D.trg.preserves_cod)
          have [simp]: "src\<^sub>D v' = a'"
            using v'_def \<omega>' a'_def by auto
          have [simp]: "trg\<^sub>D v' = trg\<^sub>D (F r)"
            using v'_def D.vconn_implies_hpar(4) \<omega>' u' by force

          have [simp]: "src\<^sub>D \<omega>' = a'"
            using \<omega>' a'_def by blast
          have [simp]: "trg\<^sub>D \<omega>' = trg\<^sub>D (F r)"
            using \<omega>' v'_def \<open>trg\<^sub>D v' = trg\<^sub>D (F r)\<close> by auto

          obtain a where a: "C.obj a \<and> D.equivalent_objects (map\<^sub>0 a) a'"
            using u' \<omega>' a'_def surjective_on_objects_up_to_equivalence D.obj_src by blast
          obtain e' where e': "\<guillemotleft>e' : map\<^sub>0 a \<rightarrow>\<^sub>D a'\<guillemotright> \<and> D.equivalence_map e'"
            using a D.equivalent_objects_def by auto

          have u'_in_hhom: "\<guillemotleft>u' : a' \<rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C r)\<guillemotright>"
            by (simp add: u')
          hence 1: "\<guillemotleft>u' \<star>\<^sub>D e' : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C r)\<guillemotright>"
            using e' by blast
          have v'_in_hhom: "\<guillemotleft>v' : a' \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C r)\<guillemotright>"
            by (simp add: v')
          hence 2: "\<guillemotleft>v' \<star>\<^sub>D e' : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C r)\<guillemotright>"
            using e' by blast

          obtain d' \<eta>' \<epsilon>'
          where d'\<eta>'\<epsilon>': "adjoint_equivalence_in_bicategory (\<cdot>\<^sub>D) (\<star>\<^sub>D) \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e' d' \<eta>' \<epsilon>'"
            using e' D.equivalence_map_extends_to_adjoint_equivalence by blast
          interpret e': adjoint_equivalence_in_bicategory \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e' d' \<eta>' \<epsilon>'
            using d'\<eta>'\<epsilon>' by auto
          interpret d': adjoint_equivalence_in_bicategory \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          d' e' "D.inv \<epsilon>'" "D.inv \<eta>'"
            using e'.dual_adjoint_equivalence by simp
          have [simp]: "src\<^sub>D e' = map\<^sub>0 a"
            using e' by auto
          have [simp]: "trg\<^sub>D e' = a'"
             using e' by auto
          have [simp]: "src\<^sub>D d' = a'"
            by (simp add: e'.antipar(2))
          have [simp]: "trg\<^sub>D d' = map\<^sub>0 a"
            using e'.antipar by simp

          obtain u where u: "\<guillemotleft>u : a \<rightarrow>\<^sub>C src\<^sub>C r\<guillemotright> \<and> C.ide u \<and> D.isomorphic (F u) (u' \<star>\<^sub>D e')"
            using a e' u' 1 u'_in_hhom locally_essentially_surjective [of a "src\<^sub>C r" "u' \<star>\<^sub>D e'"]
                  C.obj_src D.equivalence_map_is_ide T.base_simps(2)
            by blast
          obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : u' \<star>\<^sub>D e' \<Rightarrow>\<^sub>D F u\<guillemotright> \<and> D.iso \<phi>"
            using u D.isomorphic_symmetric by blast
          obtain v where v: "\<guillemotleft>v : a \<rightarrow>\<^sub>C trg\<^sub>C r\<guillemotright> \<and> C.ide v \<and> D.isomorphic (F v) (v' \<star>\<^sub>D e')"
            using a e' v' v'_in_hhom locally_essentially_surjective [of a "trg\<^sub>C r" "v' \<star>\<^sub>D e'"]
                  C.obj_trg D.equivalence_map_is_ide T.base_simps(2)
            by blast
          obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : F v \<Rightarrow>\<^sub>D v' \<star>\<^sub>D e'\<guillemotright> \<and> D.iso \<psi>"
            using v by blast

          have [simp]: "src\<^sub>C u = a" using u by auto
          have [simp]: "trg\<^sub>C u = src\<^sub>C r" using u by auto
          have [simp]: "src\<^sub>C v = a" using v by auto
          have [simp]: "trg\<^sub>C v = trg\<^sub>C r" using v by auto
          have [simp]: "src\<^sub>D \<phi> = map\<^sub>0 a"
            using \<phi> by (metis "1" D.dom_src D.in_hhomE D.in_homE D.src.preserves_dom)
          have [simp]: "trg\<^sub>D \<phi> = trg\<^sub>D u'"
            using \<phi>
            by (metis D.cod_trg D.hseqI D.in_homE D.isomorphic_implies_hpar(4)
                D.trg.preserves_cod D.trg_hcomp e' u u'_in_hhom)
          have [simp]: "src\<^sub>D \<psi> = map\<^sub>0 a"
            using \<psi>
            by (metis C.in_hhomE D.in_homE D.src_dom \<open>src\<^sub>D e' = map\<^sub>0 a\<close> preserves_src v)
          have [simp]: "trg\<^sub>D \<psi> = trg\<^sub>D v'"
            using \<psi>
            by (metis "2" D.cod_trg D.in_hhomE D.in_homE D.trg.preserves_cod T.base_simps(2)
                \<open>trg\<^sub>D v' = trg\<^sub>D (F r)\<close> preserves_trg)

          define F\<omega> where "F\<omega> = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi>"
          have F\<omega>: "\<guillemotleft>F\<omega> : F v \<Rightarrow>\<^sub>D F (r \<star>\<^sub>C u)\<guillemotright>"
          proof (unfold F\<omega>_def, intro D.comp_in_homI)
            show "\<guillemotleft>\<psi> : F v \<Rightarrow>\<^sub>D v' \<star>\<^sub>D e'\<guillemotright>"
              using \<psi> by simp
            show "\<guillemotleft>\<omega>' \<star>\<^sub>D e' : v' \<star>\<^sub>D e' \<Rightarrow>\<^sub>D (F r \<star>\<^sub>D u') \<star>\<^sub>D e'\<guillemotright>"
              using e' \<omega>' D.equivalence_map_is_ide v'_in_hhom by blast
            show "\<guillemotleft>\<a>\<^sub>D[F r, u', e'] : (F r \<star>\<^sub>D u') \<star>\<^sub>D e' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D u' \<star>\<^sub>D e'\<guillemotright>"
              using e' u' D.equivalence_map_is_ide D.in_hhom_def u'_in_hhom by auto
            show "\<guillemotleft>F r \<star>\<^sub>D \<phi> : F r \<star>\<^sub>D u' \<star>\<^sub>D e' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D F u\<guillemotright>"
              using e' u' u \<phi>
              by (metis C.in_hhomE D.hcomp_in_vhom D.isomorphic_implies_hpar(4)
                  T'.base_in_hom(2) T.base_simps(2) preserves_src preserves_trg)
            show "\<guillemotleft>\<Phi> (r, u) : F r \<star>\<^sub>D F u \<Rightarrow>\<^sub>D F (r \<star>\<^sub>C u)\<guillemotright>"
              using u \<Phi>_in_hom(2) [of r u] by auto
          qed

          obtain \<omega> where \<omega>: "\<guillemotleft>\<omega> : v \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<guillemotright> \<and> F \<omega> = F\<omega>"
            using u v \<omega>' \<phi> \<psi> F\<omega> locally_full [of v "r \<star>\<^sub>C u" F\<omega>]
            by (metis C.ide_hcomp C.hseqI C.in_hhomE C.src_hcomp C.trg_hcomp
                T.ide_base T.base_in_hom(1))
          have [simp]: "src\<^sub>C \<omega> = src\<^sub>C u"
            using \<omega>
            by (metis C.hseqI C.in_homE C.src_cod C.src_hcomp T.base_in_hom(1) u)
          have [simp]: "trg\<^sub>C \<omega> = trg\<^sub>C r"
            using \<omega>
            by (metis C.ide_char C.ide_trg C.in_homE C.trg.preserves_hom \<open>trg\<^sub>C v = trg\<^sub>C r\<close>)
  
          text \<open>Apply \<open>T.T1\<close> to \<open>u\<close> and \<open>\<omega>\<close> to obtain \<open>w\<close>, \<open>\<theta>\<close>, \<open>\<nu>\<close>.\<close>

          obtain w \<theta> \<nu>
          where w\<theta>\<nu>: "C.ide w \<and> \<guillemotleft>\<theta> : f \<star>\<^sub>C w \<Rightarrow>\<^sub>C u\<guillemotright> \<and> \<guillemotleft>\<nu> : C.dom \<omega> \<Rightarrow>\<^sub>C g \<star>\<^sub>C w\<guillemotright> \<and>
                      C.iso \<nu> \<and> T.composite_cell w \<theta> \<cdot>\<^sub>C \<nu> = \<omega>"
            using u \<omega> T.T1 [of u \<omega>] by auto
          text \<open>
          Combining \<open>\<omega>\<close> and \<open>w\<theta>\<nu>\<close> yields the situation depicted in the diagram below.
          In this as well as subsequent diagrams, canonical isomorphisms have been suppressed
          in the interests of clarity.
$$
F (
\xy/67pt/
\xymatrix{
  & {\scriptstyle{a}}
  \xlowertwocell[ddddl]{}_{v}{^\nu}
  \xuppertwocell[ddddr]{}^{u}{^\theta}
  \ar@ {.>}[dd]^{w}
  \\
  \\
  & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f} \xtwocell[ddd]{}\omit{^\rho}
  \ar[ddl] _{g}
  \ar[ddr] ^{f}
  \\
  \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll] ^{r}
  \\
  &
}
\endxy
)
\qquad = \qquad
\xy/67pt/
\xymatrix{
  & {\scriptstyle{{\rm src}(F a)}}
  \xlowertwocell[ddddl]{}^{<2>F v}{^{\psi}}
  \xuppertwocell[ddddr]{}^{<2>F u}{^{\phi}}
  \ar[dd] ^{e'}
  \\
  \\
  & \scriptstyle{a'} \xtwocell[ddd]{}\omit{^{\omega'}}
  \ar[ddl] _{v'}
  \ar[ddr] ^{u'}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
$$
          \<close>
          have [simp]: "src\<^sub>C w = src\<^sub>C u"
            by (metis C.arrI C.seqE C.src_hcomp C.src_vcomp C.vseq_implies_hpar(1)
                \<omega> \<open>src\<^sub>C \<omega> = src\<^sub>C u\<close> w\<theta>\<nu>)
          have [simp]: "trg\<^sub>C w = src\<^sub>C f"
            by (metis C.arrI C.hseq_char C.seqE T.tab_simps(2) \<omega> w\<theta>\<nu>)
          have [simp]: "src\<^sub>D (F u) = map\<^sub>0 a"
            using e'.antipar(1) u by auto
          have [simp]: "src\<^sub>D (F v) = map\<^sub>0 a"
              using v e' e'.antipar by force
          have [simp]: "src\<^sub>D (F w) = map\<^sub>0 a"
            by (simp add: w\<theta>\<nu>)

          have *: "F (T.composite_cell w \<theta> \<cdot>\<^sub>C \<nu>) =
                     \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                       (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu>"
          text \<open>
$$
F (
\xy/67pt/
\xymatrix{
  & {\scriptstyle{a}}
  \xlowertwocell[ddddl]{}_{v}{^\nu}
  \xuppertwocell[ddddr]{}^{u}{^\theta}
  \ar[dd] ^{w}
  \\
  \\
  & \scriptstyle{{\rm src}~g \;=\;{\rm src}~f} \xtwocell[ddd]{}\omit{^\rho}
  \ar[ddl] _{g}
  \ar[ddr] ^{f}
  \\
  \\
  \scriptstyle{{\rm trg}~r} & & \scriptstyle{{\rm src}~r} \ar[ll] ^{r}
  \\
  &
}
\endxy
)
\qquad = \qquad
\xy/67pt/
\xymatrix{
  & {\scriptstyle{{\rm src}(F a)}}
  \xlowertwocell[ddddl]{}^{<2>F v}{^{F \nu}}
  \xuppertwocell[ddddr]{}^{<2>F u}{^{F \theta}}
  \ar[dd] ^{Fw}
  \\
  \\
  & \scriptstyle{{\rm src}(F g) \;=\;{\rm src}(F f)} \xtwocell[ddd]{}\omit{^{F \rho}}
  \ar[ddl] _{F g}
  \ar[ddr] ^{F f}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
$$
          \<close>
          proof -
            have "F (T.composite_cell w \<theta> \<cdot>\<^sub>C \<nu>) = F ((r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>C \<a>\<^sub>C[r, f, w] \<cdot>\<^sub>C (\<rho> \<star>\<^sub>C w) \<cdot>\<^sub>C \<nu>)"
              using C.comp_assoc by simp
            also have "... = F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D F \<a>\<^sub>C[r, f, w] \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w) \<cdot>\<^sub>D F \<nu>"
              by (metis C.arr_dom_iff_arr C.comp_assoc C.in_homE C.seqE preserves_comp_2 w\<theta>\<nu>)
            also have "... =
                       F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D (\<Phi> (r, f \<star>\<^sub>C w) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                         (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w))) \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w) \<cdot>\<^sub>D F \<nu>"
              using \<omega> w\<theta>\<nu> preserves_assoc [of r f w]
              by (metis C.hseqE C.in_homE C.seqE T.tab_simps(2) T.ide_leg0 T.ide_base
                  T.leg0_simps(3))
            also have "... =
                       ((F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w))) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                         ((D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w))) \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w) \<cdot>\<^sub>D F \<nu>"
              using D.comp_assoc by simp
            also have "... =
                       \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                         ((D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w)) \<cdot>\<^sub>D F \<nu>"
            proof -
              have "(F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) =
                    (\<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)))"
              proof -
                have "F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w) = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>)"
                  using \<omega> \<Phi>.naturality [of "(r, \<theta>)"] FF_def w\<theta>\<nu> C.VV.arr_char
                  apply simp
                  by (metis (no_types, lifting) C.hseqE C.in_homE C.seqE)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w))"
              proof -
                have "(F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) = F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<omega> w\<theta>\<nu> D.whisker_right [of "F r" "F \<theta>" "\<Phi> (f, w)"]
                  by (metis C.hseqE C.in_homE C.seqE D.comp_ide_self D.interchange D.seqI'
                      T'.ide_base T'.base_in_hom(2) T.tab_simps(2) T.ide_leg0 \<Phi>_in_hom(2)
                      preserves_hom)
                thus ?thesis by simp
              qed
              finally have "(F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) =
                            \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w))"
                by simp
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                               ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))) \<cdot>\<^sub>D F \<nu>"
            proof -
              have "(D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w) =
                    ((D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w)) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
              proof -
                have "D.inv (\<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w) = (F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
                proof -
                  have "src\<^sub>C (r \<star>\<^sub>C f) = trg\<^sub>C w"
                    using \<omega> w\<theta>\<nu>
                    by (metis C.arrI C.hseq_char C.seqE C.hcomp_simps(1) T.tab_simps(2)
                        T.leg0_simps(2) T.leg0_simps(3))
                  hence "D.seq (\<Phi> (r \<star>\<^sub>C f, w)) (F \<rho> \<star>\<^sub>D F w)"
                    using \<omega> w\<theta>\<nu> \<Phi>_in_hom(2) [of "r \<star>\<^sub>C f" w] C.VV.arr_char FF_def by auto
                  moreover have "\<Phi> (r \<star>\<^sub>C f, w) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w) = F (\<rho> \<star>\<^sub>C w) \<cdot>\<^sub>D \<Phi> (g, w)"
                    using \<omega> w\<theta>\<nu> \<Phi>.naturality [of "(\<rho>, w)"] \<Phi>_components_are_iso FF_def
                          C.VV.arr_char
                    by simp
                  moreover have "D.iso (\<Phi> (r \<star>\<^sub>C f, w))"
                    using w\<theta>\<nu> \<Phi>_components_are_iso
                    by (metis C.arrI C.ide_hcomp C.hseqE C.hseqI' C.seqE C.src_hcomp
                        T.tab_simps(2) T.ide_leg0 T.ide_base T.leg0_simps(2-3) \<omega>)
                  moreover have "D.iso (\<Phi> (g, w))"
                    using w\<theta>\<nu> \<Phi>_components_are_iso
                    by (metis C.arrI C.hseqE C.seqE T.tab_simps(2) T.ide_leg1 T.leg1_simps(3) \<omega>)
                  ultimately show ?thesis
                    using \<omega> w\<theta>\<nu> \<Phi>.naturality \<Phi>_components_are_iso FF_def C.VV.arr_char
                          D.invert_opposite_sides_of_square
                    by presburger
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
                using \<omega> w\<theta>\<nu> D.whisker_right \<Phi>_components_are_iso \<Phi>_in_hom D.comp_assoc
                by auto
              finally show ?thesis
                using D.comp_assoc by simp
            qed
            finally show ?thesis
              using D.comp_assoc by simp
          qed

          text \<open>We can now define the \<open>w'\<close>, \<open>\<theta>'\<close>, and \<open>\<nu>'\<close> that we are required to exhibit.\<close>

          define \<phi>' where "\<phi>' = e'.trnr\<^sub>\<epsilon> u' (D.inv \<phi>)"
          have "\<phi>' = \<r>\<^sub>D[u'] \<cdot>\<^sub>D (u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[u', e', d'] \<cdot>\<^sub>D (D.inv \<phi> \<star>\<^sub>D d')"
            unfolding \<phi>'_def e'.trnr\<^sub>\<epsilon>_def by simp
          have \<phi>': "\<guillemotleft>\<phi>' : F u \<star>\<^sub>D d' \<Rightarrow>\<^sub>D u'\<guillemotright>"
            using \<phi> \<phi>'_def u u' e'.adjoint_transpose_right(2) [of u' "F u"] by auto

          have [simp]: "src\<^sub>D \<phi>' = src\<^sub>D u'"
            using \<phi>' by fastforce
          have [simp]: "trg\<^sub>D \<phi>' = trg\<^sub>D u'"
            using \<phi>' by fastforce

          define \<psi>' where "\<psi>' = d'.trnr\<^sub>\<eta> v' (D.inv \<psi>)"
          have \<psi>'_eq: "\<psi>' = (D.inv \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d'] \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
            unfolding \<psi>'_def d'.trnr\<^sub>\<eta>_def by simp
          have \<psi>': "\<guillemotleft>\<psi>' : v' \<Rightarrow>\<^sub>D F v \<star>\<^sub>D d'\<guillemotright>"
            using \<psi> \<psi>'_def v v' d'.adjoint_transpose_right(1) [of "F v" v'] by auto
          have iso_\<psi>': "D.iso \<psi>'"
            unfolding \<psi>'_def d'.trnr\<^sub>\<eta>_def
            using \<psi> e'.counit_is_iso
            by (metis D.arrI D.iso_hcomp D.hseq_char D.ide_is_iso D.iso_assoc'
                D.iso_inv_iso D.iso_runit' D.isos_compose D.seqE \<psi>'_eq
                \<psi>' d'.unit_simps(5) e'.antipar(1) e'.antipar(2) e'.ide_left e'.ide_right v')

          have [simp]: "src\<^sub>D \<psi>' = src\<^sub>D v'"
            using \<psi>' by fastforce
          have [simp]: "trg\<^sub>D \<psi>' = trg\<^sub>D v'"
            using \<psi>' by fastforce

          define w' where "w' = F w \<star>\<^sub>D d'"
          define \<theta>' where "\<theta>' = \<phi>' \<cdot>\<^sub>D (F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']"
          define \<nu>' where "\<nu>' = \<a>\<^sub>D[F g, F w, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
          have w': "D.ide w' \<and> \<guillemotleft>w' : src\<^sub>D u' \<rightarrow>\<^sub>D src\<^sub>D (F f)\<guillemotright>"
            using w'_def \<omega> w\<theta>\<nu> by simp
          have \<theta>': "\<guillemotleft>\<theta>' : F f \<star>\<^sub>D w' \<Rightarrow>\<^sub>D u'\<guillemotright>"
            unfolding \<theta>'_def w'_def
            using \<phi>' \<omega> w\<theta>\<nu> \<Phi>_in_hom
            apply (intro D.comp_in_homI D.hcomp_in_vhom)
              apply auto
            by (intro D.comp_in_homI D.hcomp_in_vhom, auto)
          have \<nu>': "\<guillemotleft>\<nu>' : v' \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w'\<guillemotright>"
            unfolding \<nu>'_def w'_def
            using \<psi>' \<omega> w\<theta>\<nu> \<Phi>_in_hom \<Phi>_components_are_iso
            apply (intro D.comp_in_homI)
              apply auto
            by (intro D.hcomp_in_vhom D.comp_in_homI, auto)
          have iso_\<nu>': "D.iso \<nu>'"
            using \<nu>'_def iso_\<psi>' \<Phi>_in_hom \<Phi>.components_are_iso D.isos_compose preserves_iso
            by (metis (no_types, lifting) C.ideD(1) D.arrI D.iso_hcomp D.hseqE D.ide_is_iso
                D.iso_assoc D.iso_inv_iso D.seqE T.ide_leg1 T.leg1_simps(3) \<Phi>_components_are_iso
                \<nu>' \<open>src\<^sub>D (F w) = map\<^sub>0 a\<close> \<open>src\<^sub>D e' = map\<^sub>0 a\<close> \<open>trg\<^sub>C w = src\<^sub>C f\<close> e'.antipar(1)
                e'.ide_right preserves_ide preserves_src preserves_trg w\<theta>\<nu>)

          have "T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<nu>' = \<omega>'"
          text \<open>
$$
\xy/67pt/
\xymatrix{
  &
  \xlowertwocell[ddddddl]{\scriptstyle{a'}}<-13>^{<2>v'}{^{\psi'}}
  \xuppertwocell[ddddddr]{}<13>^{<2>u'}{^{\phi'}}
  \ar [dd] ^{d'}
  \\
  \\
  & {\scriptstyle{{\rm src}(F g) \;=\;{\rm src}(F f)}}
  \xlowertwocell[ddddl]{}^{<2>F v}{^{F \nu}}
  \xuppertwocell[ddddr]{}^{<2>F u}{^{F \theta}}
  \ar[dd] ^{Fw}
  \\
  \\
  & \scriptstyle{a'} \xtwocell[ddd]{}\omit{^{F \rho}}
  \ar[ddl] _{F g}
  \ar[ddr] ^{F f}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
\qquad = \qquad
\xy/33pt/
\xymatrix{
  & \scriptstyle{\scriptstyle{a'}} \xtwocell[ddd]{}\omit{^{\omega'}}
  \ar[ddl] _{v'}
  \ar[ddr] ^{u'}
  \\
  \\
  \scriptstyle{{\rm trg}~(Fr)} & & \scriptstyle{{\rm src}~(Fr)} \ar[ll] ^{Fr}
  \\
  &
}
\endxy
$$
          \<close>
          proof -
            have 1: "\<guillemotleft>T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<nu>' : v' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D u'\<guillemotright>"
              using w' \<theta>' \<nu>' w\<theta>\<nu> T'.composite_cell_in_hom by blast
            have "T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<nu>' =
                  (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D
                    (F (T.composite_cell w \<theta> \<cdot>\<^sub>C \<nu>) \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
            proof -
              have "T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<nu>' =
                    (F r \<star>\<^sub>D \<phi>' \<cdot>\<^sub>D (F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']) \<cdot>\<^sub>D
                      \<a>\<^sub>D[F r, F f, w'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D w') \<cdot>\<^sub>D \<a>\<^sub>D[F g, F w, d'] \<cdot>\<^sub>D
                      (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using \<theta>'_def \<nu>'_def D.comp_assoc by simp
              also have
                "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D (F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F w, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using \<theta>' \<theta>'_def w'_def D.comp_assoc D.whisker_left by auto
              also have
                "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D (F \<theta> \<star>\<^sub>D d') \<cdot>\<^sub>D (\<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<cdot>\<^sub>D
                         ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F w, d']) \<cdot>\<^sub>D (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using \<theta>' \<theta>'_def D.whisker_right \<Phi>_in_hom D.comp_assoc by fastforce
              also have
                "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D (F \<theta> \<star>\<^sub>D d') \<cdot>\<^sub>D (\<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<cdot>\<^sub>D
                         \<a>\<^sub>D[F r \<star>\<^sub>D F f, F w, d'] \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                         (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              proof -
                have "(D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F g, F w, d'] =
                      \<a>\<^sub>D[F r \<star>\<^sub>D F f, F w, d'] \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d')"
                  using D.assoc_naturality [of "D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>" "F w" d']
                        \<Phi>_in_hom \<Phi>_components_are_iso
                  by (simp add: w\<theta>\<nu>)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<cdot>\<^sub>D \<a>\<^sub>D[F r \<star>\<^sub>D F f, F w, d']) \<cdot>\<^sub>D 
                                 ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using 1 D.whisker_left D.comp_assoc
                by (metis D.arrI D.hseq_char D.seqE T'.ide_base calculation)
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<star>\<^sub>D d') \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f \<star>\<^sub>D F w, d']) \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, F w] \<star>\<^sub>D d') \<cdot>\<^sub>D 
                                 ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              proof -
                have "D.seq \<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<a>\<^sub>D[F r \<star>\<^sub>D F f, F w, d']"
                  by (metis 1 D.arrI D.seqE calculation)
                moreover have "D.iso (F r \<star>\<^sub>D \<a>\<^sub>D[F f, F w, d'])"
                  by (simp add: w\<theta>\<nu>)
                moreover have "D.inv (F r \<star>\<^sub>D \<a>\<^sub>D[F f, F w, d']) = F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']"
                  using D.inv_hcomp [of "F r" "\<a>\<^sub>D[F f, F w, d']"] by (simp add: w\<theta>\<nu>)
                ultimately
                have "(F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F w, d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<cdot>\<^sub>D
                        \<a>\<^sub>D[F r \<star>\<^sub>D F f, F w, d'] =
                      \<a>\<^sub>D[F r, F f \<star>\<^sub>D F w, d'] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, F w] \<star>\<^sub>D d')"
                  using w\<theta>\<nu> D.pentagon
                        D.invert_side_of_triangle(1)
                           [of "\<a>\<^sub>D[F r, F f, F w \<star>\<^sub>D d'] \<cdot>\<^sub>D \<a>\<^sub>D[F r \<star>\<^sub>D F f, F w, d']"
                               "F r \<star>\<^sub>D \<a>\<^sub>D[F f, F w, d']"
                               "\<a>\<^sub>D[F r, F f \<star>\<^sub>D F w, d'] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, F w] \<star>\<^sub>D d')"]
                  by simp
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D ((F r \<star>\<^sub>D F \<theta> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F (f \<star>\<^sub>C w), d']) \<cdot>\<^sub>D 
                                 ((F r \<star>\<^sub>D \<Phi> (f, w)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, F w] \<star>\<^sub>D d') \<cdot>\<^sub>D 
                                 ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              proof -
                have "(F r \<star>\<^sub>D \<Phi> (f, w) \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f \<star>\<^sub>D F w, d'] =
                      \<a>\<^sub>D[F r, F (f \<star>\<^sub>C w), d'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<Phi> (f, w)) \<star>\<^sub>D d')"
                  using 1 w\<theta>\<nu> D.assoc_naturality [of "F r" "\<Phi> (f, w)" d']
                        \<open>trg\<^sub>C w = src\<^sub>C f\<close> e'.ide_right
                  by (metis D.arrI D.hseq_char D.ide_char D.seqE T'.base_simps(3)
                      T'.base_simps(4) T'.leg0_simps(3) T.ide_leg0 \<Phi>_simps(1-5) w'_def)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (((F r \<star>\<^sub>D F \<theta>) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D \<Phi> (f, w)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, F w] \<star>\<^sub>D d') \<cdot>\<^sub>D 
                                 ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d')) \<cdot>\<^sub>D \<psi>'"
              proof -
                have "src\<^sub>D (F r) = trg\<^sub>D (F \<theta>)"
                  using w\<theta>\<nu> by (metis C.arrI C.hseqE C.seqE \<omega> preserves_hseq)
                moreover have "src\<^sub>D (F \<theta>) = trg\<^sub>D d'"
                  using w\<theta>\<nu> C.arrI C.vconn_implies_hpar(1) by auto
                ultimately
                have "(F r \<star>\<^sub>D F \<theta> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F (f \<star>\<^sub>C w), d'] =
                      \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F \<theta>) \<star>\<^sub>D d')"
                  using w\<theta>\<nu> D.assoc_naturality [of "F r" "F \<theta>" d'] by auto
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                 (((F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w))) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                                 (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              proof -
                have "((F r \<star>\<^sub>D F \<theta>) \<star>\<^sub>D d') \<cdot>\<^sub>D
                        ((F r \<star>\<^sub>D \<Phi> (f, w)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, F w] \<star>\<^sub>D d') \<cdot>\<^sub>D 
                        ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<star>\<^sub>D d') \<cdot>\<^sub>D
                        (D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') =
                      (F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                        (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu>
                        \<star>\<^sub>D d'"
                proof -
                  have "\<guillemotleft>(F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                           (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> :
                             F v \<Rightarrow>\<^sub>D F r \<star>\<^sub>D F u\<guillemotright>"
                    using w\<theta>\<nu> \<omega> \<Phi>_in_hom
                    apply (intro D.comp_in_homI)
                         apply auto
                    by (intro D.hcomp_in_vhom, auto)
                  hence "D.arr ((F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                                 (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu>)"
                    by auto
                  thus ?thesis
                    using D.whisker_right by fastforce
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                                 (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using w\<theta>\<nu> D.whisker_left \<Phi>_in_hom
                by (metis D.seqI' T'.ide_base T.ide_leg0 \<open>trg\<^sub>C w = src\<^sub>C f\<close> preserves_hom)
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                 ((D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w))) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                                 (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              proof -
                have "(D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u)) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) =
                      F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)"
                proof -  
                  have "(D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u)) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) =
                        (F r \<star>\<^sub>D F u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w))"
                    using u \<Phi>_components_are_iso
                    by (simp add: D.comp_inv_arr')
                  also have "... = F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)"
                    using u \<omega> w\<theta>\<nu> \<Phi>_in_hom \<open>trg\<^sub>C u = src\<^sub>C r\<close>
                          D.comp_cod_arr [of "F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)" "F r \<star>\<^sub>D F u"]
                    by (metis (full_types) "*" D.arrI D.cod_comp D.seqE F\<omega> T.ide_base
                        \<Phi>_simps(4))
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using D.comp_assoc by simp
               qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                               (D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using D.comp_assoc by simp
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 (\<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D 
                                 (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              proof -
                have "D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d' =
                      (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D F \<nu> \<star>\<^sub>D d')"
                  using D.whisker_right \<Phi>_in_hom \<Phi>_components_are_iso
                  by (metis * D.arrI D.invert_side_of_triangle(1) F\<omega> T.ide_base \<omega>
                       \<open>trg\<^sub>C u = src\<^sub>C r\<close> e'.ide_right u w\<theta>\<nu>)
                thus ?thesis
                   using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 (F (T.composite_cell w \<theta> \<cdot>\<^sub>C \<nu>) \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using D.comp_assoc * by simp
             finally show ?thesis by simp
           qed
           also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D
                               (F \<omega> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
              using w\<theta>\<nu> by simp
            also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D
                               (\<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D
                               \<psi>'"
               using \<omega> F\<omega>_def by simp
            text \<open>
$$
\xy/67pt/
\xymatrix{
  & {\scriptstyle{a'}}
  \xlowertwocell[ddddl]{}^{<2>F v}{^{\psi'}}
  \xuppertwocell[ddddr]{}^{<2>F u}{^{\phi'}}
  \ar@ {.}[dd] ^{d'}
  \\
  \\
  & \scriptstyle{{\rm src}(F a)} \xtwocell[ddd]{}\omit{^{F \omega}}
  \ar[ddl] _{F v}
  \ar[ddr] ^{F u}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
\qquad = \qquad
\xy/67pt/
\xymatrix{
  &
  \xlowertwocell[ddddddl]{\scriptstyle{a'}}<-13>^{<2>v'}{^{\psi'}}
  \xuppertwocell[ddddddr]{}<13>^{<2>u'}{^{\phi'}}
  \ar@ {.}[dd] ^{d'}
  \\
  \\
  & {\scriptstyle{{\rm src}(F a)}}
  \xlowertwocell[ddddl]{}^{<2>F v}{^{\psi}}
  \xuppertwocell[ddddr]{}^{<2>F u}{^{\phi}}
  \ar@ {.}[dd] ^{e'}
  \\
  \\
  & \scriptstyle{a'} \xtwocell[ddd]{}\omit{^{\omega'}}
  \ar[ddl] _{v'}
  \ar[ddr] ^{u'}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
$$
            \<close>
            also have "... = \<omega>'"
            text \<open>
$$
\xy/67pt/
\xymatrix{
  &
  \xlowertwocell[ddddddl]{\scriptstyle{a'}}<-13>^{<2>v'}{^{\psi'}}
  \xuppertwocell[ddddddr]{}<13>^{<2>u'}{^{\phi'}}
  \ar[dd] ^{d'}
  \\
  \\
  & {\scriptstyle{{\rm src}(F a)}}
  \xlowertwocell[ddddl]{}^{<2>F v}{^{\psi}}
  \xuppertwocell[ddddr]{}^{<2>F u}{^{\phi}}
  \ar[dd] ^{e'}
  \\
  \\
  & \scriptstyle{a'} \xtwocell[ddd]{}\omit{^{\omega'}}
  \ar[ddl] _{v'}
  \ar[ddr] ^{u'}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
\qquad = \qquad
\xy/33pt/
\xymatrix{
  & \scriptstyle{a'} \xtwocell[ddd]{}\omit{^{\omega'}}
  \ar[ddl] _{v'}
  \ar[ddr] ^{u'}
  \\
  \\
  \scriptstyle{{\rm trg}~(F r)} & & \scriptstyle{{\rm src}~)(F r)} \ar[ll] ^{F r}
  \\
  &
}
\endxy
$$
            \<close>
            proof -
              have "(F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D
                      (\<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>' =
                    (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                      ((D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<Phi> (r, u) \<star>\<^sub>D d')) \<cdot>\<^sub>D
                      ((F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using D.whisker_right \<Phi>_in_hom D.comp_assoc
                by (metis D.arrI F\<omega> F\<omega>_def e'.ide_right)
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
               proof -
                 have "(D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<Phi> (r, u) \<star>\<^sub>D d') =
                       D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u) \<star>\<^sub>D d'"
                   using \<Phi>_in_hom \<Phi>_components_are_iso D.whisker_right
                   by (metis C.hseqI D.comp_arr_inv' D.in_homE D.invert_opposite_sides_of_square
                       D.iso_inv_iso T.ide_base T.base_in_hom(1) \<open>trg\<^sub>C u = src\<^sub>C r\<close> e'.ide_right
                       preserves_arr u)
                 also have "... = (F r \<star>\<^sub>D F u) \<star>\<^sub>D d'"
                   using u \<Phi>_components_are_iso D.comp_inv_arr' by simp
                 finally have "(F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                 ((D.inv (\<Phi> (r, u)) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<Phi> (r, u) \<star>\<^sub>D d')) \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>' =
                               (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F u) \<star>\<^sub>D d') \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                   by simp
                 also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F u) \<star>\<^sub>D d')) \<cdot>\<^sub>D
                                    ((F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                   using D.comp_assoc by auto
                 also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                  ((F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                   using u D.comp_arr_dom by simp
                 finally show ?thesis by blast
               qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D
                                  ((F r \<star>\<^sub>D \<phi>) \<star>\<^sub>D d')) \<cdot>\<^sub>D (\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d') \<cdot>\<^sub>D
                                  ((\<omega>' \<star>\<^sub>D e') \<star>\<^sub>D d') \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
               proof -
                 have
                   "(F r \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e') \<cdot>\<^sub>D \<psi> \<star>\<^sub>D d' =
                    ((F r \<star>\<^sub>D \<phi>) \<star>\<^sub>D d') \<cdot>\<^sub>D (\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d') \<cdot>\<^sub>D ((\<omega>' \<star>\<^sub>D e') \<star>\<^sub>D d') \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D d')"
                   using D.whisker_right \<phi> \<phi>' e' e'.antipar(1) u' u'_in_hhom
                   by (metis D.arrI D.seqE F\<omega> F\<omega>_def e'.ide_right)
                 thus ?thesis
                   using D.comp_assoc by simp
               qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d'] \<cdot>\<^sub>D
                                  ((\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d') \<cdot>\<^sub>D ((\<omega>' \<star>\<^sub>D e') \<star>\<^sub>D d')) \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
               proof -
                 have "\<a>\<^sub>D[F r, F u, d'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<phi>) \<star>\<^sub>D d') =
                       (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d']"
                   using D.assoc_naturality [of "F r" \<phi> d'] \<phi> by auto
                 thus ?thesis
                   using D.comp_assoc by simp
               qed
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d'] \<cdot>\<^sub>D
                                 ((\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d') \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D u', e', d'] \<cdot>\<^sub>D
                                 (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[v', e', d'])) \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
                using F\<omega> F\<omega>_def \<omega>' D.comp_assoc D.hcomp_reassoc(1) [of \<omega>' e' d']
                by (elim D.in_homE, simp)
              also have "... = (F r \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) \<cdot>\<^sub>D
                                  \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D
                                  (\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<psi>'"
               proof -
                 have "D.seq (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d'])
                             (\<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d'] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d'))"
                   using u' by simp
                 moreover have "(F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d'] \<cdot>\<^sub>D
                                  (\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d') =
                                \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] \<cdot>\<^sub>D \<a>\<^sub>D[F r \<star>\<^sub>D u', e', d']"
                   using u' D.pentagon by simp
                 moreover have "D.iso (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d'])"
                   using u' by simp
                 moreover have "D.inv (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) = F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']"
                   using u' by simp
                 ultimately
                 have "\<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d'] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D u', e', d'] =
                         (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d']"
                   using u' D.comp_assoc
                         D.invert_opposite_sides_of_square
                           [of "F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']"
                               "\<a>\<^sub>D[F r, u' \<star>\<^sub>D e', d'] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, u', e'] \<star>\<^sub>D d')"
                               "\<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d']" "\<a>\<^sub>D[F r \<star>\<^sub>D u', e', d']"]
                   by simp
                 thus ?thesis
                   using D.comp_assoc by metis
               qed
              also have
                "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u'] \<cdot>\<^sub>D (u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[u', e', d'] \<cdot>\<^sub>D (D.inv \<phi> \<star>\<^sub>D d')) \<cdot>\<^sub>D
                         (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] \<cdot>\<^sub>D
                         (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D (D.inv \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d'] \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
                unfolding \<phi>'_def \<psi>'_def e'.trnr\<^sub>\<epsilon>_def d'.trnr\<^sub>\<eta>_def by simp
              also have
                "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D
                         (F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D
                         (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D (D.inv \<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d'] \<cdot>\<^sub>D
                         (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "F r \<star>\<^sub>D \<r>\<^sub>D[u'] \<cdot>\<^sub>D (u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[u', e', d'] \<cdot>\<^sub>D (D.inv \<phi> \<star>\<^sub>D d') =
                      (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D
                        (F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d')"
                proof -
                  have "D.ide (F r)" by simp
                  moreover have "D.seq \<r>\<^sub>D[u'] ((u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[u', e', d'] \<cdot>\<^sub>D (D.inv \<phi> \<star>\<^sub>D d')) \<and>
                                 D.seq (u' \<star>\<^sub>D \<epsilon>') (\<a>\<^sub>D[u', e', d'] \<cdot>\<^sub>D (D.inv \<phi> \<star>\<^sub>D d')) \<and>
                                 D.seq \<a>\<^sub>D[u', e', d'] (D.inv \<phi> \<star>\<^sub>D d')"
                    using \<phi>' \<phi>'_def unfolding e'.trnr\<^sub>\<epsilon>_def by blast
                  ultimately show ?thesis
                    using D.whisker_left by metis
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D
                         (((F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d')) \<cdot>\<^sub>D
                         (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d'])) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D
                         \<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D (((\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D (D.inv \<psi> \<star>\<^sub>D d')) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d']) \<cdot>\<^sub>D
                         (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
                using D.comp_assoc by simp
              also have
                "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D
                         (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d']) \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>')) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "((F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) =
                      F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']"
                proof -
                have "(F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') = F r \<star>\<^sub>D D.inv \<phi> \<cdot>\<^sub>D \<phi> \<star>\<^sub>D d'"
                  using u u' \<phi> 1 2 D.src_dom e'.antipar D.whisker_left D.whisker_right
                  by auto
                also have "... = F r \<star>\<^sub>D (u' \<star>\<^sub>D e') \<star>\<^sub>D d'"
                  using \<phi> D.comp_inv_arr' by auto
                finally have
                  "(F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d') = F r \<star>\<^sub>D (u' \<star>\<^sub>D e') \<star>\<^sub>D d'"
                  by simp
                hence
                  "((F r \<star>\<^sub>D D.inv \<phi> \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<phi> \<star>\<^sub>D d')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']) =
                   (F r \<star>\<^sub>D (u' \<star>\<^sub>D e') \<star>\<^sub>D d') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d'])"
                  using D.comp_assoc by simp
                also have "... = F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']"
                proof -
                  have "\<guillemotleft>F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d'] :
                            F r \<star>\<^sub>D u' \<star>\<^sub>D e' \<star>\<^sub>D d' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D (u' \<star>\<^sub>D e') \<star>\<^sub>D d'\<guillemotright>"
                    using u' e'.antipar \<phi>' D.assoc'_in_hom
                    unfolding e'.trnr\<^sub>\<epsilon>_def
                    by (intro D.hcomp_in_vhom, auto)
                  thus ?thesis
                    using D.comp_cod_arr by blast
                qed
                finally show ?thesis by simp
              qed
              moreover have
                "((\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D (D.inv \<psi> \<star>\<^sub>D d')) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d'] = \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d']"
              proof -
                have "(\<psi> \<star>\<^sub>D d') \<cdot>\<^sub>D (D.inv \<psi> \<star>\<^sub>D d') = (v' \<star>\<^sub>D e') \<star>\<^sub>D d'"
                  using \<psi> e'.antipar D.src_cod v' e'.antipar \<psi>' d'.trnr\<^sub>\<eta>_def
                        D.whisker_right [of d' \<psi> "D.inv \<psi>"] D.comp_arr_inv'
                  by auto
                moreover have "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d'] : v' \<star>\<^sub>D e' \<star>\<^sub>D d' \<Rightarrow>\<^sub>D (v' \<star>\<^sub>D e') \<star>\<^sub>D d'\<guillemotright>"
                  using v' e'.antipar \<psi>' D.assoc'_in_hom
                  unfolding d'.trnr\<^sub>\<eta>_def
                  by fastforce
                ultimately show ?thesis
                  using D.comp_cod_arr by auto
              qed
              ultimately show ?thesis
                using D.comp_assoc by simp
            qed
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (((F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D
                               (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d'])) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d']) \<cdot>\<^sub>D
                               (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "(\<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d']) \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') = v' \<star>\<^sub>D D.inv \<epsilon>'"
                proof -
                  have 1: "D.hseq v' e'"
                    using v' e'.antipar \<psi>' unfolding d'.trnr\<^sub>\<eta>_def by fastforce
                  have "\<a>\<^sub>D[v', e', d'] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[v', e', d'] = v' \<star>\<^sub>D e' \<star>\<^sub>D d'"
                    using v' e'.antipar 1 D.comp_assoc_assoc' by auto
                  moreover have "\<guillemotleft>v' \<star>\<^sub>D D.inv \<epsilon>' : v' \<star>\<^sub>D trg\<^sub>D e' \<Rightarrow>\<^sub>D v' \<star>\<^sub>D e' \<star>\<^sub>D d'\<guillemotright>"
                    using v' e'.antipar 1
                    apply (intro D.hcomp_in_vhom)
                      apply auto
                    by (metis D.ideD(1) D.trg_src \<open>trg\<^sub>D e' = a'\<close> e'.antipar(2) e'.ide_right)
                  ultimately show ?thesis
                    using D.comp_cod_arr by auto
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D ((F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d']) \<cdot>\<^sub>D
                               (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "((F r \<star>\<^sub>D \<a>\<^sub>D[u', e', d']) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d'])) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] =
                      \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d']"
                  using \<phi> u' e'.antipar 1 D.comp_cod_arr D.comp_assoc_assoc'
                        D.whisker_left [of "F r" "\<a>\<^sub>D[u', e', d']" "\<a>\<^sub>D\<^sup>-\<^sup>1[u', e', d']"]
                  by auto
                thus ?thesis
                using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', trg\<^sub>D e'] \<cdot>\<^sub>D (((F r \<star>\<^sub>D u') \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D
                               (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d')) \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "(F r \<star>\<^sub>D u' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', e' \<star>\<^sub>D d'] =
                      \<a>\<^sub>D[F r, u', trg\<^sub>D e'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D u') \<star>\<^sub>D \<epsilon>')"
                  using D.assoc_naturality [of "F r" u' \<epsilon>'] e' u' u'_in_hhom by force
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', trg\<^sub>D e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D trg\<^sub>D e') \<cdot>\<^sub>D
                               ((v' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>')) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "((F r \<star>\<^sub>D u') \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') = (\<omega>' \<star>\<^sub>D trg\<^sub>D e') \<cdot>\<^sub>D (v' \<star>\<^sub>D \<epsilon>')"
                proof -
                  have "((F r \<star>\<^sub>D u') \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D e' \<star>\<^sub>D d') =
                        ((F r \<star>\<^sub>D u') \<cdot>\<^sub>D \<omega>' \<star>\<^sub>D \<epsilon>' \<cdot>\<^sub>D (e' \<star>\<^sub>D d'))"
                    using D.interchange
                    by (metis D.comp_arr_dom D.hcomp_simps(3) D.hseqI D.ide_char D.in_hhomE
                        D.in_homE D.seqI T'.base_in_hom(1) T'.base_simps(3) T.base_simps(2)
                        \<omega>' e'.counit_simps(1) e'.counit_simps(2) preserves_src u' u'_in_hhom)
                  also have "... = \<omega>' \<cdot>\<^sub>D v' \<star>\<^sub>D trg\<^sub>D e' \<cdot>\<^sub>D \<epsilon>'"
                    using \<omega>' D.comp_arr_dom D.comp_cod_arr by auto
                  also have "... = (\<omega>' \<star>\<^sub>D trg\<^sub>D e') \<cdot>\<^sub>D (v' \<star>\<^sub>D \<epsilon>')"
                    using D.interchange
                    by (metis D.arrI D.comp_cod_arr D.ide_char D.seqI \<omega>' \<open>trg\<^sub>D e' = a'\<close>
                        e'.counit_simps(1) e'.counit_simps(3) e'.counit_simps(5) v' v'_def)
                  finally show ?thesis by simp
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u', trg\<^sub>D e'] \<cdot>\<^sub>D (\<omega>' \<star>\<^sub>D trg\<^sub>D e') \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[v']"
              proof -
                have "(v' \<star>\<^sub>D \<epsilon>') \<cdot>\<^sub>D (v' \<star>\<^sub>D D.inv \<epsilon>') = v' \<star>\<^sub>D trg\<^sub>D e'"
                  using v' D.whisker_left D.comp_arr_inv D.inv_is_inverse
                  by (metis D.comp_arr_inv' D.seqI' d'.unit_in_vhom e'.counit_in_hom(2)
                      e'.counit_is_iso e'.counit_simps(3))
                moreover have "\<guillemotleft>\<r>\<^sub>D\<^sup>-\<^sup>1[v'] : v' \<Rightarrow>\<^sub>D v' \<star>\<^sub>D trg\<^sub>D e'\<guillemotright>"
                  using v' 1 by simp
                ultimately show ?thesis
                using v' D.comp_cod_arr by auto
              qed
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (\<a>\<^sub>D[F r, u', trg\<^sub>D e'] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D u']) \<cdot>\<^sub>D \<omega>'"
                using u' v' \<omega>' D.runit'_naturality D.comp_assoc
                by (metis D.in_hhomE D.in_homE a'_def e')
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[u']) \<cdot>\<^sub>D \<omega>'"
                using 1 T'.ide_base u' D.runit_hcomp [of "F r" u'] by fastforce
              also have "... = ((F r \<star>\<^sub>D \<r>\<^sub>D[u']) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[u'])) \<cdot>\<^sub>D \<omega>'"
                using D.comp_assoc by simp
              also have "... = (F r \<star>\<^sub>D \<r>\<^sub>D[u'] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[u']) \<cdot>\<^sub>D \<omega>'"
                using 1 T'.ide_base u' D.whisker_left by simp
              also have "... = (F r \<star>\<^sub>D u') \<cdot>\<^sub>D \<omega>'"
                using u'
                by (metis D.comp_ide_self D.ide_in_hom(2) D.ide_is_iso
                  D.invert_opposite_sides_of_square D.invert_side_of_triangle(1)
                  D.iso_runit D.runit_in_vhom D.seqI')
              also have "... = \<omega>'"
                using \<omega>' D.comp_cod_arr by auto
              finally show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          thus "\<exists>w' \<theta>' \<nu>'. D.ide w' \<and>  \<guillemotleft>\<theta>' : F f \<star>\<^sub>D w' \<Rightarrow>\<^sub>D u'\<guillemotright> \<and>
                    \<guillemotleft>\<nu>' : D.dom \<omega>' \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w'\<guillemotright> \<and> D.iso \<nu>' \<and> T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<nu>' = \<omega>'"
            using w' \<theta>' \<nu>' iso_\<nu>' v'_def by blast
        qed

        text \<open>Now we establish \<open>T'.T2\<close>.\<close>
        next
        fix u w w' \<theta> \<theta>' \<beta>
        assume w: "D.ide w"
        assume w': "D.ide w'"
        assume \<theta>: "\<guillemotleft>\<theta> : F f \<star>\<^sub>D w \<Rightarrow>\<^sub>D u\<guillemotright>"
        assume \<theta>': "\<guillemotleft>\<theta>' : F f \<star>\<^sub>D w' \<Rightarrow>\<^sub>D u\<guillemotright>"
        assume \<beta>: "\<guillemotleft>\<beta> : F g \<star>\<^sub>D w \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w'\<guillemotright>"
        assume eq: "T'.composite_cell w \<theta> = T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<beta>"
        show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow>\<^sub>D w'\<guillemotright> \<and> \<beta> = F g \<star>\<^sub>D \<gamma> \<and> \<theta> = \<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>)"
        proof -
          define a where "a = src\<^sub>D w"
          have a: "D.obj a"
            unfolding a_def by (simp add: w)

          have [simp]: "src\<^sub>D \<theta> = a"
            using \<theta> a_def
            by (metis D.dom_src D.in_homE D.src.preserves_dom D.src.preserves_reflects_arr
              D.src_hcomp)
          have [simp]: "trg\<^sub>D \<theta> = trg\<^sub>D (F f)"
            using \<theta>
            by (metis D.arr_dom D.in_homE D.trg_hcomp D.vconn_implies_hpar(2))
          have [simp]: "src\<^sub>D \<theta>' = a"
            using \<theta>' a_def
            by (metis D.horizontal_homs_axioms D.in_homE \<open>src\<^sub>D \<theta> = a\<close> \<theta> horizontal_homs.src_cod)
          have [simp]: "trg\<^sub>D \<theta>' = trg\<^sub>D (F f)"
            using \<theta>'
            by (metis D.vconn_implies_hpar(2) D.vconn_implies_hpar(4) \<open>trg\<^sub>D \<theta> = trg\<^sub>D (F f)\<close> \<theta>)
          have [simp]: "src\<^sub>D w = a"
            using a_def by simp
          have [simp]: "trg\<^sub>D w = map\<^sub>0 (src\<^sub>C \<rho>)"
            by (metis D.horizontal_homs_axioms D.hseq_char D.in_homE T.tab_simps(2) T.leg0_simps(2)
              \<theta> category.ideD(1) category.ide_dom horizontal_homs_def preserves_src)
          have [simp]: "src\<^sub>D w' = a"
            using a_def
            by (metis D.ideD(1) D.in_homE D.src_hcomp D.vconn_implies_hpar(1) \<open>src\<^sub>D \<theta>' = a\<close>
                \<theta>' category.ide_dom horizontal_homs_def weak_arrow_of_homs_axioms
                weak_arrow_of_homs_def)
          have [simp]: "trg\<^sub>D w' = map\<^sub>0 (src\<^sub>C \<rho>)"
            by (metis D.horizontal_homs_axioms D.hseq_char D.in_homE T.tab_simps(2) T.leg0_simps(2)
                \<theta>' category.ideD(1) category.ide_dom horizontal_homs_def preserves_src)

          text \<open>First, reflect the picture back to \<open>C\<close>, so that we will be able to apply \<open>T.T2\<close>.
          We need to choose arrows in \<open>C\<close> carefully, so that their \<open>F\<close> images will enable the
          cancellation of the various isomorphisms that appear.\<close>

          obtain a\<^sub>C where a\<^sub>C: "C.obj a\<^sub>C \<and> D.equivalent_objects (map\<^sub>0 a\<^sub>C) a"
            using w a_def surjective_on_objects_up_to_equivalence D.obj_src D.ideD(1)
            by presburger
          obtain e where e: "\<guillemotleft>e : map\<^sub>0 a\<^sub>C \<rightarrow>\<^sub>D a\<guillemotright> \<and> D.equivalence_map e"
            using a\<^sub>C D.equivalent_objects_def by auto
          obtain d \<eta> \<epsilon>
            where d\<eta>\<epsilon>: "adjoint_equivalence_in_bicategory (\<cdot>\<^sub>D) (\<star>\<^sub>D) \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e d \<eta> \<epsilon>"
              using e D.equivalence_map_extends_to_adjoint_equivalence by blast
          interpret e: adjoint_equivalence_in_bicategory \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e d \<eta> \<epsilon>
            using d\<eta>\<epsilon> by auto
          interpret d: adjoint_equivalence_in_bicategory \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          d e "D.inv \<epsilon>" "D.inv \<eta>"
            using e.dual_adjoint_equivalence by simp

          have [simp]: "src\<^sub>D e = map\<^sub>0 a\<^sub>C"
            using e by auto
          have [simp]: "trg\<^sub>D e = a"
            using e by auto
          have [simp]: "src\<^sub>D d = a"
            using e.antipar by simp
          have [simp]: "trg\<^sub>D d = map\<^sub>0 a\<^sub>C"
            using e.antipar by simp

          have we: "\<guillemotleft>w \<star>\<^sub>D e : map\<^sub>0 a\<^sub>C \<rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C \<rho>)\<guillemotright>"
            using a\<^sub>C e D.ideD(1) \<open>trg\<^sub>D w = map\<^sub>0 (src\<^sub>C \<rho>)\<close> a_def by blast
          obtain w\<^sub>C where
            w\<^sub>C: "C.ide w\<^sub>C \<and> \<guillemotleft>w\<^sub>C : a\<^sub>C \<rightarrow>\<^sub>C src\<^sub>C \<rho>\<guillemotright> \<and> D.isomorphic (F w\<^sub>C) (w \<star>\<^sub>D e)"
            using a\<^sub>C e we locally_essentially_surjective [of a\<^sub>C "src\<^sub>C \<rho>" "w \<star>\<^sub>D e"]
                  C.obj_src T.tab_simps(1) e.ide_left w by blast
          have w'e: "\<guillemotleft>w' \<star>\<^sub>D e : map\<^sub>0 a\<^sub>C \<rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C \<rho>)\<guillemotright>"
            using a\<^sub>C e D.ideD(1) \<open>trg\<^sub>D w' = map\<^sub>0 (src\<^sub>C \<rho>)\<close> a_def \<open>src\<^sub>D w' = a\<close> w' by blast
          obtain w\<^sub>C' where
            w\<^sub>C': "C.ide w\<^sub>C' \<and> \<guillemotleft>w\<^sub>C' : a\<^sub>C \<rightarrow>\<^sub>C src\<^sub>C \<rho>\<guillemotright> \<and> D.isomorphic (F w\<^sub>C') (w' \<star>\<^sub>D e)"
            using a\<^sub>C e a_def locally_essentially_surjective
            by (metis C.obj_src D.ide_hcomp D.hseq_char D.in_hhomE T.tab_simps(2)
                T.leg0_simps(2) e.ide_left w' w'e)

          have [simp]: "src\<^sub>C w\<^sub>C = a\<^sub>C"
            using w\<^sub>C by auto
          have [simp]: "trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>"
            using w\<^sub>C by auto
          have [simp]: "src\<^sub>C w\<^sub>C' = a\<^sub>C"
            using w\<^sub>C' by auto
          have [simp]: "trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>"
            using w\<^sub>C' by auto

          obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : F w\<^sub>C \<Rightarrow>\<^sub>D w \<star>\<^sub>D e\<guillemotright> \<and> D.iso \<phi>"
            using w\<^sub>C D.isomorphicE by blast
          obtain \<phi>' where \<phi>': "\<guillemotleft>\<phi>' : F w\<^sub>C' \<Rightarrow>\<^sub>D w' \<star>\<^sub>D e\<guillemotright> \<and> D.iso \<phi>'"
            using w\<^sub>C' D.isomorphicE by blast

          have ue: "\<guillemotleft>u \<star>\<^sub>D e : map\<^sub>0 a\<^sub>C \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C f)\<guillemotright> \<and> D.ide (u \<star>\<^sub>D e)"
            using a\<^sub>C e \<theta> e.ide_left
            by (intro conjI, auto)
          obtain u\<^sub>C where
            u\<^sub>C: "C.ide u\<^sub>C \<and> \<guillemotleft>u\<^sub>C : a\<^sub>C \<rightarrow>\<^sub>C trg\<^sub>C f\<guillemotright> \<and> D.isomorphic (F u\<^sub>C) (u \<star>\<^sub>D e)"
            using a\<^sub>C e ue locally_essentially_surjective [of a\<^sub>C "trg\<^sub>C f" "u \<star>\<^sub>D e"] by auto

          have [simp]: "src\<^sub>C u\<^sub>C = a\<^sub>C"
            using u\<^sub>C by auto
          have [simp]: "trg\<^sub>C u\<^sub>C = trg\<^sub>C f"
            using u\<^sub>C by auto

          obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : u \<star>\<^sub>D e \<Rightarrow>\<^sub>D F u\<^sub>C\<guillemotright> \<and> D.iso \<psi>"
            using u\<^sub>C D.isomorphic_symmetric D.isomorphicE by blast

          define F\<theta>\<^sub>C where
            "F\<theta>\<^sub>C = \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
          have 1: "\<guillemotleft>F\<theta>\<^sub>C : F (f \<star>\<^sub>C w\<^sub>C) \<Rightarrow>\<^sub>D F u\<^sub>C\<guillemotright>"
          proof (unfold F\<theta>\<^sub>C_def, intro D.comp_in_homI)
            show "\<guillemotleft>D.inv (\<Phi> (f, w\<^sub>C)) : F (f \<star>\<^sub>C w\<^sub>C) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F w\<^sub>C\<guillemotright>"
              by (simp add: \<Phi>_in_hom(2) w\<^sub>C)
            show "\<guillemotleft>F f \<star>\<^sub>D \<phi> : F f \<star>\<^sub>D F w\<^sub>C \<Rightarrow>\<^sub>D F f \<star>\<^sub>D w \<star>\<^sub>D e\<guillemotright>"
              using w w\<^sub>C \<phi> by (intro D.hcomp_in_vhom, auto)
            show "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] : F f \<star>\<^sub>D w \<star>\<^sub>D e \<Rightarrow>\<^sub>D (F f \<star>\<^sub>D w) \<star>\<^sub>D e\<guillemotright>"
              using w D.assoc'_in_hom by simp
            show "\<guillemotleft>\<theta> \<star>\<^sub>D e : (F f \<star>\<^sub>D w) \<star>\<^sub>D e \<Rightarrow>\<^sub>D u \<star>\<^sub>D e\<guillemotright>"
              using w \<theta> by (intro D.hcomp_in_vhom, auto)
            show "\<guillemotleft>\<psi> : u \<star>\<^sub>D e \<Rightarrow>\<^sub>D F u\<^sub>C\<guillemotright>"
              using \<psi> by simp
          qed
          have 2: "\<exists>\<theta>\<^sub>C. \<guillemotleft>\<theta>\<^sub>C : f \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C u\<^sub>C\<guillemotright> \<and> F \<theta>\<^sub>C = F\<theta>\<^sub>C"
            using u\<^sub>C w\<^sub>C 1 e \<theta> \<phi> locally_full by simp
          obtain \<theta>\<^sub>C where \<theta>\<^sub>C: "\<guillemotleft>\<theta>\<^sub>C : f \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C u\<^sub>C\<guillemotright> \<and> F \<theta>\<^sub>C = F\<theta>\<^sub>C"
            using 2 by auto

          define F\<theta>\<^sub>C' where
            "F\<theta>\<^sub>C' = \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C'))"
          have 1: "\<guillemotleft>F\<theta>\<^sub>C' : F (f \<star>\<^sub>C w\<^sub>C') \<Rightarrow>\<^sub>D F u\<^sub>C\<guillemotright>"
          proof (unfold F\<theta>\<^sub>C'_def, intro D.comp_in_homI)
            show "\<guillemotleft>D.inv (\<Phi> (f, w\<^sub>C')) : F (f \<star>\<^sub>C w\<^sub>C') \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F w\<^sub>C'\<guillemotright>"
              by (simp add: \<Phi>_in_hom(2) w\<^sub>C')
            show "\<guillemotleft>F f \<star>\<^sub>D \<phi>' : F f \<star>\<^sub>D F w\<^sub>C' \<Rightarrow>\<^sub>D F f \<star>\<^sub>D w' \<star>\<^sub>D e\<guillemotright>"
              using w' w\<^sub>C' \<phi>' by (intro D.hcomp_in_vhom, auto)
            show "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] : F f \<star>\<^sub>D w' \<star>\<^sub>D e \<Rightarrow>\<^sub>D (F f \<star>\<^sub>D w') \<star>\<^sub>D e\<guillemotright>"
              using w' D.assoc'_in_hom by simp
            show "\<guillemotleft>\<theta>' \<star>\<^sub>D e : (F f \<star>\<^sub>D w') \<star>\<^sub>D e \<Rightarrow>\<^sub>D u \<star>\<^sub>D e\<guillemotright>"
              using w' \<theta>' by (intro D.hcomp_in_vhom, auto)
            show "\<guillemotleft>\<psi> : u \<star>\<^sub>D e \<Rightarrow>\<^sub>D F u\<^sub>C\<guillemotright>"
              using \<psi> by simp
          qed
          have 2: "\<exists>\<theta>\<^sub>C'. \<guillemotleft>\<theta>\<^sub>C' : f \<star>\<^sub>C w\<^sub>C' \<Rightarrow>\<^sub>C u\<^sub>C\<guillemotright> \<and> F \<theta>\<^sub>C' = F\<theta>\<^sub>C'"
            using u\<^sub>C w\<^sub>C' 1 e \<theta> \<phi> locally_full by simp
          obtain \<theta>\<^sub>C' where \<theta>\<^sub>C': "\<guillemotleft>\<theta>\<^sub>C' : f \<star>\<^sub>C w\<^sub>C' \<Rightarrow>\<^sub>C u\<^sub>C\<guillemotright> \<and> F \<theta>\<^sub>C' = F\<theta>\<^sub>C'"
            using 2 by auto

          define F\<beta>\<^sub>C where
            "F\<beta>\<^sub>C = \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                     \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
          have F\<beta>\<^sub>C: "\<guillemotleft>F\<beta>\<^sub>C: F (g \<star>\<^sub>C w\<^sub>C) \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C w\<^sub>C')\<guillemotright>"
          proof (unfold F\<beta>\<^sub>C_def, intro D.comp_in_homI)
            show "\<guillemotleft>D.inv (\<Phi> (g, w\<^sub>C)) : F (g \<star>\<^sub>C w\<^sub>C) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F w\<^sub>C\<guillemotright>"
              by (simp add: \<Phi>_in_hom(2) w\<^sub>C)
            show "\<guillemotleft>F g \<star>\<^sub>D \<phi> : F g \<star>\<^sub>D F w\<^sub>C \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w \<star>\<^sub>D e\<guillemotright>"
              using w\<^sub>C \<phi> apply (intro D.hcomp_in_vhom) by auto
            show "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] : F g \<star>\<^sub>D w \<star>\<^sub>D e \<Rightarrow>\<^sub>D (F g \<star>\<^sub>D w) \<star>\<^sub>D e\<guillemotright>"
              using w D.assoc'_in_hom by simp
            show "\<guillemotleft>\<beta> \<star>\<^sub>D e : (F g \<star>\<^sub>D w) \<star>\<^sub>D e \<Rightarrow>\<^sub>D (F g \<star>\<^sub>D w') \<star>\<^sub>D e\<guillemotright>"
              using w \<beta> apply (intro D.hcomp_in_vhom) by auto
            show "\<guillemotleft>\<a>\<^sub>D[F g, w', e] : (F g \<star>\<^sub>D w') \<star>\<^sub>D e \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w' \<star>\<^sub>D e\<guillemotright>"
              using w' e.antipar D.assoc_in_hom by simp
            show "\<guillemotleft>F g \<star>\<^sub>D D.inv \<phi>' : F g \<star>\<^sub>D w' \<star>\<^sub>D e \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F w\<^sub>C'\<guillemotright>"
              using w' w\<^sub>C' \<phi>' by (intro D.hcomp_in_vhom, auto)
            show "\<guillemotleft>\<Phi> (g, w\<^sub>C') : F g \<star>\<^sub>D F w\<^sub>C' \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C w\<^sub>C')\<guillemotright>"
              using w\<^sub>C' \<Phi>_in_hom by simp
          qed

          have 1: "\<exists>\<beta>\<^sub>C. \<guillemotleft>\<beta>\<^sub>C : g \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C g \<star>\<^sub>C w\<^sub>C'\<guillemotright> \<and> F \<beta>\<^sub>C = F\<beta>\<^sub>C"
            using w\<^sub>C w\<^sub>C' F\<beta>\<^sub>C locally_full by simp
          obtain \<beta>\<^sub>C where \<beta>\<^sub>C: "\<guillemotleft>\<beta>\<^sub>C : g \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C g \<star>\<^sub>C w\<^sub>C'\<guillemotright> \<and> F \<beta>\<^sub>C = F\<beta>\<^sub>C"
            using 1 by auto

          text \<open>
            The following is the main calculation that needs to be done, to permit us
            to apply \<open>T.T2\<close>.
            Once again, it started out looking simple, but once all the necessary
            isomorphisms are thrown in it looks much more complicated.
          \<close>

          have *: "T.composite_cell w\<^sub>C \<theta>\<^sub>C = T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C"
          proof -
            have par: "C.par (T.composite_cell w\<^sub>C \<theta>\<^sub>C) (T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C)"
            proof -
              have "\<guillemotleft>T.composite_cell w\<^sub>C \<theta>\<^sub>C : g \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<^sub>C\<guillemotright>"
                using w\<^sub>C \<theta>\<^sub>C T.composite_cell_in_hom by simp
              moreover have "\<guillemotleft>T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C : g \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<^sub>C\<guillemotright>"
              proof (intro C.comp_in_homI)
                show "\<guillemotleft>\<beta>\<^sub>C : g \<star>\<^sub>C w\<^sub>C \<Rightarrow>\<^sub>C g \<star>\<^sub>C w\<^sub>C'\<guillemotright>"
                  using \<beta>\<^sub>C by simp
                show "\<guillemotleft>\<rho> \<star>\<^sub>C w\<^sub>C' : g \<star>\<^sub>C w\<^sub>C' \<Rightarrow>\<^sub>C (r \<star>\<^sub>C f) \<star>\<^sub>C w\<^sub>C'\<guillemotright>"
                  using w\<^sub>C' by (intro C.hcomp_in_vhom, auto)
                show "\<guillemotleft>\<a>\<^sub>C[r, f, w\<^sub>C'] : (r \<star>\<^sub>C f) \<star>\<^sub>C w\<^sub>C' \<Rightarrow>\<^sub>C r \<star>\<^sub>C f \<star>\<^sub>C w\<^sub>C'\<guillemotright>"
                  using w\<^sub>C' C.assoc_in_hom by simp
                show "\<guillemotleft>r \<star>\<^sub>C \<theta>\<^sub>C' : r \<star>\<^sub>C f \<star>\<^sub>C w\<^sub>C' \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<^sub>C\<guillemotright>"
                  using w\<^sub>C' \<theta>\<^sub>C' by (intro C.hcomp_in_vhom, auto)
              qed
              ultimately show ?thesis
                by (metis C.in_homE)
            qed
            moreover have "F (T.composite_cell w\<^sub>C \<theta>\<^sub>C) = F (T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C)"
            proof -
              have "F (T.composite_cell w\<^sub>C \<theta>\<^sub>C) = F (r \<star>\<^sub>C \<theta>\<^sub>C) \<cdot>\<^sub>D F \<a>\<^sub>C[r, f, w\<^sub>C] \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w\<^sub>C)"
                using par by auto
              also have "... = (\<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C))) \<cdot>\<^sub>D
                                 (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C] \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C))) \<cdot>\<^sub>D
                                 (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C)))"
              proof -
                have "src\<^sub>C f = trg\<^sub>C w\<^sub>C \<and> C.hseq r \<theta>\<^sub>C \<and> C.hseq \<rho> w\<^sub>C"
                using par by auto
                thus ?thesis
                  using w\<^sub>C \<theta>\<^sub>C preserves_assoc preserves_hcomp
                  by (metis C.ideD(2) C.ideD(3) C.in_homE T.ide_base T.ide_leg0 T.leg0_simps(3)
                    T.tab_simps(4) T.tab_simps(5))
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C) \<cdot>\<^sub>D (((D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C))) \<cdot>\<^sub>D
                         (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C))) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C))) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C] \<cdot>\<^sub>D
                         (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D ((D.inv (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C))) \<cdot>\<^sub>D
                         (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C)) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C)) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                using D.comp_assoc by simp
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D ((F r \<star>\<^sub>D F \<theta>\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F r, F f, F w\<^sub>C] \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C)) \<cdot>\<^sub>D
                         D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have
                  "(D.inv (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (r \<star>\<^sub>C f, w\<^sub>C)) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C) = F \<rho> \<star>\<^sub>D F w\<^sub>C"
                  using w\<^sub>C \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> D.comp_inv_arr' \<Phi>_in_hom \<Phi>_components_are_iso
                        D.comp_cod_arr
                  by simp
                moreover have
                  "((D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C))) \<cdot>\<^sub>D (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C))) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C)) =
                   F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C)"
                  using w\<^sub>C D.comp_cod_arr D.comp_inv_arr'  \<Phi>_simps(1,4) by auto
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C] \<cdot>\<^sub>D
                         (?\<rho>' \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "(F r \<star>\<^sub>D F \<theta>\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C)) = F r \<star>\<^sub>D F \<theta>\<^sub>C \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C)"
                  using \<theta>\<^sub>C w\<^sub>C D.whisker_left \<Phi>_in_hom
                  by (metis C.hseqE C.seqE D.seqI' T'.ide_base T.tab_simps(2) T.ide_leg0
                      par preserves_hom)
                moreover have "(D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C) = ?\<rho>' \<star>\<^sub>D F w\<^sub>C"
                  using D.whisker_right by (simp add: w\<^sub>C)
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D
                         D.inv (\<Phi> (f, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C] \<cdot>\<^sub>D
                         (?\<rho>' \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                using \<theta>\<^sub>C F\<theta>\<^sub>C_def D.comp_assoc by simp
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D
                         ((F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C]) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C) \<cdot>\<^sub>D
                         D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "F r \<star>\<^sub>D \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D
                        D.inv (\<Phi> (f, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C) =
                      F r \<star>\<^sub>D \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>)"
                  using \<Phi>_in_hom \<Phi>_components_are_iso D.comp_arr_dom
                  by (metis C.arrI D.cod_inv D.comp_inv_arr' D.seqE F\<theta>\<^sub>C_def T.tab_simps(2)
                      T.ide_leg0 \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> \<theta>\<^sub>C preserves_arr w\<^sub>C)
                also have "... = (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D
                                   (F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>)"
                  using D.whisker_left
                  by (metis (no_types, lifting) C.in_homE D.comp_assoc D.seqE F\<theta>\<^sub>C_def T'.ide_base
                      \<theta>\<^sub>C preserves_arr)
                finally have "F r \<star>\<^sub>D \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D
                                D.inv (\<Phi> (f, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C) =
                              (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D
                                (F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>)"
                  by simp
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F r, F f, w \<star>\<^sub>D e] \<cdot>\<^sub>D (((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C)) \<cdot>\<^sub>D
                         D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "(F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C] =
                      \<a>\<^sub>D[F r, F f, w \<star>\<^sub>D e] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>)"
                  using w\<^sub>C \<phi> \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> D.assoc_naturality [of "F r" "F f" \<phi>]
                  by (metis (mono_tags, lifting) C.ideD(1) D.in_homE D.vconn_implies_hpar(2)
                      T'.base_simps(2-4) T'.leg0_simps(2-5) T.leg0_simps(2)
                      T.tab_simps(2) preserves_src preserves_trg)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F r, F f, w \<star>\<^sub>D e]) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D w \<star>\<^sub>D e) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D
                         D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C) = ?\<rho>' \<star>\<^sub>D \<phi> \<cdot>\<^sub>D F w\<^sub>C"
                  using \<phi> D.interchange
                  by (metis D.comp_arr_dom D.comp_cod_arr D.in_homE T'.tab_simps(1,5))
                also have "... = ?\<rho>' \<star>\<^sub>D (w \<star>\<^sub>D e) \<cdot>\<^sub>D \<phi>"
                  using \<phi> w\<^sub>C D.comp_arr_dom D.comp_cod_arr by auto
                also have "... = (?\<rho>' \<star>\<^sub>D w \<star>\<^sub>D e) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>)"
                  using \<phi> D.interchange
                  by (metis D.comp_arr_ide D.comp_cod_arr D.in_homE D.seqI' T'.ide_leg1
                      T'.leg1_in_hom(2) T'.tab_in_vhom')
                finally have
                  "((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C) = (?\<rho>' \<star>\<^sub>D w \<star>\<^sub>D e) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>)"
                  by simp
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f \<star>\<^sub>D w, e]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D F f, w, e] \<cdot>\<^sub>D
                         (?\<rho>' \<star>\<^sub>D w \<star>\<^sub>D e)) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "D.inv (F r \<star>\<^sub>D \<a>\<^sub>D[F f, w, e]) = F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                  using w by simp
                moreover have "D.seq (F r \<star>\<^sub>D \<a>\<^sub>D[F f, w, e])
                                     (\<a>\<^sub>D[F r, F f \<star>\<^sub>D w, e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e))"
                  using w by simp
                moreover have
                  "(F r \<star>\<^sub>D \<a>\<^sub>D[F f, w, e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f \<star>\<^sub>D w, e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e) =
                   \<a>\<^sub>D[F r, F f, w \<star>\<^sub>D e] \<cdot>\<^sub>D \<a>\<^sub>D[F r \<star>\<^sub>D F f, w, e]"
                  using w D.pentagon by simp
                ultimately
                have "(F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w \<star>\<^sub>D e] =
                      \<a>\<^sub>D[F r, F f \<star>\<^sub>D w, e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D F f, w, e]"
                  using w D.comp_assoc
                        D.invert_opposite_sides_of_square
                          [of "F r \<star>\<^sub>D \<a>\<^sub>D[F f, w, e]" "\<a>\<^sub>D[F r, F f \<star>\<^sub>D w, e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e)"
                              "\<a>\<^sub>D[F r, F f, w \<star>\<^sub>D e]"  "\<a>\<^sub>D[F r \<star>\<^sub>D F f, w, e]"]
                  by auto
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D (((F r \<star>\<^sub>D \<theta>) \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e) \<cdot>\<^sub>D ((?\<rho>' \<star>\<^sub>D w) \<star>\<^sub>D e)) \<cdot>\<^sub>D
                                  \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have
                  "(F r \<star>\<^sub>D \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f \<star>\<^sub>D w, e] = \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<theta>) \<star>\<^sub>D e)"
                  using D.assoc_naturality [of "F r" \<theta> e] \<theta> by auto
                moreover have "\<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D F f, w, e] \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D w \<star>\<^sub>D e) =
                               ((?\<rho>' \<star>\<^sub>D w) \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]"
                  using w we e.ide_left D.assoc'_naturality [of ?\<rho>' w e] by simp
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D
                                 (T'.composite_cell w \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "((F r \<star>\<^sub>D \<theta>) \<star>\<^sub>D e) \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w] \<star>\<^sub>D e) \<cdot>\<^sub>D ((?\<rho>' \<star>\<^sub>D w) \<star>\<^sub>D e) =
                       T'.composite_cell w \<theta> \<star>\<^sub>D e"
                proof -
                  have "\<guillemotleft>T'.composite_cell w \<theta> : F g \<star>\<^sub>D w \<Rightarrow>\<^sub>D F r \<star>\<^sub>D u\<guillemotright>"
                    using w we \<theta> \<open>src\<^sub>D \<theta> = a\<close> \<open>trg\<^sub>D e = a\<close> T'.composite_cell_in_hom
                    by (metis D.ideD(1) D.ide_in_hom(1) D.not_arr_null D.seq_if_composable
                        T'.leg1_simps(3) T.leg1_simps(2-3) T.tab_simps(2)
                        \<open>trg\<^sub>D w = map\<^sub>0 (src\<^sub>C \<rho>)\<close> a_def preserves_src ue)
                  thus ?thesis
                    using D.whisker_right D.arrI by auto
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              finally have L: "F (T.composite_cell w\<^sub>C \<theta>\<^sub>C) =
                               \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D
                                 (T'.composite_cell w \<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                by simp

              have "F (T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C) =
                    F ((r \<star>\<^sub>C \<theta>\<^sub>C') \<cdot>\<^sub>C \<a>\<^sub>C[r, f, w\<^sub>C'] \<cdot>\<^sub>C (\<rho> \<star>\<^sub>C w\<^sub>C') \<cdot>\<^sub>C \<beta>\<^sub>C)"
                using C.comp_assoc by simp
              also have "... = F(r \<star>\<^sub>C \<theta>\<^sub>C') \<cdot>\<^sub>D F \<a>\<^sub>C[r, f, w\<^sub>C'] \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w\<^sub>C') \<cdot>\<^sub>D F \<beta>\<^sub>C"
                using C.comp_assoc par by fastforce
              also have "... = (\<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C') \<cdot>\<^sub>D D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C'))) \<cdot>\<^sub>D
                                 (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C'] \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C'))) \<cdot>\<^sub>D
                                 (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C'))) \<cdot>\<^sub>D
                                 \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "C.hseq r \<theta>\<^sub>C' \<and> C.hseq \<rho> w\<^sub>C'"
                  using par by blast
                thus ?thesis
                  using w\<^sub>C' \<theta>\<^sub>C' \<beta>\<^sub>C F\<beta>\<^sub>C_def preserves_assoc [of r f w\<^sub>C'] preserves_hcomp
                  by force
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C') \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C'))) \<cdot>\<^sub>D
                                 (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C'))) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C'] \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D ((D.inv (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C')) \<cdot>\<^sub>D
                                 \<Phi> (r \<star>\<^sub>C f, w\<^sub>C')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C')) \<cdot>\<^sub>D ((D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D
                                 \<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                using D.comp_assoc by simp
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F r, F f, F w\<^sub>C'] \<cdot>\<^sub>D
                         ((D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "(D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C'))) \<cdot>\<^sub>D (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')) =
                      F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')"
                proof -
                  have "D.seq (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C')) (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')) \<and>
                        D.arr (D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C'))) \<and>
                        D.dom (D.inv (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C'))) =
                        D.cod (\<Phi> (r, f \<star>\<^sub>C w\<^sub>C') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')))"
                    by (metis D.seqE calculation par preserves_arr)
                  thus ?thesis
                    using C.ide_hcomp C.ideD(1) C.trg_hcomp D.invert_side_of_triangle(1)
                          T.ide_base T.ide_leg0 T.leg0_simps(3) T.tab_simps(2) \<Phi>_components_are_iso
                          \<open>trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>\<close> w\<^sub>C'
                    by presburger
                qed
                moreover have
                  "(D.inv (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (r \<star>\<^sub>C f, w\<^sub>C')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w\<^sub>C') =
                   F \<rho> \<star>\<^sub>D F w\<^sub>C'"
                proof -
                  have "D.seq (F \<rho> \<star>\<^sub>D F w\<^sub>C') (D.inv (\<Phi> (C.dom \<rho>, C.dom w\<^sub>C'))) \<and>
                        D.arr (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C')) \<and>
                        D.dom (\<Phi> (r \<star>\<^sub>C f, w\<^sub>C')) =
                        D.cod ((F \<rho> \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D D.inv (\<Phi> (C.dom \<rho>, C.dom w\<^sub>C')))"
                    by (metis C.hseqI' C.ide_char D.seqE T.tab_simps(1) T.tab_simps(5)
                        \<open>trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>\<close> preserves_arr preserves_hcomp w\<^sub>C')
                  thus ?thesis
                    by (metis (no_types) C.ide_hcomp C.ide_char C.hcomp_simps(1)
                        D.cod_comp D.comp_inv_arr' D.seqE T.ide_base T.ide_leg0 T.leg0_simps(3)
                        T.tab_simps(2) \<Phi>_components_are_iso D.comp_cod_arr
                        \<open>trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>\<close> w\<^sub>C')
                qed
                moreover have "(D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') =
                               F g \<star>\<^sub>D D.inv \<phi>'"
                proof -
                  have "(D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') =
                        (F g \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')"
                    using w\<^sub>C' \<beta>\<^sub>C F\<beta>\<^sub>C_def \<Phi>_components_are_iso D.comp_inv_arr' by simp
                  also have "... = F g \<star>\<^sub>D D.inv \<phi>'"
                    using D.comp_cod_arr [of "F g \<star>\<^sub>D D.inv \<phi>'" "F g \<star>\<^sub>D F w\<^sub>C'"]
                    by (metis D.cod_inv D.comp_null(2) D.hseq_char' D.in_homE
                        D.is_weak_composition T'.leg1_simps(6) \<phi>'
                        weak_composition.hcomp_simps\<^sub>W\<^sub>C(3))
                  finally show ?thesis by blast
                qed
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>\<^sub>C') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w\<^sub>C'] \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                using w\<^sub>C' D.whisker_right \<Phi>_in_hom \<Phi>_components_are_iso by simp
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                                   D.inv (\<Phi> (f, w\<^sub>C'))) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w\<^sub>C'] \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                using \<theta>\<^sub>C' F\<theta>\<^sub>C'_def by simp
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D (F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                                 (((F r \<star>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C'))) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C'))) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w\<^sub>C']) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "F r \<star>\<^sub>D \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                        D.inv (\<Phi> (f, w\<^sub>C')) =
                      (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D
                        (F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F r \<star>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C')))"
                  using D.whisker_left \<Phi>_in_hom \<Phi>_components_are_iso
                  by (metis C.arrI D.src.preserves_reflects_arr D.src_vcomp D.vseq_implies_hpar(1)
                      F\<theta>\<^sub>C'_def T'.ide_base \<theta>\<^sub>C' preserves_arr)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D ((F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f, F w\<^sub>C']) \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "((F r \<star>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C'))) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w\<^sub>C'))) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F r, F f, F w\<^sub>C'] =
                      \<a>\<^sub>D[F r, F f, F w\<^sub>C']"
                  using \<Phi>_in_hom \<Phi>_components_are_iso D.comp_cod_arr
                        D.whisker_left [of "F r" "D.inv (\<Phi> (f, w\<^sub>C'))" "\<Phi> (f, w\<^sub>C')"]
                  by (simp add: D.comp_inv_arr' w\<^sub>C')
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e] \<cdot>\<^sub>D
                                  (((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "(F r \<star>\<^sub>D F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w\<^sub>C'] =
                      \<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>')"
                  using w\<^sub>C' \<phi>' D.assoc_naturality [of "F r" "F f" \<phi>']
                  by (metis C.ideD(1) D.dom_trg D.in_homE D.trg.preserves_dom
                      T'.leg0_simps(2-5) T'.base_simps(2-4) T.tab_simps(2) T.leg0_simps(2)
                      \<open>trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>\<close> preserves_src preserves_trg)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 (F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e] \<cdot>\<^sub>D
                                 (?\<rho>' \<star>\<^sub>D w' \<star>\<^sub>D e) \<cdot>\<^sub>D (((F g \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e]) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "((F r \<star>\<^sub>D F f) \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D F w\<^sub>C') = (?\<rho>' \<star>\<^sub>D w' \<star>\<^sub>D e) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>')"
                  using \<phi>' D.interchange D.comp_arr_dom D.comp_cod_arr
                  by (metis D.in_homE T'.tab_in_hom(2))
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 ((F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e]) \<cdot>\<^sub>D
                                 (?\<rho>' \<star>\<^sub>D w' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                                 (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "((F g \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] = \<a>\<^sub>D[F g, w', e]"
                proof -
                  have "((F g \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] =
                        (F g \<star>\<^sub>D w' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e]"
                    by (metis D.arr_inv D.cod_inv D.comp_arr_inv' D.in_homE D.seqI
                        D.whisker_left T'.ide_leg1 \<phi>')
                  also have "... = \<a>\<^sub>D[F g, w', e]"
                    using w' D.comp_cod_arr by simp
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F r, F f \<star>\<^sub>D w', e]) \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 (\<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D F f, w', e] \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D w' \<star>\<^sub>D e)) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D
                                 (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "D.inv (F r \<star>\<^sub>D \<a>\<^sub>D[F f, w', e]) = F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]"
                  using w' by simp
                moreover have "D.seq (F r \<star>\<^sub>D \<a>\<^sub>D[F f, w', e])
                                     (\<a>\<^sub>D[F r, F f \<star>\<^sub>D w', e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e))"
                  using w' by simp
                moreover have "D.iso (F r \<star>\<^sub>D \<a>\<^sub>D[F f, w', e])"
                  using w' by simp
                moreover have "D.iso \<a>\<^sub>D[F r \<star>\<^sub>D F f, w', e]"
                  using w' by simp
                moreover have "(F r \<star>\<^sub>D \<a>\<^sub>D[F f, w', e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f \<star>\<^sub>D w', e] \<cdot>\<^sub>D
                                 (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e) =
                               \<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e] \<cdot>\<^sub>D \<a>\<^sub>D[F r \<star>\<^sub>D F f, w', e]"
                  using w' D.pentagon by simp
                ultimately
                have "(F r \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e] =
                      \<a>\<^sub>D[F r, F f \<star>\<^sub>D w', e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D F f, w', e]"
                  using w' D.comp_assoc
                        D.invert_opposite_sides_of_square
                          [of "F r \<star>\<^sub>D \<a>\<^sub>D[F f, w', e]" "\<a>\<^sub>D[F r, F f \<star>\<^sub>D w', e] \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e)"
                              "\<a>\<^sub>D[F r, F f, w' \<star>\<^sub>D e]"  "\<a>\<^sub>D[F r \<star>\<^sub>D F f, w', e]"]
                  by auto
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D (((F r \<star>\<^sub>D \<theta>') \<star>\<^sub>D e) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e) \<cdot>\<^sub>D ((?\<rho>' \<star>\<^sub>D w') \<star>\<^sub>D e)) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w', e] \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e]) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "(F r \<star>\<^sub>D \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f \<star>\<^sub>D w', e] =
                      \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<theta>') \<star>\<^sub>D e)"
                  using D.assoc_naturality [of "F r" \<theta>' e] \<theta>' by auto
                moreover have "\<a>\<^sub>D\<^sup>-\<^sup>1[F r \<star>\<^sub>D F f, w', e] \<cdot>\<^sub>D (?\<rho>' \<star>\<^sub>D w' \<star>\<^sub>D e) =
                               ((?\<rho>' \<star>\<^sub>D w') \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w', e]"
                  using w' w'e D.assoc'_naturality [of ?\<rho>' w' e] by simp
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D
                                (T'.composite_cell w' \<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "((F r \<star>\<^sub>D \<theta>') \<star>\<^sub>D e) \<cdot>\<^sub>D (\<a>\<^sub>D[F r, F f, w'] \<star>\<^sub>D e) \<cdot>\<^sub>D ((?\<rho>' \<star>\<^sub>D w') \<star>\<^sub>D e) =
                       T'.composite_cell w' \<theta>' \<star>\<^sub>D e"
                proof -
                  have "\<guillemotleft>T'.composite_cell w' \<theta>' : F g \<star>\<^sub>D w' \<Rightarrow>\<^sub>D F r \<star>\<^sub>D u\<guillemotright>"
                    using \<theta>' w' T'.composite_cell_in_hom D.vconn_implies_hpar(3) by simp
                  thus ?thesis
                    using D.whisker_right D.arrI by auto
                qed
                moreover have "(\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w', e] \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e]) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) = \<beta> \<star>\<^sub>D e"
                  using w' \<beta> e.ide_left \<open>src\<^sub>D w' = a\<close> \<open>trg\<^sub>D e = a\<close> F\<beta>\<^sub>C F\<beta>\<^sub>C_def D.comp_cod_arr
                        D.comp_arr_inv'
                  by (metis (no_types, lifting) D.comp_assoc_assoc'(2) D.hcomp_simps(1)
                      D.hcomp_simps(4) D.hseqI' D.ide_char D.in_homE D.vconn_implies_hpar(1)
                      D.vconn_implies_hpar(3) T'.ide_leg1 T.leg1_simps(2) T.leg1_simps(3)
                      T.tab_simps(2) \<open>trg\<^sub>D w' = map\<^sub>0 (src\<^sub>C \<rho>)\<close> preserves_src)
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D
                                 (T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
              proof -
                have "D.arr (T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<beta>)"
                  by (metis (full_types) D.hseq_char D.seqE L eq par preserves_arr)
                thus ?thesis
                  using D.whisker_right by (metis D.comp_assoc e.ide_left)
              qed
              finally have R: "F (T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C) =
                               \<Phi> (r, u\<^sub>C) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<psi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, u, e] \<cdot>\<^sub>D
                                 (T'.composite_cell w' \<theta>' \<cdot>\<^sub>D \<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                by simp

              show "F (T.composite_cell w\<^sub>C \<theta>\<^sub>C) = F (T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C)"
                using eq L R by simp
            qed
            ultimately show ?thesis
              using is_faithful [of "T.composite_cell w\<^sub>C \<theta>\<^sub>C" "T.composite_cell w\<^sub>C' \<theta>\<^sub>C' \<cdot>\<^sub>C \<beta>\<^sub>C"]
              by simp
          qed
          have **: "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w\<^sub>C \<Rightarrow>\<^sub>C w\<^sub>C'\<guillemotright> \<and> \<beta>\<^sub>C = g \<star>\<^sub>C \<gamma> \<and> \<theta>\<^sub>C = \<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)"
            using * w\<^sub>C w\<^sub>C' \<theta>\<^sub>C \<theta>\<^sub>C' \<beta>\<^sub>C T.T2 [of w\<^sub>C w\<^sub>C' \<theta>\<^sub>C u\<^sub>C \<theta>\<^sub>C' \<beta>\<^sub>C] by simp
          obtain \<gamma>\<^sub>C where
            \<gamma>\<^sub>C: "\<guillemotleft>\<gamma>\<^sub>C : w\<^sub>C \<Rightarrow>\<^sub>C w\<^sub>C'\<guillemotright> \<and> \<beta>\<^sub>C = g \<star>\<^sub>C \<gamma>\<^sub>C \<and> \<theta>\<^sub>C = \<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C)"
            using ** by auto
          have \<gamma>\<^sub>C_unique: "\<And>\<gamma>\<^sub>C'. \<guillemotleft>\<gamma>\<^sub>C' : w\<^sub>C \<Rightarrow>\<^sub>C w\<^sub>C'\<guillemotright> \<and> \<beta>\<^sub>C = g \<star>\<^sub>C \<gamma>\<^sub>C' \<and>
                                 \<theta>\<^sub>C = \<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C') \<Longrightarrow> \<gamma>\<^sub>C' = \<gamma>\<^sub>C"
            using \<gamma>\<^sub>C ** by blast

          text \<open>
            Now use \<open>F\<close> to map everything back to \<open>D\<close>, transport the result along the
            equivalence map \<open>e\<close>, and cancel all of the isomorphisms that got introduced.
          \<close>

          let ?P = "\<lambda>\<gamma>. \<guillemotleft>\<gamma> : w \<star>\<^sub>D e \<Rightarrow>\<^sub>D w' \<star>\<^sub>D e\<guillemotright> \<and>
                        \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] = F g \<star>\<^sub>D \<gamma> \<and>
                        \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] =
                        \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>)"
          define \<gamma>e where "\<gamma>e = \<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi>"
          have P\<gamma>e: "?P \<gamma>e"
          proof -
            have 1: "\<guillemotleft>F \<gamma>\<^sub>C : F w\<^sub>C \<Rightarrow>\<^sub>D F w\<^sub>C'\<guillemotright> \<and>
                     F \<beta>\<^sub>C = \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C)) \<and>
                     F \<theta>\<^sub>C = F \<theta>\<^sub>C' \<cdot>\<^sub>D \<Phi> (f, C.cod \<gamma>\<^sub>C) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
              using \<beta>\<^sub>C \<theta>\<^sub>C \<gamma>\<^sub>C preserves_hcomp [of f \<gamma>\<^sub>C] preserves_hcomp [of g \<gamma>\<^sub>C] by force
            have A: "\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] =
                     F g \<star>\<^sub>D \<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi>"
            proof -
              have "F g \<star>\<^sub>D F \<gamma>\<^sub>C = D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D F \<beta>\<^sub>C \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C)"
              proof -
                have "F \<beta>\<^sub>C = \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                  using 1 by simp
                hence "D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D F \<beta>\<^sub>C = (F g \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                  using w\<^sub>C w\<^sub>C' \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> \<open>trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>\<close> \<Phi>_components_are_iso
                        D.invert_side_of_triangle(1)
                  by (metis D.arrI F\<beta>\<^sub>C T.ide_leg1 T.leg1_simps(3) T.tab_simps(2) \<beta>\<^sub>C)
                hence "(D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D F \<beta>\<^sub>C) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C) = F g \<star>\<^sub>D F \<gamma>\<^sub>C"
                  using \<Phi>_components_are_iso D.invert_side_of_triangle(2)
                  by (metis "1" D.arrI D.inv_inv D.iso_inv_iso D.seqE F\<beta>\<^sub>C T.ide_leg1
                      T.leg1_simps(3) T.tab_simps(2) \<beta>\<^sub>C \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> w\<^sub>C)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = ((D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D
                                 D.inv (\<Phi> (g, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C)"
                    using \<beta>\<^sub>C F\<beta>\<^sub>C_def D.comp_assoc by simp
              also have "... = (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>)"
              proof -
                have "(D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') = F g \<star>\<^sub>D D.inv \<phi>'"
                proof -
                  have "(D.inv (\<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') =
                        (F g \<star>\<^sub>D F w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>')"
                    using w\<^sub>C' \<phi>' \<Phi>_components_are_iso D.comp_inv_arr' by simp
                  also have "... = F g \<star>\<^sub>D D.inv \<phi>'"
                    using w\<^sub>C' \<phi>' D.comp_cod_arr
                    by (metis D.arr_inv D.cod_inv D.in_homE D.whisker_left T'.ide_leg1)
                  finally show ?thesis by blast
                qed
                moreover have "(F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C) = F g \<star>\<^sub>D \<phi>"
                proof -
                  have "(F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C)) \<cdot>\<^sub>D \<Phi> (g, w\<^sub>C) =
                        (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D (F g \<star>\<^sub>D F w\<^sub>C)"
                    using w\<^sub>C \<phi> \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> \<Phi>_components_are_iso \<Phi>_in_hom
                          D.comp_inv_arr'
                    by simp
                  also have "... = F g \<star>\<^sub>D \<phi>"
                    using w\<^sub>C \<phi> D.comp_arr_dom
                    by (metis D.hcomp_simps(3) D.hseqI' D.in_hhom_def D.in_homE
                        D.vconn_implies_hpar(2) D.vconn_implies_hpar(4) T'.leg1_simps(2,5)
                        T.leg1_simps(2-3) T.tab_simps(2) preserves_src we)
                  finally show ?thesis by blast
                qed
                ultimately show ?thesis by simp
              qed
              finally have 2: "(F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D (\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) =
                               F g \<star>\<^sub>D F \<gamma>\<^sub>C"
                using D.comp_assoc by simp
              have 3: "(\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) =
                       (F g \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>C)"
              proof -
                have "D.hseq (F g) (F \<gamma>\<^sub>C)"
                  using "1" F\<beta>\<^sub>C \<beta>\<^sub>C by auto
                moreover have "D.iso (F g \<star>\<^sub>D D.inv \<phi>')"
                  by (metis "2" D.iso_hcomp D.hseqE D.ide_is_iso D.iso_inv_iso D.seqE
                      T'.ide_leg1 \<phi>' calculation)
                moreover have "D.inv (F g \<star>\<^sub>D D.inv \<phi>') = F g \<star>\<^sub>D \<phi>'"
                  by (metis D.hseqE D.ide_is_iso D.inv_hcomp D.inv_ide D.inv_inv D.iso_inv_iso
                      D.iso_is_arr T'.ide_leg1 \<phi>' calculation(2))
                ultimately show ?thesis
                  using 2 \<phi> \<phi>'
                        D.invert_side_of_triangle(1)
                          [of "F g \<star>\<^sub>D F \<gamma>\<^sub>C" "F g \<star>\<^sub>D D.inv \<phi>'"
                              "(\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>)"]
                  by auto
              qed
              hence "\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] =
                     ((F g \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>C)) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>)"
              proof -
                have "D.seq (F g \<star>\<^sub>D \<phi>') (F g \<star>\<^sub>D F \<gamma>\<^sub>C)"
                  by (metis "1" "2" "3" D.arrI D.comp_null(1) D.comp_null(2) D.ext F\<beta>\<^sub>C \<beta>\<^sub>C)
                moreover have "D.iso (F g \<star>\<^sub>D \<phi>)"
                  using D.vconn_implies_hpar(2) D.vconn_implies_hpar(4) \<phi> we by auto
                moreover have "D.inv (F g \<star>\<^sub>D \<phi>) = F g \<star>\<^sub>D D.inv \<phi>"
                  by (metis D.hseqE D.ide_is_iso D.inv_hcomp D.inv_ide D.iso_is_arr
                      T'.ide_leg1 \<phi> calculation(2))
                ultimately show ?thesis
                  using 3 \<phi> \<phi>'
                        D.invert_side_of_triangle(2)
                          [of "(F g \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>C)"
                              "\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]" "F g \<star>\<^sub>D \<phi>"]
                  by auto
              qed
              also have "... = F g \<star>\<^sub>D \<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi>"
                using \<phi>' D.whisker_left
                by (metis "1" D.arr_inv D.cod_comp D.cod_inv D.comp_assoc D.in_homE D.seqI
                    T'.ide_leg1 \<phi>)
              finally show ?thesis by simp
            qed
            have B: "\<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] =
                     \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi>)"
            proof -
              have "F \<theta>\<^sub>C' \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C)) =
                    (\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D
                      \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C)) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                using \<gamma>\<^sub>C \<theta>\<^sub>C' F\<theta>\<^sub>C'_def D.comp_assoc by auto
              also have "... = \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
              proof -
                have "(D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) = F f \<star>\<^sub>D F \<gamma>\<^sub>C"
                  using D.comp_cod_arr
                  by (metis (mono_tags, lifting) C.in_homE D.cod_comp D.comp_inv_arr' D.seqE
                      T.tab_simps(2) T.ide_leg0 \<Phi>_components_are_iso \<gamma>\<^sub>C 1 \<open>trg\<^sub>C w\<^sub>C' = src\<^sub>C \<rho>\<close>
                      \<theta>\<^sub>C preserves_arr w\<^sub>C')
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              finally have "F \<theta>\<^sub>C' \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C)) =
                            \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                              (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                by simp
              hence 3: "F \<theta>\<^sub>C' \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) =
                        \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C)"
                using \<Phi>_components_are_iso D.iso_inv_iso D.iso_is_retraction D.retraction_is_epi
                      D.epiE
                by (metis C.in_homE D.comp_assoc T.tab_simps(2) T.ide_leg0 \<gamma>\<^sub>C 1
                    \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> \<theta>\<^sub>C preserves_arr w\<^sub>C)
              hence "(\<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>)) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C)) =
                     (\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                       (F f \<star>\<^sub>D F \<gamma>\<^sub>C)) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                using 1 \<theta>\<^sub>C F\<theta>\<^sub>C_def D.comp_assoc by (metis C.in_homE \<gamma>\<^sub>C)
              hence 2: "(\<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) =
                         \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C)"
                using \<gamma>\<^sub>C \<Phi>_components_are_iso D.iso_inv_iso D.iso_is_retraction D.retraction_is_epi
                      D.epiE
                by (metis (mono_tags, lifting) 1 3 C.in_homE D.comp_assoc T.tab_simps(2)
                      T.ide_leg0 \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close> \<theta>\<^sub>C preserves_arr w\<^sub>C)
              hence "\<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] =
                     (\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e]) \<cdot>\<^sub>D
                       (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<phi>)"
              proof -
                have "D.inv (F f \<star>\<^sub>D \<phi>) = F f \<star>\<^sub>D D.inv \<phi>"
                  using \<phi>
                  by (metis C.arrI D.hseq_char D.ide_is_iso D.inv_hcomp D.inv_ide D.seqE F\<theta>\<^sub>C_def
                      T'.ide_leg0 preserves_arr \<theta>\<^sub>C)
                thus ?thesis
                  using \<phi> \<phi>' \<theta> \<theta>' \<gamma>\<^sub>C D.invert_side_of_triangle(2)
                  by (metis 2 C.arrI D.comp_assoc D.iso_hcomp D.hseqE D.ide_is_iso D.seqE
                      F\<theta>\<^sub>C_def T'.ide_leg0 \<theta>\<^sub>C preserves_arr)
              qed
              also have "... = \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D
                                (F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>C) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<phi>)"
                using D.comp_assoc by simp
              also have
                "... = \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi>)"
              proof -
                have "D.arr (\<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi>)"
                  using "1" \<phi> \<phi>' by blast
                thus ?thesis
                  using D.whisker_left by auto
              qed
              finally show ?thesis by simp
            qed
            have C: "\<guillemotleft>\<phi>' \<cdot>\<^sub>D F \<gamma>\<^sub>C \<cdot>\<^sub>D D.inv \<phi> : w \<star>\<^sub>D e \<Rightarrow>\<^sub>D w' \<star>\<^sub>D e\<guillemotright>"
              using \<phi> \<phi>' \<gamma>\<^sub>C 1 by (meson D.comp_in_homI D.inv_in_hom)
            show ?thesis
              unfolding \<gamma>e_def
              using A B C by simp
          qed
          have UN: "\<And>\<gamma>. ?P \<gamma> \<Longrightarrow> \<gamma> = \<gamma>e"
          proof -
            fix \<gamma>
            assume \<gamma>: "?P \<gamma>"
            show "\<gamma> = \<gamma>e"
            proof -
              let ?\<gamma>' = "D.inv \<phi>' \<cdot>\<^sub>D \<gamma> \<cdot>\<^sub>D \<phi>"
              have \<gamma>': "\<guillemotleft>?\<gamma>' : F w\<^sub>C \<Rightarrow>\<^sub>D F w\<^sub>C'\<guillemotright>"
                using \<gamma> \<phi> \<phi>' by auto
              obtain \<gamma>\<^sub>C' where \<gamma>\<^sub>C': "\<guillemotleft>\<gamma>\<^sub>C' : w\<^sub>C \<Rightarrow>\<^sub>C w\<^sub>C'\<guillemotright> \<and> F \<gamma>\<^sub>C' = ?\<gamma>'"
                using w\<^sub>C w\<^sub>C' \<gamma> \<gamma>' locally_full by fastforce
              have 1: "\<beta>\<^sub>C = g \<star>\<^sub>C \<gamma>\<^sub>C'"
              proof -
                have "F \<beta>\<^sub>C = F (g \<star>\<^sub>C \<gamma>\<^sub>C')"
                proof -
                  have "F \<beta>\<^sub>C =
                        \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D
                          \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                    using \<beta>\<^sub>C F\<beta>\<^sub>C_def by simp
                  have "F (g \<star>\<^sub>C \<gamma>\<^sub>C') =
                        \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>' \<cdot>\<^sub>D \<gamma> \<cdot>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                    using \<gamma>\<^sub>C' preserves_hcomp
                    by (metis C.hseqI' C.in_homE C.trg_dom T.tab_simps(2) T.leg1_simps(2)
                        T.leg1_simps(3,5-6) \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close>)
                  also have "... = \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>) \<cdot>\<^sub>D
                                     (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                    using \<phi> \<phi>' D.whisker_left D.comp_assoc
                    by (metis D.arrI D.seqE F\<beta>\<^sub>C_def T'.ide_leg1 \<gamma> \<gamma>')
                  also have "... = \<Phi> (g, w\<^sub>C') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D
                                     (\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]) \<cdot>\<^sub>D
                                     (F g \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (g, w\<^sub>C))"
                    using \<gamma> D.comp_assoc by simp
                  also have "... = F \<beta>\<^sub>C"
                    using \<beta>\<^sub>C F\<beta>\<^sub>C_def D.comp_assoc by simp
                  finally show ?thesis by simp
                qed
                moreover have "C.par \<beta>\<^sub>C (g \<star>\<^sub>C \<gamma>\<^sub>C')"
                proof (intro conjI)
                  show "C.arr \<beta>\<^sub>C"
                    using \<beta>\<^sub>C by blast
                  show 2: "C.hseq g \<gamma>\<^sub>C'"
                    using F\<beta>\<^sub>C \<beta>\<^sub>C calculation by fastforce
                  show "C.dom \<beta>\<^sub>C = C.dom (g \<star>\<^sub>C \<gamma>\<^sub>C')"
                    using 2 \<beta>\<^sub>C \<gamma>\<^sub>C' by fastforce
                  show "C.cod \<beta>\<^sub>C = C.cod (g \<star>\<^sub>C \<gamma>\<^sub>C')"
                    using 2 \<beta>\<^sub>C \<gamma>\<^sub>C' by fastforce
                qed
                ultimately show ?thesis using is_faithful by blast
              qed
              have 2: "\<theta>\<^sub>C = \<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C')"
              proof -
                have "F \<theta>\<^sub>C = F (\<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C'))"
                proof -
                  have "F (\<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C')) = F \<theta>\<^sub>C' \<cdot>\<^sub>D F (f \<star>\<^sub>C \<gamma>\<^sub>C')"
                    using \<theta>\<^sub>C' \<gamma>\<^sub>C' by force
                  also have
                    "... = F \<theta>\<^sub>C' \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<phi>' \<cdot>\<^sub>D \<gamma> \<cdot>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                    using w\<^sub>C w\<^sub>C' \<theta>\<^sub>C' \<gamma>\<^sub>C' preserves_hcomp
                    by (metis C.hseqI' C.in_homE C.trg_dom T.tab_simps(2) T.leg0_simps(2)
                        T.leg0_simps(4-5) \<open>trg\<^sub>C w\<^sub>C = src\<^sub>C \<rho>\<close>)
                  also have "... = F \<theta>\<^sub>C' \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C') \<cdot>\<^sub>D
                                     ((F f \<star>\<^sub>D D.inv \<phi>') \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>)) \<cdot>\<^sub>D
                                     D.inv (\<Phi> (f, w\<^sub>C))"
                    using D.whisker_left
                    by (metis D.arrI D.seqE T'.ide_leg0 \<gamma>')
                  also have "... = \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (((F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D
                                     (D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D
                                     (F f \<star>\<^sub>D \<gamma>)) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                    using \<theta>\<^sub>C' F\<theta>\<^sub>C'_def D.comp_assoc by simp
                  also have "... = (\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>)) \<cdot>\<^sub>D
                                     (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                  proof -
                    have "D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C') = F f \<star>\<^sub>D F w\<^sub>C'"
                      using w\<^sub>C' \<Phi>_in_hom \<Phi>_components_are_iso
                      by (simp add: D.comp_inv_arr')
                    moreover have "D.hseq (F f) (D.inv \<phi>')"
                      using \<phi>' D.hseqI'
                      by (metis D.ide_is_iso D.in_hhom_def D.iso_inv_iso D.iso_is_arr
                          D.trg_inv D.vconn_implies_hpar(2) D.vconn_implies_hpar(4)
                          T'.ide_leg0 T'.leg1_simps(3) T.leg1_simps(2-3)
                          T.tab_simps(2) \<gamma> preserves_src we)
                    ultimately have "(D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<phi>') =
                                     F f \<star>\<^sub>D D.inv \<phi>'"
                      using w\<^sub>C' \<phi>' D.comp_cod_arr [of "F f \<star>\<^sub>D D.inv \<phi>'" "F f \<star>\<^sub>D F w\<^sub>C'"]
                      by fastforce
                    hence "((F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D
                             (F f \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>) =
                           ((F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>)"
                      by simp
                    also have "... = F f \<star>\<^sub>D \<gamma>"
                      using \<gamma> \<phi>' \<theta>\<^sub>C' F\<theta>\<^sub>C'_def D.comp_cod_arr D.whisker_left D.hseqI'
                      by (metis D.comp_arr_inv' D.in_hhom_def D.in_homE T'.ide_leg0 w'e)
                    finally have "((F f \<star>\<^sub>D \<phi>') \<cdot>\<^sub>D (D.inv (\<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D \<Phi> (f, w\<^sub>C')) \<cdot>\<^sub>D
                                    (F f \<star>\<^sub>D D.inv \<phi>')) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>) =
                                  F f \<star>\<^sub>D \<gamma>"
                      by simp
                    thus ?thesis
                      using D.comp_assoc by simp
                  qed
                  also have "... = \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<cdot>\<^sub>D
                                     (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w\<^sub>C))"
                    using \<gamma> D.comp_assoc by metis
                  also have "... = F \<theta>\<^sub>C"
                    using \<theta>\<^sub>C F\<theta>\<^sub>C_def by simp
                  finally show ?thesis by simp
                qed
                moreover have "C.par \<theta>\<^sub>C (\<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C'))"
                proof (intro conjI)
                  show "C.arr \<theta>\<^sub>C"
                    using \<theta>\<^sub>C by auto
                  show 1: "C.seq \<theta>\<^sub>C' (f \<star>\<^sub>C \<gamma>\<^sub>C')"
                    using \<theta>\<^sub>C' \<gamma>\<^sub>C'
                    by (metis C.arrI \<theta>\<^sub>C calculation preserves_reflects_arr)
                  show "C.dom \<theta>\<^sub>C = C.dom (\<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C'))"
                    using 1 \<theta>\<^sub>C \<gamma>\<^sub>C' by fastforce
                  show "C.cod \<theta>\<^sub>C = C.cod (\<theta>\<^sub>C' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>C'))"
                    using 1 \<theta>\<^sub>C \<gamma>\<^sub>C' \<gamma>\<^sub>C by auto
                qed
                ultimately show ?thesis
                  using is_faithful by blast
              qed
              have "F \<gamma>\<^sub>C' = F \<gamma>\<^sub>C"
                using ** \<gamma>\<^sub>C \<gamma>\<^sub>C' 1 2 by blast
              hence "?\<gamma>' = F \<gamma>\<^sub>C"
                using \<gamma>\<^sub>C' by simp
              thus "\<gamma> = \<gamma>e"
                unfolding \<gamma>e_def
                by (metis D.arrI D.comp_assoc D.inv_inv D.invert_side_of_triangle(1)
                    D.invert_side_of_triangle(2) D.iso_inv_iso \<gamma>' \<phi> \<phi>')
            qed
          qed

          text \<open>We are now in a position to exhibit the 2-cell \<open>\<gamma>\<close> and show that it
          is unique with the required properties.\<close>

          show ?thesis
          proof
            let ?\<gamma> = "\<r>\<^sub>D[w'] \<cdot>\<^sub>D (w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[w', e, d] \<cdot>\<^sub>D (\<gamma>e \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D
                        (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
            have \<gamma>: "\<guillemotleft>?\<gamma> : w \<Rightarrow>\<^sub>D w'\<guillemotright>"
              using P\<gamma>e w w' e.counit_in_hom(2) e.counit_is_iso
              apply (intro D.comp_in_homI)
                    apply auto[2]
                   apply fastforce
                  apply auto[3]
                apply fastforce
              by auto
            moreover have "\<beta> = F g \<star>\<^sub>D ?\<gamma>"
            proof -
              have "F g \<star>\<^sub>D ?\<gamma> =
                    (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D (F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                      (F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) \<cdot>\<^sub>D
                      (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using w w' \<gamma> P\<gamma>e D.whisker_left e.antipar
                by (metis D.arrI D.seqE T'.ide_leg1)
              also have "... =
                         (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D (F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F g \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F g \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d] =
                      \<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                  using w w' e.antipar P\<gamma>e D.assoc'_naturality [of "F g" \<gamma>e d]
                  by (metis D.dom_trg D.ideD(1-3) D.in_hhomE D.in_homE
                      D.src_dom D.trg.preserves_dom T'.leg1_simps(2) T'.leg1_simps(3,5-6)
                      T.tab_simps(2) T.leg0_simps(2) e e.ide_right preserves_src we)
                also have
                  "... = (\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                  using D.comp_assoc by simp
                also have "... = F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                proof -
                  have "(\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) =
                        (F g \<star>\<^sub>D (w' \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                    using w'e D.isomorphic_implies_ide(2) w\<^sub>C' D.comp_assoc_assoc'(1) by auto
                  also have "... = F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                  proof -
                    have "\<guillemotleft>F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d : F g \<star>\<^sub>D (w \<star>\<^sub>D e) \<star>\<^sub>D d \<Rightarrow>\<^sub>D F g \<star>\<^sub>D (w' \<star>\<^sub>D e) \<star>\<^sub>D d\<guillemotright>"
                      using we e.ide_right e.antipar P\<gamma>e by fastforce
                    thus ?thesis
                      using D.comp_cod_arr by auto
                  qed
                  finally show ?thesis by blast
                qed
                finally have
                  "\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F g \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d] =
                   F g \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                  by simp
                thus ?thesis by simp
              qed
              also have "... =
                         (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D (F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D
                           (\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using P\<gamma>e by simp
              also have
                "... =
                 (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D (F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D
                   (F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (\<a>\<^sub>D[F g, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                   ((\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                   (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                   (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d =
                      (\<a>\<^sub>D[F g, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D ((\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d)"
                proof -
                  have "D.arr (\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e])"
                    using D.arrI D.in_hhom_def D.vconn_implies_hpar(2) P\<gamma>e we by auto
                  thus ?thesis
                    using D.whisker_right by auto
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... =
                 (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D (F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D
                   ((F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (\<a>\<^sub>D[F g, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                   (\<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w', e, d]) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D[F g \<star>\<^sub>D w, e, d]) \<cdot>\<^sub>D 
                   (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d])) \<cdot>\<^sub>D
                   (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d =
                      \<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w', e, d] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D[F g \<star>\<^sub>D w, e, d]"
                proof -
                  have "src\<^sub>D \<beta> = trg\<^sub>D e"
                    using \<beta>
                    by (metis D.dom_trg D.hseq_char' D.in_homE D.src_dom D.src_hcomp
                        D.trg.is_extensional D.trg.preserves_arr D.trg.preserves_dom
                        \<open>trg\<^sub>D e = a\<close> a_def)
                  moreover have "src\<^sub>D (F g) = trg\<^sub>D w"
                    by simp
                  moreover have "src\<^sub>D (F g) = trg\<^sub>D w'"
                    by simp
                  moreover have
                    "\<guillemotleft>(\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d : ((F g \<star>\<^sub>D w) \<star>\<^sub>D e) \<star>\<^sub>D d \<Rightarrow>\<^sub>D ((F g \<star>\<^sub>D w') \<star>\<^sub>D e) \<star>\<^sub>D d\<guillemotright>"
                    using \<beta> w w' e e.antipar
                    by (intro D.hcomp_in_vhom, auto)
                  ultimately have
                    "\<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w', e, d] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D[F g \<star>\<^sub>D w, e, d] =
                     \<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w', e, d] \<cdot>\<^sub>D \<a>\<^sub>D[F g \<star>\<^sub>D w', e, d] \<cdot>\<^sub>D ((\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d)"
                    using w' e e.ide_left e.ide_right e.antipar \<beta> D.assoc'_naturality
                    by (metis D.assoc_naturality D.in_homE e.triangle_equiv_form(1)
                              e.triangle_in_hom(3) e.triangle_in_hom(4) e.triangle_right
                              e.triangle_right' e.triangle_right_implies_left)
                  also have
                    "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w', e, d] \<cdot>\<^sub>D \<a>\<^sub>D[F g \<star>\<^sub>D w', e, d]) \<cdot>\<^sub>D ((\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d)"
                    using D.comp_assoc by simp
                  also have "... = (((F g \<star>\<^sub>D w') \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D ((\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d)"
                    using w' e e.antipar \<beta> D.comp_assoc_assoc' by simp
                  also have "... = (\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d"
                  proof -
                    have "\<guillemotleft>(\<beta> \<star>\<^sub>D e) \<star>\<^sub>D d : ((F g \<star>\<^sub>D w) \<star>\<^sub>D e) \<star>\<^sub>D d \<Rightarrow>\<^sub>D ((F g \<star>\<^sub>D w') \<star>\<^sub>D e) \<star>\<^sub>D d\<guillemotright>"
                      using w e e.antipar \<beta>
                      by (intro D.hcomp_in_vhom, auto)
                    thus ?thesis
                      using D.comp_cod_arr by auto
                  qed
                  finally show ?thesis by simp
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D ((F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e \<star>\<^sub>D d]) \<cdot>\<^sub>D
                         (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e \<star>\<^sub>D d] \<cdot>\<^sub>D (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (\<a>\<^sub>D[F g, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w', e, d] =
                      \<a>\<^sub>D[F g, w', e \<star>\<^sub>D d]"
                proof -
                  have "D.seq (F g \<star>\<^sub>D \<a>\<^sub>D[w', e, d])
                              (\<a>\<^sub>D[F g, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (\<a>\<^sub>D[F g, w', e] \<star>\<^sub>D d))"
                    using w w' e e.antipar by simp
                  thus ?thesis
                    using w w' e e.antipar D.pentagon [of "F g" w' e d] D.invert_side_of_triangle(2)
                          D.assoc'_eq_inv_assoc D.comp_assoc D.ide_hcomp D.ideD(1)
                          D.iso_assoc D.hcomp_simps(1) T'.ide_leg1 T.leg1_simps(2-3)
                          T.tab_simps(2) \<open>src\<^sub>D w' = a\<close> \<open>trg\<^sub>D e = a\<close> \<open>trg\<^sub>D w' = map\<^sub>0 (src\<^sub>C \<rho>)\<close>
                          e.ide_left e.ide_right preserves_src
                    by metis
                qed
                moreover have
                  "\<a>\<^sub>D[F g \<star>\<^sub>D w, e, d] \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D
                     (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) =
                   \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e \<star>\<^sub>D d]"
                proof -
                  have "D.seq (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] \<star>\<^sub>D d)
                              (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]))"
                    using w w' e e.antipar by simp
                  moreover have "D.inv \<a>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w, e, d] = \<a>\<^sub>D[F g \<star>\<^sub>D w, e, d]"
                    using w w' e e.antipar D.iso_inv_iso D.inv_inv by simp
                  ultimately show ?thesis
                    using w w' e e.antipar D.pentagon' [of "F g" w e d]
                          D.iso_inv_iso D.inv_inv D.comp_assoc D.invert_side_of_triangle(1)
                    by (metis D.assoc'_simps(3) D.comp_null(2) D.ide_hcomp D.ideD(1)
                        D.iso_assoc' D.not_arr_null D.seq_if_composable D.src_hcomp T'.ide_leg1
                        \<open>trg\<^sub>D e = a\<close> a_def e.ide_left e.ide_right)
                qed
                ultimately show ?thesis
                  using w w' e e.antipar \<beta> D.comp_assoc by metis
              qed
              also have "... = (F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', trg\<^sub>D e] \<cdot>\<^sub>D
                                 (((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D ((F g \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, trg\<^sub>D e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(F g \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', e \<star>\<^sub>D d] =
                      \<a>\<^sub>D[F g, w', trg\<^sub>D e] \<cdot>\<^sub>D ((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>)"
                  using w' e e.antipar D.assoc_naturality [of "F g" w' \<epsilon>] by simp
                moreover have "\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e \<star>\<^sub>D d] \<cdot>\<^sub>D (F g \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) =
                               ((F g \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, trg\<^sub>D e]"
                 using w e e.antipar D.assoc'_naturality [of "F g" w "D.inv \<epsilon>"]
                        e.counit_is_iso e.counit_in_hom
                  by simp
                ultimately show ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = ((F g \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D \<a>\<^sub>D[F g, w', trg\<^sub>D e]) \<cdot>\<^sub>D
                                (\<beta> \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D
                                 (\<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, trg\<^sub>D e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]))"
              proof -
                have "((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D ((F g \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>) =
                      \<beta> \<star>\<^sub>D trg\<^sub>D e"
               proof -
                  have "((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D ((F g \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>) =
                        ((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D D.inv \<epsilon>)"
                    using w w' e e.antipar D.interchange [of \<beta> "F g \<star>\<^sub>D w" "e \<star>\<^sub>D d" "D.inv \<epsilon>"]
                          D.comp_arr_dom D.comp_cod_arr e.counit_is_iso
                    by (metis D.in_homE \<beta> d.unit_simps(1) d.unit_simps(3))
                  also have "... = ((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((F g \<star>\<^sub>D w') \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D trg\<^sub>D e)"
                    using w w' e e.antipar \<beta> D.interchange [of "F g \<star>\<^sub>D w'" \<beta> "D.inv \<epsilon>" "trg\<^sub>D e"]
                          D.comp_arr_dom D.comp_cod_arr e.counit_is_iso
                    by auto
                  also have
                    "... = (((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((F g \<star>\<^sub>D w') \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D trg\<^sub>D e)"
                    using D.comp_assoc by simp
                  also have "... = ((F g \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon> \<cdot>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D trg\<^sub>D e)"
                    using w' D.whisker_left [of "F g \<star>\<^sub>D w'"] by simp
                  also have "... = ((F g \<star>\<^sub>D w') \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D trg\<^sub>D e)"
                    by (simp add: D.comp_arr_inv')
                  also have "... = \<beta> \<star>\<^sub>D trg\<^sub>D e"
                    using \<beta> D.comp_cod_arr D.hseqI'
                    by (metis D.cod_cod D.hcomp_simps(1) D.hcomp_simps(4)
                        D.in_homE D.trg.preserves_reflects_arr D.vconn_implies_hpar(1)
                        D.vconn_implies_hpar(2) D.vconn_implies_hpar(3) D.vconn_implies_hpar(4)
                        \<open>src\<^sub>D w' = a\<close> \<open>trg\<^sub>D e = a\<close> e.counit_in_hom(2) e.counit_simps(5))
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[F g \<star>\<^sub>D w'] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w]"
                using w w' D.runit_hcomp D.runit_hcomp [of "F g" w] by simp
              also have "... = \<r>\<^sub>D[F g \<star>\<^sub>D w'] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w'] \<cdot>\<^sub>D \<beta>"
                using \<beta> D.runit'_naturality
                by (metis D.arr_cod D.arr_dom D.cod_dom D.in_homE D.src.preserves_cod
                  D.src_dom D.src_hcomp \<open>src\<^sub>D w' = a\<close> \<open>trg\<^sub>D e = a\<close>)
              also have "... = (\<r>\<^sub>D[F g \<star>\<^sub>D w'] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D w']) \<cdot>\<^sub>D \<beta>"
                using D.comp_assoc by simp
              also have "... = \<beta>"
                using w' \<beta> D.comp_cod_arr D.comp_arr_inv' D.iso_runit by auto
              finally show ?thesis by simp
            qed
            moreover have "\<theta> = \<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D ?\<gamma>)"
            proof -
              have "\<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D ?\<gamma>) =
                    \<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D[w']) \<cdot>\<^sub>D (F f \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                      (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) \<cdot>\<^sub>D
                      (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                 using w \<theta> \<gamma> D.whisker_left
                 by (metis D.arrI D.seqE T'.ide_leg0)
              also have
                "... = (\<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D[w'])) \<cdot>\<^sub>D (F f \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have 1: "\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] =
                         \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                  using w w' e we w'e e.antipar P\<gamma>e D.assoc'_naturality [of "F f" \<gamma>e d]
                  by (metis D.cod_trg D.in_hhomE D.in_homE D.src_cod D.trg.preserves_cod
                      T'.leg0_simps(2,4-5) T.tab_simps(2) T.leg0_simps(2)
                      e.triangle_in_hom(4) e.triangle_right' preserves_src)
                also have
                  2: "... = (\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                  using D.comp_assoc by simp
                also have "... = F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                proof -
                  have "(\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) =
                        (F f \<star>\<^sub>D (w' \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                    using 1 2 e.antipar D.isomorphic_implies_ide(2) w\<^sub>C' w'e D.comp_assoc_assoc'
                    by auto
                  also have "... = F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                  proof -
                    have "\<guillemotleft>F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d : F f \<star>\<^sub>D (w \<star>\<^sub>D e) \<star>\<^sub>D d \<Rightarrow>\<^sub>D F f \<star>\<^sub>D (w' \<star>\<^sub>D e) \<star>\<^sub>D d\<guillemotright>"
                      using we 1 2 e.antipar P\<gamma>e by fastforce
                    thus ?thesis
                      using D.comp_cod_arr by blast
                  qed
                  finally show ?thesis by blast
                qed
                finally have
                  "\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]) =
                   F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                  by simp
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = ((\<theta>' \<cdot>\<^sub>D \<r>\<^sub>D[F f \<star>\<^sub>D w']) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', src\<^sub>D w']) \<cdot>\<^sub>D (F f \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D (\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using w' D.runit_hcomp(3) [of "F f" w'] D.comp_assoc by simp
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D src\<^sub>D w') \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', src\<^sub>D w'] \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w' \<star>\<^sub>D \<epsilon>)) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                                 (\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using \<theta>' D.runit_naturality [of \<theta>'] D.comp_assoc by fastforce
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D ((\<theta>' \<star>\<^sub>D src\<^sub>D w') \<cdot>\<^sub>D ((F f \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e \<star>\<^sub>D d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using w' D.assoc'_naturality [of "F f" w' \<epsilon>] D.comp_assoc by simp
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e \<star>\<^sub>D d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                                 (\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<theta>' \<star>\<^sub>D src\<^sub>D w') \<cdot>\<^sub>D ((F f \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) = \<theta>' \<star>\<^sub>D \<epsilon>"
                  using D.interchange D.comp_arr_dom D.comp_cod_arr
                  by (metis D.in_homE \<open>src\<^sub>D w' = a\<close> \<open>trg\<^sub>D e = a\<close> \<theta>' e.counit_simps(1)
                      e.counit_simps(3))
                also have "... = (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d)"
                  using \<theta>' D.interchange [of u \<theta>' \<epsilon> "e \<star>\<^sub>D d"] D.comp_arr_dom D.comp_cod_arr
                  by auto
                finally have "(\<theta>' \<star>\<^sub>D src\<^sub>D w') \<cdot>\<^sub>D ((F f \<star>\<^sub>D w') \<star>\<^sub>D \<epsilon>) = (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d)"
                  by simp
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e \<star>\<^sub>D d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) \<cdot>\<^sub>D ((\<a>\<^sub>D[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d])) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) =
                      (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D[F f, w \<star>\<^sub>D e, d]"
                  using D.assoc_naturality [of "F f" \<gamma>e d]
                  by (metis D.cod_trg D.in_hhomE D.in_homE D.src_cod D.trg.preserves_cod P\<gamma>e
                      T'.leg0_simps(2,4-5) T.tab_simps(2) T.leg0_simps(2) e e.antipar(1)
                      e.triangle_in_hom(4) e.triangle_right' preserves_src w'e)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e \<star>\<^sub>D d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<a>\<^sub>D[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) =
                      F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]"
                  using w D.comp_cod_arr D.comp_assoc_assoc' by simp
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e \<star>\<^sub>D d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D
                         ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d =
                      \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d]"
                proof -
                  have "\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] =
                        \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                    using P\<gamma>e e.antipar D.assoc'_naturality
                    by (metis D.in_hhom_def D.in_homE D.vconn_implies_hpar(1)
                        D.vconn_implies_hpar(2) T'.leg0_simps(2,4-5)
                        T.leg0_simps(2) T.tab_simps(2) \<open>src\<^sub>D e = map\<^sub>0 a\<^sub>C\<close>
                        d.triangle_equiv_form(1) d.triangle_in_hom(3) d.triangle_left
                        preserves_src we)
                  also have
                    "... = (\<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                    using D.comp_assoc by simp
                  also have "... = (F f \<star>\<^sub>D (w' \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d)"
                    using w'e D.isomorphic_implies_ide(2) w\<^sub>C' D.comp_assoc_assoc' by auto
                  also have "... = F f \<star>\<^sub>D \<gamma>e \<star>\<^sub>D d"
                    using D.comp_cod_arr
                    by (metis D.comp_cod_arr D.comp_null(2) D.hseq_char D.hseq_char'
                        D.in_homE D.whisker_left D.whisker_right P\<gamma>e T'.ide_leg0 e.ide_right)
                  finally show ?thesis by simp
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F f \<star>\<^sub>D w', e, d]) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e \<star>\<^sub>D d]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d] =
                      \<a>\<^sub>D[F f \<star>\<^sub>D w', e, d] \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<star>\<^sub>D d)"
                proof -
                  have "\<a>\<^sub>D[F f, w', e \<star>\<^sub>D d] \<cdot>\<^sub>D \<a>\<^sub>D[F f \<star>\<^sub>D w', e, d] =
                        ((F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d]) \<cdot>\<^sub>D (\<a>\<^sub>D[F f, w', e] \<star>\<^sub>D d)"
                    using w' D.pentagon D.comp_assoc by simp
                  moreover have "D.seq \<a>\<^sub>D[F f, w', e \<star>\<^sub>D d] \<a>\<^sub>D[F f \<star>\<^sub>D w', e, d]"
                    using w' by simp
                  moreover have "D.inv (\<a>\<^sub>D[F f, w', e] \<star>\<^sub>D d) = \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<star>\<^sub>D d"
                    using w' by simp
                  ultimately show ?thesis
                    using w' D.comp_assoc
                          D.invert_opposite_sides_of_square
                            [of "\<a>\<^sub>D[F f, w', e \<star>\<^sub>D d]" "\<a>\<^sub>D[F f \<star>\<^sub>D w', e, d]"
                                "(F f \<star>\<^sub>D \<a>\<^sub>D[w', e, d]) \<cdot>\<^sub>D \<a>\<^sub>D[F f, w' \<star>\<^sub>D e, d]"
                                "\<a>\<^sub>D[F f, w', e] \<star>\<^sub>D d"]
                    by simp
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have
                "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D
                         (((\<theta>' \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<theta>' \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D[F f \<star>\<^sub>D w', e, d] = \<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D ((\<theta>' \<star>\<^sub>D e) \<star>\<^sub>D d)"
                  using w' \<theta>' e.ide_left e.ide_right e.antipar D.assoc_naturality [of \<theta>' e d]
                  by auto
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D
                                 ((\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "((\<theta>' \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<star>\<^sub>D d) \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d) =
                       (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e) \<star>\<^sub>D d"
                  using w' w'e \<theta>' \<theta>\<^sub>C e.ide_left e.ide_right e.antipar D.whisker_right
                  by (metis (full_types) C.arrI D.cod_comp D.seqE D.seqI F\<theta>\<^sub>C_def P\<gamma>e
                      preserves_arr)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D
                                 ((\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e) =
                      \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                  using P\<gamma>e by simp
                moreover have "D.arr (\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e))"
                  by (metis C.in_homE D.comp_assoc D.comp_null(1) D.ext F\<theta>\<^sub>C_def P\<gamma>e \<theta>\<^sub>C
                      preserves_arr)
                moreover have "D.arr (\<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e])"
                  using P\<gamma>e calculation(2) by auto
                ultimately have "(\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>e) =
                                 (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                  using \<psi> \<theta>\<^sub>C F\<theta>\<^sub>C_def D.iso_is_section D.section_is_mono
                  by (metis D.monoE)
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D
                                 ((\<theta> \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D ((\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<star>\<^sub>D d) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w \<star>\<^sub>D e, d] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d])) \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<star>\<^sub>D d =
                      ((\<theta> \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] \<star>\<^sub>D d)"
                proof -
                  have "D.arr ((\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e])"
                    by (metis C.arrI D.cod_comp D.seqE D.seqI F\<theta>\<^sub>C_def \<theta>\<^sub>C preserves_arr)
                  thus ?thesis
                    using D.whisker_right e.ide_right by blast
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D
                                 (((\<theta> \<star>\<^sub>D e) \<star>\<^sub>D d) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f \<star>\<^sub>D w, e, d]) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e \<star>\<^sub>D d] \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using w D.pentagon' D.comp_assoc by simp
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((\<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[u, e, d]) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e \<star>\<^sub>D d] \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using \<theta> e.antipar D.assoc'_naturality [of \<theta> e d] D.comp_assoc by fastforce
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e \<star>\<^sub>D d] \<cdot>\<^sub>D
                                 (F f \<star>\<^sub>D w \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(\<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u, e, d]) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d) = \<theta> \<star>\<^sub>D e \<star>\<^sub>D d"
                proof -
                  have "(\<a>\<^sub>D[u, e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[u, e, d]) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d) =
                        (u \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d)"
                    using \<theta> ue e.ide_left e.ide_right e.antipar D.comp_arr_inv' D.comp_cod_arr
                    by auto
                  also have "... = \<theta> \<star>\<^sub>D e \<star>\<^sub>D d"
                    using ue e.ide_left e.ide_right e.antipar D.hcomp_simps(4) D.hseq_char' \<theta>
                          D.comp_cod_arr [of "\<theta> \<star>\<^sub>D e \<star>\<^sub>D d" "u \<star>\<^sub>D e \<star>\<^sub>D d"]
                    by force
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D ((u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d)) \<cdot>\<^sub>D ((F f \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
                using w e.antipar D.assoc'_naturality [of "F f" w "D.inv \<epsilon>"] D.comp_assoc by simp
              also have
                "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D (((F f \<star>\<^sub>D w) \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((F f \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e]) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(u \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e \<star>\<^sub>D d) = (\<theta> \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D ((F f \<star>\<^sub>D w) \<star>\<^sub>D \<epsilon>)"
                  using \<theta> e.antipar D.interchange D.comp_arr_dom D.comp_cod_arr
                  by (metis D.in_homE \<open>trg\<^sub>D e = a\<close> e.counit_simps(1-3,5))
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = \<r>\<^sub>D[u] \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w])"
              proof -
                have "(((F f \<star>\<^sub>D w) \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((F f \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e] =
                      \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e]"
                proof -
                  have "(((F f \<star>\<^sub>D w) \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D ((F f \<star>\<^sub>D w) \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e] =
                        ((F f \<star>\<^sub>D w) \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e]"
                    using w e.ide_left e.ide_right e.antipar e.counit_is_iso D.comp_arr_inv'
                          D.comp_assoc D.whisker_left
                    by (metis D.ide_hcomp D.seqI' T'.ide_leg0 T'.leg1_simps(3)
                        T.leg1_simps(2-3) T.tab_simps(2) \<open>trg\<^sub>D w = map\<^sub>0 (src\<^sub>C \<rho>)\<close>
                        d.unit_in_vhom e.counit_in_hom(2) e.counit_simps(3) preserves_src)
                  also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, trg\<^sub>D e]"
                    using w D.comp_cod_arr D.assoc'_in_hom(2) [of "F f" w "trg\<^sub>D e"]
                          \<open>trg\<^sub>D e = a\<close> \<open>trg\<^sub>D w = map\<^sub>0 (src\<^sub>C \<rho>)\<close>
                    by (metis D.assoc'_is_natural_1 D.ideD(1) D.ideD(2) D.trg.preserves_ide
                        D.trg_trg T'.leg0_simps(2,4) T'.leg1_simps(3)
                        T.leg1_simps(2-3) T.tab_simps(2) a_def e.ide_left
                        preserves_src)
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using D.comp_assoc by simp
              qed
              also have "... = (\<r>\<^sub>D[u] \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D trg\<^sub>D e)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f \<star>\<^sub>D w]"
                using w D.runit_hcomp(2) [of "F f" w] D.comp_assoc by simp
              also have 1: "... = (\<theta> \<cdot>\<^sub>D \<r>\<^sub>D[F f \<star>\<^sub>D w]) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f \<star>\<^sub>D w]"
                using \<theta> D.runit_naturality [of \<theta>] by auto
              also have "... = \<theta>"
                using w \<theta> D.comp_arr_dom D.comp_assoc
                by (metis D.hcomp_arr_obj(2) D.in_homE D.obj_src 1 \<open>src\<^sub>D \<theta> = a\<close> \<open>trg\<^sub>D e = a\<close>)
              finally show ?thesis by simp
            qed
            ultimately show "\<guillemotleft>?\<gamma> : w \<Rightarrow>\<^sub>D w'\<guillemotright> \<and> \<beta> = F g \<star>\<^sub>D ?\<gamma> \<and> \<theta> = \<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D ?\<gamma>)"
              by simp

            show "\<And>\<gamma>'. \<guillemotleft>\<gamma>' : w \<Rightarrow>\<^sub>D w'\<guillemotright> \<and> \<beta> = F g \<star>\<^sub>D \<gamma>' \<and> \<theta> = \<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>') \<Longrightarrow> \<gamma>' = ?\<gamma>"
            proof -
              fix \<gamma>'
              assume \<gamma>': "\<guillemotleft>\<gamma>' : w \<Rightarrow>\<^sub>D w'\<guillemotright> \<and> \<beta> = F g \<star>\<^sub>D \<gamma>' \<and> \<theta> = \<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>')"
              show "\<gamma>' = ?\<gamma>"
              proof -
                have "?\<gamma> = \<r>\<^sub>D[w'] \<cdot>\<^sub>D (w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<a>\<^sub>D[w', e, d] \<cdot>\<^sub>D ((\<gamma>' \<star>\<^sub>D e) \<star>\<^sub>D d)) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                proof -
                  have "\<gamma>e = \<gamma>' \<star>\<^sub>D e"
                  proof -
                    have "\<guillemotleft>\<gamma>' \<star>\<^sub>D e : w \<star>\<^sub>D e \<Rightarrow>\<^sub>D w' \<star>\<^sub>D e\<guillemotright>"
                      using \<gamma>' by (intro D.hcomp_in_vhom, auto)
                    moreover have
                      "\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] = F g \<star>\<^sub>D \<gamma>' \<star>\<^sub>D e"
                    proof -
                      have "\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D (\<beta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e] =
                            \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D ((F g \<star>\<^sub>D \<gamma>') \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w, e]"
                        using \<gamma>' by simp
                      also have "... = \<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w', e] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>' \<star>\<^sub>D e)"
                        using \<gamma>' D.assoc_naturality
                        by (metis D.assoc'_naturality D.hcomp_in_vhomE D.ideD(2) D.ideD(3)
                            D.in_homE T'.leg1_simps(5-6) \<beta>
                            \<open>\<guillemotleft>\<gamma>' \<star>\<^sub>D e : w \<star>\<^sub>D e \<Rightarrow>\<^sub>D w' \<star>\<^sub>D e\<guillemotright>\<close> e.ide_left)
                      also have "... = (\<a>\<^sub>D[F g, w', e] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, w', e]) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>' \<star>\<^sub>D e)"
                        using D.comp_assoc by simp
                      also have "... = F g \<star>\<^sub>D \<gamma>' \<star>\<^sub>D e"
                        by (metis D.hcomp_reassoc(2) D.in_homE D.not_arr_null D.seq_if_composable
                            T'.leg1_simps(2,5-6) \<beta> \<gamma>' calculation
                            \<open>\<guillemotleft>\<gamma>' \<star>\<^sub>D e : w \<star>\<^sub>D e \<Rightarrow>\<^sub>D w' \<star>\<^sub>D e\<guillemotright>\<close> e.triangle_equiv_form(1)
                            e.triangle_in_hom(3) e.triangle_right e.triangle_right_implies_left)
                      finally show ?thesis by simp
                    qed
                    moreover have "\<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e] =
                                   \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>' \<star>\<^sub>D e)"
                    proof -
                      have "\<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w', e] \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>' \<star>\<^sub>D e) =
                            \<psi> \<cdot>\<^sub>D (\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>') \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                        using \<gamma>' \<theta> e.ide_left D.assoc'_naturality
                        by (metis D.hcomp_in_vhomE D.ideD(2) D.ideD(3) D.in_homE
                            T'.leg0_simps(2,4-5) T'.leg1_simps(3) \<beta> calculation(1))
                      also have "... = \<psi> \<cdot>\<^sub>D ((\<theta>' \<star>\<^sub>D e) \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<gamma>') \<star>\<^sub>D e)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                        using D.comp_assoc by simp
                      also have "... = \<psi> \<cdot>\<^sub>D (\<theta>' \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>') \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                        using D.whisker_right \<gamma>' \<theta> by auto
                      also have "... = \<psi> \<cdot>\<^sub>D (\<theta> \<star>\<^sub>D e) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, w, e]"
                        using \<gamma>' by simp
                      finally show ?thesis by simp
                    qed
                    ultimately show ?thesis
                      using UN by simp
                  qed
                  thus ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<r>\<^sub>D[w'] \<cdot>\<^sub>D ((w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<gamma>' \<star>\<^sub>D e \<star>\<^sub>D d)) \<cdot>\<^sub>D \<a>\<^sub>D[w, e, d] \<cdot>\<^sub>D
                                   \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                  using w' \<gamma>' D.comp_assoc D.assoc_naturality
                  by (metis D.in_homE D.src_dom \<open>trg\<^sub>D e = a\<close> a_def e.antipar(1)
                      e.triangle_equiv_form(1) e.triangle_in_hom(3-4)
                      e.triangle_right e.triangle_right' e.triangle_right_implies_left)
                also have "... = (\<r>\<^sub>D[w'] \<cdot>\<^sub>D (\<gamma>' \<star>\<^sub>D trg\<^sub>D e)) \<cdot>\<^sub>D (w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[w, e, d] \<cdot>\<^sub>D
                                   \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                proof -
                  have "(w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<gamma>' \<star>\<^sub>D e \<star>\<^sub>D d) = \<gamma>' \<star>\<^sub>D \<epsilon>"
                    using w' \<gamma>' e.antipar D.comp_arr_dom D.comp_cod_arr
                          D.interchange [of w' \<gamma>' \<epsilon> "e \<star>\<^sub>D d"]
                    by auto
                  also have "... = (\<gamma>' \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D (w \<star>\<^sub>D \<epsilon>)"
                    using w \<gamma>' e.antipar D.comp_arr_dom D.comp_cod_arr D.interchange
                    by (metis D.in_homE \<open>trg\<^sub>D e = a\<close> e.counit_simps(1) e.counit_simps(3,5))
                  finally have "(w' \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<gamma>' \<star>\<^sub>D e \<star>\<^sub>D d) = (\<gamma>' \<star>\<^sub>D trg\<^sub>D e) \<cdot>\<^sub>D (w \<star>\<^sub>D \<epsilon>)"
                    by simp
                  thus ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<gamma>' \<cdot>\<^sub>D \<r>\<^sub>D[w] \<cdot>\<^sub>D (w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[w, e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D
                                   (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                  using \<gamma>' D.runit_naturality D.comp_assoc
                  by (metis D.in_homE D.src_dom \<open>trg\<^sub>D e = a\<close> a_def)
                also have "... = \<gamma>'"
                proof -
                  have "\<r>\<^sub>D[w] \<cdot>\<^sub>D (w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[w, e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D
                          \<r>\<^sub>D\<^sup>-\<^sup>1[w] =
                        \<r>\<^sub>D[w] \<cdot>\<^sub>D ((w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (\<a>\<^sub>D[w, e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d]) \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D
                          \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                    using D.comp_assoc by simp
                  also have "... = \<r>\<^sub>D[w] \<cdot>\<^sub>D ((w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (w \<star>\<^sub>D e \<star>\<^sub>D d) \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D
                                     \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                    using w \<gamma> e.ide_left e.ide_right we e.antipar D.comp_assoc_assoc'(1)
                          \<open>trg\<^sub>D e = a\<close> a_def
                    by presburger
                  also have "... = \<r>\<^sub>D[w] \<cdot>\<^sub>D ((w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D (w \<star>\<^sub>D D.inv \<epsilon>)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                    using w \<gamma> e.ide_left e.ide_right we e.antipar D.comp_cod_arr
                    by (metis D.whisker_left d.unit_simps(1,3))
                  also have "... = \<r>\<^sub>D[w] \<cdot>\<^sub>D (w \<star>\<^sub>D src\<^sub>D w) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                    using w e.counit_is_iso C.comp_arr_inv'
                    by (metis D.comp_arr_inv' D.seqI' D.whisker_left \<open>trg\<^sub>D e = a\<close> a_def
                        d.unit_in_vhom e.counit_in_hom(2) e.counit_simps(3))
                  also have "... = \<r>\<^sub>D[w] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w]"
                    using w e.antipar D.comp_cod_arr by simp
                  also have "... = w"
                    using w 
                    by (simp add: D.comp_arr_inv')
                  finally have "\<r>\<^sub>D[w] \<cdot>\<^sub>D (w \<star>\<^sub>D \<epsilon>) \<cdot>\<^sub>D \<a>\<^sub>D[w, e, d] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[w, e, d] \<cdot>\<^sub>D
                                 (w \<star>\<^sub>D D.inv \<epsilon>) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[w] = w"
                    by simp
                  thus ?thesis
                    using \<gamma>' D.comp_arr_dom by auto
                qed
                finally show ?thesis by simp
              qed
           qed
          qed
        qed
      qed
      show ?thesis ..
    qed

    lemma reflects_tabulation:
    assumes "C.ide r" and "C.ide f" and "\<guillemotleft>\<rho> : g \<Rightarrow>\<^sub>C r \<star>\<^sub>C f\<guillemotright>"
    assumes "tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F r) (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>) (F f) (F g)"
    shows "tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> f g"
    proof -
      interpret \<rho>': tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                      \<open>F r\<close> \<open>D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>\<close> \<open>F f\<close> \<open>F g\<close>
        using assms by auto
      interpret \<rho>: tabulation_data V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> f g
        using assms by (unfold_locales, simp_all)
      interpret \<rho>: tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> f g
      proof
        show "\<And>u \<omega>. \<lbrakk> C.ide u; \<guillemotleft>\<omega> : C.dom \<omega> \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<guillemotright> \<rbrakk> \<Longrightarrow>
                     \<exists>w \<theta> \<nu>. C.ide w \<and> \<guillemotleft>\<theta> : f \<star>\<^sub>C w \<Rightarrow>\<^sub>C u\<guillemotright> \<and> \<guillemotleft>\<nu> : C.dom \<omega> \<Rightarrow>\<^sub>C g \<star>\<^sub>C w\<guillemotright> \<and>
                             C.iso \<nu> \<and> \<rho>.composite_cell w \<theta> \<cdot>\<^sub>C \<nu> = \<omega>"
        proof -
          fix u \<omega>
          assume u: "C.ide u"
          assume \<omega>: "\<guillemotleft>\<omega> : C.dom \<omega> \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<guillemotright>"
          have hseq_ru: "src\<^sub>C r = trg\<^sub>C u"
            using \<omega> C.ide_cod C.ideD(1) by fastforce
          hence 1: "\<guillemotleft>D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F \<omega> : F (C.dom \<omega>) \<Rightarrow>\<^sub>D F r \<star>\<^sub>D F u\<guillemotright>"
            using assms u \<omega> \<Phi>_in_hom \<Phi>_components_are_iso
            by (intro D.comp_in_homI, auto)
          hence 2: "D.dom (D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F \<omega>) = F (C.dom \<omega>)"
            by auto
          obtain w \<theta> \<nu>
            where w\<theta>\<nu>: "D.ide w \<and> \<guillemotleft>\<theta> : F f \<star>\<^sub>D w \<Rightarrow>\<^sub>D F u\<guillemotright> \<and>
                        \<guillemotleft>\<nu> : F (C.dom \<omega>) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w\<guillemotright> \<and> D.iso \<nu> \<and>
                        \<rho>'.composite_cell w \<theta> \<cdot>\<^sub>D \<nu> = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F \<omega>"
            using 1 2 u \<rho>'.T1 [of "F u" "D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F \<omega>"] by auto
          have hseq_Ff_w: "src\<^sub>D (F f) = trg\<^sub>D w"
            using u \<omega> w\<theta>\<nu>
            by (metis "1" D.arrI D.not_arr_null D.seqE D.seq_if_composable \<rho>'.tab_simps(2))
          have hseq_Fg_w: "src\<^sub>D (F g) = trg\<^sub>D w"
            using u \<omega> w\<theta>\<nu> by (simp add: hseq_Ff_w)
          have w: "\<guillemotleft>w : map\<^sub>0 (src\<^sub>C \<omega>) \<rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C f)\<guillemotright>"
              using u \<omega> w\<theta>\<nu> hseq_Fg_w
              by (metis "1" C.arrI D.arrI D.hseqI' D.ideD(1) D.in_hhom_def D.src_hcomp
                  D.src_vcomp D.vconn_implies_hpar(1) D.vconn_implies_hpar(3)
                  D.vseq_implies_hpar(1) \<rho>'.leg1_simps(2) \<rho>.leg0_simps(2) hseq_Ff_w
                  preserves_src)
          obtain w' where w': "\<guillemotleft>w' : src\<^sub>C \<omega> \<rightarrow>\<^sub>C src\<^sub>C f\<guillemotright> \<and> C.ide w' \<and> D.isomorphic (F w') w"
            using assms w \<omega> w\<theta>\<nu> locally_essentially_surjective by force
          obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : F w' \<Rightarrow>\<^sub>D w\<guillemotright> \<and> D.iso \<phi>"
            using w' D.isomorphic_def by blast
          have src_fw': "src\<^sub>C (f \<star>\<^sub>C w') = src\<^sub>C u"
            using u w' \<omega>
            by (metis C.hseqI' C.ideD(1) C.in_hhomE C.src_hcomp C.vconn_implies_hpar(1)
                C.vconn_implies_hpar(3) \<rho>.base_simps(2) \<rho>.leg0_in_hom(1) hseq_ru)
          have 3: "\<guillemotleft>\<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w')) : F (f \<star>\<^sub>C w') \<Rightarrow>\<^sub>D F u\<guillemotright>"
          proof (intro D.comp_in_homI)
            show "\<guillemotleft>D.inv (\<Phi> (f, w')) : F (f \<star>\<^sub>C w') \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F w'\<guillemotright>"
              using assms w' \<Phi>_in_hom \<Phi>_components_are_iso by auto
            show "\<guillemotleft>F f \<star>\<^sub>D \<phi> : F f \<star>\<^sub>D F w' \<Rightarrow>\<^sub>D F f \<star>\<^sub>D w\<guillemotright>"
              using \<phi> \<rho>'.leg0_in_hom(2) w' by fastforce
            show "\<guillemotleft>\<theta> : F f \<star>\<^sub>D w \<Rightarrow>\<^sub>D F u\<guillemotright>"
              using w\<theta>\<nu> by simp
          qed
          have 4: "\<exists>\<theta>'. \<guillemotleft>\<theta>' : f \<star>\<^sub>C w' \<Rightarrow>\<^sub>C u\<guillemotright> \<and> F \<theta>' = \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w'))"
            using w' u hseq_ru src_fw' 3 locally_full by auto
          obtain \<theta>' where
            \<theta>': "\<guillemotleft>\<theta>' : f \<star>\<^sub>C w' \<Rightarrow>\<^sub>C u\<guillemotright> \<and> F \<theta>' = \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w'))"
            using 4 by auto
          have 5: "\<guillemotleft>\<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D \<nu> : F (C.dom \<omega>) \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C w')\<guillemotright>"
          proof (intro D.comp_in_homI)
            show "\<guillemotleft>\<nu> : F (C.dom \<omega>) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D w\<guillemotright>"
              using w\<theta>\<nu> by simp
            show "\<guillemotleft>F g \<star>\<^sub>D D.inv \<phi> : F g \<star>\<^sub>D w \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F w'\<guillemotright>"
              using assms \<phi>
              by (meson D.hcomp_in_vhom D.inv_in_hom \<rho>'.leg1_in_hom(2) hseq_Fg_w)
            show "\<guillemotleft>\<Phi> (g, w') : F g \<star>\<^sub>D F w' \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C w')\<guillemotright>"
              using assms w' \<Phi>_in_hom by auto
          qed
          have 6: "\<exists>\<nu>'. \<guillemotleft>\<nu>' : C.dom \<omega> \<Rightarrow>\<^sub>C g \<star>\<^sub>C w'\<guillemotright> \<and>
                        F \<nu>' = \<Phi>(g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D \<nu>"
            using u w' \<omega> C.in_hhom_def hseq_ru C.hseqI' C.hcomp_simps(1-2)
            by (metis "5" C.arrI C.ide_hcomp C.ideD(1) C.ide_dom C.vconn_implies_hpar(1,4)
                \<rho>.base_simps(2) \<rho>.ide_leg1 \<rho>.leg1_in_hom(1) locally_full)
          obtain \<nu>' where
            \<nu>': "\<guillemotleft>\<nu>' : C.dom \<omega> \<Rightarrow>\<^sub>C g \<star>\<^sub>C w'\<guillemotright> \<and> F \<nu>' = \<Phi>(g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D \<nu>"
            using 6 by auto
          have "C.ide w' \<and> \<guillemotleft>\<theta>' : f \<star>\<^sub>C w' \<Rightarrow>\<^sub>C u\<guillemotright> \<and> \<guillemotleft>\<nu>' : C.dom \<omega> \<Rightarrow>\<^sub>C g \<star>\<^sub>C w'\<guillemotright> \<and> C.iso \<nu>' \<and>
                \<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>' = \<omega>"
            using w' \<theta>' \<nu>'
            apply (intro conjI)
                apply auto
          proof -
            show "C.iso \<nu>'"
            proof -
              have "D.iso (F \<nu>')"
              proof -
                have "D.iso (\<Phi>(g, w'))"
                  using w' \<Phi>_components_are_iso by auto
                moreover have "D.iso (F g \<star>\<^sub>D D.inv \<phi>)"
                  using \<phi>
                  by (meson "5" D.arrI D.iso_hcomp D.hseq_char' D.ide_is_iso D.iso_inv_iso
                      D.seqE D.seq_if_composable \<rho>'.ide_leg1)
                moreover have "D.iso \<nu>"
                  using w\<theta>\<nu> by simp
                ultimately show ?thesis
                  using \<nu>' D.isos_compose
                  by (metis "5" D.arrI D.seqE)
              qed
              thus ?thesis using reflects_iso by blast
            qed
            have 7: "\<guillemotleft>\<rho>.composite_cell w' \<theta>' : g \<star>\<^sub>C w' \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<guillemotright>"
              using u w' \<theta>' \<rho>.composite_cell_in_hom hseq_ru src_fw' C.hseqI'
              by (metis C.in_hhomE C.hcomp_simps(1) \<rho>.leg0_simps(2))
            hence 8: "\<guillemotleft>\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>' : C.dom \<omega> \<Rightarrow>\<^sub>C r \<star>\<^sub>C u\<guillemotright>"
              using \<nu>' by blast
            show "\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>' = \<omega>"
            proof -
              have 1: "C.par (\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>') \<omega>"
                using \<omega> 8 hseq_ru C.hseqI' C.in_homE by metis
              moreover have "F (\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>') = F \<omega>"
              proof -
                have "F (\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>') =
                      F (r \<star>\<^sub>C \<theta>') \<cdot>\<^sub>D F \<a>\<^sub>C[r, f, w'] \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w') \<cdot>\<^sub>D F \<nu>'"
                  using w' \<theta>' \<nu>' 1 C.comp_assoc
                  by (metis C.seqE preserves_comp)
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D
                                   \<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w'))) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D
                                   ((D.inv (\<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D
                                   \<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w')) \<cdot>\<^sub>D D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<nu>'"
                proof -
                  have "F \<a>\<^sub>C[r, f, w'] =
                        \<Phi> (r, f \<star>\<^sub>C w') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D
                         (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w'))"
                    using assms w'
                    by (simp add: C.in_hhom_def preserves_assoc(1))
                  moreover have
                    "F (r \<star>\<^sub>C \<theta>') = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D D.inv (\<Phi> (r, f \<star>\<^sub>C w'))"
                    using assms \<theta>' preserves_hcomp [of r \<theta>']
                    by (metis "1" C.in_homE C.seqE \<rho>.base_simps(3) \<rho>.base_simps(4))
                  moreover have
                    "F (\<rho> \<star>\<^sub>C w') = \<Phi> (r \<star>\<^sub>C f, w') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D D.inv (\<Phi> (g, w'))"
                    using w' preserves_hcomp [of \<rho> w'] by auto
                  ultimately show ?thesis
                    by (simp add: D.comp_assoc)
                qed
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D
                                   (F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<nu>'"
                proof -
                  have "(D.inv (\<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) =
                        F r \<star>\<^sub>D \<Phi> (f, w')"
                    using w' \<Phi>_components_are_iso D.comp_cod_arr C.hseqI' D.hseqI'
                          C.in_hhom_def C.trg_hcomp D.comp_inv_arr' C.ide_hcomp
                    by (metis C.ideD(1) D.hcomp_simps(4) \<Phi>_simps(1,3-5)
                        \<rho>'.leg0_simps(3) \<rho>'.base_simps(2,4) \<rho>.ide_leg0 \<rho>.ide_base
                        \<rho>.leg0_simps(3))
                  moreover have "(D.inv (\<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D \<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w') =
                                 F \<rho> \<star>\<^sub>D F w'"
                    using w' D.comp_inv_arr' hseq_Fg_w D.comp_cod_arr by auto
                  ultimately show ?thesis by simp
                qed
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w'))) \<cdot>\<^sub>D
                                   (F r \<star>\<^sub>D \<Phi> (f, w'))) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D
                                   ((D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w')) \<cdot>\<^sub>D
                                   D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D \<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D \<nu>"
                  using w' \<theta>' \<nu>' D.comp_assoc by simp
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w')) \<cdot>\<^sub>D
                                   \<Phi> (f, w')) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D
                                   F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D ((D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D \<Phi> (g, w')) \<cdot>\<^sub>D
                                   (F g \<star>\<^sub>D D.inv \<phi>)) \<cdot>\<^sub>D \<nu>"
                proof -
                  have "(F r \<star>\<^sub>D \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w'))) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) =
                        F r \<star>\<^sub>D (\<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w'))) \<cdot>\<^sub>D \<Phi> (f, w')"
                  proof - 
                    have "D.seq (\<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w'))) (\<Phi> (f, w'))"
                      using assms 3 \<rho>.ide_base w' w\<theta>\<nu> \<Phi>_in_hom [of f w'] \<Phi>_components_are_iso
                            C.in_hhom_def
                      apply (intro D.seqI)
                      using C.in_hhom_def
                            apply auto[3]
                         apply blast
                      by auto
                    thus ?thesis
                      using assms w' w\<theta>\<nu> \<Phi>_in_hom \<Phi>_components_are_iso D.whisker_left by simp
                  qed
                  moreover have "(D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w') =
                                 D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w'"
                    using w' D.whisker_right by simp
                  ultimately show ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>)) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D
                                   (F g \<star>\<^sub>D D.inv \<phi>)) \<cdot>\<^sub>D \<nu>"
                proof -
                  have "(F f \<star>\<^sub>D \<phi>) \<cdot>\<^sub>D D.inv (\<Phi> (f, w')) \<cdot>\<^sub>D \<Phi> (f, w') = F f \<star>\<^sub>D \<phi>"
                    using assms(2) w' \<phi> 3 \<Phi>_components_are_iso \<Phi>_in_hom D.hseqI' D.comp_inv_arr'
                          D.comp_arr_dom
                    by (metis C.in_hhom_def D.arrI D.cod_inv D.seqE)
                  moreover have "(D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D \<Phi> (g, w')) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) =
                                 F g \<star>\<^sub>D D.inv \<phi>"
                    using assms w' \<phi> 3 \<Phi>_components_are_iso \<Phi>_in_hom D.hseqI' D.comp_inv_arr'
                          D.comp_cod_arr
                    by (metis "5" C.in_hhom_def D.arrI D.comp_assoc D.seqE \<rho>.ide_leg1
                        \<rho>.leg1_simps(3))
                  ultimately show ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>)) \<cdot>\<^sub>D
                                   (\<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F f) \<star>\<^sub>D D.inv \<phi>)) \<cdot>\<^sub>D
                                   (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D w) \<cdot>\<^sub>D \<nu>"
                proof -
                  have "(D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) =
                        D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D D.inv \<phi>"
                    using assms w' \<phi> \<Phi>_in_hom \<Phi>_components_are_iso D.comp_arr_dom D.comp_cod_arr
                          D.interchange [of "D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>" "F g" "F w'" "D.inv \<phi>"]
                    by auto
                  also have "... = ((F r \<star>\<^sub>D F f) \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D w)"
                    using assms w' \<phi> \<Phi>_components_are_iso D.comp_arr_dom D.comp_cod_arr
                          D.interchange [of "F r \<star>\<^sub>D F f" "D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho>" "D.inv \<phi>" w]
                    by auto
                  finally have "(D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv \<phi>) =
                                ((F r \<star>\<^sub>D F f) \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D w)"
                    by simp
                  thus ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D ((F r \<star>\<^sub>D \<theta> \<cdot>\<^sub>D (F f \<star>\<^sub>D \<phi>)) \<cdot>\<^sub>D
                                    (F r \<star>\<^sub>D F f \<star>\<^sub>D D.inv \<phi>)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w] \<cdot>\<^sub>D
                                   (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D w) \<cdot>\<^sub>D \<nu>"
                proof -
                  have "\<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D ((F r \<star>\<^sub>D F f) \<star>\<^sub>D D.inv \<phi>) =
                        (F r \<star>\<^sub>D F f \<star>\<^sub>D D.inv \<phi>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w]"
                  proof -
                    have "src\<^sub>D (F r) = trg\<^sub>D (F f)"
                      by simp
                    moreover have "src\<^sub>D (F f) = trg\<^sub>D (D.inv \<phi>)"
                      using \<phi>
                      by (metis "5" D.arrI D.hseqE D.seqE \<rho>'.leg1_simps(3))
                    ultimately show ?thesis
                      using assms w' \<phi> D.assoc_naturality [of "F r" "F f" "D.inv \<phi>"] by auto
                  qed
                  thus ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<theta>) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, w] \<cdot>\<^sub>D
                                   (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D w) \<cdot>\<^sub>D \<nu>"
                  using assms \<phi> w\<theta>\<nu> D.comp_arr_inv' D.comp_arr_dom D.comp_cod_arr
                        D.whisker_left D.whisker_left D.comp_assoc
                  by (metis D.ideD(1) D.in_homE \<rho>'.ide_base tabulation_data.leg0_simps(1)
                            tabulation_def)
                also have "... = (\<Phi> (r, u) \<cdot>\<^sub>D D.inv (\<Phi> (r, u))) \<cdot>\<^sub>D F \<omega>"
                  using w\<theta>\<nu> D.comp_assoc by simp
                also have "... = F \<omega>"
                  using u \<omega> \<Phi>_in_hom \<Phi>.components_are_iso D.comp_arr_inv'
                  by (metis C.in_homE \<Phi>_components_are_iso \<Phi>_simps(5) \<rho>.ide_base is_natural_1
                      naturality hseq_ru)
                finally show ?thesis by blast
              qed
              ultimately show ?thesis
                using is_faithful [of "\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<nu>'" \<omega>] by simp
            qed
          qed
          thus "\<exists>w \<theta> \<nu>. C.ide w \<and> \<guillemotleft>\<theta> : f \<star>\<^sub>C w \<Rightarrow>\<^sub>C u\<guillemotright> \<and> \<guillemotleft>\<nu> : C.dom \<omega> \<Rightarrow>\<^sub>C g \<star>\<^sub>C w\<guillemotright> \<and>
                        C.iso \<nu> \<and> \<rho>.composite_cell w \<theta> \<cdot>\<^sub>C \<nu> = \<omega>"
            by auto
        qed

        show "\<And>u w w' \<theta> \<theta>' \<beta>. \<lbrakk> C.ide w; C.ide w'; \<guillemotleft>\<theta> : f \<star>\<^sub>C w \<Rightarrow>\<^sub>C u\<guillemotright>; \<guillemotleft>\<theta>' : f \<star>\<^sub>C w' \<Rightarrow>\<^sub>C u\<guillemotright>;
                                \<guillemotleft>\<beta> : g \<star>\<^sub>C w \<Rightarrow>\<^sub>C g \<star>\<^sub>C w'\<guillemotright>;
                                \<rho>.composite_cell w \<theta> = \<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<beta> \<rbrakk>
                                   \<Longrightarrow> \<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma> \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)"
        proof -
          fix u w w' \<theta> \<theta>' \<beta>
          assume w: "C.ide w"
          assume w': "C.ide w'"
          assume \<theta>: "\<guillemotleft>\<theta> : f \<star>\<^sub>C w \<Rightarrow>\<^sub>C u\<guillemotright>"
          assume \<theta>': "\<guillemotleft>\<theta>' : f \<star>\<^sub>C w' \<Rightarrow>\<^sub>C u\<guillemotright>"
          assume \<beta>: "\<guillemotleft>\<beta> : g \<star>\<^sub>C w \<Rightarrow>\<^sub>C g \<star>\<^sub>C w'\<guillemotright>"
          assume eq: "\<rho>.composite_cell w \<theta> = \<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<beta>"
          show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma> \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)"
          proof -
            have hseq_ru: "src\<^sub>C r = trg\<^sub>C u"
            using w \<theta>
            by (metis C.hseq_char' C.in_homE C.trg.is_extensional C.trg.preserves_hom
                C.trg_hcomp C.vconn_implies_hpar(2) C.vconn_implies_hpar(4) \<rho>.leg0_simps(3))
            have hseq_fw: "src\<^sub>C f = trg\<^sub>C w \<and> src\<^sub>C f = trg\<^sub>C w'"
              using w w' \<rho>.ide_leg0 \<theta> \<theta>'
              by (metis C.horizontal_homs_axioms C.ideD(1) C.in_homE C.not_arr_null
                  C.seq_if_composable category.ide_dom horizontal_homs_def)
            have hseq_gw: "src\<^sub>C g = trg\<^sub>C w \<and> src\<^sub>C g = trg\<^sub>C w'"
              using w w' \<rho>.ide_leg0 \<theta> \<theta>' \<open>src\<^sub>C f = trg\<^sub>C w \<and> src\<^sub>C f = trg\<^sub>C w'\<close> by auto
            have *: "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : F w \<Rightarrow>\<^sub>D F w'\<guillemotright> \<and>
                          D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) = F g \<star>\<^sub>D \<gamma> \<and>
                          F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) = (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>)"
            proof -
              have "D.ide (F w) \<and> D.ide (F w')"
                using w w' by simp
              moreover have 1: "\<guillemotleft>F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) : F f \<star>\<^sub>D F w \<Rightarrow>\<^sub>D F u\<guillemotright>"
                using w \<theta> \<Phi>_in_hom \<rho>.ide_leg0 hseq_fw by blast
              moreover have 2: "\<guillemotleft>F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') : F f \<star>\<^sub>D F w' \<Rightarrow>\<^sub>D F u\<guillemotright>"
                using w' \<theta>' \<Phi>_in_hom \<rho>.ide_leg0 hseq_fw by blast
              moreover have
                "\<guillemotleft>D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) : F g \<star>\<^sub>D F w \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F w'\<guillemotright>"
                using w w' \<beta> \<rho>.ide_leg1 \<Phi>_in_hom \<Phi>_components_are_iso hseq_gw preserves_hom
                by fastforce
              moreover have "\<rho>'.composite_cell (F w) (F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)) =
                             \<rho>'.composite_cell (F w') (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D
                               D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
              proof -
                have "\<rho>'.composite_cell (F w') (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D
                        D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) =
                      (F r \<star>\<^sub>D F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D
                        (D.inv (\<Phi> (r, f)) \<cdot>\<^sub>D F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D
                        D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
                  using D.comp_assoc by simp
                also have "... =
                           (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D
                             (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D
                             D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
                  using w' \<theta>' 2 D.whisker_left D.whisker_right D.comp_assoc by auto
                also have "... = (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D
                                   \<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w'))) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D
                                   ((D.inv (\<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D
                                   \<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w')) \<cdot>\<^sub>D
                                   D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
                proof -
                  have "(D.inv (\<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) =
                        F r \<star>\<^sub>D \<Phi> (f, w')"
                    using w' \<Phi>_components_are_iso D.comp_cod_arr C.hseqI' D.hseqI'
                          C.in_hhom_def C.trg_hcomp D.comp_inv_arr' C.ide_hcomp
                    by (metis C.ideD(1) D.hcomp_simps(4) \<Phi>_simps(1) \<Phi>_simps(3-5)
                        \<rho>'.leg0_simps(3) \<rho>'.base_simps(2,4) \<rho>.ide_leg0 \<rho>.ide_base
                        \<rho>.leg0_simps(3) hseq_fw)
                  moreover have "(D.inv (\<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D \<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w') =
                                 F \<rho> \<star>\<^sub>D F w'"
                    using w' D.comp_inv_arr' D.comp_cod_arr hseq_fw by auto
                  ultimately show ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D
                                   (\<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D (D.inv (\<Phi> (r, f \<star>\<^sub>C w'))) \<cdot>\<^sub>D
                                   (\<Phi> (r, f \<star>\<^sub>C w')) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D
                                   (D.inv (\<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D
                                   (\<Phi> (r \<star>\<^sub>C f, w')) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w')) \<cdot>\<^sub>D
                                   D.inv (\<Phi> (g, w'))) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
                proof -
                  have "(D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u)) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>') = F r \<star>\<^sub>D F \<theta>'"
                    using assms(1) \<theta>' D.comp_cod_arr hseq_ru D.comp_inv_arr' by auto
                  thus ?thesis
                    using D.comp_assoc by metis
                qed
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D
                                  (F (r \<star>\<^sub>C \<theta>') \<cdot>\<^sub>D F \<a>\<^sub>C[r, f, w'] \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w')) \<cdot>\<^sub>D
                                  F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
                proof -
                  have "F (r \<star>\<^sub>C \<theta>') = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>') \<cdot>\<^sub>D D.inv (\<Phi> (r, f \<star>\<^sub>C w'))"
                    using w' \<theta>' preserves_hcomp hseq_ru by auto
                  moreover have "F \<a>\<^sub>C[r, f, w'] =
                                 \<Phi> (r, f \<star>\<^sub>C w') \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w'] \<cdot>\<^sub>D
                                   (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w') \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w'))"
                    using w' preserves_assoc(1) hseq_fw by force
                  moreover have
                    "F (\<rho> \<star>\<^sub>C w') = \<Phi> (r \<star>\<^sub>C f, w') \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w') \<cdot>\<^sub>D D.inv (\<Phi> (g, w'))"
                    using w' preserves_hcomp hseq_fw by fastforce
                  ultimately show ?thesis
                    using D.comp_assoc by auto
                qed
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F (\<rho>.composite_cell w' \<theta>') \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"
                  using w' \<theta>' C.comp_assoc hseq_ru hseq_fw by auto
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D (F (\<rho>.composite_cell w' \<theta>') \<cdot>\<^sub>D F \<beta>) \<cdot>\<^sub>D \<Phi> (g, w)"
                  using D.comp_assoc by simp
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F (\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<beta>) \<cdot>\<^sub>D \<Phi> (g, w)"
                proof -
                  have "F (\<rho>.composite_cell w' \<theta>') \<cdot>\<^sub>D F \<beta> = F (\<rho>.composite_cell w' \<theta>' \<cdot>\<^sub>C \<beta>)"
                    using w w' \<theta>' \<beta> \<rho>.composite_cell_in_hom
                          preserves_comp [of "\<rho>.composite_cell w' \<theta>'" \<beta>]
                    by (metis C.dom_comp C.hcomp_simps(3) C.ide_char C.in_homE C.seqE C.seqI
                        D.ext D.seqE \<rho>.tab_simps(4) is_extensional preserves_reflects_arr)
                  thus ?thesis by simp
                qed
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D F (\<rho>.composite_cell w \<theta>) \<cdot>\<^sub>D \<Phi> (g, w)"
                  using eq by simp
                also have "... = D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D
                                   F (r \<star>\<^sub>C \<theta>) \<cdot>\<^sub>D F \<a>\<^sub>C[r, f, w] \<cdot>\<^sub>D F (\<rho> \<star>\<^sub>C w) \<cdot>\<^sub>D \<Phi> (g, w)"
                  using w \<theta> C.comp_assoc hseq_ru hseq_fw D.comp_assoc by auto
                also have "... = ((D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D
                                   \<Phi> (r, u)) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>)) \<cdot>\<^sub>D ((D.inv (\<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D
                                   \<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w))) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D
                                   ((D.inv (\<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D
                                   \<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w)) \<cdot>\<^sub>D D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D \<Phi> (g, w)"
                proof -
                  have "F (r \<star>\<^sub>C \<theta>) = \<Phi> (r, u) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D D.inv (\<Phi> (r, f \<star>\<^sub>C w))"
                    using w \<theta> preserves_hcomp hseq_ru by auto
                  moreover have "F \<a>\<^sub>C[r, f, w] =
                        \<Phi> (r, f \<star>\<^sub>C w) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                         (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (r \<star>\<^sub>C f, w))"
                    using w preserves_assoc(1) hseq_fw by force
                  moreover have
                    "F (\<rho> \<star>\<^sub>C w) = \<Phi> (r \<star>\<^sub>C f, w) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
                    using w preserves_hcomp hseq_fw by fastforce
                  ultimately show ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = (F r \<star>\<^sub>D F \<theta>) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) \<cdot>\<^sub>D \<a>\<^sub>D[F r, F f, F w] \<cdot>\<^sub>D
                                   (D.inv (\<Phi> (r, f)) \<star>\<^sub>D F w) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w)"
                proof -
                  have "(D.inv (\<Phi> (r, u)) \<cdot>\<^sub>D \<Phi> (r, u)) \<cdot>\<^sub>D (F r \<star>\<^sub>D F \<theta>) = F r \<star>\<^sub>D F \<theta>"
                    using \<theta> D.comp_cod_arr hseq_ru D.comp_inv_arr' by auto
                  moreover have
                    "(D.inv (\<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D \<Phi> (r, f \<star>\<^sub>C w)) \<cdot>\<^sub>D (F r \<star>\<^sub>D \<Phi> (f, w)) =
                     F r \<star>\<^sub>D \<Phi> (f, w)"
                    using w \<Phi>_components_are_iso D.comp_cod_arr C.hseqI' D.hseqI'
                          C.in_hhom_def C.trg_hcomp D.comp_inv_arr' C.ide_hcomp
                    by (metis C.ideD(1) D.hcomp_simps(4) \<Phi>_simps(1) \<Phi>_simps(3-5)
                        \<rho>'.leg0_simps(3) \<rho>'.base_simps(2,4) \<rho>.ide_leg0 \<rho>.ide_base
                        \<rho>.leg0_simps(3) hseq_fw)
                  moreover have "(D.inv (\<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D \<Phi> (r \<star>\<^sub>C f, w)) \<cdot>\<^sub>D (F \<rho> \<star>\<^sub>D F w) =
                                 F \<rho> \<star>\<^sub>D F w"
                    using w D.comp_inv_arr' D.comp_cod_arr hseq_fw by simp
                  moreover have "(F \<rho> \<star>\<^sub>D F w) \<cdot>\<^sub>D D.inv (\<Phi> (g, w)) \<cdot>\<^sub>D \<Phi> (g, w) = F \<rho> \<star>\<^sub>D F w"
                    using w \<theta> D.comp_arr_dom D.comp_inv_arr' hseq_gw by simp
                  ultimately show ?thesis
                    using D.comp_assoc by simp
                qed
                also have "... = \<rho>'.composite_cell (F w) (F \<theta> \<cdot>\<^sub>D \<Phi> (f, w))"
                  using w \<theta> 1 D.whisker_left D.whisker_right D.comp_assoc by auto
                finally show ?thesis by simp
              qed
              ultimately show ?thesis
                using w w' \<theta> \<theta>' \<beta> eq
                      \<rho>'.T2 [of "F w" "F w'" "F \<theta> \<cdot>\<^sub>D \<Phi> (f, w)" "F u" "F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')"
                                "D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w)"]
                by blast
            qed

            obtain \<gamma>' where \<gamma>': "\<guillemotleft>\<gamma>' : F w \<Rightarrow>\<^sub>D F w'\<guillemotright> \<and>
                                 D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) = F g \<star>\<^sub>D \<gamma>' \<and>
                                 F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) = (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>')"
              using * by auto
            obtain \<gamma> where \<gamma>: "\<guillemotleft>\<gamma> : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> F \<gamma> = \<gamma>'"
              using \<theta> \<theta> w w' \<gamma>' locally_full [of w w' \<gamma>']
              by (metis C.hseqI' C.ideD(1) C.src_hcomp C.vconn_implies_hpar(3)
                  \<rho>.leg0_simps(2) \<theta>' hseq_fw)
            have "\<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)"
            proof -
              have "F \<theta> = F (\<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>))"
              proof -
                have "F \<theta> = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D \<gamma>') \<cdot>\<^sub>D D.inv (\<Phi> (f, w))"
                  using w' \<theta>' \<gamma>' preserves_hcomp hseq_fw D.comp_assoc D.invert_side_of_triangle
                  by (metis C.in_homE D.comp_arr_inv' \<Phi>_components_are_iso \<Phi>_simps(5) \<rho>.ide_leg0
                      \<theta> is_natural_1 w)
                also have "... = F \<theta>' \<cdot>\<^sub>D F (f \<star>\<^sub>C \<gamma>)"
                  using w' D.comp_assoc hseq_fw preserves_hcomp \<Phi>_components_are_iso
                        D.comp_arr_inv'
                  by (metis C.hseqI' C.in_homE C.trg_cod \<gamma> \<rho>.leg0_in_hom(2))
                also have "... = F (\<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>))"
                  using \<gamma> \<theta> \<theta>' hseq_fw C.hseqI' preserves_comp by force
                finally show ?thesis by simp
              qed
              moreover have "C.par \<theta> (\<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>))"
                using \<gamma> \<theta> \<theta>' hseq_fw by fastforce
              ultimately show ?thesis
                using is_faithful by blast
            qed
            moreover have "\<beta> = g \<star>\<^sub>C \<gamma>"
            proof -
              have "F \<beta> = F (g \<star>\<^sub>C \<gamma>)"
              proof -
                have "F \<beta> = \<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D \<gamma>') \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
                  by (metis (no_types) C.in_homE D.comp_arr_inv' D.comp_assoc
                      \<Phi>_components_are_iso \<Phi>_simps(5) \<beta> \<gamma>' \<rho>.ide_leg1 hseq_gw is_natural_1
                      naturality w w')
                also have "... = F (g \<star>\<^sub>C \<gamma>)"
                  using w \<gamma> \<gamma>' preserves_hcomp hseq_gw
                  by (metis C.hseqE C.hseqI' C.in_homE C.seqE \<open>\<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)\<close>
                      \<rho>.leg1_simps(2) \<rho>.leg1_simps(5) \<rho>.leg1_simps(6) \<theta> hseq_fw)
                finally show ?thesis by simp
              qed
              moreover have "C.par \<beta> (g \<star>\<^sub>C \<gamma>)"
              proof (intro conjI)
                show "C.arr \<beta>"
                  using \<beta> by blast
                show 1: "C.hseq g \<gamma>"
                  using \<gamma> hseq_gw by fastforce
                show "C.dom \<beta> = C.dom (g \<star>\<^sub>C \<gamma>)"
                  using \<gamma> \<beta> 1 by fastforce
                show "C.cod \<beta> = C.cod (g \<star>\<^sub>C \<gamma>)"
                  using \<gamma> \<beta> 1 by fastforce
              qed
              ultimately show ?thesis
                using is_faithful by blast
            qed
            ultimately have "\<exists>\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma> \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)"
              using \<gamma> by blast
            moreover have "\<And>\<gamma>\<^sub>1 \<gamma>\<^sub>2. \<guillemotleft>\<gamma>\<^sub>1 : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma>\<^sub>1 \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>1) \<Longrightarrow>
                                   \<guillemotleft>\<gamma>\<^sub>2 : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma>\<^sub>2 \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>2) \<Longrightarrow> \<gamma>\<^sub>1 = \<gamma>\<^sub>2"
            proof -
              fix \<gamma>\<^sub>1 \<gamma>\<^sub>2
              assume \<gamma>\<^sub>1: "\<guillemotleft>\<gamma>\<^sub>1 : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma>\<^sub>1 \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>1)"
              assume \<gamma>\<^sub>2: "\<guillemotleft>\<gamma>\<^sub>2 : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma>\<^sub>2 \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>2)"
              have F\<beta>\<^sub>1: "F \<beta> = \<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>1) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
                using w w' \<beta> hseq_gw \<gamma>\<^sub>1 preserves_hcomp [of g \<gamma>\<^sub>1] \<Phi>_components_are_iso
                by auto
              have F\<beta>\<^sub>2: "F \<beta> = \<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>2) \<cdot>\<^sub>D D.inv (\<Phi> (g, w))"
                using w w' \<beta> hseq_gw \<gamma>\<^sub>2 preserves_hcomp [of g \<gamma>\<^sub>2] \<Phi>_components_are_iso
                by auto
              have "D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) = F g \<star>\<^sub>D F \<gamma>\<^sub>1"
              proof -
                have "F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) = \<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>1)"
                  using w w' \<beta> hseq_gw \<gamma>\<^sub>1 F\<beta>\<^sub>1 preserves_hcomp \<Phi>_components_are_iso
                        D.invert_side_of_triangle D.iso_inv_iso
                  by (metis C.arrI D.comp_assoc D.inv_inv \<rho>.ide_leg1 preserves_reflects_arr)
                thus ?thesis
                  using w w' \<beta> hseq_gw \<gamma>\<^sub>1 preserves_hcomp \<Phi>_components_are_iso
                        D.invert_side_of_triangle
                  by (metis C.arrI D.cod_comp D.seqE D.seqI F\<beta>\<^sub>1 \<rho>.ide_leg1 preserves_arr)
              qed
              moreover have "D.inv (\<Phi> (g, w')) \<cdot>\<^sub>D F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) = F g \<star>\<^sub>D F \<gamma>\<^sub>2"
              proof -
                have "F \<beta> \<cdot>\<^sub>D \<Phi> (g, w) = \<Phi> (g, w') \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<gamma>\<^sub>2)"
                  using w w' \<beta> hseq_gw \<gamma>\<^sub>2 F\<beta>\<^sub>2 preserves_hcomp \<Phi>_components_are_iso
                        D.invert_side_of_triangle D.iso_inv_iso
                  by (metis C.arrI D.comp_assoc D.inv_inv \<rho>.ide_leg1 preserves_reflects_arr)
                thus ?thesis
                  using w w' \<beta> hseq_gw \<gamma>\<^sub>2 preserves_hcomp \<Phi>_components_are_iso
                        D.invert_side_of_triangle
                  by (metis C.arrI D.cod_comp D.seqE D.seqI F\<beta>\<^sub>2 \<rho>.ide_leg1 preserves_arr)
              qed
              moreover have "F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) = (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>1)"
              proof -
                have "F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) = F (\<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>1)) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<gamma>\<^sub>1 by blast
                also have "... = (F \<theta>' \<cdot>\<^sub>D F (f \<star>\<^sub>C \<gamma>\<^sub>1)) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<gamma>\<^sub>1 \<theta> by auto
                also have
                  "... = (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>1) \<cdot>\<^sub>D D.inv (\<Phi> (f, w))) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<gamma>\<^sub>1 hseq_fw preserves_hcomp by auto
                also have
                  "... = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>1) \<cdot>\<^sub>D D.inv (\<Phi> (f, w)) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using D.comp_assoc by simp
                also have "... = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>1) \<cdot>\<^sub>D (F f \<star>\<^sub>D F w)"
                  by (simp add: D.comp_inv_arr' hseq_fw w)
                also have "... = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>1)"
                  using w \<gamma>\<^sub>1 D.whisker_left [of "F f" "F \<gamma>\<^sub>1" "F w"] D.comp_arr_dom by auto
                finally show ?thesis
                  using D.comp_assoc by simp
              qed
              moreover have "F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) = (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w')) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>2)"
              proof -
                have "F \<theta> \<cdot>\<^sub>D \<Phi> (f, w) = F (\<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>\<^sub>2)) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<gamma>\<^sub>2 by blast
                also have "... = (F \<theta>' \<cdot>\<^sub>D F (f \<star>\<^sub>C \<gamma>\<^sub>2)) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<gamma>\<^sub>2 \<theta> by auto
                also have
                  "... = (F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>2) \<cdot>\<^sub>D D.inv (\<Phi> (f, w))) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using \<gamma>\<^sub>2 hseq_fw preserves_hcomp by auto
                also have
                  "... = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>2) \<cdot>\<^sub>D D.inv (\<Phi> (f, w)) \<cdot>\<^sub>D \<Phi> (f, w)"
                  using D.comp_assoc by simp
                also have "... = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>2) \<cdot>\<^sub>D (F f \<star>\<^sub>D F w)"
                  by (simp add: D.comp_inv_arr' hseq_fw w)
                also have "... = F \<theta>' \<cdot>\<^sub>D \<Phi> (f, w') \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<gamma>\<^sub>2)"
                  using w \<gamma>\<^sub>2 D.whisker_left [of "F f" "F \<gamma>\<^sub>2" "F w"] D.comp_arr_dom by auto
                finally show ?thesis
                  using D.comp_assoc by simp
              qed
              ultimately have "F \<gamma>\<^sub>1 = F \<gamma>\<^sub>2"
                using \<gamma>\<^sub>1 \<gamma>\<^sub>2 * by blast
              thus "\<gamma>\<^sub>1 = \<gamma>\<^sub>2"
                using \<gamma>\<^sub>1 \<gamma>\<^sub>2 is_faithful [of \<gamma>\<^sub>1 \<gamma>\<^sub>2] by auto
            qed
            ultimately show "\<exists>!\<gamma>. \<guillemotleft>\<gamma> : w \<Rightarrow>\<^sub>C w'\<guillemotright> \<and> \<beta> = g \<star>\<^sub>C \<gamma> \<and> \<theta> = \<theta>' \<cdot>\<^sub>C (f \<star>\<^sub>C \<gamma>)"
              by blast
          qed
        qed
      qed
      show ?thesis ..
    qed

  end

end
