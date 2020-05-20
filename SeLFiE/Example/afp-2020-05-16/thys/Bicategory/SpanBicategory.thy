(*  Title:       SpanBicategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Span Bicategories"

text \<open>
  In this section we construct the bicategory \<open>Span(C)\<close>, where \<open>C\<close> is a category with pullbacks.
  The $0$-cells of \<open>Span(C)\<close> are the objects of \<open>C\<close>, the $1$-cells of \<open>Span(C)\<close> are pairs
  \<open>(f\<^sub>0, f\<^sub>1)\<close> of arrows of \<open>C\<close> having a common domain, and the $2$-cells of \<open>Span(C)\<close>
  are ``arrows of spans''.  An arrow of spans from \<open>(f\<^sub>0, f\<^sub>1)\<close> to \<open>(g\<^sub>0, g\<^sub>1)\<close> is
  an arrow \<open>\<guillemotleft>u: dom f\<^sub>0 \<rightarrow> dom g\<^sub>0\<guillemotright>\<close> of \<open>C\<close>, such that \<open>g\<^sub>0 \<cdot> u = f\<^sub>0\<close> and \<open>g\<^sub>1 \<cdot> u = f\<^sub>1\<close>.

  In the present development, a \emph{span} is formalized as a structure \<open>\<lparr>Leg0 = f\<^sub>0, Leg1 = f\<^sub>1\<rparr>\<close>,
  where \<open>f\<^sub>0\<close> and \<open>f\<^sub>1\<close> are arrows of \<open>C\<close> with a common domain, which we call the \emph{apex} of
  the span.
  An \emph{arrow of spans}  is formalized as a structure \<open>\<lparr>Chn = u, Dom = S, Cod = T\<rparr>\<close>,
  where \<open>S\<close> and \<open>T\<close> are spans, and \<open>\<guillemotleft>u : S.apex \<rightarrow> T.apex\<guillemotright>\<close> satisfies \<open>Leg0 T \<cdot> u = Leg0 S\<close>
  and \<open>Leg1 T \<cdot> u = Leg1 S\<close>.  We refer to the arrow \<open>u\<close> as the \emph{chine} of the arrow of spans.

  Arrows of spans inherit a composition from that of \<open>C\<close>; this is ``vertical composition''.
  Spans may be composed via pullback in \<open>C\<close>; this ``horizontal composition'' extends to
  arrows of spans, so that it is functorial with respect to vertical composition.
  These two compositions determine a bicategory, as we shall show.
\<close>

theory SpanBicategory
imports Bicategory CategoryWithPullbacks InternalAdjunction Category3.FreeCategory
begin

subsection "Spans"

  record 'a span_data =
    Leg0 :: 'a
    Leg1 :: 'a

  locale span_in_category =
    C: category +
  fixes S :: "'a span_data" (structure)
  assumes is_span: "C.span (Leg0 S) (Leg1 S)"
  begin

    abbreviation leg0
    where "leg0 \<equiv> Leg0 S"

    abbreviation leg1
    where "leg1 \<equiv> Leg1 S"

    abbreviation src
    where "src \<equiv> C.cod leg0"

    abbreviation trg
    where "trg \<equiv> C.cod leg1"

    definition apex
    where "apex \<equiv> C.dom leg0"

    lemma ide_apex [simp]:
    shows "C.ide apex"
      using is_span apex_def by simp

    lemma leg_in_hom [intro]:
    shows "\<guillemotleft>leg0 : apex \<rightarrow> src\<guillemotright>"
    and "\<guillemotleft>leg1 : apex \<rightarrow> trg\<guillemotright>"
      using is_span apex_def by auto

    lemma leg_simps [simp]:
    shows "C.arr leg0" and "C.dom leg0 = apex"
    and "C.arr leg1" and "C.dom leg1 = apex"
      using leg_in_hom by auto

  end

  record 'a arrow_of_spans_data =
    Chn :: 'a
    Dom :: "'a span_data"
    Cod :: "'a span_data"

  locale arrow_of_spans =
    C: category C +
    dom: span_in_category C \<open>Dom \<mu>\<close> +
    cod: span_in_category C \<open>Cod \<mu>\<close>
  for C :: "'a comp"  (infixr "\<cdot>" 55)
  and \<mu> :: "'a arrow_of_spans_data" (structure) +
  assumes chine_in_hom [intro]: "\<guillemotleft>Chn \<mu> : dom.apex \<rightarrow> cod.apex\<guillemotright>"
  and leg0_commutes [simp]: "cod.leg0 \<cdot> Chn \<mu> = dom.leg0"
  and leg1_commutes [simp]: "cod.leg1 \<cdot> (Chn \<mu>) = dom.leg1"
  begin

    abbreviation chine
    where "chine \<equiv> Chn \<mu>"

    lemma chine_simps [simp]:
    shows "C.arr chine" and "C.dom chine = dom.apex" and "C.cod chine = cod.apex"
      using chine_in_hom by auto

    lemma cod_src_eq_dom_src [simp]:
    shows "cod.src = dom.src"
      using dom.is_span cod.is_span
      by (metis C.cod_comp leg0_commutes)

    lemma cod_trg_eq_dom_trg [simp]:
    shows "cod.trg = dom.trg"
      using dom.is_span cod.is_span
      by (metis C.cod_comp leg1_commutes)

    abbreviation dsrc
    where "dsrc \<equiv> dom.src"

    abbreviation dtrg
    where "dtrg \<equiv> dom.trg"

  end

  locale identity_arrow_of_spans =
    arrow_of_spans +
  assumes chine_is_identity [simp]: "C.ide (Chn \<mu>)"
  begin

    abbreviation apex
    where "apex \<equiv> dom.apex"

    abbreviation leg0
    where "leg0 \<equiv> dom.leg0"

    abbreviation leg1
    where "leg1 \<equiv> dom.leg1"

    lemma chine_eq_apex [simp]:
    shows "chine = apex"
      using chine_is_identity C.ideD(2) chine_simps(2) by presburger

    lemma cod_simps [simp]:
    shows "cod.apex = apex" and "cod.leg0 = leg0" and "cod.leg1 = leg1"
      using chine_is_identity chine_simps(3) C.comp_arr_ide leg0_commutes leg1_commutes
      by force+

  end

  subsection "The Vertical Category of Spans"

  text \<open>
    The following locale constructs the category of spans and arrows of spans in
    an underlying category C, which is not yet assumed to have pullbacks.
    The composition is vertical composition of arrows of spans, to which we will
    later add horizontal composition to obtain a bicategory.
  \<close>

  locale span_vertical_category =
    C: category
  begin

    abbreviation Null
    where "Null \<equiv> \<lparr>Chn = C.null,
                   Dom = \<lparr>Leg0 = C.null, Leg1 = C.null\<rparr>,
                   Cod = \<lparr>Leg0 = C.null, Leg1 = C.null\<rparr>\<rparr>"

    lemma not_arr_Null:
    shows "\<not> arrow_of_spans C Null"
      unfolding arrow_of_spans_def arrow_of_spans_axioms_def
      by auto

    text \<open>
      Arrows of spans are composed simply by composing their chines.
    \<close>

    definition vcomp
    where "vcomp \<nu> \<mu> \<equiv> if arrow_of_spans C \<mu> \<and> arrow_of_spans C \<nu> \<and> Dom \<nu> = Cod \<mu>
                       then \<lparr>Chn = Chn \<nu> \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Cod \<nu>\<rparr>
                       else Null"

    notation vcomp        (infixr "\<bullet>" 55)

    (*
     * TODO: The reason why the this and the subsequent category interpretation are declared
     * as V: is that subsequently proved facts with the same names as the partial_magma and
     * category locales silently override the latter, resulting in problems proving things.
     * The presence of the extra "V" is only an issue up until a later sublocale declaration
     * inherits everything from horizontal_homs.  I wish I could say that I completely
     * understood the inheritance and overriding rules for locales.
     *)
    interpretation V: partial_magma vcomp
      using not_arr_Null vcomp_def
      apply unfold_locales
      by (metis (no_types, hide_lams))

    lemma is_partial_magma:
    shows "partial_magma vcomp"
      ..

    lemma null_char:
    shows "V.null = Null"
      using V.null_def vcomp_def not_arr_Null
      by (metis (no_types, lifting) V.comp_null(2))

    text \<open>
      Identities are arrows of spans whose chines are identities of C.
    \<close>

    lemma ide_char:
    shows "V.ide \<mu> \<longleftrightarrow> arrow_of_spans C \<mu> \<and> C.ide (Chn \<mu>)"
    proof
      show "V.ide \<mu> \<Longrightarrow> arrow_of_spans C \<mu> \<and> C.ide (Chn \<mu>)"
      proof
        assume 0: "V.ide \<mu>"
        have 1: "vcomp \<mu> \<mu> \<noteq> Null \<and> (\<forall>\<nu>. (\<nu> \<bullet> \<mu> \<noteq> Null \<longrightarrow> \<nu> \<bullet> \<mu> = \<nu>) \<and>
                                          (\<mu> \<bullet> \<nu> \<noteq> Null \<longrightarrow> \<mu> \<bullet> \<nu> = \<nu>))"
          using 0 V.ide_def null_char by simp
        show \<mu>: "arrow_of_spans C \<mu>"
          using 1 vcomp_def by metis
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> by auto
        show "C.ide (Chn \<mu>)"
        proof -
          have "\<mu>.chine \<cdot> \<mu>.chine \<noteq> C.null"
            using 1 vcomp_def
            by (metis C.in_homE C.not_arr_null C.seqI \<mu>.chine_in_hom)
          moreover have "\<And>f. f \<cdot> Chn \<mu> \<noteq> C.null \<Longrightarrow> f \<cdot> Chn \<mu> = f"
          proof -
            fix f
            assume "f \<cdot> \<mu>.chine \<noteq> C.null"
            hence f: "\<guillemotleft>f : \<mu>.cod.apex \<rightarrow> C.cod f\<guillemotright>"
              using C.ext C.in_homI by force
            let ?cod_\<mu> = "\<lparr>Chn = C.cod \<mu>.chine, Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>"
            interpret cod_\<mu>: arrow_of_spans C ?cod_\<mu>
              using C.ide_in_hom \<mu>.cod.ide_apex \<mu>.chine_in_hom C.comp_arr_dom
              by (unfold_locales, auto)
            have "?cod_\<mu> \<bullet> \<mu> = ?cod_\<mu>"
            proof -
              have "?cod_\<mu> \<bullet> \<mu> \<noteq> Null"
                unfolding vcomp_def
                using \<mu> cod_\<mu>.arrow_of_spans_axioms \<mu>.cod.is_span C.comp_cod_arr
                apply simp
                using \<mu>.chine_simps(1) by force
              thus ?thesis
                using 1 by simp
            qed
            thus "f \<cdot> \<mu>.chine = f"
              unfolding vcomp_def
              using f C.comp_arr_ide C.comp_cod_arr \<mu>.arrow_of_spans_axioms
                    cod_\<mu>.arrow_of_spans_axioms
              by auto
          qed
          moreover have "\<And>f. \<mu>.chine \<cdot> f \<noteq> C.null \<Longrightarrow> \<mu>.chine \<cdot> f = f"
          proof -
            fix f
            assume "\<mu>.chine \<cdot> f \<noteq> C.null"
            hence f: "\<guillemotleft>f : C.dom f \<rightarrow> \<mu>.dom.apex\<guillemotright>"
              using C.ext C.in_homI by force
            let ?dom_\<mu> = "\<lparr>Chn = C.cod f, Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>"
            interpret dom_\<mu>: arrow_of_spans C ?dom_\<mu>
              using f C.ide_in_hom \<mu>.dom.ide_apex \<mu>.chine_in_hom C.comp_arr_dom
              by (unfold_locales, auto)
            have "\<mu> \<bullet> ?dom_\<mu> = ?dom_\<mu>"
            proof -
              have "\<mu> \<bullet> ?dom_\<mu> \<noteq> Null"
                unfolding vcomp_def
                using \<mu> dom_\<mu>.arrow_of_spans_axioms \<mu>.cod.is_span by (simp, force)
              thus ?thesis
                using 1 by simp
            qed
            hence "\<mu>.chine \<cdot> C.cod f = C.cod f"
              unfolding vcomp_def
              using \<mu> dom_\<mu>.arrow_of_spans_axioms f 0 C.comp_ide_arr C.comp_arr_ide
              by simp
            thus "\<mu>.chine \<cdot> f = f"
              unfolding vcomp_def
              using f C.comp_ide_arr C.comp_arr_dom \<mu>.arrow_of_spans_axioms
                    dom_\<mu>.arrow_of_spans_axioms
              by auto
          qed
          ultimately show "C.ide \<mu>.chine"
            unfolding C.ide_def by simp
        qed
      qed
      show "arrow_of_spans C \<mu> \<and> C.ide (Chn \<mu>) \<Longrightarrow> V.ide \<mu>"
      proof -
        assume \<mu>: "arrow_of_spans C \<mu> \<and> C.ide (Chn \<mu>)"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> by auto
        have 1: "Dom \<mu> = Cod \<mu>"
        proof -
          have "\<mu>.dom.leg0 = \<mu>.cod.leg0 \<and> \<mu>.dom.leg1 = \<mu>.cod.leg1"
            using \<mu> C.comp_arr_ide \<mu>.cod.is_span by force
          thus ?thesis by simp
        qed
        show "V.ide \<mu>"
        proof -
          have "\<mu> \<bullet> \<mu> \<noteq> V.null"
            using \<mu> 1 vcomp_def by (simp add: C.ide_def null_char)
          moreover have "\<And>\<nu>. vcomp \<nu> \<mu> \<noteq> V.null \<Longrightarrow> vcomp \<nu> \<mu> = \<nu>"
          proof -
            fix \<nu> :: "'a arrow_of_spans_data"
            assume \<nu>: "\<nu> \<bullet> \<mu> \<noteq> V.null"
            have 2: "arrow_of_spans C \<nu> \<and> Dom \<nu> = Cod \<mu>"
              using \<nu> 1 vcomp_def by (metis V.comp_null(2))
            interpret \<nu>: arrow_of_spans C \<nu>
              using 2 by auto
            show "\<nu> \<bullet> \<mu> = \<nu>"
              unfolding vcomp_def
              using \<mu> 1 2 C.comp_arr_ide by simp
          qed
          moreover have "\<And>\<nu>. \<mu> \<bullet> \<nu> \<noteq> V.null \<Longrightarrow> \<mu> \<bullet> \<nu> = \<nu>"
          proof -
            fix \<nu> :: "'a arrow_of_spans_data"
            assume \<nu>: "\<mu> \<bullet> \<nu> \<noteq> V.null"
            have 2: "arrow_of_spans C \<nu> \<and> Dom \<mu> = Cod \<nu>"
              using \<nu> 1 vcomp_def by (metis V.comp_null(1))
            interpret \<nu>: arrow_of_spans C \<nu>
              using 2 by auto
            show "\<mu> \<bullet> \<nu> = \<nu>"
              unfolding vcomp_def
              using \<mu> 1 2 C.comp_ide_arr by simp
          qed
          ultimately show ?thesis
            unfolding V.ide_def by blast
        qed
      qed
    qed

    lemma has_domain_char:
    shows "V.domains \<mu> \<noteq> {} \<longleftrightarrow> arrow_of_spans C \<mu>"
    proof
      show "V.domains \<mu> \<noteq> {} \<Longrightarrow> arrow_of_spans C \<mu>"
        using V.domains_def null_char vcomp_def by fastforce
      show "arrow_of_spans C \<mu> \<Longrightarrow> V.domains \<mu> \<noteq> {}"
      proof -
        assume \<mu>: "arrow_of_spans C \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> by auto
        let ?dom_\<mu> = "\<lparr>Chn = \<mu>.dom.apex, Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>"
        interpret dom_\<mu>: arrow_of_spans C ?dom_\<mu>
          using C.comp_arr_dom by (unfold_locales, auto)
        have "?dom_\<mu> \<in> V.domains \<mu>"
        proof -
          have "V.ide ?dom_\<mu>"
            using ide_char dom_\<mu>.arrow_of_spans_axioms by simp
          moreover have "\<mu> \<bullet> ?dom_\<mu> \<noteq> V.null"
            using \<mu> vcomp_def \<mu>.cod.span_in_category_axioms dom_\<mu>.arrow_of_spans_axioms
                  null_char span_in_category.leg_simps(1)
            by fastforce
          ultimately show ?thesis
            unfolding V.domains_def by blast
        qed
        thus "V.domains \<mu> \<noteq> {}" by blast
      qed
    qed

    lemma has_codomain_char:
    shows "V.codomains \<mu> \<noteq> {} \<longleftrightarrow> arrow_of_spans C \<mu>"
    proof
      show "V.codomains \<mu> \<noteq> {} \<Longrightarrow> arrow_of_spans C \<mu>"
        using V.codomains_def null_char vcomp_def by fastforce
      show "arrow_of_spans C \<mu> \<Longrightarrow> V.codomains \<mu> \<noteq> {}"
      proof -
        assume \<mu>: "arrow_of_spans C \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> by auto
        let ?cod_f = "\<lparr>Chn = \<mu>.cod.apex, Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>"
        interpret cod_f: arrow_of_spans C ?cod_f
          using C.comp_arr_dom by (unfold_locales, auto)
        have "?cod_f \<in> V.codomains \<mu>"
        proof -
          have "V.ide ?cod_f"
            using ide_char cod_f.arrow_of_spans_axioms by simp
          moreover have "?cod_f \<bullet> \<mu> \<noteq> V.null"
            using \<mu> vcomp_def \<mu>.cod.span_in_category_axioms cod_f.arrow_of_spans_axioms
                  null_char span_in_category.leg_simps(1)
            by fastforce
          ultimately show ?thesis
            unfolding V.codomains_def by blast
        qed
        thus "V.codomains \<mu> \<noteq> {}" by blast
      qed
    qed

    lemma arr_char:
    shows "V.arr \<mu> \<longleftrightarrow> arrow_of_spans C \<mu>"
      unfolding V.arr_def
      using has_domain_char has_codomain_char by simp

    lemma seq_char:
    shows "V.seq \<nu> \<mu> \<longleftrightarrow> arrow_of_spans C \<mu> \<and> arrow_of_spans C \<nu> \<and> Dom \<nu> = Cod \<mu>"
    proof
      show "V.seq \<nu> \<mu> \<Longrightarrow> arrow_of_spans C \<mu> \<and> arrow_of_spans C \<nu> \<and> Dom \<nu> = Cod \<mu>"
        using vcomp_def by (metis V.not_arr_null null_char)
      show "arrow_of_spans C \<mu> \<and> arrow_of_spans C \<nu> \<and> Dom \<nu> = Cod \<mu> \<Longrightarrow> V.seq \<nu> \<mu>"
      proof -
        assume 1: "arrow_of_spans C \<mu> \<and> arrow_of_spans C \<nu> \<and> Dom \<nu> = Cod \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using 1 by auto
        interpret \<nu>: arrow_of_spans C \<nu>
          using 1 by auto
        show "V.seq \<nu> \<mu>"
        proof -
          let ?\<nu>\<mu> = "\<lparr>Chn = Chn \<nu> \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Cod \<nu>\<rparr>"
          have "\<nu> \<bullet> \<mu> = ?\<nu>\<mu>"
            using 1 vcomp_def by metis
          moreover have "V.arr ?\<nu>\<mu>"
          proof -
            interpret Dom: span_in_category C \<open>Dom ?\<nu>\<mu>\<close>
              by (simp add: \<mu>.dom.span_in_category_axioms)
            interpret Cod: span_in_category C \<open>Cod ?\<nu>\<mu>\<close>
              by (simp add: \<nu>.cod.span_in_category_axioms)
            have "arrow_of_spans C ?\<nu>\<mu>"
              using 1 \<mu>.chine_in_hom \<nu>.chine_in_hom C.comp_reduce
              by (unfold_locales, cases ?\<nu>\<mu>, auto)
            thus ?thesis
              using arr_char by blast
          qed
          ultimately show ?thesis by simp
        qed
      qed
    qed

    interpretation V: category vcomp
    proof
      show "\<And>\<mu>. (V.domains \<mu> \<noteq> {}) = (V.codomains \<mu> \<noteq> {})"
        using has_domain_char has_codomain_char by simp
      show "\<And>\<nu> \<mu>. \<nu> \<bullet> \<mu> \<noteq> V.null \<Longrightarrow> V.seq \<nu> \<mu>"
        using seq_char vcomp_def null_char by metis
      show "\<And>\<pi> \<nu> \<mu>. V.seq \<pi> \<nu> \<Longrightarrow> V.seq (\<pi> \<bullet> \<nu>) \<mu> \<Longrightarrow> V.seq \<nu> \<mu>"
        using seq_char vcomp_def by (metis arrow_of_spans_data.select_convs(2))
      show "\<And>\<pi> \<nu> \<mu>. V.seq \<pi> (\<nu> \<bullet> \<mu>) \<Longrightarrow> V.seq \<nu> \<mu> \<Longrightarrow> V.seq \<pi> \<nu>"
        using seq_char vcomp_def by (metis arrow_of_spans_data.select_convs(3))
      show "\<And>\<nu> \<mu> \<pi>. V.seq \<nu> \<mu> \<Longrightarrow> V.seq \<pi> \<nu> \<Longrightarrow> V.seq (\<pi> \<bullet> \<nu>) \<mu>"
        using seq_char vcomp_def by (metis arr_char arrow_of_spans_data.select_convs(2))
      show "\<And>\<nu> \<mu> \<pi>. V.seq \<nu> \<mu> \<Longrightarrow> V.seq \<pi> \<nu> \<Longrightarrow> (\<pi> \<bullet> \<nu>) \<bullet> \<mu> = \<pi> \<bullet> \<nu> \<bullet> \<mu>"
      proof -
        fix \<mu> \<nu> \<pi>
        assume \<mu>\<nu>: "V.seq \<nu> \<mu>" and \<nu>\<pi>: "V.seq \<pi> \<nu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu>\<nu> seq_char by auto
        interpret \<nu>: arrow_of_spans C \<nu>
          using \<mu>\<nu> seq_char by auto
        interpret \<pi>: arrow_of_spans C \<pi>
          using \<nu>\<pi> seq_char by auto
        show "(\<pi> \<bullet> \<nu>) \<bullet> \<mu> = \<pi> \<bullet> \<nu> \<bullet> \<mu>"
          unfolding vcomp_def
          using \<mu>\<nu> \<nu>\<pi> seq_char \<mu>.chine_in_hom \<nu>.chine_in_hom \<pi>.chine_in_hom
          by (simp add: C.comp_assoc, metis arr_char vcomp_def)
      qed
    qed

    lemma is_category:
    shows "category vcomp"
      ..

    lemma dom_char:
    shows "V.dom = (\<lambda>\<mu>. if V.arr \<mu> then
                          \<lparr>Chn = span_in_category.apex C (Dom \<mu>), Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>
                        else V.null)"
    proof
      fix \<mu>
      have "\<not> V.arr \<mu> \<Longrightarrow> V.dom \<mu> = V.null"
        by (simp add: V.arr_def V.dom_def)
      moreover have "V.arr \<mu> \<Longrightarrow> V.dom \<mu> = \<lparr>Chn = span_in_category.apex C (Dom \<mu>),
                                            Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>"
      proof (intro V.dom_eqI)
        assume \<mu>: "V.arr \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> arr_char by auto
        let ?dom_\<mu> = "\<lparr>Chn = \<mu>.dom.apex, Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>"
        interpret dom_\<mu>: arrow_of_spans C ?dom_\<mu>
          using C.comp_arr_dom by (unfold_locales, auto)
        show "V.ide ?dom_\<mu>"
          using ide_char dom_\<mu>.arrow_of_spans_axioms by simp
        thus "V.seq \<mu> ?dom_\<mu>"
          using seq_char ide_char \<mu>.arrow_of_spans_axioms by simp
      qed
      ultimately show "V.dom \<mu> = (if V.arr \<mu> then
                                     \<lparr>Chn = span_in_category.apex C (Dom \<mu>),
                                      Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>
                                  else V.null)"
        by argo
    qed

    lemma cod_char:
    shows "V.cod = (\<lambda>\<mu>. if V.arr \<mu> then
                          \<lparr>Chn = span_in_category.apex C (Cod \<mu>), Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>
                        else V.null)"
    proof
      fix \<mu>
      have "\<not> V.arr \<mu> \<Longrightarrow> V.cod \<mu> = V.null"
        by (simp add: V.arr_def V.cod_def)
      moreover have "V.arr \<mu> \<Longrightarrow> V.cod \<mu> = \<lparr>Chn = span_in_category.apex C (Cod \<mu>),
                                            Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>"
      proof (intro V.cod_eqI)
        assume \<mu>: "V.arr \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> arr_char by auto
        let ?cod_\<mu> = "\<lparr>Chn = \<mu>.cod.apex, Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>"
        interpret cod_\<mu>: arrow_of_spans C ?cod_\<mu>
          using C.comp_arr_dom by (unfold_locales, auto)
       show "V.ide ?cod_\<mu>"
          using ide_char cod_\<mu>.arrow_of_spans_axioms by simp
        thus "V.seq ?cod_\<mu> \<mu>"
          using seq_char ide_char \<mu>.arrow_of_spans_axioms by simp
      qed
      ultimately show "V.cod \<mu> = (if V.arr \<mu> then
                                    \<lparr>Chn = span_in_category.apex C (Cod \<mu>),
                                     Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>
                                  else V.null)"
        by argo
    qed

    lemma vcomp_char:
    shows "vcomp = (\<lambda>\<nu> \<mu>. if V.seq \<nu> \<mu> then
                             \<lparr>Chn = Chn \<nu> \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Cod \<nu>\<rparr>
                           else V.null)"
    proof -
      have "\<And>\<mu> \<nu>. \<nu> \<bullet> \<mu> = (if V.seq \<nu> \<mu> then
                             \<lparr>Chn = Chn \<nu> \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Cod \<nu>\<rparr>
                           else V.null)"
        using vcomp_def seq_char null_char by simp
      thus ?thesis by auto
    qed

    lemma vcomp_eq:
    assumes "V.seq \<nu> \<mu>"
    shows "\<nu> \<bullet> \<mu> = \<lparr>Chn = Chn \<nu> \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Cod \<nu>\<rparr>"
      using assms vcomp_char by meson

    lemma Chn_vcomp:
    assumes "V.seq \<nu> \<mu>"
    shows "Chn (\<nu> \<bullet> \<mu>) = Chn \<nu> \<cdot> Chn \<mu>"
      using assms vcomp_eq [of \<nu> \<mu>] by simp

    lemma ide_char':
    shows "V.ide \<mu> \<longleftrightarrow> identity_arrow_of_spans C \<mu>"
      using arr_char ide_char identity_arrow_of_spans_axioms_def identity_arrow_of_spans_def
            identity_arrow_of_spans.axioms(1) identity_arrow_of_spans.chine_is_identity
      by metis

    lemma Chn_in_hom:
    assumes "V.in_hom \<tau> f g"
    shows "C.in_hom (Chn \<tau>) (Chn f) (Chn g)"
      using assms ide_char arr_char dom_char cod_char
      by (metis (no_types, lifting) C.ide_char arrow_of_spans.chine_in_hom
          arrow_of_spans.chine_simps(3) arrow_of_spans_data.simps(3) V.ide_cod
          V.ide_dom V.in_homE)

    abbreviation mkIde
    where "mkIde f0 f1 \<equiv>
           \<lparr>Chn = C.dom f0, Dom = \<lparr>Leg0 = f0, Leg1 = f1\<rparr>, Cod = \<lparr>Leg0 = f0, Leg1 = f1\<rparr>\<rparr>"

    lemma ide_mkIde:
    assumes "C.span f0 f1"
    shows "V.ide (mkIde f0 f1)"
    proof -
      interpret f: span_in_category C \<open>\<lparr>Leg0 = f0, Leg1 = f1\<rparr>\<close>
        using assms by (unfold_locales, auto)
      interpret ff: arrow_of_spans C \<open>mkIde f0 f1\<close>
        using assms f.apex_def C.comp_arr_dom
        by (unfold_locales, auto)
      show ?thesis
        using assms ff.arrow_of_spans_axioms ide_char by simp
    qed

    abbreviation mkObj
    where "mkObj a \<equiv> mkIde a a"

    lemma ide_mkObj:
    assumes "C.ide a"
    shows "V.ide (mkObj a)"
      using assms ide_mkIde [of a a] by auto

    lemma inverse_arrows:
    assumes "V.arr \<mu>" and "C.iso (Chn \<mu>)"
    shows "V.inverse_arrows \<mu> \<lparr>Chn = C.inv (Chn \<mu>), Dom = Cod \<mu>, Cod = Dom \<mu>\<rparr>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      let ?\<nu> = "\<lparr>Chn = C.inv (Chn \<mu>), Dom = Cod \<mu>, Cod = Dom \<mu>\<rparr>"
      interpret \<nu>: arrow_of_spans C ?\<nu>
        using assms C.invert_side_of_triangle(2) [of \<mu>.dom.leg0 \<mu>.cod.leg0 \<mu>.chine]
              C.invert_side_of_triangle(2) [of \<mu>.dom.leg1 \<mu>.cod.leg1 \<mu>.chine]
        by (unfold_locales, auto)
      show "V.inverse_arrows \<mu> ?\<nu>"
      proof
        show "V.ide (?\<nu> \<bullet> \<mu>)"
        proof -
          have 1: "V.seq ?\<nu> \<mu>"
            using arr_char ide_char dom_char cod_char vcomp_def \<mu>.arrow_of_spans_axioms
                  \<nu>.arrow_of_spans_axioms
            by (intro V.seqI', auto)
          have 2: "?\<nu> \<bullet> \<mu> = \<lparr>Chn = C.inv (Chn \<mu>) \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>"
            using 1 arr_char ide_char dom_char cod_char vcomp_def \<mu>.arrow_of_spans_axioms
                  \<nu>.arrow_of_spans_axioms
            by simp
          moreover have
            "V.ide \<lparr>Chn = C.inv (Chn \<mu>) \<cdot> Chn \<mu>, Dom = Dom \<mu>, Cod = Dom \<mu>\<rparr>"
            using assms 1 2 arr_char ide_char by (simp add: C.comp_inv_arr')
          ultimately show ?thesis by simp
        qed
        show "V.ide (\<mu> \<bullet> ?\<nu>)"
        proof -
          have 1: "V.seq \<mu> ?\<nu>"
            using arr_char ide_char dom_char cod_char vcomp_def \<mu>.arrow_of_spans_axioms
                  \<nu>.arrow_of_spans_axioms
            by (intro V.seqI', auto)
          have 2: "\<mu> \<bullet> ?\<nu> = \<lparr>Chn = Chn \<mu> \<cdot> C.inv (Chn \<mu>), Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>"
            using 1 arr_char ide_char dom_char cod_char vcomp_def \<mu>.arrow_of_spans_axioms
                  \<nu>.arrow_of_spans_axioms
            by simp
          moreover have "V.ide \<lparr>Chn = Chn \<mu> \<cdot> C.inv (Chn \<mu>), Dom = Cod \<mu>, Cod = Cod \<mu>\<rparr>"
            using assms 1 2 arr_char ide_char by (simp add: C.comp_arr_inv')
          ultimately show ?thesis by simp
        qed
      qed
    qed

    lemma iso_char:
    shows "V.iso \<mu> \<longleftrightarrow> V.arr \<mu> \<and> C.iso (Chn \<mu>)"
    proof
      show "V.iso \<mu> \<Longrightarrow> V.arr \<mu> \<and> C.iso (Chn \<mu>)"
        using vcomp_eq ide_char
        by (metis C.iso_iff_section_and_retraction C.retractionI C.sectionI Chn_vcomp
            V.arr_cod V.arr_dom V.comp_arr_inv' V.comp_inv_arr' V.ide_cod V.ide_dom
            V.iso_is_arr)
      show "V.arr \<mu> \<and> C.iso (Chn \<mu>) \<Longrightarrow> V.iso \<mu>"
        using inverse_arrows by auto
    qed

    lemma inv_eq:
    assumes "V.iso \<mu>"
    shows "V.inv \<mu> = \<lparr>Chn = C.inv (Chn \<mu>), Dom = Cod \<mu>, Cod = Dom \<mu>\<rparr>"
      using assms inverse_arrows iso_char by (simp add: V.inverse_unique)

  end

  subsection "Putting Spans in Homs"

  context span_vertical_category
  begin

    interpretation V: category vcomp
      using is_category by simp

    definition src
    where "src \<mu> \<equiv> if V.arr \<mu> then mkObj (C.cod (Leg0 (Dom \<mu>))) else V.null"

    lemma ide_src [simp]:
    assumes "V.arr \<mu>"
    shows "V.ide (src \<mu>)"
      using assms src_def arr_char ide_mkObj C.ide_cod
      by (simp add: arrow_of_spans_def span_in_category.leg_simps(1))

    interpretation src: endofunctor vcomp src
    proof
      show "\<And>\<mu>. \<not> V.arr \<mu> \<Longrightarrow> src \<mu> = V.null"
        using arr_char by (simp add: src_def null_char)
      show 1: "\<And>\<mu>. V.arr \<mu> \<Longrightarrow> V.arr (src \<mu>)"
        using ide_src by simp
      show 2: "\<And>\<mu>. V.arr \<mu> \<Longrightarrow> V.dom (src \<mu>) = src (V.dom \<mu>)"
        using 1 arr_char src_def dom_char ide_src V.arr_dom V.ideD(2) by force      
      show 3: "\<And>\<mu>. V.arr \<mu> \<Longrightarrow> V.cod (src \<mu>) = src (V.cod \<mu>)"
        using 1 arr_char src_def cod_char ide_src V.arr_cod V.ideD(3)
              arrow_of_spans.cod_src_eq_dom_src
        by force
      show "\<And>\<mu> \<nu>. V.seq \<nu> \<mu> \<Longrightarrow> src (\<nu> \<bullet> \<mu>) = src \<nu> \<bullet> src \<mu>"
      proof -
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "V.seq \<nu> \<mu>"
        show "src (\<nu> \<bullet> \<mu>) = src \<nu> \<bullet> src \<mu>"
        proof -
          have "src (\<nu> \<bullet> \<mu>) = mkObj (C.cod (Leg0 (Dom \<mu>)))"
            using \<mu>\<nu> src_def vcomp_def
            apply simp
            using V.not_arr_null null_char by auto
          also have
            "... = \<lparr>Chn = C.dom (C.cod (Leg0 (Dom \<mu>))) \<cdot> C.dom (C.cod (Leg0 (Dom \<mu>))),
                    Dom = \<lparr>Leg0 = C.cod (Leg0 (Dom \<mu>)), Leg1 = C.cod (Leg0 (Dom \<mu>))\<rparr>,
                    Cod = \<lparr>Leg0 = C.cod (Leg0 (Dom \<mu>)), Leg1 = C.cod (Leg0 (Dom \<mu>))\<rparr>\<rparr>"
            using \<mu>\<nu> 1
            by (simp add: arrow_of_spans_def seq_char span_in_category.leg_simps(1))
          also have "... = src \<nu> \<bullet> src \<mu>"
            using \<mu>\<nu> 1 src_def vcomp_def
            apply (elim V.seqE, simp)
            by (metis \<mu>\<nu> arrow_of_spans.cod_src_eq_dom_src ide_char seq_char ide_src)
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma src_is_endofunctor:
    shows "endofunctor vcomp src"
      ..

    lemma src_vcomp:
    assumes "V.seq \<nu> \<mu>"
    shows "src (\<nu> \<bullet> \<mu>) = src \<nu> \<bullet> src \<mu>"
      using assms src.preserves_comp by simp

    definition trg
    where "trg \<mu> \<equiv> if V.arr \<mu> then mkObj (C.cod (Leg1 (Dom \<mu>))) else V.null"

    lemma ide_trg [simp]:
    assumes "V.arr \<mu>"
    shows "V.ide (trg \<mu>)"
      using assms trg_def arr_char ide_mkObj C.ide_cod
      by (simp add: arrow_of_spans_def span_in_category.leg_simps(3))

    interpretation trg: endofunctor vcomp trg
    proof
      show "\<And>\<mu>. \<not> V.arr \<mu> \<Longrightarrow> trg \<mu> = V.null"
        using arr_char by (simp add: trg_def null_char)
      show 1: "\<And>\<mu>. V.arr \<mu> \<Longrightarrow> V.arr (trg \<mu>)"
        using ide_trg by simp
      show 2: "\<And>\<mu>. V.arr \<mu> \<Longrightarrow> V.dom (trg \<mu>) = trg (V.dom \<mu>)"
        using 1 arr_char trg_def dom_char ide_trg V.arr_dom V.ideD(2) by force      
      show 3: "\<And>\<mu>. V.arr \<mu> \<Longrightarrow> V.cod (trg \<mu>) = trg (V.cod \<mu>)"
        using 1 arr_char trg_def cod_char ide_trg V.arr_cod V.ideD(3)
              arrow_of_spans.cod_trg_eq_dom_trg
        by force
      show "\<And>\<mu> \<nu>. V.seq \<nu> \<mu> \<Longrightarrow> trg (\<nu> \<bullet> \<mu>) = trg \<nu> \<bullet> trg \<mu>"
      proof -
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "V.seq \<nu> \<mu>"
        show "trg (\<nu> \<bullet> \<mu>) = trg \<nu> \<bullet> trg \<mu>"
        proof -
          have "trg (\<nu> \<bullet> \<mu>) = mkObj (C.cod (Leg1 (Dom \<mu>)))"
            using \<mu>\<nu> trg_def vcomp_def
            apply simp
            using V.not_arr_null null_char by auto
          also have "... = \<lparr>Chn = Chn (trg \<nu>) \<cdot> Chn (trg \<mu>),
                            Dom = Dom (trg \<mu>), Cod = Cod (trg \<nu>)\<rparr>"
            using \<mu>\<nu> 1 trg_def vcomp_def
            apply (elim V.seqE, simp)
            by (metis C.ide_def \<mu>\<nu> arrow_of_spans.cod_trg_eq_dom_trg select_convs(1) ide_char
                ide_trg seq_char)
          also have "... = trg \<nu> \<bullet> trg \<mu>"
            using \<mu>\<nu> 1 src_def vcomp_def
            apply (elim V.seqE, simp)
            by (metis "2" "3" V.ideD(2) V.ideD(3) select_convs(2) select_convs(3) ide_char
                ide_trg trg_def)  
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma trg_is_endofunctor:
    shows "endofunctor vcomp trg"
      ..

    lemma trg_vcomp:
    assumes "V.seq \<nu> \<mu>"
    shows "trg (\<nu> \<bullet> \<mu>) = trg \<nu> \<bullet> trg \<mu>"
      using assms trg.preserves_comp by simp

    lemma src_trg_simps [simp]:
    assumes "V.arr \<mu>"
    shows "src (src \<mu>) = src \<mu>"
    and "src (trg \<mu>) = trg \<mu>"
    and "trg (src \<mu>) = src \<mu>"
    and "trg (trg \<mu>) = trg \<mu>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      have 1: "V.arr \<lparr>Chn = \<mu>.dsrc, Dom = \<lparr>Leg0 = \<mu>.dsrc, Leg1 = \<mu>.dsrc\<rparr>,
                      Cod = \<lparr>Leg0 = \<mu>.dsrc, Leg1 = \<mu>.dsrc\<rparr>\<rparr>"
        using ide_mkObj by auto
      have 2: "V.arr \<lparr>Chn = \<mu>.dtrg, Dom = \<lparr>Leg0 = \<mu>.dtrg, Leg1 = \<mu>.dtrg\<rparr>,
                      Cod = \<lparr>Leg0 = \<mu>.dtrg, Leg1 = \<mu>.dtrg\<rparr>\<rparr>"
        using ide_mkObj by auto
      show "src (src \<mu>) = src \<mu>"
        using assms 1 src_def by simp
      show "trg (src \<mu>) = src \<mu>"
        using assms 1 src_def trg_def by simp
      show "src (trg \<mu>) = trg \<mu>"
        using assms 2 src_def trg_def by simp
      show "trg (trg \<mu>) = trg \<mu>"
        using assms 2 trg_def by simp
    qed

    sublocale horizontal_homs vcomp src trg
      by (unfold_locales, simp_all)

    lemma has_horizontal_homs:
    shows "horizontal_homs vcomp src trg"
      ..

    lemma obj_char:
    shows "obj a \<longleftrightarrow> V.ide a \<and> a = mkObj (Chn a)"
    proof
      show "obj a \<Longrightarrow> V.ide a \<and> a = mkObj (Chn a)"
      proof
        assume a: "obj a"
        show 1: "V.ide a"
          using a by auto
        show "a = mkObj (Chn a)"
          using a 1 obj_def src_def ide_char
          apply simp
          by (metis arrow_of_spans_data.select_convs(1) arrow_of_spans_def category.dom_cod
              span_in_category.is_span)
      qed
      show "V.ide a \<and> a = mkObj (Chn a) \<Longrightarrow> obj a"
      proof -
        assume a: "V.ide a \<and> a = mkObj (Chn a)"
        show "obj a"
          unfolding obj_def src_def
          using a
          apply simp
          by (metis C.ide_char arrow_of_spans_data.select_convs(2) ide_char
              span_data.select_convs(1))
      qed
    qed

  end

  subsection "Horizontal Composite of Spans"

  text \<open>
    We now define the horizontal composite \<open>S \<star> T\<close> of spans \<open>S\<close> and \<open>T\<close>,
    assuming that \<open>C\<close> is a category with chosen pullbacks.
    We think of Leg0 as an input and Leg1 as an output.
    The following then defines the composite span \<open>S \<star> T\<close>, with \<open>T\<close> on the ``input side'' of \<open>S\<close>.
    The notation is such that the \<open>\<p>\<^sub>0\<close> projections of \<open>C\<close> are used for legs on the input
    (\emph{i.e.} the ``0'') side and the \<open>\<p>\<^sub>1\<close> projections are used for legs on the output
    (\emph{i.e.} the ``1'') side.
  \<close>

  locale composite_span =
    C: elementary_category_with_pullbacks +
    S: span_in_category C S +
    T: span_in_category C T
  for S (structure)
  and T (structure) +
  assumes composable: "C.cod (Leg0 S) = C.cod (Leg1 T)"
  begin

    abbreviation this
    where "this \<equiv> \<lparr>Leg0 = T.leg0 \<cdot> \<p>\<^sub>0[S.leg0, T.leg1], Leg1 = S.leg1 \<cdot> \<p>\<^sub>1[S.leg0, T.leg1]\<rparr>"

    lemma leg0_prj_in_hom:
    shows "\<guillemotleft>T.leg0 \<cdot> \<p>\<^sub>0[S.leg0, T.leg1] : S.leg0 \<down>\<down> T.leg1 \<rightarrow> C.cod (Leg0 T)\<guillemotright>"
      using S.is_span T.is_span C.prj0_in_hom [of "Leg0 S" "Leg1 T"] composable by auto

    lemma leg1_prj_in_hom:
    shows "\<guillemotleft>S.leg1 \<cdot> \<p>\<^sub>1[S.leg0, T.leg1] : S.leg0 \<down>\<down> T.leg1 \<rightarrow> C.cod (Leg1 S)\<guillemotright>"
      using S.is_span T.is_span C.prj1_in_hom [of "Leg0 S" "Leg1 T"] composable by auto

    lemma is_span [simp]:
    shows "span_in_category C this"
      using leg0_prj_in_hom leg1_prj_in_hom
      by (unfold_locales, fastforce)

    sublocale span_in_category C this
      using is_span by auto

  end

  locale span_bicategory =
  C: elementary_category_with_pullbacks +
     span_vertical_category
  begin

    definition chine_hcomp
    where "chine_hcomp \<nu> \<mu> \<equiv>
           \<langle>Chn \<nu> \<cdot> \<p>\<^sub>1[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)]
             \<lbrakk>Leg0 (Cod \<nu>), Leg1 (Cod \<mu>)\<rbrakk>
            Chn \<mu> \<cdot> \<p>\<^sub>0[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)]\<rangle>"

    text \<open>
$$\xymatrix{
  & & \scriptstyle{{\rm src}({\rm Dom}~\nu)} \;=\; {{\rm trg}({\rm Dom}~\mu)} & &\\
  &
    \ar[ddl] _{{\rm Leg1}({\rm Dom}~\nu)}
    \ar [ur] ^<>(0.4){{\rm Leg0}({\rm Dom}~\nu)\hspace{20pt}}
    \ar[dddd] ^{{\rm Chn}~\nu}
  &
  &
    \ar[ul] _<>(0.4){\hspace{20pt}{\rm Leg1}({\rm Dom}~\mu)}
    \ar[ddr] ^{{\rm Leg0}({\rm Dom}~\mu)}
    \ar[dddd] _{{\rm Chn}~\mu}
  \\
  & &
    \ar[ul] ^{p_1}
    \ar[ur] _{p_0}
    \ar@ {.>}[dd]^<>(0.3){{\rm chn\_hcomp~\mu~\nu}}
  \\
  \scriptstyle{{\rm trg}~\nu} & & & & \scriptstyle{{\rm src}~\mu} \\
  & &
    \ar[dl] _{p_1}
    \ar[dr] ^{p_0}
  & &
  \\
  &
    \ar[uul] ^{{\rm Leg1}({\rm Cod}~\nu)}
    \ar[dr] _<>(0.4){{\rm Leg1}({\rm Cod}~\nu)\hspace{20pt}}
  & &
    \ar[dl] ^<>(0.4){\hspace{20pt}{\rm Leg1}({\rm Cod}~\mu)}
    \ar[uur] _{{\rm Leg0}({\rm Cod}~\mu)}
  \\
  & & \scriptstyle{{\rm src}({\rm Cod}~\nu)} \;=\; {{\rm trg}({\rm Cod}~\mu)} & &
}$$
    \<close>

    definition hcomp
    where "hcomp \<nu> \<mu> \<equiv> if arr \<mu> \<and> arr \<nu> \<and> src \<nu> = trg \<mu> then
                          \<lparr>Chn = chine_hcomp \<nu> \<mu>,
                           Dom = composite_span.this C prj0 prj1 (Dom \<nu>) (Dom \<mu>),
                           Cod = composite_span.this C prj0 prj1 (Cod \<nu>) (Cod \<mu>)\<rparr>
                       else
                          null"

    notation hcomp        (infixr "\<star>" 53)

    lemma chine_hcomp_props:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "\<guillemotleft>chine_hcomp \<nu> \<mu> :
              Leg0 (Dom \<nu>) \<down>\<down> Leg1 (Dom \<mu>) \<rightarrow>  Leg0 (Cod \<nu>) \<down>\<down> Leg1 (Cod \<mu>)\<guillemotright>"
    and "C.commutative_square (Leg0 (Cod \<nu>)) (Leg1 (Cod \<mu>))
            (Chn \<nu> \<cdot> \<p>\<^sub>1[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)])
            (Chn \<mu> \<cdot> \<p>\<^sub>0[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)])"
    and "C.commutative_square \<p>\<^sub>1[Leg0 (Cod \<nu>), Leg1 (Cod \<mu>)] (Chn \<nu>)
            (chine_hcomp \<nu> \<mu>) \<p>\<^sub>1[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)]"
    and "C.commutative_square \<p>\<^sub>0[Leg0 (Cod \<nu>), Leg1 (Cod \<mu>)] (Chn \<mu>)
            (chine_hcomp \<nu> \<mu>) \<p>\<^sub>0[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)]"
    and "\<p>\<^sub>0[Leg0 (Cod \<nu>), Leg1 (Cod \<mu>)] \<cdot> chine_hcomp \<nu> \<mu> =
         Chn \<mu> \<cdot> \<p>\<^sub>0[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)]"
    and "\<p>\<^sub>1[Leg0 (Cod \<nu>), Leg1 (Cod \<mu>)] \<cdot> chine_hcomp \<nu> \<mu> =
         Chn \<nu> \<cdot> \<p>\<^sub>1[Leg0 (Dom \<nu>), Leg1 (Dom \<mu>)]"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu>
        using assms arr_char by auto
      show 0: "C.commutative_square \<nu>.cod.leg0 \<mu>.cod.leg1
                 (\<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]) (\<mu>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1])"
        using assms src_def trg_def C.pullback_commutes C.comp_reduce C.commutative_square_def
        by auto
      show 1: "\<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1] \<cdot> chine_hcomp \<nu> \<mu> = \<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
        unfolding chine_hcomp_def
        using 0 by simp
      show 2: "\<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1] \<cdot> chine_hcomp \<nu> \<mu> = \<mu>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
        unfolding chine_hcomp_def
        using 0 by simp
      show 3: "\<guillemotleft>chine_hcomp \<nu> \<mu> : \<nu>.dom.leg0 \<down>\<down> \<mu>.dom.leg1 \<rightarrow> \<nu>.cod.leg0 \<down>\<down> \<mu>.cod.leg1\<guillemotright>"
        unfolding chine_hcomp_def
        using assms 0 src_def trg_def C.tuple_in_hom by auto
      show "C.commutative_square \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1] \<nu>.chine
               (chine_hcomp \<nu> \<mu>) \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
        using assms src_def trg_def 1 3 by auto
      show "C.commutative_square \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1] \<mu>.chine
               (chine_hcomp \<nu> \<mu>) \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
        using assms src_def trg_def 2 3 by auto
    qed

    lemma chine_hcomp_in_hom [intro]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "\<guillemotleft>chine_hcomp \<nu> \<mu> :
              Leg0 (Dom \<nu>) \<down>\<down> Leg1 (Dom \<mu>) \<rightarrow>  Leg0 (Cod \<nu>) \<down>\<down> Leg1 (Cod \<mu>)\<guillemotright>"
      using assms chine_hcomp_props(1) by simp

    lemma arrow_of_spans_hcomp:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "arrow_of_spans C (\<nu> \<star> \<mu>)"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu>
        using assms arr_char by auto
      show ?thesis
      proof
        show span_Dom: "C.span (Leg0 (Dom (\<nu> \<star> \<mu>))) (Leg1 (Dom (\<nu> \<star> \<mu>)))"
          using assms src_def trg_def hcomp_def C.seqI' by auto
        interpret Dom: span_in_category C \<open>Dom (\<nu> \<star> \<mu>)\<close>
          using span_Dom by (unfold_locales, auto)
        show span_Cod: "C.span (Leg0 (Cod (\<nu> \<star> \<mu>))) (Leg1 (Cod (\<nu> \<star> \<mu>)))"
          using assms hcomp_def src_def trg_def by auto
        interpret Cod: span_in_category C \<open>Cod (\<nu> \<star> \<mu>)\<close>
          using span_Cod by (unfold_locales, auto)
        show map: "\<guillemotleft>Chn (\<nu> \<star> \<mu>) : Dom.apex \<rightarrow> Cod.apex\<guillemotright>"
          using assms src_def trg_def chine_hcomp_props hcomp_def Cod.apex_def Dom.apex_def
          by auto
        show "Cod.leg0 \<cdot> Chn (\<nu> \<star> \<mu>) = Dom.leg0"
        proof -
          have "(\<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1]) \<cdot> chine_hcomp \<nu> \<mu> =
                \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
          proof -
            have "(\<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1]) \<cdot> chine_hcomp \<nu> \<mu> =
                  \<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1] \<cdot> chine_hcomp \<nu> \<mu>"
              using assms
              by (metis (full_types) C.category_axioms C.comp_reduce C.dom_comp C.match_2
                  C.seqE C.seqI category.ext)
            also have "... = \<mu>.cod.leg0 \<cdot> \<mu>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
              using assms src_def trg_def
              by (simp add: chine_hcomp_def chine_hcomp_props(2))
            also have "... = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
              using assms \<mu>.leg0_commutes C.comp_reduce
              by (metis (mono_tags, lifting) C.commutative_squareE \<mu>.dom.leg_simps(1)
                  chine_hcomp_props(2))
            finally show ?thesis by simp
          qed
          thus ?thesis
            using assms src_def trg_def hcomp_def chine_hcomp_props \<mu>.chine_in_hom C.comp_reduce
            by auto
        qed
        show "Cod.leg1 \<cdot> Chn (\<nu> \<star> \<mu>) = Dom.leg1"
        proof -
          have "(\<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]) \<cdot> chine_hcomp \<nu> \<mu> =
                 \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
          proof -
            have "(\<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]) \<cdot> chine_hcomp \<nu> \<mu> =
                  \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1] \<cdot> chine_hcomp \<nu> \<mu>"
              using assms
              by (metis (full_types) C.category_axioms C.comp_reduce C.dom_comp C.match_2
                  C.seqE C.seqI category.ext)
            also have "... = \<nu>.cod.leg1 \<cdot> \<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
              using assms src_def trg_def
              by (simp add: chine_hcomp_def chine_hcomp_props(2))
            also have "... = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
              using assms \<nu>.leg1_commutes C.comp_reduce
              by (metis (mono_tags, lifting) C.commutative_squareE \<nu>.dom.leg_simps(3)
                  chine_hcomp_props(2))
            finally show ?thesis by blast
          qed
          thus ?thesis
            using assms src_def trg_def hcomp_def chine_hcomp_props \<nu>.chine_in_hom C.comp_reduce
            by auto
        qed
      qed
    qed

    lemma chine_hcomp_ide_arr:
    assumes "ide f" and "arr \<mu>" and "src f = trg \<mu>"
    shows "chine_hcomp f \<mu> =
           \<langle>\<p>\<^sub>1[Leg0 (Dom f), Leg1 (Dom \<mu>)]
              \<lbrakk>Leg0 (Cod f), Leg1 (Cod \<mu>)\<rbrakk>
            Chn \<mu> \<cdot> \<p>\<^sub>0[Leg0 (Dom f), Leg1 (Dom \<mu>)]\<rangle>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret f: arrow_of_spans C f
        using assms ide_char by auto
      have 1: "C.cospan f.dom.leg0 \<mu>.dom.leg1"
        using assms src_def trg_def by auto
      have "chine_hcomp f \<mu> = \<langle>f.chine \<cdot> \<p>\<^sub>1[f.dom.leg0, \<mu>.dom.leg1]
                                 \<lbrakk>f.cod.leg0, \<mu>.cod.leg1\<rbrakk>
                               \<mu>.chine \<cdot> \<p>\<^sub>0[f.dom.leg0, \<mu>.dom.leg1]\<rangle>"
        unfolding chine_hcomp_def
        using assms ide_char by simp
      moreover have "f.chine \<cdot> \<p>\<^sub>1[f.dom.leg0, \<mu>.dom.leg1] = \<p>\<^sub>1[f.dom.leg0, \<mu>.dom.leg1]"
        using assms 1 C.comp_ide_arr ide_char by auto
      ultimately show ?thesis by argo
    qed

    lemma chine_hcomp_arr_ide:
    assumes "arr \<mu>" and "ide f" and "src \<mu> = trg f"
    shows "chine_hcomp \<mu> f =
           \<langle>Chn \<mu> \<cdot> \<p>\<^sub>1[Leg0 (Dom \<mu>), Leg1 (Dom f)]
              \<lbrakk>Leg0 (Cod \<mu>), Leg1 (Cod f)\<rbrakk>
            \<p>\<^sub>0[Leg0 (Dom \<mu>), Leg1 (Dom f)]\<rangle>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret f: arrow_of_spans C f
        using assms ide_char by auto
      have 1: "C.cospan \<mu>.dom.leg0 f.dom.leg1"
        using assms src_def trg_def by auto
      have "chine_hcomp \<mu> f = \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, f.dom.leg1]
                                 \<lbrakk>\<mu>.cod.leg0, f.cod.leg1\<rbrakk>
                               f.chine \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, f.dom.leg1]\<rangle>"
        unfolding chine_hcomp_def
        using assms ide_char by simp
      moreover have "f.chine \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, f.dom.leg1] = \<p>\<^sub>0[\<mu>.dom.leg0, f.dom.leg1]"
        using assms 1 C.comp_ide_arr ide_char by auto
      ultimately show ?thesis by argo
    qed

    lemma chine_hcomp_ide_ide:
    assumes "ide g" and "ide f" and "src g = trg f"
    shows "chine_hcomp g f = Leg0 (Dom g) \<down>\<down> Leg1 (Dom f)"
    proof -
      interpret g: identity_arrow_of_spans C g
        using assms ide_char' by auto
      interpret f: identity_arrow_of_spans C f
        using assms ide_char' by auto
      have 1: "C.cospan g.dom.leg0 f.dom.leg1"
        using assms src_def trg_def by auto
       have "chine_hcomp g f = \<langle>g.chine \<cdot> \<p>\<^sub>1[g.dom.leg0, f.dom.leg1]
                               \<lbrakk>g.cod.leg0, f.cod.leg1\<rbrakk>
                              \<p>\<^sub>0[g.dom.leg0, f.dom.leg1]\<rangle>"
        using assms chine_hcomp_arr_ide by simp
      moreover have "g.chine \<cdot> \<p>\<^sub>1[g.dom.leg0, f.dom.leg1] = \<p>\<^sub>1[g.dom.leg0, f.dom.leg1]"
        using assms 1 C.comp_ide_arr ide_char by auto
      ultimately have "chine_hcomp g f = \<langle>\<p>\<^sub>1[g.dom.leg0, f.dom.leg1]
                                          \<lbrakk>g.cod.leg0, f.cod.leg1\<rbrakk>
                                        \<p>\<^sub>0[g.dom.leg0, f.dom.leg1]\<rangle>"
        by simp
      also have "... =
                 \<langle>\<p>\<^sub>1[g.dom.leg0, f.dom.leg1] \<cdot> (g.dom.leg0 \<down>\<down> f.dom.leg1)
                    \<lbrakk>g.cod.leg0, f.cod.leg1\<rbrakk>
                  \<p>\<^sub>0[g.dom.leg0, f.dom.leg1] \<cdot> (g.dom.leg0 \<down>\<down> f.dom.leg1)\<rangle>"
        using assms 1 C.comp_arr_dom by simp
      also have "... = g.dom.leg0 \<down>\<down> f.dom.leg1"
        using 1 C.pullback_commutes C.tuple_prj by simp
      finally show ?thesis by simp
    qed

    lemma chine_hcomp_trg_arr:
    assumes "arr \<mu>"
    shows "chine_hcomp (trg \<mu>) \<mu> =
           \<langle>\<p>\<^sub>1[C.cod (Leg1 (Dom \<mu>)), Leg1 (Dom \<mu>)]
              \<lbrakk>C.cod (Leg1 (Dom \<mu>)), Leg1 (Cod \<mu>)\<rbrakk>
            Chn \<mu> \<cdot> \<p>\<^sub>0[C.cod (Leg1 (Dom \<mu>)), Leg1 (Dom \<mu>)]\<rangle>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret trg_\<mu>: arrow_of_spans C \<open>trg \<mu>\<close>
        using assms ide_trg ide_char by simp
      have "trg_\<mu>.dom.leg0 = C.cod \<mu>.dom.leg1 \<and> trg_\<mu>.cod.leg0 = C.cod \<mu>.dom.leg1 \<and>
            trg_\<mu>.dom.leg0 = C.cod \<mu>.dom.leg1"
        using assms ide_char src_def trg_def by simp
      thus ?thesis
        using assms chine_hcomp_ide_arr [of "trg \<mu>" \<mu>] by auto
    qed

    lemma chine_hcomp_trg_ide:
    assumes "ide f"
    shows "chine_hcomp (trg f) f = C.cod (Leg1 (Dom f)) \<down>\<down> Leg1 (Dom f)"
    proof -
      interpret f: arrow_of_spans C f
        using assms arr_char by auto
      interpret trg_f: arrow_of_spans C \<open>trg f\<close>
        using assms ide_trg ide_char by simp
      have "trg_f.dom.leg0 = C.cod f.dom.leg1"
        using assms trg_def by simp
      thus ?thesis
        using assms chine_hcomp_ide_ide [of "trg f" f] by auto
    qed

    lemma chine_hcomp_arr_src:
    assumes "arr \<mu>"
    shows "chine_hcomp \<mu> (src \<mu>) =
           \<langle>Chn \<mu> \<cdot> \<p>\<^sub>1[Leg0 (Dom \<mu>), C.cod (Leg0 (Dom \<mu>))]
              \<lbrakk>Leg0 (Cod \<mu>), C.cod (Leg0 (Dom \<mu>))\<rbrakk>
            \<p>\<^sub>0[Leg0 (Dom \<mu>), C.cod (Leg0 (Dom \<mu>))]\<rangle>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret src_\<mu>: arrow_of_spans C \<open>src \<mu>\<close>
        using assms ide_src ide_char by simp
      have "src_\<mu>.dom.leg1 = \<mu>.dsrc \<and> src_\<mu>.cod.leg1 = \<mu>.dsrc"
        using assms ide_char src_def trg_def by simp
      thus ?thesis
        using assms chine_hcomp_arr_ide by auto
    qed

    lemma chine_hcomp_ide_src:
    assumes "ide f"
    shows "chine_hcomp f (src f) = Leg0 (Dom f) \<down>\<down> C.cod (Leg0 (Dom f))"
    proof -
      interpret f: arrow_of_spans C f
        using assms arr_char by auto
      interpret src_f: arrow_of_spans C \<open>src f\<close>
        using assms ide_src ide_char by simp
      have "C.cod f.dom.leg0 = src_f.dom.leg1"
        using assms src_def by simp
      thus ?thesis
        using assms chine_hcomp_ide_ide by auto
    qed

    lemma src_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "src (\<nu> \<star> \<mu>) = src \<mu>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu>
        using assms arr_char by auto
      have "C.cod (\<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]) = C.cod \<mu>.dom.leg0"
        using assms C.commutative_squareE chine_hcomp_props(2)
        by (metis (mono_tags, lifting) C.cod_comp C.match_3 \<mu>.leg0_commutes \<mu>.dom.is_span)
      thus ?thesis
        using assms arr_char hcomp_def src_def C.comp_cod_arr C.comp_arr_dom arrow_of_spans_hcomp
        by simp
    qed

    lemma trg_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "trg (\<nu> \<star> \<mu>) = trg \<nu>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu>
        using assms arr_char by auto
      have "C.cod (\<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]) = \<nu>.dtrg"
        using assms C.commutative_squareE chine_hcomp_props(2)
        by (metis (mono_tags, lifting) C.cod_comp C.match_3 \<nu>.leg1_commutes \<nu>.dom.is_span)
      thus ?thesis
        using assms arr_char hcomp_def trg_def C.comp_cod_arr C.comp_arr_dom arrow_of_spans_hcomp
        by simp
    qed

    lemma dom_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "dom (\<nu> \<star> \<mu>) = dom \<nu> \<star> dom \<mu>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu>
        using assms arr_char by auto
      interpret \<nu>\<mu>: arrow_of_spans C \<open>hcomp \<nu> \<mu>\<close>
        using assms arr_char arrow_of_spans_hcomp by simp
      have 1: "C.cospan \<mu>.dom.leg1 \<nu>.dom.leg0"
        using assms \<mu>.dom.is_span \<nu>.dom.is_span src_def trg_def by auto
      have "dom (\<nu> \<star> \<mu>) = 
            \<lparr>Chn = \<nu>.dom.leg0 \<down>\<down> \<mu>.dom.leg1,
             Dom = \<lparr>Leg0 = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1],
                    Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rparr>,
             Cod = \<lparr>Leg0 = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1],
                    Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rparr>\<rparr>"
        using assms \<nu>\<mu>.arrow_of_spans_axioms \<nu>\<mu>.dom.leg_simps(2) \<nu>\<mu>.dom.is_span
              arr_char dom_char hcomp_def
        by auto
      also have "... =
                 \<lparr>Chn = chine_hcomp (dom \<nu>) (dom \<mu>),
                  Dom = \<lparr>Leg0 = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1],
                         Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rparr>,
                  Cod = \<lparr>Leg0 = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1],
                         Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rparr>\<rparr>"
        using assms src_dom trg_dom ide_dom dom_char chine_hcomp_ide_ide by auto
      also have "... = dom \<nu> \<star> dom \<mu>"
        using assms src_dom trg_dom arr_dom dom_char hcomp_def by auto
      finally show ?thesis by blast
    qed

    lemma cod_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "cod (\<nu> \<star> \<mu>) = cod \<nu> \<star> cod \<mu>"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu>
        using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu>
        using assms arr_char by auto
      interpret \<nu>\<mu>: arrow_of_spans C \<open>hcomp \<nu> \<mu>\<close>
        using assms arr_char arrow_of_spans_hcomp by simp
      have 1: "C.cospan \<mu>.cod.leg1 \<nu>.cod.leg0"
        using assms \<mu>.cod.is_span \<nu>.cod.is_span src_def trg_def by simp
      have 2: "cod (\<nu> \<star> \<mu>) =
               \<lparr>Chn = \<nu>.cod.leg0 \<down>\<down> \<mu>.cod.leg1,
                Dom = \<lparr>Leg0 = \<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1],
                       Leg1 = \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]\<rparr>,
                Cod = \<lparr>Leg0 = \<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1],
                       Leg1 = \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]\<rparr>\<rparr>"
        using assms \<nu>\<mu>.arrow_of_spans_axioms \<nu>\<mu>.cod.leg_simps(2) \<nu>\<mu>.cod.is_span
              arr_char cod_char hcomp_def
        by auto
      also have "... =
               \<lparr>Chn = chine_hcomp (cod \<nu>) (cod \<mu>),
                Dom = \<lparr>Leg0 = \<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1],
                       Leg1 = \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]\<rparr>,
                Cod = \<lparr>Leg0 = \<mu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1],
                       Leg1 = \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]\<rparr>\<rparr>"
        using assms src_cod trg_cod ide_cod cod_char chine_hcomp_ide_ide by auto
      also have "... = cod \<nu> \<star> cod \<mu>"
        using assms src_cod trg_cod arr_cod cod_char hcomp_def by auto
      finally show ?thesis by simp
    qed

    lemma hcomp_vcomp:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    and "arr \<mu>'" and "arr \<nu>'" and "src \<nu>' = trg \<mu>'"
    and "seq \<mu>' \<mu>" and "seq \<nu>' \<nu>"
    shows "(\<nu>' \<bullet> \<nu>) \<star> (\<mu>' \<bullet> \<mu>) = (\<nu>' \<star> \<mu>') \<bullet> (\<nu> \<star> \<mu>)"
    proof -
      interpret \<mu>: arrow_of_spans C \<mu> using assms arr_char by auto
      interpret \<nu>: arrow_of_spans C \<nu> using assms arr_char by auto
      interpret \<mu>': arrow_of_spans C \<mu>' using assms arr_char by auto
      interpret \<nu>': arrow_of_spans C \<nu>' using assms arr_char by auto
      interpret \<nu>\<mu>: arrow_of_spans C \<open>hcomp \<nu> \<mu>\<close>
        using assms arr_char arrow_of_spans_hcomp by auto
      interpret \<nu>'\<mu>': arrow_of_spans C \<open>hcomp \<nu>' \<mu>'\<close>
        using assms arr_char arrow_of_spans_hcomp by auto

      have 1: "Dom \<nu>' = Cod \<nu> \<and> Dom \<mu>' = Cod \<mu>"
          using assms src_def trg_def seq_char by blast
      have 2: "Dom (\<mu>' \<bullet> \<mu>) = Dom \<mu> \<and> Dom (\<nu>' \<bullet> \<nu>) = Dom \<nu> \<and>
               Cod (\<mu>' \<bullet> \<mu>) = Cod \<mu>' \<and> Cod (\<nu>' \<bullet> \<nu>) = Cod \<nu>'"
        using assms seq_char arr_char vcomp_def
        by (metis arrow_of_spans_data.select_convs(2) arrow_of_spans_data.select_convs(3))
      have 3: "chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>) =
               \<langle>Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]
                  \<lbrakk>\<nu>'.cod.leg0, \<mu>'.cod.leg1\<rbrakk>
                Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rangle>"
        unfolding chine_hcomp_def using 2 by simp

      have C1: "C.commutative_square \<nu>'.cod.leg0 \<mu>'.cod.leg1
                 (Chn \<nu>' \<cdot> \<p>\<^sub>1[\<nu>'.dom.leg0, \<mu>'.dom.leg1])
                 (Chn \<mu>' \<cdot> \<p>\<^sub>0[\<nu>'.dom.leg0, \<mu>'.dom.leg1])"
         using assms 1 vcomp_def seq_char arr_char chine_hcomp_props(2) by blast
      have C2: "C.commutative_square \<nu>'.cod.leg0 \<mu>'.cod.leg1
                 (Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1])
                 (Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1])"
      (* using assms 1 2 vcomp_def seq_char arr_char chine_hcomp_props(1-2) src_vcomp trg_vcomp
         by smt *)
      proof
        show 3: "C.cospan \<nu>'.cod.leg0 \<mu>'.cod.leg1"
          using assms 1 2 vcomp_def seq_char arr_char chine_hcomp_props(1-2)
                src_vcomp trg_vcomp
          by (meson C.commutative_squareE)
        show 4: "C.span (Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1])
                     (Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1])"
          using assms 1 2 3 vcomp_def seq_char arr_char chine_hcomp_props(1-2)
                src_vcomp trg_vcomp
          by simp
        show "C.dom \<nu>'.cod.leg0 = C.cod (Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1])"
          using assms 1 2 4 vcomp_def seq_char arr_char chine_hcomp_props(1-2)
                src_vcomp trg_vcomp
          by simp
        show "\<nu>'.cod.leg0 \<cdot> Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1] =
              \<mu>'.cod.leg1 \<cdot> Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
          using assms 1 2 vcomp_def seq_char arr_char chine_hcomp_props(1-2)
                src_vcomp trg_vcomp
          by (metis (mono_tags, lifting) C.comp_assoc C.pullback_commutes' Chn_vcomp
              \<mu>'.cod_trg_eq_dom_trg \<mu>'.leg1_commutes \<mu>.cod_trg_eq_dom_trg \<mu>.dom.leg_simps(3)
              \<mu>.leg1_commutes \<nu>'.cod_src_eq_dom_src \<nu>'.leg0_commutes \<nu>.cod_src_eq_dom_src
              \<nu>.dom.leg_simps(1) \<nu>.leg0_commutes \<open>C.cospan \<nu>'.cod.leg0 \<mu>'.cod.leg1\<close>)
      qed
      have "(\<nu>' \<bullet> \<nu>) \<star> (\<mu>' \<bullet> \<mu>) =
            \<lparr>Chn = chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>),
             Dom = \<lparr>Leg0 = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1],
                    Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rparr>,
             Cod = \<lparr>Leg0 = \<mu>'.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1],
                    Leg1 = \<nu>'.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1]\<rparr>\<rparr>"
      proof -
        have "\<nu>' \<bullet> \<nu> \<star> \<mu>' \<bullet> \<mu> =
              \<lparr>Chn = chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>),
               Dom =
                 \<lparr>Leg0 = Leg0 (Dom (\<mu>' \<bullet> \<mu>)) \<cdot> \<p>\<^sub>0[Leg0 (Dom (\<nu>' \<bullet> \<nu>)), Leg1 (Dom (\<mu>' \<bullet> \<mu>))],
                  Leg1 = Leg1 (Dom (\<nu>' \<bullet> \<nu>)) \<cdot> \<p>\<^sub>1[Leg0 (Dom (\<nu>' \<bullet> \<nu>)), Leg1 (Dom (\<mu>' \<bullet> \<mu>))]\<rparr>,
               Cod = \<lparr>Leg0 = Leg0 (Cod (\<mu>' \<bullet> \<mu>)) \<cdot> \<p>\<^sub>0[Leg0 (Cod (\<nu>' \<bullet> \<nu>)), Leg1 (Cod (\<mu>' \<bullet> \<mu>))],
               Leg1 = Leg1 (Cod (\<nu>' \<bullet> \<nu>)) \<cdot> \<p>\<^sub>1[Leg0 (Cod (\<nu>' \<bullet> \<nu>)), Leg1 (Cod (\<mu>' \<bullet> \<mu>))]\<rparr>\<rparr>"
          by (simp add: assms(3) assms(6-8) hcomp_def)
        then show ?thesis
          by (metis "2")
      qed
      moreover
      have "(\<nu>' \<star> \<mu>') \<bullet> (\<nu> \<star> \<mu>) =
            \<lparr>Chn = chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>,
             Dom = \<lparr>Leg0 = \<mu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1],
                    Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rparr>,
             Cod = \<lparr>Leg0 = \<mu>'.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1],
                    Leg1 = \<nu>'.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1]\<rparr>\<rparr>"
      proof -
        have "arr (\<nu>' \<star> \<mu>') \<and> arr (\<nu> \<star> \<mu>)"
          using assms arrow_of_spans_hcomp arr_char by simp
        moreover have "Dom (\<nu>' \<star> \<mu>') = Cod (\<nu> \<star> \<mu>)"
          using assms src_def trg_def seq_char hcomp_def src_hcomp trg_hcomp by simp
        ultimately show ?thesis
          using assms seq_char arr_char vcomp_eq hcomp_def by auto
      qed
      moreover have "chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>) = chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>"
      proof -
        have "C.cospan \<nu>'.cod.leg0 \<mu>'.cod.leg1"
          using assms src_def trg_def by simp
        moreover have "C.seq \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] (chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>))"
          using assms 2 C2 chine_hcomp_props [of "\<mu>' \<bullet> \<mu>" "\<nu>' \<bullet> \<nu>"] by auto
        moreover have "C.seq \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] (chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>)"
          using assms 1 chine_hcomp_props [of \<mu> \<nu>] chine_hcomp_props [of \<mu>' \<nu>'] by auto
        moreover have "\<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>) =
                       \<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>"
        proof -
          have "\<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>) =
                Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
            using C2 3 by simp
          also have "... = (\<mu>'.chine \<cdot> \<mu>.chine) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
            using assms vcomp_def seq_char arr_char
            by (metis arrow_of_spans_data.select_convs(1))
          also have "... = \<mu>'.chine \<cdot> \<mu>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"
            using C.comp_assoc by simp
          also have "... = (\<mu>'.chine \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<mu>.cod.leg1]) \<cdot> chine_hcomp \<nu> \<mu>"
            using assms 1
                  C.prj_tuple(1)
                    [of "\<nu>.cod.leg0" "\<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
                        "\<mu>.cod.leg1" "\<mu>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"]
            by (metis (mono_tags, lifting) C.commutative_squareE C.comp_assoc chine_hcomp_props(4))
          also have "... = (\<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp \<nu>' \<mu>') \<cdot> chine_hcomp \<nu> \<mu>"
            using assms 1
              by (metis (mono_tags, lifting) C.commutative_squareE chine_hcomp_props(4))
          also have "... = \<p>\<^sub>0[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>"
            using C.comp_assoc by simp
          finally show ?thesis by blast
        qed
        moreover have "\<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>) =
                       \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>"
        proof -
          have "\<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>) =
                \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot>
                   \<langle>Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]
                     \<lbrakk>Leg0 (Cod \<nu>'), Leg1 (Cod \<mu>')\<rbrakk>
                    Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]\<rangle>"
            using 3 by simp
          also have "... = Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
             using C2 C.prj_tuple(2) [of "Leg0 (Cod \<nu>')"
                                         "Chn (\<nu>' \<bullet> \<nu>) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
                                         "Leg1 (Cod \<mu>')"
                                         "Chn (\<mu>' \<bullet> \<mu>) \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1]"]
               by simp
          also have "... = (\<nu>'.chine \<cdot> \<nu>.chine) \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
            using assms vcomp_def seq_char arr_char
            by (metis (no_types, lifting) arrow_of_spans_data.select_convs(1))
          also have "... = \<nu>'.chine \<cdot> \<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1]"
            using C.comp_assoc by simp
          also have "... = (\<nu>'.chine \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<mu>.cod.leg1]) \<cdot> chine_hcomp \<nu> \<mu>"
          proof -
            have "C.commutative_square \<nu>.cod.leg0 \<mu>.cod.leg1
                     (\<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<mu>.dom.leg1])
                     (\<mu>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<mu>.dom.leg1])"
              using assms 1 vcomp_def seq_char arr_char chine_hcomp_props(2) by auto            
            thus ?thesis
              using assms 1 \<nu>'.leg0_commutes C.prj_tuple(2) apply (simp add: C.comp_assoc)
              by (metis (mono_tags, lifting) C.commutative_squareE chine_hcomp_props(3))
          qed
          also have "... = (\<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp \<nu>' \<mu>') \<cdot> chine_hcomp \<nu> \<mu>"
            unfolding chine_hcomp_def using C1 1 C.prj_tuple(2) by simp
          also have "... = \<p>\<^sub>1[\<nu>'.cod.leg0, \<mu>'.cod.leg1] \<cdot> chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>"
            using C.comp_assoc by simp
          finally show ?thesis by blast
        qed
        ultimately show ?thesis
          using C.prj_joint_monic
                  [of "\<nu>'.cod.leg0" "\<mu>'.cod.leg1"
                      "chine_hcomp (\<nu>' \<bullet> \<nu>) (\<mu>' \<bullet> \<mu>)" "chine_hcomp \<nu>' \<mu>' \<cdot> chine_hcomp \<nu> \<mu>"]
          by simp
      qed
      ultimately show ?thesis by auto
    qed

    interpretation VxV: product_category vcomp vcomp ..
    interpretation VV: subcategory VxV.comp
                         \<open>\<lambda>\<nu>\<mu>. arr (fst \<nu>\<mu>) \<and> arr (snd \<nu>\<mu>) \<and> src (fst \<nu>\<mu>) = trg (snd \<nu>\<mu>)\<close>
      by (unfold_locales, simp_all)

    interpretation H: "functor" VV.comp vcomp \<open>\<lambda>\<nu>\<mu>. fst \<nu>\<mu> \<star> snd \<nu>\<mu>\<close>
    proof
      show "\<And>\<nu>\<mu>. \<not> VV.arr \<nu>\<mu> \<Longrightarrow> fst \<nu>\<mu> \<star> snd \<nu>\<mu> = null"
        using hcomp_def VV.arr_char null_char by auto
      show "\<And>\<nu>\<mu>. VV.arr \<nu>\<mu> \<Longrightarrow> arr (fst \<nu>\<mu> \<star> snd \<nu>\<mu>)"
        using arr_char arrow_of_spans_hcomp VV.arr_char by simp
      show "\<And>\<nu>\<mu>. VV.arr \<nu>\<mu> \<Longrightarrow>
                    dom (fst \<nu>\<mu> \<star> snd \<nu>\<mu>) = fst (VV.dom \<nu>\<mu>) \<star> snd (VV.dom \<nu>\<mu>)"
        using VV.arr_char VV.dom_char dom_hcomp by auto
      show "\<And>\<nu>\<mu>. VV.arr \<nu>\<mu> \<Longrightarrow> cod (fst \<nu>\<mu> \<star> snd \<nu>\<mu>) = fst (VV.cod \<nu>\<mu>) \<star> snd (VV.cod \<nu>\<mu>)"
        using VV.arr_char VV.cod_char cod_hcomp by auto
      show "\<And>\<nu>\<mu>' \<nu>\<mu>. VV.seq \<nu>\<mu>' \<nu>\<mu> \<Longrightarrow> fst (VV.comp \<nu>\<mu>' \<nu>\<mu>) \<star> snd (VV.comp \<nu>\<mu>' \<nu>\<mu>) =
                                        (fst \<nu>\<mu>' \<star> snd \<nu>\<mu>') \<bullet> (fst \<nu>\<mu> \<star> snd \<nu>\<mu>)"
      proof -
        fix \<nu>\<mu>' \<nu>\<mu>
        assume 1: "VV.seq \<nu>\<mu>' \<nu>\<mu>"
        have "VV.comp \<nu>\<mu>' \<nu>\<mu> = (fst \<nu>\<mu>' \<bullet> fst \<nu>\<mu>, snd \<nu>\<mu>' \<bullet> snd \<nu>\<mu>)"
          using 1 VV.comp_char VV.seq_char VxV.comp_char by auto
        thus "fst (VV.comp \<nu>\<mu>' \<nu>\<mu>) \<star> snd (VV.comp \<nu>\<mu>' \<nu>\<mu>) =
              (fst \<nu>\<mu>' \<star> snd \<nu>\<mu>') \<bullet> (fst \<nu>\<mu> \<star> snd \<nu>\<mu>)"
          using 1 hcomp_vcomp VV.seq_char VV.arr_char VV.comp_char
          by (metis (no_types, lifting) fst_conv snd_conv)
      qed
    qed

    lemma hcomp_is_functor:
    shows "functor VV.comp vcomp (\<lambda>\<nu>\<mu>. fst \<nu>\<mu> \<star> snd \<nu>\<mu>)"
      ..

    lemma ide_hcomp:
    assumes "ide f" and "ide g" and "src f = trg g"
    shows "ide (f \<star> g)"
      using assms VV.ide_char VV.arr_char H.preserves_ide [of "(f, g)"] by auto

    sublocale horizontal_composition vcomp hcomp src trg
      using src_hcomp trg_hcomp VV.arr_char not_arr_null hcomp_def null_char
      by (unfold_locales, auto)

    lemma has_horizontal_composition:
    shows "horizontal_composition vcomp hcomp src trg"
      ..

  end

  subsection "The Bicategory Span(C)"

  context span_bicategory
  begin

    interpretation VxVxV: product_category vcomp VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                          \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                 src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by auto

    interpretation HoHV: "functor" VVV.comp vcomp HoHV
      using functor_HoHV by blast
    interpretation HoVH: "functor" VVV.comp vcomp HoVH
      using functor_HoVH by blast

    lemma arr_eqI:
    assumes "par \<mu> \<mu>'" and "Chn \<mu> = Chn \<mu>'"
    shows "\<mu> = \<mu>'"
      using assms dom_char cod_char by auto

    interpretation L: endofunctor vcomp L
      using endofunctor_L by auto

    abbreviation \<l>
    where "\<l> f \<equiv> \<lparr>Chn = \<p>\<^sub>0[C.cod (Leg1 (Dom f)), Leg1 (Dom f)],
                  Dom = Dom (L f), Cod = Cod f\<rparr>"

    interpretation \<ll>: transformation_by_components vcomp vcomp L map \<l>
    proof
      have *: "\<And>f. ide f \<Longrightarrow> arrow_of_spans C (\<l> f)"
      proof -
        fix f
        assume f: "ide f"
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        interpret \<l>f: arrow_of_spans C \<open>\<l> f\<close>
        proof
          show Dom: "C.span (Leg0 (Dom (\<l> f))) (Leg1 (Dom (\<l> f)))"
            using f
            by (simp add: arrow_of_spans_hcomp arrow_of_spans.axioms(2)
                span_in_category.is_span)
          interpret Dom: span_in_category C \<open>Dom (\<l> f)\<close>
            using Dom by (unfold_locales, auto)
          show Cod: "C.span (Leg0 (Cod (\<l> f))) (Leg1 (Cod (\<l> f)))"
            using f hcomp_def trg_def src_def ide_mkObj C.pullback_commutes by force
          interpret Cod: span_in_category C \<open>Cod (\<l> f)\<close>
            using Cod by (unfold_locales, auto)
          show "\<guillemotleft>Chn (\<l> f) : Dom.apex \<rightarrow>\<^sub>C Cod.apex\<guillemotright>"
          proof -
            have "C.dom Dom.leg0 = C.cod f.dom.leg1 \<down>\<down> f.dom.leg1"
            proof -
              have "arr (trg f)"
                using f by simp
              hence "Dom (\<l> f) = \<lparr>Leg0 = f.dom.leg0 \<cdot> \<p>\<^sub>0[C.cod f.dom.leg1, f.dom.leg1],
                                 Leg1 = C.cod f.dom.leg1 \<cdot> \<p>\<^sub>1[C.cod f.dom.leg1, f.dom.leg1]\<rparr>"
                using f src_def trg_def hcomp_def by simp
              thus ?thesis
                using f Dom hcomp_def by auto
            qed
            thus ?thesis
              using f ide_char Dom.apex_def Cod.apex_def by simp
          qed
          show "Cod.leg0 \<cdot> Chn (\<l> f) = Dom.leg0"
            using f ide_char hcomp_def src_def trg_def C.comp_arr_ide ide_mkObj by simp
          show "Cod.leg1 \<cdot> Chn (\<l> f) = Dom.leg1"
            using f ide_char hcomp_def src_def trg_def C.pullback_commutes ide_mkObj
                  C.comp_arr_ide
            by (simp add: C.commutative_square_def)
        qed
        show "arrow_of_spans C (\<l> f)" ..
      qed
      show 0: "\<And>f. ide f \<Longrightarrow> \<guillemotleft>\<l> f : L f \<rightarrow> map f\<guillemotright>"
      proof -
        fix f
        assume f: "ide f"
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        interpret \<l>f: arrow_of_spans C \<open>\<l> f\<close>
          using f * by blast
        show "in_hom (\<l> f) (L f) (map f)"
        proof
          show 1: "arr (\<l> f)"
            using f * arr_char by blast
          show "dom (\<l> f) = L f"
            using f 1 dom_char ideD(2) by auto
          show "cod (\<l> f) = map f"
            using f 1 cod_char ideD(3) by auto
         qed
      qed
      show "\<And>\<mu>. arr \<mu> \<Longrightarrow> \<l> (cod \<mu>) \<bullet> L \<mu> = map \<mu> \<bullet> \<l> (dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "arr \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> arr_char by auto
        interpret \<l>_dom_\<mu>: arrow_of_spans C \<open>\<l> (dom \<mu>)\<close>
          using \<mu> * [of "dom \<mu>"] by fastforce
        interpret \<l>_cod_\<mu>: arrow_of_spans C \<open>\<l> (cod \<mu>)\<close>
          using \<mu> * [of "cod \<mu>"] by fastforce
        interpret L\<mu>: arrow_of_spans C \<open>L \<mu>\<close>
          using \<mu> arr_char by blast
        show "\<l> (cod \<mu>) \<bullet> L \<mu> = map \<mu> \<bullet> \<l> (dom \<mu>)"
        proof (intro arr_eqI)
          show par: "par (\<l> (cod \<mu>) \<bullet> L \<mu>) (map \<mu> \<bullet> \<l> (dom \<mu>))"
            using \<mu> 0 [of "dom \<mu>"] 0 [of "cod \<mu>"] by fastforce
          show "Chn (\<l> (cod \<mu>) \<bullet> L \<mu>) = Chn (map \<mu> \<bullet> \<l> (dom \<mu>))"
          proof -
            have "Chn (\<l> (cod \<mu>) \<bullet> L \<mu>) =
                   \<p>\<^sub>0[\<mu>.dtrg, \<mu>.cod.leg1] \<cdot>
                     \<langle>\<p>\<^sub>1[\<mu>.dtrg, \<mu>.dom.leg1] \<lbrakk>\<mu>.dtrg, \<mu>.cod.leg1\<rbrakk> \<mu>.chine \<cdot> \<p>\<^sub>0[\<mu>.dtrg, \<mu>.dom.leg1]\<rangle>"
            proof -
              have "Chn (\<l> (cod \<mu>) \<bullet> L \<mu>) = \<p>\<^sub>0[\<mu>.dtrg, \<mu>.cod.leg1] \<cdot> Chn (trg \<mu> \<star> \<mu>)"
              proof -
                have "Dom (trg \<mu> \<star> cod \<mu>) = Cod (trg \<mu> \<star> \<mu>)"
                  using \<mu> seq_char by fastforce
                moreover have "\<p>\<^sub>0[C.cod (Leg1 (Dom (cod \<mu>))), Leg1 (Dom (cod \<mu>))] \<cdot>
                                 Chn (trg \<mu> \<star> \<mu>) =
                               \<p>\<^sub>0[\<mu>.dtrg, \<mu>.cod.leg1] \<cdot> Chn (trg \<mu> \<star> \<mu>)"
                  by (simp add: \<mu> cod_char)
                moreover have "arrow_of_spans (\<cdot>)
                                 \<lparr>Chn = \<p>\<^sub>0[C.cod (Leg1 (Dom (cod \<mu>))), Leg1 (Dom (cod \<mu>))],
                                  Dom = Cod (trg \<mu> \<star> \<mu>), Cod = Cod (cod \<mu>)\<rparr>"
                  using \<mu> par seq_char by auto
                ultimately show ?thesis
                  using \<mu> vcomp_def L\<mu>.arrow_of_spans_axioms by auto
              qed
              moreover
              have "Chn (trg \<mu> \<star> \<mu>) = \<langle>\<p>\<^sub>1[\<mu>.dtrg, \<mu>.dom.leg1]
                                        \<lbrakk>\<mu>.dtrg, \<mu>.cod.leg1\<rbrakk>
                                       \<mu>.chine \<cdot> \<p>\<^sub>0[\<mu>.dtrg, \<mu>.dom.leg1]\<rangle>"
                using \<mu> hcomp_def chine_hcomp_trg_arr by simp
              ultimately show ?thesis
                using \<mu> by (auto simp add: cod_char)
            qed
            also have "... = \<mu>.chine \<cdot> \<p>\<^sub>0[C.cod \<mu>.dom.leg1, \<mu>.dom.leg1]"
              using \<mu> C.in_homE C.pullback_commutes [of "C.cod \<mu>.dom.leg1" "\<mu>.dom.leg1"]
                    C.comp_reduce ide_char C.prj_tuple(1)
              by auto
            also have "... = Chn (map \<mu> \<bullet> \<l> (dom \<mu>))"
              using \<mu> par seq_char dom_char vcomp_eq map_simp by simp
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    interpretation \<ll>: natural_isomorphism vcomp vcomp L map \<ll>.map
    proof
      fix f
      assume f: "ide f"
      show "iso (\<ll>.map f)"
      proof -
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        have 1: "\<ll>.map f = \<lparr>Chn = \<p>\<^sub>0[f.dtrg, f.leg1], Dom = Dom (trg f \<star> f), Cod = Dom f\<rparr>"
          using f ide_char cod_char by simp
        interpret \<l>f: arrow_of_spans C \<open>\<ll>.map f\<close>
          using f arr_char \<ll>.preserves_reflects_arr by fastforce
        let ?\<l>f' = "\<lparr>Chn = \<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> C.dom f.leg1\<rangle>,
                    Dom = Dom f, Cod = Dom (trg f \<star> f)\<rparr>"
        have 2: "C.inverse_arrows \<l>f.chine (Chn ?\<l>f')"
          using 1 C.pullback_arr_cod(2) [of "f.leg1"] by simp
        interpret \<l>f': arrow_of_spans C ?\<l>f'
        proof
          show Dom: "C.span (Leg0 (Dom ?\<l>f')) (Leg1 (Dom ?\<l>f'))"
            using f 1 by auto
          interpret Dom: span_in_category C \<open>Dom ?\<l>f'\<close>
            using Dom by (unfold_locales, auto)
          show Cod: "C.span (Leg0 (Cod ?\<l>f')) (Leg1 (Cod ?\<l>f'))"
            using f 1 \<l>f.dom.is_span by auto
          interpret Cod: span_in_category C \<open>Cod ?\<l>f'\<close>
            using Cod by (unfold_locales, auto)
          show "\<guillemotleft>Chn ?\<l>f' : Dom.apex \<rightarrow>\<^sub>C Cod.apex\<guillemotright>"
            using f src_def trg_def hcomp_def ide_mkObj Cod.apex_def Dom.apex_def
                  C.comp_arr_dom C.comp_cod_arr
            by auto
          show "Cod.leg0 \<cdot> Chn ?\<l>f' = Dom.leg0"
            using 2 \<l>f.leg0_commutes C.invert_side_of_triangle
            by (metis (no_types, lifting) "1" C.inverse_unique C.isoI \<l>f.dom.is_span
                arrow_of_spans_data.select_convs(2) arrow_of_spans_data.select_convs(3))
          show "Cod.leg1 \<cdot> Chn ?\<l>f' = Dom.leg1"
            using 2 \<l>f.leg1_commutes C.invert_side_of_triangle
            by (metis (no_types, lifting) "1" C.inverse_unique C.isoI \<l>f.dom.is_span
                arrow_of_spans_data.select_convs(2) arrow_of_spans_data.select_convs(3))
        qed
        have "inverse_arrows (\<ll>.map f) ?\<l>f'"
        proof
          show "ide (?\<l>f' \<bullet> \<ll>.map f)"
          proof -
            have "?\<l>f' \<bullet> \<ll>.map f = dom (\<ll>.map f)"
            proof -
              have "?\<l>f' \<bullet> \<ll>.map f =
                    \<lparr>Chn = f.dtrg \<down>\<down> f.leg1, Dom = Dom (\<ll>.map f), Cod = Dom (\<ll>.map f)\<rparr>"
                using f 1 2 f.arrow_of_spans_axioms \<l>f.arrow_of_spans_axioms
                      \<l>f'.arrow_of_spans_axioms vcomp_def ide_char arr_char
                by (simp add: vcomp_def C.comp_inv_arr)
              also have "... = dom (\<ll>.map f)"
              proof -
                have "C.cod f.dom.leg1 \<down>\<down> f.dom.leg1 = C.dom (Leg1 (Dom (hcomp (trg f) f)))"
                  using f f.arrow_of_spans_axioms hcomp_def src_def trg_def ide_mkObj
                  by auto
                thus ?thesis
                  using 1 f.arrow_of_spans_axioms arr_char dom_char \<l>f.dom.is_span
                        \<l>f.arrow_of_spans_axioms \<l>f'.cod.apex_def
                  by auto
              qed
              finally show ?thesis by blast
            qed
            thus ?thesis
              using \<l>f.arrow_of_spans_axioms arr_char by simp
          qed
          show "ide (\<ll>.map f \<bullet> ?\<l>f')"
          proof -
            have "\<ll>.map f \<bullet> ?\<l>f' = dom ?\<l>f'"
            proof -
              have "\<ll>.map f \<bullet> ?\<l>f' = \<lparr>Chn = Chn f, Dom = Dom ?\<l>f', Cod = Dom ?\<l>f'\<rparr>"
                using f 1 2 f.arrow_of_spans_axioms \<l>f.arrow_of_spans_axioms
                      \<l>f'.arrow_of_spans_axioms vcomp_def ide_char arr_char
                by fastforce
              also have "... = dom ?\<l>f'"
                using 1 \<l>f'.arrow_of_spans_axioms arr_char dom_char by simp
              finally show ?thesis by blast
            qed
            thus ?thesis
              using \<l>f'.arrow_of_spans_axioms arr_char by simp
          qed
        qed
        thus ?thesis by auto
      qed
    qed

    lemma \<ll>_is_natural_isomorphism:
    shows "natural_isomorphism vcomp vcomp L map \<ll>.map"
      ..

    interpretation equivalence_functor vcomp vcomp L
      using L.isomorphic_to_identity_is_equivalence \<ll>.natural_isomorphism_axioms by simp

    lemma equivalence_functor_L:
    shows "equivalence_functor vcomp vcomp L"
      ..

    interpretation R: endofunctor vcomp R
      using endofunctor_R by auto

    abbreviation \<r>
    where "\<r> f \<equiv> \<lparr>Chn = \<p>\<^sub>1[Leg0 (Dom f), C.cod (Leg0 (Dom f))],
                  Dom = Dom (R f), Cod = Cod f\<rparr>"

    interpretation \<rho>: transformation_by_components vcomp vcomp R map \<r>
    proof
      have *: "\<And>f. ide f \<Longrightarrow> arrow_of_spans C (\<r> f)"
      proof -
        fix f
        assume f: "ide f"
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        interpret \<r>f: arrow_of_spans C \<open>\<r> f\<close>
        proof
          show Dom: "C.span (Leg0 (Dom (\<r> f))) (Leg1 (Dom (\<r> f)))"
            using f
            by (simp add: arrow_of_spans_hcomp arrow_of_spans.axioms(2)
                span_in_category.is_span)
          interpret Dom: span_in_category C \<open>Dom (\<r> f)\<close>
            using Dom by (unfold_locales, auto)
          show Cod: "C.span (Leg0 (Cod (\<r> f))) (Leg1 (Cod (\<r> f)))"
            using f hcomp_def trg_def src_def ide_mkObj C.pullback_commutes by force
          interpret Cod: span_in_category C \<open>Cod (\<r> f)\<close>
            using Cod by (unfold_locales, auto)
          show "\<guillemotleft>Chn (\<r> f) : Dom.apex \<rightarrow>\<^sub>C Cod.apex\<guillemotright>"
          proof -
            have "C.dom Dom.leg0 = f.dom.leg0 \<down>\<down> C.cod f.dom.leg0"
            proof -
              have "arr (src f)"
                using f by simp
              hence "Dom (\<r> f) = \<lparr>Leg0 = C.cod f.dom.leg0 \<cdot> \<p>\<^sub>0[f.dom.leg0, C.cod f.dom.leg0],
                                  Leg1 = f.dom.leg1 \<cdot> \<p>\<^sub>1[f.dom.leg0, C.cod f.dom.leg0]\<rparr>"
                using f src_def trg_def by (simp add: hcomp_def)
              thus ?thesis
                using f ide_char Dom.apex_def Cod.apex_def by simp
            qed
            thus ?thesis
              using f ide_char Dom.apex_def Cod.apex_def by simp
          qed
          show "Cod.leg0 \<cdot> Chn (\<r> f) = Dom.leg0"
            using f ide_char hcomp_def src_def trg_def C.pullback_commutes
                  ide_mkObj C.comp_arr_ide
            by (simp add: C.commutative_square_def)
          show "Cod.leg1 \<cdot> Chn (\<r> f) = Dom.leg1"
            using f ide_char hcomp_def src_def trg_def ide_mkObj C.comp_arr_ide
            by (simp add: C.commutative_square_def)
        qed
        show "arrow_of_spans C (\<r> f)" ..
      qed
      show 0: "\<And>f. ide f \<Longrightarrow> in_hom (\<r> f) (R f) (map f)"
      proof -
        fix f
        assume f: "ide f"
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        interpret \<r>f: arrow_of_spans C \<open>\<r> f\<close>
          using f * by blast
        show "in_hom (\<r> f) (R f) (map f)"
        proof
          show 1: "arr (\<r> f)"
            using f * arr_char by blast
          show "dom (\<r> f) = R f"
            using f 1 dom_char ideD(2) by auto
          show "cod (\<r> f) = map f"
            using f 1 cod_char ideD(3) by auto
         qed
      qed
      show "\<And>\<mu>. arr \<mu> \<Longrightarrow> \<r> (cod \<mu>) \<bullet> R \<mu> = map \<mu> \<bullet> \<r> (dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "arr \<mu>"
        interpret \<mu>: arrow_of_spans C \<mu>
          using \<mu> arr_char by auto
        interpret \<r>_dom_\<mu>: arrow_of_spans C \<open>\<r> (dom \<mu>)\<close>
          using \<mu> * [of "dom \<mu>"] by fastforce
        interpret \<r>_cod_\<mu>: arrow_of_spans C \<open>\<r> (cod \<mu>)\<close>
          using \<mu> * [of "cod \<mu>"] by fastforce
        interpret R\<mu>: arrow_of_spans C \<open>R \<mu>\<close>
          using \<mu> arr_char by blast
        show "\<r> (cod \<mu>) \<bullet> R \<mu> = map \<mu> \<bullet> \<r> (dom \<mu>)"
        proof (intro arr_eqI)
          show par: "par (\<r> (cod \<mu>) \<bullet> R \<mu>) (map \<mu> \<bullet> \<r> (dom \<mu>))"
            using \<mu> 0 [of "dom \<mu>"] 0 [of "cod \<mu>"] by force
          show "Chn (\<r> (cod \<mu>) \<bullet> R \<mu>) = Chn (map \<mu> \<bullet> \<r> (dom \<mu>))"
          proof -
            have "Chn (\<r> (cod \<mu>) \<bullet> R \<mu>) =
                  \<p>\<^sub>1[\<mu>.cod.leg0, \<mu>.cod.src] \<cdot>
                    \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<mu>.dsrc] \<lbrakk>\<mu>.cod.leg0, \<mu>.cod.src\<rbrakk> \<p>\<^sub>0[\<mu>.dom.leg0, \<mu>.dsrc]\<rangle>"
            proof -
              have "Chn (\<r> (cod \<mu>) \<bullet> R \<mu>) = \<p>\<^sub>1[\<mu>.cod.leg0, \<mu>.cod.src] \<cdot> Chn (\<mu> \<star> src \<mu>)"
              proof -
                have "Dom (cod \<mu> \<star> src \<mu>) = Cod (\<mu> \<star> src \<mu>)"
                  using \<mu> seq_char by fastforce
                moreover have "\<p>\<^sub>1[Leg0 (Dom (cod \<mu>)), C.cod (Leg0 (Dom (cod \<mu>)))] \<cdot>
                                 Chn (\<mu> \<star> src \<mu>) =
                               \<p>\<^sub>1[\<mu>.cod.leg0, \<mu>.dsrc] \<cdot> Chn (\<mu> \<star> src \<mu>)"
                  by (simp add: \<mu> cod_char)
                moreover have "arrow_of_spans (\<cdot>)
                                 \<lparr>Chn = \<p>\<^sub>1[Leg0 (Dom (cod \<mu>)), C.cod (Leg0 (Dom (cod \<mu>)))],
                                  Dom = Cod (\<mu> \<star> src \<mu>), Cod = Cod (cod \<mu>)\<rparr>"
                  using \<mu> par seq_char by auto
                ultimately show ?thesis
                  using \<mu> vcomp_def R\<mu>.arrow_of_spans_axioms by auto
              qed
              moreover
              have "Chn (\<mu> \<star> src \<mu>) = \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<mu>.dsrc]
                                        \<lbrakk>\<mu>.cod.leg0, \<mu>.dsrc\<rbrakk>
                                       \<p>\<^sub>0[\<mu>.dom.leg0, \<mu>.dsrc]\<rangle>"
                using \<mu> hcomp_def chine_hcomp_arr_src by simp
              ultimately show ?thesis
                using \<mu> by (auto simp add: cod_char)
            qed
            also have "... = \<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, C.cod \<mu>.dom.leg0]"
              using \<mu> ide_char C.prj_tuple(2)
                    C.in_homE C.pullback_commutes [of "\<mu>.dom.leg0" "C.cod \<mu>.dom.leg0"]
                    C.comp_reduce
              by auto
            also have "... = Chn (map \<mu> \<bullet> \<r> (dom \<mu>))"
              using \<mu> par seq_char dom_char vcomp_eq map_simp by simp
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    interpretation \<rho>: natural_isomorphism vcomp vcomp R map \<rho>.map
    proof
      fix f
      assume f: "ide f"
      show "iso (\<rho>.map f)"
      proof -
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        have 1: "\<rho>.map f = \<lparr>Chn = \<p>\<^sub>1[f.leg0, f.dsrc], Dom = Dom (f \<star> src f), Cod = Dom f\<rparr>"
          using f ide_char by auto
        interpret \<rho>f: arrow_of_spans C \<open>\<rho>.map f\<close>
          using f arr_char \<rho>.preserves_reflects_arr by fastforce
        let ?\<rho>f' = "\<lparr>Chn = \<langle>C.dom f.leg0 \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>,
                     Dom = Dom f, Cod = Dom (f \<star> src f)\<rparr>"
        have 2: "C.inverse_arrows (Chn (\<rho>.map f)) (Chn ?\<rho>f')"
          using 1 C.pullback_arr_cod(1) [of "f.dom.leg0"] by simp
        interpret \<rho>f': arrow_of_spans C ?\<rho>f'
        proof
          show Dom: "C.span (Leg0 (Dom ?\<rho>f')) (Leg1 (Dom ?\<rho>f'))"
            using f 1 by auto
          interpret Dom: span_in_category C \<open>Dom ?\<rho>f'\<close>
            using Dom by (unfold_locales, auto)
          show Cod: "C.span (Leg0 (Cod ?\<rho>f')) (Leg1 (Cod ?\<rho>f'))"
            using f 1 \<rho>f.dom.is_span by auto
          interpret Cod: span_in_category C \<open>Cod ?\<rho>f'\<close>
            using Cod by (unfold_locales, auto)
          show "\<guillemotleft>Chn ?\<rho>f' : Dom.apex \<rightarrow>\<^sub>C Cod.apex\<guillemotright>"
            using f src_def trg_def hcomp_def ide_mkObj Cod.apex_def Dom.apex_def
                  C.comp_arr_dom C.comp_cod_arr
            by auto
          show "Cod.leg0 \<cdot> Chn ?\<rho>f' = Dom.leg0"
            using 2 \<rho>f.leg0_commutes C.invert_side_of_triangle
            by (metis (no_types, lifting) "1" C.inverse_unique C.isoI \<rho>f.dom.is_span
                arrow_of_spans_data.select_convs(2) arrow_of_spans_data.select_convs(3))
          show "Cod.leg1 \<cdot> Chn ?\<rho>f' = Dom.leg1"
            using 2 \<rho>f.leg1_commutes C.invert_side_of_triangle
            by (metis (no_types, lifting) "1" C.inverse_unique C.isoI \<rho>f.dom.is_span
                arrow_of_spans_data.select_convs(2) arrow_of_spans_data.select_convs(3))
        qed
        have "inverse_arrows (\<rho>.map f) ?\<rho>f'"
        proof
          show "ide (?\<rho>f' \<bullet> \<rho>.map f)"
          proof -
            have "?\<rho>f' \<bullet> \<rho>.map f = dom (\<rho>.map f)"
            proof -
              have "?\<rho>f' \<bullet> \<rho>.map f =
                     \<lparr>Chn = f.leg0 \<down>\<down> f.dsrc, Dom = Dom (\<rho>.map f), Cod = Dom (\<rho>.map f)\<rparr>"
                using f 1 2 f.arrow_of_spans_axioms
                      \<rho>f.arrow_of_spans_axioms \<rho>f'.arrow_of_spans_axioms
                      vcomp_def ide_char arr_char C.comp_inv_arr
                by (simp add: vcomp_def)
              also have "... = dom (\<rho>.map f)"
              proof -
                have "C.dom (Leg0 (Dom (f \<star> src f))) = C.dom (Leg1 (Dom (f \<star> src f)))"
                  using f f.arrow_of_spans_axioms hcomp_def src_def trg_def ide_mkObj
                  by auto
                thus ?thesis
                  using 1 f.arrow_of_spans_axioms arr_char dom_char \<rho>f.dom.is_span
                        \<rho>f.arrow_of_spans_axioms \<rho>f'.cod.apex_def \<rho>f.chine_simps(2)
                  by auto
              qed
              finally show ?thesis by blast
            qed
            thus ?thesis
              using \<rho>f.arrow_of_spans_axioms arr_char by simp
          qed
          show "ide (\<rho>.map f \<bullet> ?\<rho>f')"
          proof -
            have "\<rho>.map f \<bullet> ?\<rho>f' = dom ?\<rho>f'"
            proof -
              have "\<rho>.map f \<bullet> ?\<rho>f' = \<lparr>Chn = Chn f, Dom = Dom ?\<rho>f', Cod = Dom ?\<rho>f'\<rparr>"
                using f 1 2 f.arrow_of_spans_axioms
                      \<rho>f.arrow_of_spans_axioms \<rho>f'.arrow_of_spans_axioms
                      vcomp_def ide_char arr_char
                by fastforce
              also have "... = dom ?\<rho>f'"
                using 1 \<rho>f'.arrow_of_spans_axioms arr_char dom_char by simp
              finally show ?thesis by blast
            qed
            thus ?thesis
              using \<rho>f'.arrow_of_spans_axioms arr_char by simp
          qed
        qed
        thus ?thesis by auto
      qed
    qed

    lemma \<rho>_is_natural_isomorphism:
    shows "natural_isomorphism vcomp vcomp R map \<rho>.map"
      ..

    interpretation equivalence_functor vcomp vcomp R
      using R.isomorphic_to_identity_is_equivalence \<rho>.natural_isomorphism_axioms by simp

    lemma equivalence_functor_R:
    shows "equivalence_functor vcomp vcomp R"
      ..

    definition unit  ("\<i>[_]")
    where "\<i>[a] \<equiv> \<lparr>Chn = \<p>\<^sub>0[Chn a, Chn a], Dom = Dom (a \<star> a), Cod = Cod a\<rparr>"

    lemma unit_in_hom [intro]:
    assumes "obj a"
    shows "in_hhom \<i>[a] a a"
    and "\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
    proof -
      show "\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
      proof (intro in_homI)
        interpret a: identity_arrow_of_spans C a
          using assms obj_char ide_char' by auto
        have 0: "src a = trg a"
          using assms arr_char obj_char src_def trg_def by (elim objE, auto)
        interpret aa: arrow_of_spans C \<open>a \<star> a\<close>
          using assms 0 a.arrow_of_spans_axioms arrow_of_spans_hcomp by auto
        interpret aa: identity_arrow_of_spans C \<open>a \<star> a\<close>
        proof
          have "ide (a \<star> a)"
            using assms 0 obj_char H.preserves_ide by simp
          thus "C.ide aa.chine" using ide_char by auto
        qed
        have 1: "\<guillemotleft>\<p>\<^sub>0[a.chine, a.chine] : a.chine \<down>\<down> a.chine \<rightarrow>\<^sub>C a.chine\<guillemotright> \<and>
                 \<guillemotleft>\<p>\<^sub>1[a.chine, a.chine] : a.chine \<down>\<down> a.chine \<rightarrow>\<^sub>C a.chine\<guillemotright>"
          by auto
        have 2: "a.dom.leg0 = a.chine \<and> a.dom.leg1 = a.chine \<and>
                 a.cod.leg0 = a.chine \<and> a.cod.leg1 = a.chine"
          using assms obj_char by (cases a, simp_all)
        have 3: "a \<star> a = \<lparr>Chn = a.chine \<down>\<down> a.chine,
                          Dom = \<lparr>Leg0 = \<p>\<^sub>0[a.chine, a.chine], Leg1 = \<p>\<^sub>1[a.chine, a.chine]\<rparr>,
                          Cod = \<lparr>Leg0 = \<p>\<^sub>0[a.chine, a.chine], Leg1 = \<p>\<^sub>1[a.chine, a.chine]\<rparr>\<rparr>"
          using assms 0 1 2 chine_hcomp_ide_ide hcomp_def C.comp_cod_arr
                a.identity_arrow_of_spans_axioms ide_char'
          by auto
        have "aa.apex = a.chine \<down>\<down> a.chine"
          using 3 aa.chine_eq_apex by auto
        interpret \<i>a: arrow_of_spans C \<open>\<i>[a]\<close>
        proof
          have 4: "Dom \<i>[a] = Dom (a \<star> a)"
            using assms hcomp_def unit_def by simp
          have 5: "Cod \<i>[a] = Cod a"
            using assms unit_def by simp
          show Dom: "C.span (Leg0 (Dom \<i>[a])) (Leg1 (Dom \<i>[a]))"
            using 4 by simp
          interpret Dom: span_in_category C \<open>Dom \<i>[a]\<close>
            using Dom by (unfold_locales, auto)
          show Cod: "C.span (Leg0 (Cod \<i>[a])) (Leg1 (Cod \<i>[a]))"
            using 5 by simp
          interpret Cod: span_in_category C \<open>Cod \<i>[a]\<close>
            using Cod by (unfold_locales, auto)
          show "\<guillemotleft>Chn \<i>[a] : Dom.apex \<rightarrow>\<^sub>C Cod.apex\<guillemotright>"
          proof -
            have "\<guillemotleft>Chn \<i>[a] : a.chine \<down>\<down> a.chine \<rightarrow>\<^sub>C C.dom a.chine\<guillemotright>"
              using assms obj_char ide_char unit_def by simp
            moreover have "C.dom (Leg0 (Dom \<i>[a])) = Chn a \<down>\<down> Chn a"
              using assms 3 unit_def obj_char ide_char by simp
            moreover have "C.dom a.chine = C.dom Cod.leg0"
              using unit_def by auto
            ultimately show ?thesis by simp
          qed
          show "Cod.leg0 \<cdot> Chn \<i>[a] = Dom.leg0"
            unfolding unit_def using 1 2 3 C.comp_cod_arr by auto
          show "Cod.leg1 \<cdot> Chn \<i>[a] = Dom.leg1"
            unfolding unit_def using 1 2 3 C.comp_cod_arr C.pullback_ide_self by auto
        qed
        show "arr \<i>[a]"
          using \<i>a.arrow_of_spans_axioms arr_char by simp
        show "dom \<i>[a] = hcomp a a"
          using 3 unit_def \<i>a.arrow_of_spans_axioms arr_char dom_char \<i>a.dom.apex_def
          by auto
        show "cod \<i>[a] = a"
          using assms 3 obj_char arr_char dom_char cod_char unit_def
                \<i>a.arrow_of_spans_axioms
          by auto
      qed
      thus "in_hhom \<i>[a] a a"
        using assms
        by (metis arrI in_hhom_def objE vconn_implies_hpar(1) vconn_implies_hpar(2-4))
    qed

    lemma unit_simps [simp]:
    assumes "obj a"
    shows "src \<i>[a] = a" and "trg \<i>[a] = a"
    and "dom \<i>[a] = hcomp a a" and "cod \<i>[a] = a"
      using assms unit_in_hom by auto

    lemma iso_unit:
    assumes "obj a"
    shows "iso \<i>[a]"
    proof -
      have "Chn \<i>[a] = \<p>\<^sub>0[Chn a, Chn a]"
        unfolding unit_def by simp
      moreover have "C.iso \<p>\<^sub>0[Chn a, Chn a]"
        using assms C.ide_is_iso C.iso_is_arr C.iso_pullback_ide ide_char by blast
      ultimately show ?thesis
        using assms unit_in_hom iso_char by auto
    qed

  end

  locale two_composable_arrows_of_spans =
    span_bicategory +
  \<mu>: arrow_of_spans C \<mu> +
  \<nu>: arrow_of_spans C \<nu>
  for \<mu> (structure)
  and \<nu> (structure) +
  assumes composable: "src \<mu> = trg \<nu>"
  begin

    lemma are_arrows [simp]:
    shows "arr \<mu>" and "arr \<nu>"
      using arr_char \<mu>.arrow_of_spans_axioms \<nu>.arrow_of_spans_axioms by auto

    lemma legs_form_cospan:
    shows "C.cospan \<mu>.dom.leg0 \<nu>.dom.leg1" and "C.cospan \<mu>.cod.leg0 \<nu>.cod.leg1"
      using composable src_def trg_def by auto

    interpretation \<mu>\<nu>: arrow_of_spans C \<open>\<mu> \<star> \<nu>\<close>
      using arrow_of_spans_hcomp composable by auto

    lemma composite_is_arrow [simp]:
    shows "arr (\<mu> \<star> \<nu>)"
      using \<mu>\<nu>.arrow_of_spans_axioms arr_char by auto

    lemma composite_in_hom [intro]:
    shows "\<guillemotleft>\<mu> \<star> \<nu> : dom \<mu> \<star> dom \<nu> \<Rightarrow> cod \<mu> \<star> cod \<nu>\<guillemotright>"
      using composable by auto

    lemma composite_simps [simp]:
    shows "src (\<mu> \<star> \<nu>) = src \<nu>" and "trg (\<mu> \<star> \<nu>) = trg \<mu>"
    and "dom (\<mu> \<star> \<nu>) = dom \<mu> \<star> dom \<nu>" and "cod (\<mu> \<star> \<nu>) = cod \<mu> \<star> cod \<nu>"
      by (simp_all add: composable)

    lemma chine_composite:
    shows "Chn (\<mu> \<star> \<nu>) = \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1]
                           \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk>
                          \<nu>.chine \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1]\<rangle>"
       unfolding hcomp_def chine_hcomp_def using composable by simp

    lemma chine_composite_in_hom [intro]:
    shows "\<guillemotleft>Chn (\<mu> \<star> \<nu>) : \<mu>.dom.leg0 \<down>\<down> \<nu>.dom.leg1 \<rightarrow>\<^sub>C \<mu>.cod.leg0 \<down>\<down> \<nu>.cod.leg1\<guillemotright>"
      using hcomp_def chine_hcomp_props(1) composable by auto

  end

  sublocale two_composable_arrows_of_spans \<subseteq> arrow_of_spans C \<open>\<mu> \<star> \<nu>\<close>
  proof -
    interpret Dom\<mu>_Dom\<nu>: composite_span C prj0 prj1 \<open>Dom \<mu>\<close> \<open>Dom \<nu>\<close>
      using legs_form_cospan(1) by (unfold_locales, auto)
    interpret Cod\<mu>_Cod\<nu>: composite_span C prj0 prj1 \<open>Cod \<mu>\<close> \<open>Cod \<nu>\<close>
      using legs_form_cospan(1) by (unfold_locales, auto)
    interpret Dom_\<mu>\<nu>: span_in_category C \<open>Dom (\<mu> \<star> \<nu>)\<close>
      apply unfold_locales apply (unfold hcomp_def)
      using Dom\<mu>_Dom\<nu>.apex_def Dom\<mu>_Dom\<nu>.leg_simps(1) are_arrows(1) composable by auto
    interpret Cod_\<mu>\<nu>: span_in_category C \<open>Cod (\<mu> \<star> \<nu>)\<close>
      apply unfold_locales apply (unfold hcomp_def)
      using Cod\<mu>_Cod\<nu>.apex_def Cod\<mu>_Cod\<nu>.leg_simps(1) are_arrows(1) composable by auto
    show "arrow_of_spans C (\<mu> \<star> \<nu>)"
    proof
      show "\<guillemotleft>Chn (hcomp \<mu> \<nu>) : Dom_\<mu>\<nu>.apex \<rightarrow>\<^sub>C Cod_\<mu>\<nu>.apex\<guillemotright>"
        unfolding hcomp_def
        using are_arrows(1) are_arrows(2) arrow_of_spans_hcomp composable hcomp_def
              arrow_of_spans.chine_in_hom Cod\<mu>_Cod\<nu>.leg_simps(4) Dom\<mu>_Dom\<nu>.leg_simps(3)
              Dom\<mu>_Dom\<nu>.leg_simps(4) chine_composite_in_hom
        by auto
      show "Cod_\<mu>\<nu>.leg0 \<cdot> Chn (hcomp \<mu> \<nu>) = Dom_\<mu>\<nu>.leg0"
      proof (unfold hcomp_def)
        have "arrow_of_spans C
                \<lparr>Chn = chine_hcomp \<mu> \<nu>, Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>"
          using arrow_of_spans_hcomp composable hcomp_def by auto
        thus "Leg0 (Cod (if arr \<nu> \<and> arr \<mu> \<and> src \<mu> = trg \<nu> then
                            \<lparr>Chn = chine_hcomp \<mu> \<nu>,
                             Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>
                         else null)) \<cdot>
                      Chn (if arr \<nu> \<and> arr \<mu> \<and> src \<mu> = trg \<nu> then
                             \<lparr>Chn = chine_hcomp \<mu> \<nu>,
                              Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>
                           else null) =
              Leg0 (Dom (if arr \<nu> \<and> arr \<mu> \<and> src \<mu> = trg \<nu> then
                            \<lparr>Chn = chine_hcomp \<mu> \<nu>,
                             Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>
                         else null))"
          using arrow_of_spans.leg0_commutes composable by fastforce
      qed
      show "Cod_\<mu>\<nu>.leg1 \<cdot> Chn (hcomp \<mu> \<nu>) = Dom_\<mu>\<nu>.leg1"
      proof (unfold hcomp_def)
        have "arrow_of_spans C
                \<lparr>Chn = chine_hcomp \<mu> \<nu>, Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>"
          using arrow_of_spans_hcomp composable hcomp_def by force
        thus "Leg1 (Cod (if arr \<nu> \<and> arr \<mu> \<and> src \<mu> = trg \<nu> then
                           \<lparr>Chn = chine_hcomp \<mu> \<nu>,
                            Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>
                         else null)) \<cdot>
                    Chn (if arr \<nu> \<and> arr \<mu> \<and> src \<mu> = trg \<nu> then
                           \<lparr>Chn = chine_hcomp \<mu> \<nu>,
                            Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>
                         else null) =
              Leg1 (Dom (if arr \<nu> \<and> arr \<mu> \<and> src \<mu> = trg \<nu> then
                           \<lparr>Chn = chine_hcomp \<mu> \<nu>,
                            Dom = Dom\<mu>_Dom\<nu>.this, Cod = Cod\<mu>_Cod\<nu>.this\<rparr>
                         else null))"
          using arrow_of_spans.leg1_commutes composable by force
        qed
    qed
  qed

  locale two_composable_identity_arrows_of_spans =
     two_composable_arrows_of_spans +
  \<mu>: identity_arrow_of_spans C \<mu> +
  \<nu>: identity_arrow_of_spans C \<nu>
  begin

    lemma are_identities [simp]:
    shows "ide \<mu>" and "ide \<nu>"
      using ide_char \<mu>.arrow_of_spans_axioms \<nu>.arrow_of_spans_axioms by auto

    interpretation VxV: product_category vcomp vcomp ..
    interpretation VV: subcategory VxV.comp \<open>\<lambda>\<nu>\<mu>. arr (fst \<nu>\<mu>) \<and> arr (snd \<nu>\<mu>) \<and>
                                                   src (fst \<nu>\<mu>) = trg (snd \<nu>\<mu>)\<close>
      by (unfold_locales, simp_all)
    interpretation H: "functor" VV.comp vcomp \<open>\<lambda>\<nu>\<mu>. fst \<nu>\<mu> \<star> snd \<nu>\<mu>\<close>
      using hcomp_is_functor by auto

    interpretation \<mu>\<nu>: identity_arrow_of_spans C \<open>\<mu> \<star> \<nu>\<close>
    proof
      have "VV.ide (\<mu>, \<nu>)"
        using VV.ide_char composable by auto
      hence "ide (hcomp \<mu> \<nu>)"
        using H.preserves_ide [of "(\<mu>, \<nu>)"] by simp
      thus "C.ide chine"
        using ide_char by simp
    qed

    lemma ide_composite [simp]:
    shows "ide (\<mu> \<star> \<nu>)"
      using \<mu>\<nu>.identity_arrow_of_spans_axioms arrow_of_spans_axioms ide_char by auto

    lemma apex_composite:
    shows "\<mu>\<nu>.apex = \<mu>.leg0 \<down>\<down> \<nu>.leg1"
      using dom.apex_def hcomp_def chine_hcomp_ide_ide composable legs_form_cospan
      by simp

    lemma leg0_composite:
    shows "\<mu>\<nu>.leg0 = \<nu>.leg0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1]"
      using dom.apex_def hcomp_def composable legs_form_cospan by simp

    lemma leg1_composite:
    shows "\<mu>\<nu>.leg1 = \<mu>.leg1 \<cdot> \<p>\<^sub>1[\<mu>.leg0, \<nu>.leg1]"
      using dom.apex_def hcomp_def composable legs_form_cospan by simp

    lemma chine_composite:
    shows "Chn (\<mu> \<star> \<nu>) = \<mu>.leg0 \<down>\<down> \<nu>.leg1"
       unfolding hcomp_def using chine_hcomp_ide_ide composable by simp

    abbreviation prj\<^sub>0
    where "prj\<^sub>0 \<equiv> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1]"

    abbreviation prj\<^sub>1
    where "prj\<^sub>1 \<equiv> \<p>\<^sub>1[\<mu>.leg0, \<nu>.leg1]"

    lemma prj_in_hom [intro]:
    shows "\<guillemotleft>prj\<^sub>1 : \<mu>.leg0 \<down>\<down> \<nu>.leg1 \<rightarrow>\<^sub>C \<mu>.apex\<guillemotright>"
    and "\<guillemotleft>prj\<^sub>0 : \<mu>.leg0 \<down>\<down> \<nu>.leg1 \<rightarrow>\<^sub>C \<nu>.apex\<guillemotright>"
      using legs_form_cospan by auto

    lemma prj_simps [simp]:
    shows "C.arr prj\<^sub>1" and "C.dom prj\<^sub>1 = \<mu>.leg0 \<down>\<down> \<nu>.leg1" and "C.cod prj\<^sub>1 = \<mu>.apex"
    and "C.arr prj\<^sub>0" and "C.dom prj\<^sub>0 = \<mu>.leg0 \<down>\<down> \<nu>.leg1" and "C.cod prj\<^sub>0 = \<nu>.apex"
      using prj_in_hom by auto

    sublocale identity_arrow_of_spans C \<open>\<mu> \<star> \<nu>\<close>
      using apex_composite dom.ide_apex chine_composite by (unfold_locales, auto)

  end

  locale three_composable_arrows_of_spans =
     span_bicategory +
  \<mu>: arrow_of_spans C \<mu> +
  \<nu>: arrow_of_spans C \<nu> +
  \<pi>: arrow_of_spans C \<pi> +
  \<mu>\<nu>: two_composable_arrows_of_spans C prj0 prj1 \<mu> \<nu> +
  \<nu>\<pi>: two_composable_arrows_of_spans C prj0 prj1 \<nu> \<pi>
  for \<mu> (structure)
  and \<nu> (structure)
  and \<pi> (structure)
  begin

    interpretation \<mu>\<nu>\<pi>: arrow_of_spans C \<open>\<mu> \<star> \<nu> \<star> \<pi>\<close>
      using \<mu>.arrow_of_spans_axioms \<nu>\<pi>.arrow_of_spans_axioms
            arrow_of_spans_hcomp arr_char \<mu>\<nu>.composable \<nu>\<pi>.composable
      by force

    interpretation \<mu>\<nu>_\<pi>: arrow_of_spans C \<open>(\<mu> \<star> \<nu>) \<star> \<pi>\<close>
      using \<mu>\<nu>.arrow_of_spans_axioms \<pi>.arrow_of_spans_axioms
            arrow_of_spans_hcomp arr_char \<mu>\<nu>.composable \<nu>\<pi>.composable
      by force

    lemma composites_are_arrows [simp]:
    shows "arr (\<mu> \<star> \<nu> \<star> \<pi>)" and "arr ((\<mu> \<star> \<nu>) \<star> \<pi>)"
      using \<mu>\<nu>\<pi>.arrow_of_spans_axioms \<mu>\<nu>_\<pi>.arrow_of_spans_axioms arr_char by auto

    lemma composite_in_hom [intro]:
    shows "\<guillemotleft>\<mu> \<star> \<nu> \<star> \<pi> : dom \<mu> \<star> dom \<nu> \<star> dom \<pi> \<Rightarrow> cod \<mu> \<star> cod \<nu> \<star> cod \<pi>\<guillemotright>"
    and "\<guillemotleft>(\<mu> \<star> \<nu>) \<star> \<pi> : (dom \<mu> \<star> dom \<nu>) \<star> dom \<pi> \<Rightarrow> (cod \<mu> \<star> cod \<nu>) \<star> cod \<pi>\<guillemotright>"
      using \<mu>\<nu>.composable \<nu>\<pi>.composable by auto

    lemma composite_simps [simp]:
    shows "src (\<mu> \<star> \<nu> \<star> \<pi>) = src \<pi>"
    and "src ((\<mu> \<star> \<nu>) \<star> \<pi>) = src \<pi>"
    and "trg (\<mu> \<star> \<nu> \<star> \<pi>) = trg \<mu>"
    and "trg ((\<mu> \<star> \<nu>) \<star> \<pi>) = trg \<mu>"
    and "dom (\<mu> \<star> \<nu> \<star> \<pi>) = dom \<mu> \<star> dom \<nu> \<star> dom \<pi>"
    and "dom ((\<mu> \<star> \<nu>) \<star> \<pi>) = (dom \<mu> \<star> dom \<nu>) \<star> dom \<pi>"
    and "cod (\<mu> \<star> \<nu> \<star> \<pi>) = cod \<mu> \<star> cod \<nu> \<star> cod \<pi>"
    and "cod ((\<mu> \<star> \<nu>) \<star> \<pi>) = (cod \<mu> \<star> cod \<nu>) \<star> cod \<pi>"
      by (auto simp add: \<mu>\<nu>.composable \<nu>\<pi>.composable)

    lemma chine_composite:
    shows "\<mu>\<nu>\<pi>.chine =
             \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]]
               \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]\<rbrakk>
              \<langle>\<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]
                \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk>
               \<pi>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<pi>.dom.leg1]\<rangle> \<cdot>
                 \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]]\<rangle>"
    and "\<mu>\<nu>_\<pi>.chine =
           \<langle>\<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1]
              \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk>
            \<nu>.chine \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1]\<rangle> \<cdot>
              \<p>\<^sub>1[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]
              \<lbrakk>\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1\<rbrakk>
            \<pi>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]\<rangle>"
    proof -
      show "\<mu>\<nu>\<pi>.chine =
             \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]]
               \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]\<rbrakk>
              \<langle>\<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]
                \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk>
               \<pi>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<pi>.dom.leg1]\<rangle> \<cdot>
                 \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]]\<rangle>"
       unfolding hcomp_def chine_hcomp_def \<mu>\<nu>.composable \<nu>\<pi>.composable
       using trg_def \<nu>\<pi>.are_arrows(1-2) \<nu>\<pi>.composable \<nu>\<pi>.composite_is_arrow
             \<nu>\<pi>.composite_simps(2) hcomp_def
       by (simp add: chine_hcomp_def)
     show "\<mu>\<nu>_\<pi>.chine =
             \<langle>\<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1]
                \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk>
              \<nu>.chine \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1]\<rangle> \<cdot>
                \<p>\<^sub>1[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]
                \<lbrakk>\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1\<rbrakk>
              \<pi>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]\<rangle>"
        unfolding hcomp_def chine_hcomp_def \<mu>\<nu>.composable \<nu>\<pi>.composable
        using src_def \<mu>\<nu>.are_arrows(1-2) \<mu>\<nu>.composable \<mu>\<nu>.composite_is_arrow
              \<mu>\<nu>.composite_simps(1) hcomp_def \<nu>\<pi>.composable
        by (simp add: chine_hcomp_def)
    qed

  end

  locale three_composable_identity_arrows_of_spans =
    three_composable_arrows_of_spans +
  \<mu>: identity_arrow_of_spans C \<mu> +
  \<nu>: identity_arrow_of_spans C \<nu> +
  \<pi>: identity_arrow_of_spans C \<pi> +
  \<mu>\<nu>: two_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<nu> +
  \<nu>\<pi>: two_composable_identity_arrows_of_spans C prj0 prj1 \<nu> \<pi>
  begin

    lemma composites_are_identities [simp]:
    shows "ide (\<mu> \<star> \<nu> \<star> \<pi>)" and "ide ((\<mu> \<star> \<nu>) \<star> \<pi>)"
    proof -
      interpret \<mu>_H\<nu>\<pi>: two_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<open>\<nu> \<star> \<pi>\<close>
        using \<mu>\<nu>.composable \<nu>\<pi>.composable
        by (unfold_locales, simp)
      show "ide (\<mu> \<star> \<nu> \<star> \<pi>)"
        by auto
      interpret H\<mu>\<nu>_\<pi>: two_composable_identity_arrows_of_spans C prj0 prj1 \<open>\<mu> \<star> \<nu>\<close> \<pi>
        using \<mu>\<nu>.composable \<nu>\<pi>.composable
        by (unfold_locales, simp)
      show "ide ((\<mu> \<star> \<nu>) \<star> \<pi>)"
        by auto
    qed

    interpretation \<mu>\<nu>\<pi>: identity_arrow_of_spans C \<open>\<mu> \<star> \<nu> \<star> \<pi>\<close>
      using composites_are_identities ide_char' by auto
    interpretation \<mu>\<nu>_\<pi>: identity_arrow_of_spans C \<open>(\<mu> \<star> \<nu>) \<star> \<pi>\<close>
      using composites_are_identities ide_char' by auto

    abbreviation Prj\<^sub>1\<^sub>1
    where "Prj\<^sub>1\<^sub>1 \<equiv> \<p>\<^sub>1[\<mu>.leg0, \<nu>.leg1] \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1], \<pi>.leg1]"
    abbreviation Prj\<^sub>0\<^sub>1
    where "Prj\<^sub>0\<^sub>1 \<equiv> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1] \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1], \<pi>.leg1]"
    abbreviation Prj\<^sub>0
    where "Prj\<^sub>0 \<equiv> \<p>\<^sub>0[\<nu>.leg0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1], \<pi>.leg1]"

    abbreviation Prj\<^sub>1
    where "Prj\<^sub>1 \<equiv> \<p>\<^sub>1[\<mu>.leg0, \<nu>.leg1 \<cdot> \<p>\<^sub>1[\<nu>.leg0, \<pi>.leg1]]"
    abbreviation Prj\<^sub>1\<^sub>0
    where "Prj\<^sub>1\<^sub>0 \<equiv> \<p>\<^sub>1[\<nu>.leg0, \<pi>.leg1] \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<p>\<^sub>1[\<nu>.leg0, \<pi>.leg1]]"
    abbreviation Prj\<^sub>0\<^sub>0
    where "Prj\<^sub>0\<^sub>0 \<equiv> \<p>\<^sub>0[\<nu>.leg0, \<pi>.leg1] \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<p>\<^sub>1[\<nu>.leg0, \<pi>.leg1]]"

    lemma leg0_composite:
    shows "\<mu>\<nu>\<pi>.leg0 = \<pi>.leg0 \<cdot> Prj\<^sub>0\<^sub>0"
    and "\<mu>\<nu>_\<pi>.leg0 = \<pi>.leg0 \<cdot> Prj\<^sub>0"
    proof -
      show "\<mu>\<nu>\<pi>.leg0 = \<pi>.leg0 \<cdot> Prj\<^sub>0\<^sub>0"
        using hcomp_def \<mu>\<nu>.composable \<nu>\<pi>.composite_is_arrow \<nu>\<pi>.composite_simps(2)
              C.comp_assoc
        by auto
      show "\<mu>\<nu>_\<pi>.leg0 = \<pi>.leg0 \<cdot> Prj\<^sub>0"
        using hcomp_def \<mu>\<nu>.composite_is_arrow \<mu>\<nu>.composite_simps(1) \<nu>\<pi>.composable by auto
    qed

    lemma leg1_composite:
    shows "\<mu>\<nu>\<pi>.leg1 = \<mu>.leg1 \<cdot> Prj\<^sub>1"
    and "\<mu>\<nu>_\<pi>.leg1 = \<mu>.leg1 \<cdot> Prj\<^sub>1\<^sub>1"
    proof -
      show "\<mu>\<nu>\<pi>.leg1 = \<mu>.leg1 \<cdot> Prj\<^sub>1"
        using hcomp_def \<mu>\<nu>.composable \<nu>\<pi>.composite_is_arrow \<nu>\<pi>.composite_simps(2) by auto
      show "\<mu>\<nu>_\<pi>.leg1 = \<mu>.leg1 \<cdot> Prj\<^sub>1\<^sub>1"
        using hcomp_def \<mu>\<nu>.composite_is_arrow \<mu>\<nu>.composite_simps(1) \<nu>\<pi>.composable
              C.comp_assoc
        by auto
    qed

    definition chine_assoc
    where "chine_assoc \<equiv>
           \<langle>Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.leg0, \<nu>.leg1 \<cdot> \<p>\<^sub>1[\<nu>.leg0, \<pi>.leg1]\<rbrakk> \<langle>Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>.leg1\<rbrakk> Prj\<^sub>0\<rangle>\<rangle>"

    definition chine_assoc'
    where "chine_assoc' \<equiv>
           \<langle>\<langle>Prj\<^sub>1 \<lbrakk>\<mu>.leg0, \<nu>.leg1\<rbrakk> Prj\<^sub>1\<^sub>0\<rangle> \<lbrakk>\<nu>.leg0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1], \<pi>.leg1\<rbrakk> Prj\<^sub>0\<^sub>0\<rangle>"

    (*
     * Don't be fooled by how short the following proofs look -- there's a heck of a lot
     * going on behind the scenes here!
     *)
    lemma chine_composite:
    shows "\<mu>\<nu>_\<pi>.chine = \<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0 \<down>\<down> \<pi>.leg1"
    and "\<mu>\<nu>\<pi>.chine = \<mu>.leg0 \<down>\<down> \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1"
    proof -
      show "\<mu>\<nu>_\<pi>.chine = \<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0 \<down>\<down> \<pi>.leg1"
        using hcomp_def chine_hcomp_arr_ide [of "hcomp \<mu> \<nu>" \<pi>] chine_hcomp_ide_ide
              src_def trg_def \<mu>\<nu>.composable \<nu>\<pi>.composable \<mu>\<nu>.ide_composite
              \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities(2)
        by simp
      show "\<mu>\<nu>\<pi>.chine = \<mu>.leg0 \<down>\<down> \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1"
        using hcomp_def chine_hcomp_ide_arr [of \<mu> "hcomp \<nu> \<pi>"] chine_hcomp_ide_ide
              src_def trg_def \<mu>\<nu>.composable \<nu>\<pi>.composable \<nu>\<pi>.ide_composite
              \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities(2)
        by simp
    qed

    lemma prj_in_hom [intro]:
    shows "\<guillemotleft>Prj\<^sub>1\<^sub>1 : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<mu>.apex\<guillemotright>"
    and "\<guillemotleft>Prj\<^sub>0\<^sub>1 : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<nu>.apex\<guillemotright>"
    and "\<guillemotleft>Prj\<^sub>0 : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<pi>.apex\<guillemotright>"
    and "\<guillemotleft>Prj\<^sub>1 : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<mu>.apex\<guillemotright>"
    and "\<guillemotleft>Prj\<^sub>1\<^sub>0 : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<nu>.apex\<guillemotright>"
    and "\<guillemotleft>Prj\<^sub>0\<^sub>0 : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<pi>.apex\<guillemotright>"
      using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def chine_composite by auto

    lemma prj_simps [simp]:
    shows "C.arr Prj\<^sub>1\<^sub>1"
    and "C.arr Prj\<^sub>0\<^sub>1"
    and "C.arr Prj\<^sub>0"
    and "C.dom Prj\<^sub>1\<^sub>1 = \<mu>\<nu>_\<pi>.chine"
    and "C.dom Prj\<^sub>0\<^sub>1 = \<mu>\<nu>_\<pi>.chine"
    and "C.dom Prj\<^sub>0 = \<mu>\<nu>_\<pi>.chine"
    and "C.cod Prj\<^sub>1\<^sub>1 = \<mu>.apex"
    and "C.cod Prj\<^sub>0\<^sub>1 = \<nu>.apex"
    and "C.cod Prj\<^sub>0 = \<pi>.apex"
    and "C.arr Prj\<^sub>1"
    and "C.arr Prj\<^sub>1\<^sub>0"
    and "C.arr Prj\<^sub>0\<^sub>0"
    and "C.dom Prj\<^sub>1 = \<mu>\<nu>\<pi>.chine"
    and "C.dom Prj\<^sub>1\<^sub>0 = \<mu>\<nu>\<pi>.chine"
    and "C.dom Prj\<^sub>0\<^sub>0 = \<mu>\<nu>\<pi>.chine"
    and "C.cod Prj\<^sub>1 = \<mu>.apex"
    and "C.cod Prj\<^sub>1\<^sub>0 = \<nu>.apex"
    and "C.cod Prj\<^sub>0\<^sub>0 = \<pi>.apex"
      using prj_in_hom by auto

    lemma chine_assoc_props:
    shows "\<guillemotleft>chine_assoc : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>\<pi>.chine\<guillemotright>"
    and "Prj\<^sub>1 \<cdot> chine_assoc = Prj\<^sub>1\<^sub>1"
    and "Prj\<^sub>1\<^sub>0 \<cdot> chine_assoc = Prj\<^sub>0\<^sub>1"
    and "Prj\<^sub>0\<^sub>0 \<cdot> chine_assoc = Prj\<^sub>0"
    proof -
      have 1: "\<nu>.leg0 \<cdot> Prj\<^sub>0\<^sub>1 = \<pi>.leg1 \<cdot> Prj\<^sub>0"
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
              C.pullback_commutes [of "\<nu>.leg0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1]" \<pi>.leg1] C.comp_assoc
        by auto
      have 2: "\<mu>.leg0 \<cdot> Prj\<^sub>1\<^sub>1 = \<nu>.leg1 \<cdot> Prj\<^sub>0\<^sub>1"
      proof -
        have "\<mu>.leg0 \<cdot> Prj\<^sub>1\<^sub>1 = (\<mu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>1) \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1]"
          using C.comp_assoc by auto
        also have "... = \<nu>.leg1 \<cdot> Prj\<^sub>0\<^sub>1"
          using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
                C.pullback_commutes
          by (auto simp add: C.commutative_square_def C.comp_assoc)
        finally show ?thesis by simp
      qed
      show "\<guillemotleft>chine_assoc : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>\<pi>.chine\<guillemotright>"
        unfolding chine_assoc_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def chine_composite C.comp_assoc by auto
      show "Prj\<^sub>1 \<cdot> chine_assoc = Prj\<^sub>1\<^sub>1"
        unfolding chine_assoc_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def C.comp_assoc
        by auto
      show "Prj\<^sub>1\<^sub>0 \<cdot> chine_assoc = Prj\<^sub>0\<^sub>1"
        unfolding chine_assoc_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def C.comp_assoc
        by auto
      show "Prj\<^sub>0\<^sub>0 \<cdot> chine_assoc = Prj\<^sub>0"
        unfolding chine_assoc_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def C.comp_assoc
        by auto
    qed

    lemma chine_assoc_in_hom [intro]:
    shows "\<guillemotleft>chine_assoc : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>\<pi>.chine\<guillemotright>"
      using chine_assoc_props(1) by simp

    lemma prj_chine_assoc [simp]:
    shows "Prj\<^sub>1 \<cdot> chine_assoc = Prj\<^sub>1\<^sub>1"
    and "Prj\<^sub>1\<^sub>0 \<cdot> chine_assoc = Prj\<^sub>0\<^sub>1"
    and "Prj\<^sub>0\<^sub>0 \<cdot> chine_assoc = Prj\<^sub>0"
      using chine_assoc_props(2-4) by auto

    lemma chine_assoc'_props:
    shows "\<guillemotleft>chine_assoc' : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>_\<pi>.chine\<guillemotright>"
    and "Prj\<^sub>1\<^sub>1 \<cdot> chine_assoc' = Prj\<^sub>1"
    and "Prj\<^sub>0\<^sub>1 \<cdot> chine_assoc' = Prj\<^sub>1\<^sub>0"
    and "Prj\<^sub>0 \<cdot> chine_assoc' = Prj\<^sub>0\<^sub>0"
    proof -
      have 1: "\<mu>.leg0 \<cdot> Prj\<^sub>1 = \<nu>.leg1 \<cdot> Prj\<^sub>1\<^sub>0"
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable
              src_def trg_def C.pullback_commutes [of \<mu>.leg0 "\<nu>.leg1 \<cdot> \<p>\<^sub>1[\<nu>.leg0, \<pi>.leg1]"]
              C.comp_assoc
        by auto
      have 2: "\<nu>.leg0 \<cdot> Prj\<^sub>1\<^sub>0 = \<pi>.leg1 \<cdot> Prj\<^sub>0\<^sub>0"
      proof -
        have "\<nu>.leg0 \<cdot> Prj\<^sub>1\<^sub>0 = (\<nu>.leg0 \<cdot> \<nu>\<pi>.prj\<^sub>1) \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1]"
          using C.comp_assoc by simp
        also have "... = \<pi>.leg1 \<cdot> Prj\<^sub>0\<^sub>0"
          using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
                C.pullback_commutes
          by (auto simp add: C.commutative_square_def C.comp_assoc)
        finally show ?thesis by auto
      qed
      show "\<guillemotleft>chine_assoc' : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>_\<pi>.chine\<guillemotright>"
        unfolding chine_assoc'_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def chine_composite C.comp_assoc
        by auto
      show "Prj\<^sub>1\<^sub>1 \<cdot> chine_assoc' = Prj\<^sub>1"
          unfolding chine_assoc'_def
          using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
                src_def trg_def C.comp_assoc
          by auto
      show "Prj\<^sub>0\<^sub>1 \<cdot> chine_assoc' = Prj\<^sub>1\<^sub>0"
        unfolding chine_assoc'_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def C.comp_assoc
        by auto
      show "Prj\<^sub>0 \<cdot> chine_assoc' = Prj\<^sub>0\<^sub>0"
        unfolding chine_assoc'_def
        using \<mu>\<nu>.are_identities \<nu>\<pi>.are_identities \<mu>\<nu>.composable \<nu>\<pi>.composable 1 2
              src_def trg_def C.comp_assoc
        by auto
    qed

    lemma chine_assoc'_in_hom [intro]:
    shows "\<guillemotleft>chine_assoc' : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>_\<pi>.chine\<guillemotright>"
      using chine_assoc'_props(1) by simp

    lemma prj_chine_assoc' [simp]:
    shows "Prj\<^sub>1\<^sub>1 \<cdot> chine_assoc' = Prj\<^sub>1"
    and "Prj\<^sub>0\<^sub>1 \<cdot> chine_assoc' = Prj\<^sub>1\<^sub>0"
    and "Prj\<^sub>0 \<cdot> chine_assoc' = Prj\<^sub>0\<^sub>0"
      using chine_assoc'_props(2-4) by auto

    lemma prj_joint_monic:
    assumes "\<guillemotleft>h: a \<rightarrow>\<^sub>C \<mu>\<nu>_\<pi>.chine\<guillemotright>" and "\<guillemotleft>h': a \<rightarrow>\<^sub>C \<mu>\<nu>_\<pi>.chine\<guillemotright>"
    and "Prj\<^sub>1\<^sub>1 \<cdot> h = Prj\<^sub>1\<^sub>1 \<cdot> h'" and "Prj\<^sub>0\<^sub>1 \<cdot> h = Prj\<^sub>0\<^sub>1 \<cdot> h'" and "Prj\<^sub>0 \<cdot> h = Prj\<^sub>0 \<cdot> h'"
    shows "h = h'"
    proof -
      have "\<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h = \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h'"
      proof -
        have "\<mu>\<nu>.prj\<^sub>0 \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h = \<mu>\<nu>.prj\<^sub>0 \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h'"
          using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def chine_composite(1)
                C.comp_assoc
          by force
        moreover
        have "\<mu>\<nu>.prj\<^sub>1 \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h'"
          using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def chine_composite(1)
                C.comp_assoc
          by force
        ultimately show ?thesis
          using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
                chine_composite(1) cod_char
                C.prj_joint_monic
                  [of \<mu>.leg0 \<nu>.leg1 "\<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h"
                      "\<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>.leg1] \<cdot> h'"]
          by auto
      qed
      moreover have "Prj\<^sub>0 \<cdot> h = Prj\<^sub>0 \<cdot> h'"
        using assms cod_char by simp
      ultimately show ?thesis
        using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
              chine_composite(1) cod_char
              C.prj_joint_monic [of "\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0" \<pi>.leg1 h h']
        by auto
    qed

    lemma prj'_joint_monic:
    assumes "\<guillemotleft>h: a \<rightarrow>\<^sub>C \<mu>\<nu>\<pi>.chine\<guillemotright>" and "\<guillemotleft>h': a \<rightarrow>\<^sub>C \<mu>\<nu>\<pi>.chine\<guillemotright>"
    and "Prj\<^sub>1 \<cdot> h = Prj\<^sub>1 \<cdot> h'" and "Prj\<^sub>1\<^sub>0 \<cdot> h = Prj\<^sub>1\<^sub>0 \<cdot> h'" and "Prj\<^sub>0\<^sub>0 \<cdot> h = Prj\<^sub>0\<^sub>0 \<cdot> h'"
    shows "h = h'"
    proof -
      have "\<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h = \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h'"
      proof -
        have "\<nu>\<pi>.prj\<^sub>0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h = \<nu>\<pi>.prj\<^sub>0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h'"
          using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def chine_composite(2)
                C.comp_assoc
          by force
        moreover
        have "\<nu>\<pi>.prj\<^sub>1 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h = \<nu>\<pi>.prj\<^sub>1 \<cdot> \<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h'"
          using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def chine_composite(2)
                C.comp_assoc
          by force
        ultimately show ?thesis
          using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
                chine_composite(2) cod_char
                C.prj_joint_monic
                  [of \<nu>.leg0 \<pi>.leg1 "\<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h"
                      "\<p>\<^sub>0[\<mu>.leg0, \<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1] \<cdot> h'"]
          by auto
      qed
      moreover have "Prj\<^sub>1 \<cdot> h = Prj\<^sub>1 \<cdot> h'"
        using assms cod_char by simp
      ultimately show ?thesis
        using assms \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def chine_composite(2)
              C.prj_joint_monic [of \<mu>.leg0 "\<nu>.leg1 \<cdot> \<nu>\<pi>.prj\<^sub>1" h h']
        by auto
    qed

    lemma chine_assoc_inverse:
    shows "C.inverse_arrows chine_assoc chine_assoc'"
    proof
      show "C.ide (chine_assoc' \<cdot> chine_assoc)"
      proof -
        have 1: "C.ide \<mu>\<nu>_\<pi>.chine"
          using chine_assoc_props(1) C.ide_dom by fastforce
        have "chine_assoc' \<cdot> chine_assoc = \<mu>\<nu>_\<pi>.chine"
        proof -
          have 2: "C.seq chine_assoc' chine_assoc"
            using chine_assoc_props(1) chine_assoc'_props(1) by auto
          have 3: "C.seq Prj\<^sub>1\<^sub>1 chine_assoc' \<and> C.seq Prj\<^sub>0\<^sub>1 chine_assoc' \<and> C.seq Prj\<^sub>0 chine_assoc'"
            using prj_in_hom chine_assoc'_props(1) by auto
          have "Prj\<^sub>1\<^sub>1 \<cdot> chine_assoc' \<cdot> chine_assoc = Prj\<^sub>1\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>.chine"
          proof -
            have "Prj\<^sub>1\<^sub>1 \<cdot> chine_assoc' \<cdot> chine_assoc = (Prj\<^sub>1\<^sub>1 \<cdot> chine_assoc') \<cdot> chine_assoc"
              using C.comp_assoc by metis
            thus ?thesis using 1 C.comp_arr_dom by simp
          qed
          moreover have "Prj\<^sub>0\<^sub>1 \<cdot> chine_assoc' \<cdot> chine_assoc = Prj\<^sub>0\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>.chine"
          proof -
            have "Prj\<^sub>0\<^sub>1 \<cdot> chine_assoc' \<cdot> chine_assoc = (Prj\<^sub>0\<^sub>1 \<cdot> chine_assoc') \<cdot> chine_assoc"
              using C.comp_assoc by metis
            thus ?thesis using 1 C.comp_arr_dom by simp
          qed
          moreover have "Prj\<^sub>0 \<cdot> chine_assoc' \<cdot> chine_assoc = Prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>.chine"
          proof -
            have "Prj\<^sub>0 \<cdot> chine_assoc' \<cdot> chine_assoc = (Prj\<^sub>0 \<cdot> chine_assoc') \<cdot> chine_assoc"
              using C.comp_assoc by metis
            thus ?thesis using 1 C.comp_arr_dom C.comp_arr_ide prj_in_hom(3) by auto
          qed
          moreover have "\<guillemotleft>\<mu>\<nu>_\<pi>.chine : \<mu>\<nu>_\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>_\<pi>.chine\<guillemotright>"
            using chine_assoc_props(1) C.ide_dom [of chine_assoc]
            by (elim C.in_homE, auto)
          ultimately show ?thesis
            using chine_assoc_props(1) chine_assoc'_props(1)
                  prj_joint_monic [of "chine_assoc' \<cdot> chine_assoc" "\<mu>\<nu>_\<pi>.chine" "\<mu>\<nu>_\<pi>.chine"]
            by auto
        qed
        thus ?thesis
          using 1 by simp
      qed
      show "C.ide (chine_assoc \<cdot> chine_assoc')"
       proof -
        have 1: "C.ide \<mu>\<nu>\<pi>.chine"
          using chine_assoc_props(1) C.ide_cod by fastforce
        have "chine_assoc \<cdot> chine_assoc' = \<mu>\<nu>\<pi>.chine"
        proof -
          have 2: "C.seq chine_assoc chine_assoc'"
            using chine_assoc_props(1) chine_assoc'_props(1) by auto
          have 3: "C.seq Prj\<^sub>1 chine_assoc \<and> C.seq Prj\<^sub>1\<^sub>0 chine_assoc \<and> C.seq Prj\<^sub>0\<^sub>0 chine_assoc"
            using prj_in_hom chine_assoc_props(1) by auto
          have "Prj\<^sub>1 \<cdot> chine_assoc \<cdot> chine_assoc' = Prj\<^sub>1 \<cdot> \<mu>\<nu>\<pi>.chine"
          proof -
            have "Prj\<^sub>1 \<cdot> chine_assoc \<cdot> chine_assoc' = (Prj\<^sub>1 \<cdot> chine_assoc) \<cdot> chine_assoc'"
              using C.comp_assoc by metis
            thus ?thesis using 1 C.comp_arr_dom prj_in_hom(4) by auto
          qed
          moreover have "Prj\<^sub>1\<^sub>0 \<cdot> chine_assoc \<cdot> chine_assoc' = Prj\<^sub>1\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine"
          proof -
            have "Prj\<^sub>1\<^sub>0 \<cdot> chine_assoc \<cdot> chine_assoc' = (Prj\<^sub>1\<^sub>0 \<cdot> chine_assoc) \<cdot> chine_assoc'"
              using C.comp_assoc by metis
            thus ?thesis using 1 C.comp_arr_dom by simp
          qed
          moreover have "Prj\<^sub>0\<^sub>0 \<cdot> chine_assoc \<cdot> chine_assoc' = Prj\<^sub>0\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine"
          proof -
            have "Prj\<^sub>0\<^sub>0 \<cdot> chine_assoc \<cdot> chine_assoc' = (Prj\<^sub>0\<^sub>0 \<cdot> chine_assoc) \<cdot> chine_assoc'"
              using C.comp_assoc by metis
            thus ?thesis using 1 C.comp_arr_dom by simp
          qed
          moreover have "\<guillemotleft>\<mu>\<nu>\<pi>.chine : \<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<mu>\<nu>\<pi>.chine\<guillemotright>"
            using chine_assoc'_props(1) C.ide_dom [of chine_assoc']
            by (elim C.in_homE, auto)
          ultimately show ?thesis
            using chine_assoc_props(1) chine_assoc'_props(1)
                  prj'_joint_monic [of "chine_assoc \<cdot> chine_assoc'" "\<mu>\<nu>\<pi>.chine" "\<mu>\<nu>\<pi>.chine"]
            by auto
        qed
        thus ?thesis
          using 1 by simp
      qed
    qed

  end

  context three_composable_arrows_of_spans
  begin

    interpretation V: category vcomp
      using is_category by auto
    interpretation H: horizontal_homs vcomp src trg
      using has_horizontal_homs by auto

    interpretation dom_\<mu>: arrow_of_spans C \<open>dom \<mu>\<close>
      using \<mu>.arrow_of_spans_axioms arr_char [of "dom \<mu>"] by auto
    interpretation dom_\<nu>: arrow_of_spans C \<open>dom \<nu>\<close>
      using \<nu>.arrow_of_spans_axioms arr_char [of "dom \<nu>"] by auto
    interpretation dom_\<pi>: arrow_of_spans C \<open>dom \<pi>\<close>
      using \<pi>.arrow_of_spans_axioms arr_char [of "dom \<pi>"] by auto
    interpretation doms: three_composable_identity_arrows_of_spans C prj0 prj1
                           \<open>dom \<mu>\<close> \<open>dom \<nu>\<close> \<open>dom \<pi>\<close>
      using \<mu>\<nu>.composable \<nu>\<pi>.composable ide_char [of "dom \<mu>"] ide_char [of "dom \<nu>"]
            ide_char [of "dom \<pi>"]
      by (unfold_locales, auto)

    interpretation cod_\<mu>: arrow_of_spans C \<open>cod \<mu>\<close>
      using \<mu>.arrow_of_spans_axioms arr_char [of "cod \<mu>"] by auto
    interpretation cod_\<nu>: arrow_of_spans C \<open>cod \<nu>\<close>
      using \<nu>.arrow_of_spans_axioms arr_char [of "cod \<nu>"] by auto
    interpretation cod_\<pi>: arrow_of_spans C \<open>cod \<pi>\<close>
      using \<pi>.arrow_of_spans_axioms arr_char [of "cod \<pi>"] by auto
    interpretation cods: three_composable_identity_arrows_of_spans C prj0 prj1
                           \<open>cod \<mu>\<close> \<open>cod \<nu>\<close> \<open>cod \<pi>\<close>
      using \<mu>\<nu>.composable \<nu>\<pi>.composable ide_char [of "cod \<mu>"] ide_char [of "cod \<nu>"]
            ide_char [of "cod \<pi>"]
      by (unfold_locales, auto)

    interpretation \<mu>\<nu>\<pi>: arrow_of_spans C \<open>\<mu> \<star> \<nu> \<star> \<pi>\<close>
      using \<mu>.arrow_of_spans_axioms \<nu>\<pi>.arrow_of_spans_axioms
            arrow_of_spans_hcomp arr_char \<mu>\<nu>.composable \<nu>\<pi>.composable
      by force

    interpretation \<mu>\<nu>_\<pi>: arrow_of_spans C \<open>(\<mu> \<star> \<nu>) \<star> \<pi>\<close>
      using \<mu>\<nu>.arrow_of_spans_axioms \<pi>.arrow_of_spans_axioms
            arrow_of_spans_hcomp arr_char \<mu>\<nu>.composable \<nu>\<pi>.composable
      by force

    lemma chine_composite':
    shows "\<mu>\<nu>\<pi>.chine = \<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1
                         \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]\<rbrakk>
                       \<langle>\<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0\<rangle>\<rangle>"
    and "\<mu>\<nu>_\<pi>.chine = \<langle>\<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1\<rangle>
                         \<lbrakk>\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1\<rbrakk>
                       \<pi>.chine \<cdot> doms.Prj\<^sub>0\<rangle>"
    proof -
      show "\<mu>\<nu>_\<pi>.chine = \<langle>\<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1\<rangle>
                           \<lbrakk>\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1\<rbrakk>
                         \<pi>.chine \<cdot> doms.Prj\<^sub>0\<rangle>"
      proof -
        have "arr (\<mu> \<star> \<nu>)" by simp
        thus ?thesis
           unfolding hcomp_def chine_hcomp_def dom_char
           using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char chine_hcomp_props
                 C.comp_tuple_arr C.pullback_commutes C.comp_assoc
           by auto
      qed
      show "\<mu>\<nu>\<pi>.chine = \<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1
                          \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]\<rbrakk>
                        \<langle>\<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0\<rangle>\<rangle>"
      proof -
        have "arr (\<nu> \<star> \<pi>)" by simp
        thus ?thesis
           unfolding hcomp_def chine_hcomp_def dom_char
           using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char chine_hcomp_props
                 C.comp_tuple_arr C.pullback_commutes C.comp_assoc
           by auto
      qed
    qed

    lemma chine_composite_in_hom [intro]:
    shows "\<guillemotleft>\<mu>\<nu>_\<pi>.chine : Chn ((dom \<mu> \<star> dom \<nu>) \<star> dom \<pi>) \<rightarrow>\<^sub>C Chn ((cod \<mu> \<star> cod \<nu>) \<star> cod \<pi>)\<guillemotright>"
    and "\<guillemotleft>\<mu>\<nu>\<pi>.chine : Chn (dom \<mu> \<star> dom \<nu> \<star> dom \<pi>) \<rightarrow>\<^sub>C Chn (cod \<mu> \<star> cod \<nu> \<star> cod \<pi>)\<guillemotright>"
    proof -
      interpret \<mu>\<nu>: arrow_of_spans C \<open>\<mu> \<star> \<nu>\<close>
        using arrow_of_spans_hcomp \<mu>\<nu>.composable by auto
      interpret \<nu>\<pi>: arrow_of_spans C \<open>\<nu> \<star> \<pi>\<close>
        using arrow_of_spans_hcomp \<nu>\<pi>.composable by auto
      show "\<guillemotleft>\<mu>\<nu>_\<pi>.chine : Chn ((dom \<mu> \<star> dom \<nu>) \<star> dom \<pi>) \<rightarrow>\<^sub>C Chn ((cod \<mu> \<star> cod \<nu>) \<star> cod \<pi>)\<guillemotright>"
      proof -
        have "\<guillemotleft>\<mu>\<nu>_\<pi>.chine : \<mu>\<nu>.dom.leg0 \<down>\<down> \<pi>.dom.leg1 \<rightarrow>\<^sub>C \<mu>\<nu>.cod.leg0 \<down>\<down> \<pi>.cod.leg1\<guillemotright>"
        proof -
          have "src (\<mu> \<star> \<nu>) = trg \<pi>"
            using \<mu>\<nu>.composable \<nu>\<pi>.composable by simp
          moreover have "arr (\<mu> \<star> \<nu>)"
            using \<mu>\<nu>.arrow_of_spans_axioms by auto
          ultimately show ?thesis
            using hcomp_def chine_hcomp_props(1) [of \<pi> "\<mu> \<star> \<nu>"] by auto
        qed
        hence "\<guillemotleft>\<mu>\<nu>_\<pi>.chine : \<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1] \<down>\<down> \<pi>.dom.leg1 \<rightarrow>\<^sub>C
                             \<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1] \<down>\<down> \<pi>.cod.leg1\<guillemotright>"
          unfolding hcomp_def using \<mu>\<nu>.composable \<nu>\<pi>.composable by simp
        thus ?thesis
          using doms.chine_composite(1) cods.chine_composite(1) dom_char cod_char
          by auto
      qed
      show "\<guillemotleft>\<mu>\<nu>\<pi>.chine : Chn (dom \<mu> \<star> dom \<nu> \<star> dom \<pi>) \<rightarrow>\<^sub>C Chn (cod \<mu> \<star> cod \<nu> \<star> cod \<pi>)\<guillemotright>"
      proof -
        have "\<guillemotleft>\<mu>\<nu>\<pi>.chine : \<mu>.dom.leg0 \<down>\<down> \<nu>\<pi>.dom.leg1 \<rightarrow>\<^sub>C \<mu>.cod.leg0 \<down>\<down> \<nu>\<pi>.cod.leg1\<guillemotright>"
        proof -
          have "src \<mu> = trg (\<nu> \<star> \<pi>)"
            using trg_hcomp \<mu>\<nu>.composable \<nu>\<pi>.composable by simp
          moreover have "arr (\<nu> \<star> \<pi>)"
            using \<mu>\<nu>.arrow_of_spans_axioms by auto
          ultimately show ?thesis
            using hcomp_def chine_hcomp_props(1) [of "\<nu> \<star> \<pi>" \<mu>] by auto
        qed
        hence "\<guillemotleft>\<mu>\<nu>\<pi>.chine : \<mu>.dom.leg0 \<down>\<down> \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1] \<rightarrow>\<^sub>C
                            \<mu>.cod.leg0 \<down>\<down> \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]\<guillemotright>"
          unfolding hcomp_def \<mu>\<nu>.composable \<nu>\<pi>.composable by simp
        thus ?thesis
          using doms.chine_composite(2) cods.chine_composite(2) dom_char cod_char
          by auto
      qed
    qed

    lemma cospan_\<mu>\<nu>:
    shows "C.cospan \<mu>.dom.leg0 \<nu>.dom.leg1"
      using \<mu>\<nu>.legs_form_cospan by simp

    lemma cospan_\<nu>\<pi>:
    shows "C.cospan \<nu>.dom.leg0 \<pi>.dom.leg1"
      using \<nu>\<pi>.legs_form_cospan by simp

    lemma commutativities:
    shows "\<mu>.cod.leg0 \<cdot> \<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 = \<nu>.cod.leg1 \<cdot> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1"
    and "\<pi>.cod.leg1 \<cdot> \<pi>.chine \<cdot> doms.Prj\<^sub>0 =
         (\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1]) \<cdot>
           \<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1\<rangle>"
    proof -
      have AB: "\<mu>.dom.leg0 \<cdot> doms.Prj\<^sub>1\<^sub>1 = \<nu>.dom.leg1 \<cdot> doms.Prj\<^sub>0\<^sub>1"
      proof -
        have "\<mu>.dom.leg0 \<cdot> doms.Prj\<^sub>1\<^sub>1 =
              (\<mu>.dom.leg0 \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1]) \<cdot>
                \<p>\<^sub>1[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]"
          using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc
          by simp
        also have "... = (\<nu>.dom.leg1 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1]) \<cdot>
                           \<p>\<^sub>1[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]"
          using C.pullback_commutes' \<mu>\<nu>.legs_form_cospan by auto
        also have "... = \<nu>.dom.leg1 \<cdot> doms.Prj\<^sub>0\<^sub>1"
          using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc
          by simp
        finally show ?thesis by auto
      qed
      have BC: "\<nu>.dom.leg0 \<cdot> doms.Prj\<^sub>0\<^sub>1 = \<pi>.dom.leg1 \<cdot> doms.Prj\<^sub>0"
      proof -
        have "\<nu>.dom.leg0 \<cdot> doms.Prj\<^sub>0\<^sub>1 =
              (\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1]) \<cdot>
                \<p>\<^sub>1[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]"
          using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc
          by simp
        also have "... = \<pi>.dom.leg1 \<cdot> doms.Prj\<^sub>0"
          using C.pullback_commutes' dom_char cod_char \<mu>\<nu>.legs_form_cospan \<nu>\<pi>.legs_form_cospan
          by auto
        finally show ?thesis by simp
      qed                    
      show 1: "\<mu>.cod.leg0 \<cdot> \<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 = \<nu>.cod.leg1 \<cdot> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1"
        using AB C.comp_assoc [of \<mu>.cod.leg0 \<mu>.chine]
              C.comp_assoc [of \<nu>.cod.leg1 \<nu>.chine doms.Prj\<^sub>0\<^sub>1]
        by simp
      show "\<pi>.cod.leg1 \<cdot> \<pi>.chine \<cdot> doms.Prj\<^sub>0 =
            (\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1]) \<cdot>
              \<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1\<rangle>"
      proof -
        have "(\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1]) \<cdot>
                \<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1\<rangle> =
              \<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1] \<cdot>
                \<langle>\<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1 \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1\<rangle>"
          using 1 \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc by simp
        also have "... = \<nu>.cod.leg0 \<cdot> \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1"
          using 1 dom_char \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def by simp
        also have "... = (\<nu>.cod.leg0 \<cdot> \<nu>.chine) \<cdot> doms.Prj\<^sub>0\<^sub>1"
          using C.comp_assoc [of \<nu>.cod.leg0 \<nu>.chine doms.Prj\<^sub>0\<^sub>1] by simp
        also have "... = (\<pi>.cod.leg1 \<cdot> \<pi>.chine) \<cdot> doms.Prj\<^sub>0"
          using BC by simp
        also have "... = \<pi>.cod.leg1 \<cdot> \<pi>.chine \<cdot> doms.Prj\<^sub>0"
          using C.comp_assoc by blast
        finally show ?thesis by simp
      qed
    qed

    lemma prj_chine_composite:
    shows "cods.Prj\<^sub>1\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>.chine = \<mu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>1"
    and "cods.Prj\<^sub>0\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>.chine = \<nu>.chine \<cdot> doms.Prj\<^sub>0\<^sub>1"
    and "cods.Prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>.chine = \<pi>.chine \<cdot> doms.Prj\<^sub>0"
      using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char cod_char commutativities
            chine_composite' C.comp_assoc
      by auto

    lemma commutativities':
    shows "\<nu>.cod.leg0 \<cdot> \<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 = \<pi>.cod.leg1 \<cdot> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0"
    and "\<mu>.cod.leg0 \<cdot> \<mu>.chine \<cdot> doms.Prj\<^sub>1 =
         (\<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]) \<cdot>
           \<langle>\<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0\<rangle>"
    proof -
      have AB: "\<mu>.dom.leg0 \<cdot> doms.Prj\<^sub>1 = \<nu>.dom.leg1 \<cdot> doms.Prj\<^sub>1\<^sub>0"
        using C.pullback_commutes' dom_char cod_char \<mu>\<nu>.legs_form_cospan \<nu>\<pi>.legs_form_cospan
              C.comp_assoc
        by auto
      have BC: "\<nu>.dom.leg0 \<cdot> doms.Prj\<^sub>1\<^sub>0 = \<pi>.dom.leg1 \<cdot> doms.Prj\<^sub>0\<^sub>0"
      proof -
        have "\<nu>.dom.leg0 \<cdot> doms.Prj\<^sub>1\<^sub>0 =
              (\<nu>.dom.leg0 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]) \<cdot>
                 \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]]"
          using dom_char \<mu>\<nu>.legs_form_cospan \<nu>\<pi>.legs_form_cospan C.comp_assoc by simp
        also have "... = \<pi>.dom.leg1 \<cdot> doms.Prj\<^sub>0\<^sub>0"
          using C.pullback_commutes' dom_char \<mu>\<nu>.legs_form_cospan \<nu>\<pi>.legs_form_cospan C.comp_assoc
          by simp
        finally show ?thesis by auto
      qed
      show 1: "\<nu>.cod.leg0 \<cdot> \<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 = \<pi>.cod.leg1 \<cdot> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0"
        using BC C.comp_assoc [of \<nu>.cod.leg0 \<nu>.chine doms.Prj\<^sub>1\<^sub>0]
              C.comp_assoc [of \<pi>.cod.leg1 \<pi>.chine doms.Prj\<^sub>0\<^sub>0]
              doms.prj_in_hom(5-6) dom_char
         by force
      show "\<mu>.cod.leg0 \<cdot> \<mu>.chine \<cdot> doms.Prj\<^sub>1 =
            (\<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]) \<cdot>
              \<langle>\<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0\<rangle>"
      proof -
        have "(\<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]) \<cdot>
                \<langle>\<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0\<rangle> =
              \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1] \<cdot>
                \<langle>\<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0 \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk> \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0\<rangle>"
          using 1 \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc by simp
        also have "... = \<nu>.cod.leg1 \<cdot> \<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0"
          using 1 dom_char \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def
          by simp
        also have "... = (\<nu>.cod.leg1 \<cdot> \<nu>.chine) \<cdot> doms.Prj\<^sub>1\<^sub>0"
          using C.comp_assoc [of \<nu>.cod.leg1 \<nu>.chine doms.Prj\<^sub>1\<^sub>0] by auto
        also have "... = (\<mu>.cod.leg0 \<cdot> \<mu>.chine) \<cdot> doms.Prj\<^sub>1"
          using AB by simp
        also have "... = \<mu>.cod.leg0 \<cdot> \<mu>.chine \<cdot> doms.Prj\<^sub>1"
          using C.comp_assoc [of \<mu>.cod.leg0 \<mu>.chine doms.Prj\<^sub>1] doms.prj_in_hom(4) dom_char
          by auto
        finally show ?thesis by simp
      qed
    qed

    lemma prj'_chine_composite:
    shows "cods.Prj\<^sub>1 \<cdot> \<mu>\<nu>\<pi>.chine = \<mu>.chine \<cdot> doms.Prj\<^sub>1"
    and "cods.Prj\<^sub>1\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine = \<nu>.chine \<cdot> doms.Prj\<^sub>1\<^sub>0"
    and "cods.Prj\<^sub>0\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine = \<pi>.chine \<cdot> doms.Prj\<^sub>0\<^sub>0"
      using \<mu>\<nu>.composable \<nu>\<pi>.composable src_def trg_def dom_char cod_char commutativities'
            chine_composite' C.comp_assoc
      by auto

    lemma chine_assoc_naturality:
    shows "cods.chine_assoc \<cdot> \<mu>\<nu>_\<pi>.chine = \<mu>\<nu>\<pi>.chine \<cdot> doms.chine_assoc"
    proof -
      have "\<guillemotleft>cods.chine_assoc \<cdot> \<mu>\<nu>_\<pi>.chine :
               Chn ((dom \<mu> \<star> dom \<nu>) \<star> dom \<pi>) \<rightarrow>\<^sub>C Chn (cod \<mu> \<star> cod \<nu> \<star> cod \<pi>)\<guillemotright>"
        using cods.chine_assoc_props(1) chine_composite_in_hom(1) by blast
      moreover have "\<guillemotleft>\<mu>\<nu>\<pi>.chine \<cdot> doms.chine_assoc :
                        Chn ((dom \<mu> \<star> dom \<nu>) \<star> dom \<pi>) \<rightarrow>\<^sub>C Chn (cod \<mu> \<star> cod \<nu> \<star> cod \<pi>)\<guillemotright>"
        using doms.chine_assoc_props(1) chine_composite_in_hom(2) by blast
      moreover
      have "cods.Prj\<^sub>1 \<cdot> cods.chine_assoc \<cdot> \<mu>\<nu>_\<pi>.chine =
            cods.Prj\<^sub>1 \<cdot> \<mu>\<nu>\<pi>.chine \<cdot> doms.chine_assoc"
        using C.comp_assoc doms.chine_assoc_props(2) cods.chine_assoc_props(2)
              prj_chine_composite prj'_chine_composite
        by metis
      moreover have "cods.Prj\<^sub>1\<^sub>0 \<cdot> cods.chine_assoc \<cdot> \<mu>\<nu>_\<pi>.chine =
                     cods.Prj\<^sub>1\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine \<cdot> doms.chine_assoc"
        using C.comp_assoc doms.chine_assoc_props(3) cods.chine_assoc_props(3)
              prj_chine_composite prj'_chine_composite
        by metis
      moreover have "cods.Prj\<^sub>0\<^sub>0 \<cdot> cods.chine_assoc \<cdot> \<mu>\<nu>_\<pi>.chine =
                     cods.Prj\<^sub>0\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine \<cdot> doms.chine_assoc"
        using C.comp_assoc doms.chine_assoc_props(4) cods.chine_assoc_props(4)
              prj_chine_composite prj'_chine_composite
        by metis
      ultimately show ?thesis
        using cods.prj'_joint_monic by auto
    qed

  end

  context span_bicategory
  begin

    interpretation VxV: product_category vcomp vcomp ..
    interpretation VV: subcategory VxV.comp \<open>\<lambda>\<nu>\<mu>. arr (fst \<nu>\<mu>) \<and> arr (snd \<nu>\<mu>) \<and>
                                                   src (fst \<nu>\<mu>) = trg (snd \<nu>\<mu>)\<close>
      by (unfold_locales, simp_all)
    interpretation VxVxV: product_category vcomp VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                          \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                 src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by auto

    interpretation H: horizontal_composition vcomp hcomp src trg
      using has_horizontal_composition by auto
    interpretation HoHV: "functor" VVV.comp vcomp HoHV
      using functor_HoHV by blast
    interpretation HoVH: "functor" VVV.comp vcomp HoVH
      using functor_HoVH by blast

    abbreviation (input) assoc\<^sub>S\<^sub>B
    where "assoc\<^sub>S\<^sub>B f g h \<equiv> \<lparr>Chn = three_composable_identity_arrows_of_spans.chine_assoc
                                   C prj0 prj1 f g h,
                            Dom = Dom ((f \<star> g) \<star> h), Cod = Cod (f \<star> g \<star> h)\<rparr>"

    abbreviation (input) assoc'\<^sub>S\<^sub>B
    where "assoc'\<^sub>S\<^sub>B f g h \<equiv> \<lparr>Chn = three_composable_identity_arrows_of_spans.chine_assoc'
                                    C prj0 prj1 f g h,
                             Dom = Cod (f \<star> g \<star> h), Cod = Dom ((f \<star> g) \<star> h)\<rparr>"

    lemma assoc_props:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "src (assoc\<^sub>S\<^sub>B f g h) = src h" and "trg (assoc\<^sub>S\<^sub>B f g h) = trg f"
    and "\<guillemotleft>assoc\<^sub>S\<^sub>B f g h : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
    and "src (assoc'\<^sub>S\<^sub>B f g h) = src h" and "trg (assoc'\<^sub>S\<^sub>B f g h) = trg f"
    and "\<guillemotleft>assoc'\<^sub>S\<^sub>B f g h : f \<star> g \<star> h \<Rightarrow> (f \<star> g) \<star> h\<guillemotright>"
    proof -
      have fgh: "VVV.ide (f, g, h)"
        using assms VVV.ide_char VV.ide_char VVV.arr_char VV.arr_char by simp
      interpret f: arrow_of_spans C f
        using assms arr_char by fastforce
      interpret g: arrow_of_spans C g
        using assms arr_char by fastforce
      interpret h: arrow_of_spans C h
        using assms arr_char by fastforce
      interpret fgh: three_composable_arrows_of_spans C prj0 prj1 f g h
        using assms arr_char by (unfold_locales, auto)
      interpret fgh: three_composable_identity_arrows_of_spans C prj0 prj1 f g h
        using assms ide_char by (unfold_locales, auto)
      interpret HHfgh: arrow_of_spans C \<open>(f \<star> g) \<star> h\<close>
        using assms fgh.composites_are_arrows arrow_of_spans_hcomp by simp
      interpret HfHgh: arrow_of_spans C \<open>f \<star> g \<star> h\<close>
        using assms fgh.composites_are_arrows arrow_of_spans_hcomp by simp
      interpret assoc_fgh: arrow_of_spans C \<open>assoc\<^sub>S\<^sub>B f g h\<close>
        apply unfold_locales
            apply simp_all
          apply (metis C.ideD(2) C.ideD(3) HHfgh.chine_simps(2) HfHgh.chine_simps(3)
            fgh.composites_are_identities(1) fgh.composites_are_identities(2)
            fgh.chine_assoc_in_hom ide_char)
      proof -
        have 1: "arr (f \<star> g)" using fgh.\<mu>\<nu>.composite_is_arrow by simp
        have 2: "arr (g \<star> h)" using fgh.\<nu>\<pi>.composite_is_arrow by simp
        show "HfHgh.cod.leg0 \<cdot> fgh.chine_assoc = HHfgh.dom.leg0"
          using 1 2 hcomp_def src_def trg_def fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable
                fgh.chine_assoc_props(4) C.comp_assoc
          by simp
        show "HfHgh.cod.leg1 \<cdot> fgh.chine_assoc = HHfgh.dom.leg1"
          using 1 2 hcomp_def src_def trg_def fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable
                fgh.chine_assoc_props(2) C.comp_assoc
          by simp
      qed
      interpret assoc'_fgh: arrow_of_spans C \<open>assoc'\<^sub>S\<^sub>B f g h\<close>
        apply unfold_locales
            apply simp_all
          apply (metis C.ideD(2) C.ideD(3) HHfgh.chine_simps(2) HfHgh.chine_simps(3)
            fgh.composites_are_identities(1) fgh.composites_are_identities(2)
            fgh.chine_assoc'_in_hom ide_char)
      proof -
        have 1: "arr (f \<star> g)" using fgh.\<mu>\<nu>.composite_is_arrow by simp
        have 2: "arr (g \<star> h)"  using fgh.\<nu>\<pi>.composite_is_arrow by simp
        show "HHfgh.dom.leg0 \<cdot> fgh.chine_assoc' = HfHgh.cod.leg0"
          using 1 2 hcomp_def src_def trg_def fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable
                C.comp_assoc fgh.chine_assoc'_props(4)
          by simp
        show "HHfgh.dom.leg1 \<cdot> fgh.chine_assoc' = HfHgh.cod.leg1"
          using 1 2 hcomp_def src_def trg_def fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable
                C.comp_assoc fgh.chine_assoc'_props(2)
          by auto
      qed
      show 1: "\<guillemotleft>assoc\<^sub>S\<^sub>B f g h : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
      proof
        show 1: "arr (assoc\<^sub>S\<^sub>B f g h)"
          using assoc_fgh.arrow_of_spans_axioms arr_char by blast
        show "dom (assoc\<^sub>S\<^sub>B f g h) = (f \<star> g) \<star> h"
          using fgh 1 dom_char fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable ideD(2)
          by auto
        show "cod (assoc\<^sub>S\<^sub>B f g h) = f \<star> g \<star> h"
          using fgh 1 HoVH_def cod_char fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable ideD(3)
          by auto
      qed
      show 2: "\<guillemotleft>assoc'\<^sub>S\<^sub>B f g h : f \<star> g \<star> h \<Rightarrow> (f \<star> g) \<star> h\<guillemotright>"
      proof
        show 1: "arr (assoc'\<^sub>S\<^sub>B f g h)"
          using assoc'_fgh.arrow_of_spans_axioms arr_char by blast
        show "dom (assoc'\<^sub>S\<^sub>B f g h) = f \<star> g \<star> h"
          using fgh 1 dom_char cod_char ideD(3) by auto
        show "cod (assoc'\<^sub>S\<^sub>B f g h) = (f \<star> g) \<star> h"
          using fgh 1 cod_char dom_char ideD(2) by auto            
      qed
      show 3: "src (assoc\<^sub>S\<^sub>B f g h) = src h"
      proof -
        have 4: "src (assoc\<^sub>S\<^sub>B f g h) =
                 \<lparr>Chn = assoc_fgh.dsrc, Dom = \<lparr>Leg0 = assoc_fgh.dsrc, Leg1 = assoc_fgh.dsrc\<rparr>,
                  Cod = \<lparr>Leg0 = assoc_fgh.dsrc, Leg1 = assoc_fgh.dsrc\<rparr>\<rparr>"
          unfolding src_def using 1 by auto
        also have "... = src h"
          using fgh.composite_simps(2) src_def by auto
        finally show ?thesis by blast
      qed
      show "src (assoc'\<^sub>S\<^sub>B f g h) = src h"
      proof -
        have "src (assoc'\<^sub>S\<^sub>B f g h) =
              \<lparr>Chn = assoc'_fgh.dsrc, Dom = \<lparr>Leg0 = assoc'_fgh.dsrc, Leg1 = assoc'_fgh.dsrc\<rparr>,
               Cod = \<lparr>Leg0 = assoc'_fgh.dsrc, Leg1 = assoc'_fgh.dsrc\<rparr>\<rparr>"
          unfolding src_def using 2 by auto
        also have "... = src h"
          using 1 3 assoc_fgh.cod_src_eq_dom_src arrI src_def by auto
        finally show ?thesis by blast
      qed
      show 4: "trg (assoc\<^sub>S\<^sub>B f g h) = trg f"
      proof -
        have 5: "trg (assoc\<^sub>S\<^sub>B f g h) =
              \<lparr>Chn = assoc_fgh.dtrg, Dom = \<lparr>Leg0 = assoc_fgh.dtrg, Leg1 = assoc_fgh.dtrg\<rparr>,
               Cod = \<lparr>Leg0 = assoc_fgh.dtrg, Leg1 = assoc_fgh.dtrg\<rparr>\<rparr>"
          unfolding trg_def using 1 by auto
        also have "... = trg f"
          using fgh.composite_simps(4) trg_def by auto
        finally show ?thesis by blast
      qed
      show "trg (assoc'\<^sub>S\<^sub>B f g h) = trg f"
      proof -
        have 5: "trg (assoc'\<^sub>S\<^sub>B f g h) =
              \<lparr>Chn = assoc'_fgh.dtrg, Dom = \<lparr>Leg0 = assoc'_fgh.dtrg, Leg1 = assoc'_fgh.dtrg\<rparr>,
               Cod = \<lparr>Leg0 = assoc'_fgh.dtrg, Leg1 = assoc'_fgh.dtrg\<rparr>\<rparr>"
          unfolding trg_def using 2 by auto
        also have "... = trg f"
          using 1 4 assoc_fgh.cod_trg_eq_dom_trg arrI trg_def by auto
        finally show ?thesis by blast
      qed
    qed

    lemma assoc_in_hom [intro]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<guillemotleft>assoc\<^sub>S\<^sub>B f g h : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright> "
      using assms assoc_props by auto

    lemma assoc'_in_hom [intro]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<guillemotleft>assoc'\<^sub>S\<^sub>B f g h : f \<star> g \<star> h \<Rightarrow> (f \<star> g) \<star> h\<guillemotright> "
      using assms assoc_props by auto

    lemma assoc_simps [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "arr (assoc\<^sub>S\<^sub>B f g h)" and "dom (assoc\<^sub>S\<^sub>B f g h) = (f \<star> g) \<star> h"
    and "cod (assoc\<^sub>S\<^sub>B f g h) = f \<star> g \<star> h"
    and "src (assoc\<^sub>S\<^sub>B f g h) = src h" and "trg (assoc\<^sub>S\<^sub>B f g h) = trg f"
      using assms assoc_props(1-3) by (fast, fast, fast, auto)

    lemma assoc'_simps [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "arr (assoc'\<^sub>S\<^sub>B f g h)" and "dom (assoc'\<^sub>S\<^sub>B f g h) = f \<star> g \<star> h"
    and "cod (assoc'\<^sub>S\<^sub>B f g h) = (f \<star> g) \<star> h"
    and "src (assoc'\<^sub>S\<^sub>B f g h) = src h" and "trg (assoc'\<^sub>S\<^sub>B f g h) = trg f"
      using assms assoc_props(4-6) by (fast, fast, fast, auto)

    lemma inverse_assoc_assoc':
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "inverse_arrows (assoc\<^sub>S\<^sub>B f g h) (assoc'\<^sub>S\<^sub>B f g h)"
    proof -
      interpret f: arrow_of_spans C f using assms arr_char ideD(1) by simp
      interpret g: arrow_of_spans C g using assms arr_char ideD(1) by simp
      interpret h: arrow_of_spans C h using assms arr_char ideD(1) by simp
      interpret fgh: three_composable_arrows_of_spans C prj0 prj1 f g h
        using assms arr_char by (unfold_locales, auto)
      interpret fgh: three_composable_identity_arrows_of_spans C prj0 prj1 f g h
        using assms ide_char
        apply unfold_locales
          apply blast
         apply blast
        by blast
      interpret afgh: arrow_of_spans C \<open>assoc\<^sub>S\<^sub>B f g h\<close>
        using assms assoc_props(3) arr_char by blast
      interpret a'fgh: arrow_of_spans C \<open>assoc'\<^sub>S\<^sub>B f g h\<close>
        using assms assoc_props(6) arr_char by blast
      show ?thesis
      proof -
        have "inverse_arrows (assoc\<^sub>S\<^sub>B f g h)
                             \<lparr>Chn = C.inv (Chn (assoc\<^sub>S\<^sub>B f g h)),
                              Dom = Cod (assoc\<^sub>S\<^sub>B f g h), Cod = Dom (assoc\<^sub>S\<^sub>B f g h)\<rparr>"
          using inverse_arrows [of "assoc\<^sub>S\<^sub>B f g h"] afgh.arrow_of_spans_axioms
                arr_char fgh.chine_assoc_inverse
          by auto
        moreover have "C.inv (Chn (assoc\<^sub>S\<^sub>B f g h)) = fgh.chine_assoc'"
          using fgh.chine_assoc_inverse C.inv_is_inverse C.inverse_arrow_unique by auto
        ultimately show ?thesis by simp
      qed
    qed

    interpretation \<alpha>: transformation_by_components VVV.comp vcomp HoHV HoVH
                        \<open>\<lambda>fgh. assoc\<^sub>S\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh))\<close>
    proof
      show *: "\<And>fgh. VVV.ide fgh \<Longrightarrow> \<guillemotleft>assoc\<^sub>S\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh)) :
                                         HoHV fgh \<Rightarrow> HoVH fgh\<guillemotright>"
      proof -
        fix fgh
        assume fgh: "VVV.ide fgh"
        show "\<guillemotleft>assoc\<^sub>S\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh)) : HoHV fgh \<Rightarrow> HoVH fgh\<guillemotright>"
          unfolding HoHV_def HoVH_def
          using fgh assoc_in_hom [of "fst fgh" "fst (snd fgh)" "snd (snd fgh)"]
                VVV.arr_char VVV.ide_char VV.arr_char
          by simp
      qed
      show "\<And>\<mu>\<nu>\<pi>. VVV.arr \<mu>\<nu>\<pi> \<Longrightarrow>
                     assoc\<^sub>S\<^sub>B (fst (VVV.cod \<mu>\<nu>\<pi>)) (fst (snd (VVV.cod \<mu>\<nu>\<pi>)))
                             (snd (snd (VVV.cod \<mu>\<nu>\<pi>))) \<bullet>
                       HoHV \<mu>\<nu>\<pi> =
                     HoVH \<mu>\<nu>\<pi> \<bullet> assoc\<^sub>S\<^sub>B (fst (VVV.dom \<mu>\<nu>\<pi>)) (fst (snd (VVV.dom \<mu>\<nu>\<pi>)))
                                        (snd (snd (VVV.dom \<mu>\<nu>\<pi>)))"
      proof -
        fix \<mu>\<nu>\<pi>
        assume \<mu>\<nu>\<pi>: "VVV.arr \<mu>\<nu>\<pi>"
        interpret \<mu>: arrow_of_spans C \<open>fst \<mu>\<nu>\<pi>\<close>
          using \<mu>\<nu>\<pi> VVV.ide_char VVV.arr_char arr_char by auto
        interpret \<nu>: arrow_of_spans C \<open>fst (snd \<mu>\<nu>\<pi>)\<close>
          using \<mu>\<nu>\<pi> VVV.ide_char VVV.arr_char VV.arr_char arr_char by auto
        interpret \<pi>: arrow_of_spans C \<open>snd (snd \<mu>\<nu>\<pi>)\<close>
          using \<mu>\<nu>\<pi> VVV.ide_char VVV.arr_char VV.arr_char arr_char by auto
        interpret \<mu>\<nu>\<pi>: three_composable_arrows_of_spans C prj0 prj1
                         \<open>fst \<mu>\<nu>\<pi>\<close> \<open>fst (snd \<mu>\<nu>\<pi>)\<close> \<open>snd (snd \<mu>\<nu>\<pi>)\<close>
          using \<mu>\<nu>\<pi> VVV.ide_char VVV.arr_char VV.arr_char arr_char
          by (unfold_locales, auto)

        interpret HoHV_\<mu>\<nu>\<pi>: arrow_of_spans C \<open>(fst \<mu>\<nu>\<pi> \<star> fst (snd \<mu>\<nu>\<pi>)) \<star> snd (snd \<mu>\<nu>\<pi>)\<close>
        proof -
          have "arr (HoHV \<mu>\<nu>\<pi>)"
            using \<mu>\<nu>\<pi> by simp
          thus "arrow_of_spans C ((fst \<mu>\<nu>\<pi> \<star> fst (snd \<mu>\<nu>\<pi>)) \<star> snd (snd \<mu>\<nu>\<pi>))"
            using \<mu>\<nu>\<pi> HoHV_def arr_char by auto
        qed
        interpret HoVH_\<mu>\<nu>\<pi>: arrow_of_spans C \<open>fst \<mu>\<nu>\<pi> \<star> fst (snd \<mu>\<nu>\<pi>) \<star> snd (snd \<mu>\<nu>\<pi>)\<close>
        proof -
          have "arr (HoVH \<mu>\<nu>\<pi>)"
            using \<mu>\<nu>\<pi> by simp
          thus "arrow_of_spans C (fst \<mu>\<nu>\<pi> \<star> fst (snd \<mu>\<nu>\<pi>) \<star> snd (snd \<mu>\<nu>\<pi>))"
            using \<mu>\<nu>\<pi> HoVH_def arr_char by auto
        qed

        have dom_\<mu>\<nu>\<pi>: "VVV.ide (VVV.dom \<mu>\<nu>\<pi>)"
          using \<mu>\<nu>\<pi> VVV.ide_dom by blast
        interpret dom_\<mu>: identity_arrow_of_spans C \<open>fst (VVV.dom \<mu>\<nu>\<pi>)\<close>
          using dom_\<mu>\<nu>\<pi> VVV.ide_char VV.ide_char ide_char' by blast
        interpret dom_\<nu>: identity_arrow_of_spans C \<open>fst (snd (VVV.dom \<mu>\<nu>\<pi>))\<close>
          using dom_\<mu>\<nu>\<pi> VVV.ide_char VV.ide_char ide_char' by blast
        interpret dom_\<pi>: identity_arrow_of_spans C \<open>snd (snd (VVV.dom \<mu>\<nu>\<pi>))\<close>
          using dom_\<mu>\<nu>\<pi> VVV.ide_char VV.ide_char ide_char' by blast
        interpret dom_\<mu>\<nu>\<pi>: three_composable_identity_arrows_of_spans C prj0 prj1
                             \<open>fst (VVV.dom \<mu>\<nu>\<pi>)\<close> \<open>fst (snd (VVV.dom \<mu>\<nu>\<pi>))\<close>
                             \<open>snd (snd (VVV.dom \<mu>\<nu>\<pi>))\<close>
          using dom_\<mu>\<nu>\<pi> VVV.ide_char VVV.arr_char VV.arr_char
          by (unfold_locales, auto)
        interpret assoc_dom_\<mu>\<nu>\<pi>: arrow_of_spans C
                                  \<open>assoc\<^sub>S\<^sub>B (fst (VVV.dom \<mu>\<nu>\<pi>)) (fst (snd (VVV.dom \<mu>\<nu>\<pi>)))
                                    (snd (snd (VVV.dom \<mu>\<nu>\<pi>)))\<close>
          using \<mu>\<nu>\<pi> VVV.ide_dom * arr_char by fast

        have cod_\<mu>\<nu>\<pi>: "VVV.ide (VVV.cod \<mu>\<nu>\<pi>)"
          using \<mu>\<nu>\<pi> VVV.ide_cod by blast
        interpret cod_\<mu>: identity_arrow_of_spans C \<open>fst (VVV.cod \<mu>\<nu>\<pi>)\<close>
          using cod_\<mu>\<nu>\<pi> VVV.ide_char VV.ide_char ide_char' by blast
        interpret cod_\<nu>: identity_arrow_of_spans C \<open>fst (snd (VVV.cod \<mu>\<nu>\<pi>))\<close>
          using cod_\<mu>\<nu>\<pi> VVV.ide_char VV.ide_char ide_char' by blast
        interpret cod_\<pi>: identity_arrow_of_spans C \<open>snd (snd (VVV.cod \<mu>\<nu>\<pi>))\<close>
          using cod_\<mu>\<nu>\<pi> VVV.ide_char VV.ide_char ide_char' by blast
        interpret cod_\<mu>\<nu>\<pi>: three_composable_identity_arrows_of_spans C prj0 prj1
                             \<open>fst (VVV.cod \<mu>\<nu>\<pi>)\<close> \<open>fst (snd (VVV.cod \<mu>\<nu>\<pi>))\<close>
                             \<open>snd (snd (VVV.cod \<mu>\<nu>\<pi>))\<close>
          using cod_\<mu>\<nu>\<pi> VVV.ide_char VVV.arr_char VV.arr_char
          by (unfold_locales, auto)
        interpret assoc_cod_\<mu>\<nu>\<pi>: arrow_of_spans C
                               \<open>assoc\<^sub>S\<^sub>B (fst (VVV.cod \<mu>\<nu>\<pi>)) (fst (snd (VVV.cod \<mu>\<nu>\<pi>)))
                                  (snd (snd (VVV.cod \<mu>\<nu>\<pi>)))\<close>
          using \<mu>\<nu>\<pi> VVV.ide_cod * arr_char by fast

        have dom_legs:
               "dom_\<mu>.leg0 = \<mu>.dom.leg0 \<and> dom_\<nu>.leg0 = \<nu>.dom.leg0 \<and> dom_\<pi>.leg0 = \<pi>.dom.leg0 \<and>
                dom_\<mu>.leg1 = \<mu>.dom.leg1 \<and> dom_\<nu>.leg1 = \<nu>.dom.leg1 \<and> dom_\<pi>.leg1 = \<pi>.dom.leg1"
          using VVV.arr_char VVV.dom_char dom_char \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable
          by auto
        have cod_legs:
                "cod_\<mu>.leg0 = \<mu>.cod.leg0 \<and> cod_\<nu>.leg0 = \<nu>.cod.leg0 \<and> cod_\<pi>.leg0 = \<pi>.cod.leg0 \<and>
                 cod_\<mu>.leg1 = \<mu>.cod.leg1 \<and> cod_\<nu>.leg1 = \<nu>.cod.leg1 \<and> cod_\<pi>.leg1 = \<pi>.cod.leg1"
          using \<mu>\<nu>\<pi> VVV.cod_char cod_char by auto

        have Prj\<^sub>1\<^sub>1_dom: "dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1 =
                          \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1] \<cdot>
                            \<p>\<^sub>1[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]"
          using dom_legs by argo
        have Prj\<^sub>1\<^sub>1_cod: "cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1 =
                          \<p>\<^sub>1[\<mu>.cod.leg0, \<nu>.cod.leg1] \<cdot>
                            \<p>\<^sub>1[\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1]"
          using cod_legs by argo
        have Prj\<^sub>0_dom: "dom_\<mu>\<nu>\<pi>.Prj\<^sub>0 = \<p>\<^sub>0[\<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1], \<pi>.dom.leg1]"
          using dom_legs by argo
        have Prj\<^sub>0_cod: "cod_\<mu>\<nu>\<pi>.Prj\<^sub>0 = \<p>\<^sub>0[\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1]"
          using cod_legs by argo

        have Dom: "Dom ((fst (VVV.dom \<mu>\<nu>\<pi>) \<star> fst (snd (VVV.dom \<mu>\<nu>\<pi>))) \<star>
                         snd (snd (VVV.dom \<mu>\<nu>\<pi>))) =
                   \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>"
        proof -
            have "arr (dom (fst \<mu>\<nu>\<pi>) \<star> dom (fst (snd \<mu>\<nu>\<pi>)))"
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable by simp
            thus ?thesis
              using \<mu>\<nu>\<pi> hcomp_def dom_legs ide_dom dom_char
                apply simp
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc
              by auto
        qed
        have Cod: "Cod (fst (VVV.dom \<mu>\<nu>\<pi>) \<star> fst (snd (VVV.dom \<mu>\<nu>\<pi>)) \<star>
                         snd (snd (VVV.dom \<mu>\<nu>\<pi>))) =
                   \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>"
        proof -
            have "arr (dom (fst (snd \<mu>\<nu>\<pi>)) \<star> dom (snd (snd \<mu>\<nu>\<pi>)))"
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable by simp
            thus ?thesis
              using \<mu>\<nu>\<pi> hcomp_def dom_legs ide_dom dom_char
                apply simp
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def dom_char C.comp_assoc
              by auto
        qed
        have Dom': "Dom ((fst (VVV.cod \<mu>\<nu>\<pi>) \<star> fst (snd (VVV.cod \<mu>\<nu>\<pi>))) \<star>
                          snd (snd (VVV.cod \<mu>\<nu>\<pi>))) =
                    \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>"
        proof -
            have "arr (cod (fst \<mu>\<nu>\<pi>) \<star> cod (fst (snd \<mu>\<nu>\<pi>)))"
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable by simp
            moreover have "\<mu>.dsrc = \<nu>.dtrg"
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable src_def trg_def cod_char by simp
            moreover have "\<nu>.dsrc = \<pi>.dtrg"
              using \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def cod_char by simp
            ultimately show ?thesis
              using \<mu>\<nu>\<pi> hcomp_def cod_legs ide_cod cod_char
                apply simp
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def cod_char C.comp_assoc
              by simp
        qed
        have Cod': "Cod (fst (VVV.cod \<mu>\<nu>\<pi>) \<star> fst (snd (VVV.cod \<mu>\<nu>\<pi>)) \<star>
                          snd (snd (VVV.cod \<mu>\<nu>\<pi>))) =
                    \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>"
        proof -
            have "arr (cod (fst (snd \<mu>\<nu>\<pi>)) \<star> cod (snd (snd \<mu>\<nu>\<pi>)))"
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable by simp
            moreover have "\<mu>.dsrc = \<nu>.dtrg"
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable src_def trg_def cod_char by simp
            ultimately show ?thesis
              using \<mu>\<nu>\<pi> hcomp_def cod_legs ide_cod cod_char
                apply simp
              using \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def cod_char C.comp_assoc
              by auto
        qed

        have assoc_dom:
             "assoc\<^sub>S\<^sub>B (fst (VVV.dom \<mu>\<nu>\<pi>)) (fst (snd (VVV.dom \<mu>\<nu>\<pi>)))
                      (snd (snd (VVV.dom \<mu>\<nu>\<pi>))) =
              \<lparr>Chn = dom_\<mu>\<nu>\<pi>.chine_assoc,
               Dom = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>,
               Cod = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>\<rparr>"
          using Dom Cod by simp
        have assoc_cod:
             "assoc\<^sub>S\<^sub>B (fst (VVV.cod \<mu>\<nu>\<pi>)) (fst (snd (VVV.cod \<mu>\<nu>\<pi>)))
                     (snd (snd (VVV.cod \<mu>\<nu>\<pi>))) =
              \<lparr>Chn = cod_\<mu>\<nu>\<pi>.chine_assoc,
               Dom = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>,
               Cod = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>\<rparr>"
          using Dom' Cod' by simp
        have HoHV_\<mu>\<nu>\<pi>:
          "HoHV \<mu>\<nu>\<pi> =
           \<lparr>Chn = HoHV_\<mu>\<nu>\<pi>.chine,
            Dom = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>,
            Cod = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>\<rparr>"
        proof -
          have "arr \<lparr>Chn = \<langle>\<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1]
                              \<lbrakk>\<mu>.cod.leg0, \<nu>.cod.leg1\<rbrakk>
                            \<nu>.chine \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1]\<rangle>,
                     Dom = \<lparr>Leg0 = \<nu>.dom.leg0 \<cdot> \<p>\<^sub>0[\<mu>.dom.leg0, \<nu>.dom.leg1],
                            Leg1 = \<mu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<mu>.dom.leg0, \<nu>.dom.leg1]\<rparr>,
                     Cod = \<lparr>Leg0 = \<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1],
                            Leg1 = \<mu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<mu>.cod.leg0, \<nu>.cod.leg1]\<rparr>\<rparr>"
            unfolding hcomp_def chine_hcomp_def
            using \<mu>\<nu>\<pi> hcomp_def dom_legs cod_legs ide_dom ide_cod dom_char cod_char
                  \<mu>\<nu>\<pi>.\<mu>\<nu>.composable
            by (metis (no_types, lifting) hseq_char(1) \<mu>\<nu>\<pi>.\<mu>\<nu>.composite_is_arrow chine_hcomp_def)
          moreover have "(\<mu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<mu>.cod.leg0, \<nu>.cod.leg1]) \<cdot>
                           \<p>\<^sub>1[\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1] =
                          \<mu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<mu>.cod.leg0, \<nu>.cod.leg1] \<cdot>
                           \<p>\<^sub>1[\<nu>.cod.leg0 \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1], \<pi>.cod.leg1]"
           using C.comp_assoc by simp
          ultimately show ?thesis
            unfolding HoHV_def hcomp_def chine_hcomp_def
            using \<mu>\<nu>\<pi> \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def dom_legs cod_legs
                  C.comp_assoc
            by simp
        qed
        have HoVH_\<mu>\<nu>\<pi>:
          "HoVH \<mu>\<nu>\<pi> =
           \<lparr>Chn = HoVH_\<mu>\<nu>\<pi>.chine,
            Dom = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>,
            Cod = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>\<rparr>"
        proof -
          have "arr \<lparr>Chn = \<langle>\<nu>.chine \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]
                             \<lbrakk>\<nu>.cod.leg0, \<pi>.cod.leg1\<rbrakk>
                            \<pi>.chine \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<pi>.dom.leg1]\<rangle>,
                     Dom = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> \<p>\<^sub>0[\<nu>.dom.leg0, \<pi>.dom.leg1],
                            Leg1 = \<nu>.dom.leg1 \<cdot> \<p>\<^sub>1[\<nu>.dom.leg0, \<pi>.dom.leg1]\<rparr>,
                     Cod = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<pi>.cod.leg1],
                            Leg1 = \<nu>.cod.leg1 \<cdot> \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]\<rparr>\<rparr>"
            unfolding hcomp_def chine_hcomp_def
            using \<mu>\<nu>\<pi> hcomp_def dom_legs cod_legs ide_dom ide_cod dom_char cod_char
                  \<mu>\<nu>\<pi>.\<nu>\<pi>.composable
            by (metis (no_types, lifting) hseq_char \<mu>\<nu>\<pi>.\<nu>\<pi>.composite_is_arrow chine_hcomp_def)
         moreover have "(\<pi>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<pi>.cod.leg1]) \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1 \<cdot>
                          \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]] =
                         \<pi>.cod.leg0 \<cdot> \<p>\<^sub>0[\<nu>.cod.leg0, \<pi>.cod.leg1] \<cdot> \<p>\<^sub>0[\<mu>.cod.leg0, \<nu>.cod.leg1 \<cdot>
                           \<p>\<^sub>1[\<nu>.cod.leg0, \<pi>.cod.leg1]]"
           using C.comp_assoc by simp
         ultimately show ?thesis
            unfolding HoVH_def hcomp_def chine_hcomp_def
            using \<mu>\<nu>\<pi> \<mu>\<nu>\<pi>.\<mu>\<nu>.composable \<mu>\<nu>\<pi>.\<nu>\<pi>.composable src_def trg_def dom_legs cod_legs
                  C.comp_assoc
            by simp
       qed
       have "assoc\<^sub>S\<^sub>B (fst (VVV.cod \<mu>\<nu>\<pi>)) (fst (snd (VVV.cod \<mu>\<nu>\<pi>)))
                     (snd (snd (VVV.cod \<mu>\<nu>\<pi>))) \<bullet>
               HoHV \<mu>\<nu>\<pi> =
             \<lparr>Chn = cod_\<mu>\<nu>\<pi>.chine_assoc \<cdot> HoHV_\<mu>\<nu>\<pi>.chine,
              Dom = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>,
              Cod = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>\<rparr>"
        proof -
          have "arr (HoHV \<mu>\<nu>\<pi>)"
            using \<mu>\<nu>\<pi> by simp
          thus ?thesis
            using vcomp_def HoHV_\<mu>\<nu>\<pi> HoHV_\<mu>\<nu>\<pi>.arrow_of_spans_axioms
                  assoc_cod_\<mu>\<nu>\<pi>.arrow_of_spans_axioms assoc_cod dom_legs cod_legs
                  arr_char
            by simp
        qed
        moreover
        have "HoVH \<mu>\<nu>\<pi> \<bullet>
                assoc\<^sub>S\<^sub>B (fst (VVV.dom \<mu>\<nu>\<pi>)) (fst (snd (VVV.dom \<mu>\<nu>\<pi>)))
                        (snd (snd (VVV.dom \<mu>\<nu>\<pi>))) =
              \<lparr>Chn = HoVH_\<mu>\<nu>\<pi>.chine \<cdot> dom_\<mu>\<nu>\<pi>.chine_assoc,
               Dom = \<lparr>Leg0 = \<pi>.dom.leg0 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>0, Leg1 = \<mu>.dom.leg1 \<cdot> dom_\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1\<rparr>,
               Cod = \<lparr>Leg0 = \<pi>.cod.leg0 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0, Leg1 = \<mu>.cod.leg1 \<cdot> cod_\<mu>\<nu>\<pi>.Prj\<^sub>1\<rparr>\<rparr>"
        proof -
          have "arr (HoVH \<mu>\<nu>\<pi>)"
            using \<mu>\<nu>\<pi> by simp
          thus ?thesis
            using vcomp_def HoVH_\<mu>\<nu>\<pi> HoVH_\<mu>\<nu>\<pi>.arrow_of_spans_axioms
                  assoc_dom_\<mu>\<nu>\<pi>.arrow_of_spans_axioms assoc_dom dom_legs cod_legs
                  arr_char
            by simp
        qed
        moreover
        have "cod_\<mu>\<nu>\<pi>.chine_assoc \<cdot> HoHV_\<mu>\<nu>\<pi>.chine = HoVH_\<mu>\<nu>\<pi>.chine \<cdot> dom_\<mu>\<nu>\<pi>.chine_assoc"
          using \<mu>\<nu>\<pi> HoHV_def HoVH_def \<mu>\<nu>\<pi>.chine_assoc_naturality by simp
        ultimately show "assoc\<^sub>S\<^sub>B (fst (VVV.cod \<mu>\<nu>\<pi>)) (fst (snd (VVV.cod \<mu>\<nu>\<pi>)))
                                 (snd (snd (VVV.cod \<mu>\<nu>\<pi>))) \<bullet>
                           HoHV \<mu>\<nu>\<pi> =
                         HoVH \<mu>\<nu>\<pi> \<bullet>
                           assoc\<^sub>S\<^sub>B (fst (VVV.dom \<mu>\<nu>\<pi>)) (fst (snd (VVV.dom \<mu>\<nu>\<pi>)))
                                   (snd (snd (VVV.dom \<mu>\<nu>\<pi>)))"
          by argo
      qed
    qed

    definition assoc  ("\<a>[_, _, _]")
    where "assoc \<equiv> \<lambda>\<mu> \<nu> \<pi>. \<alpha>.map (\<mu>, \<nu>, \<pi>)"

    abbreviation (input) \<alpha>\<^sub>S\<^sub>B
    where "\<alpha>\<^sub>S\<^sub>B \<equiv> \<lambda>\<mu>\<nu>\<pi>. assoc (fst \<mu>\<nu>\<pi>) (fst (snd \<mu>\<nu>\<pi>)) (snd (snd \<mu>\<nu>\<pi>))"

    lemma \<alpha>_ide:
    assumes "ide f" and "ide g" and "ide h"
    and "src f = trg g" and "src g = trg h"
    shows "\<alpha>\<^sub>S\<^sub>B (f, g, h) = assoc\<^sub>S\<^sub>B f g h"
      using assms assoc_def \<alpha>.map_simp_ide VVV.ide_char VVV.arr_char VV.ide_char VV.arr_char
      by simp

    lemma natural_transformation_\<alpha>:
    shows "natural_transformation VVV.comp vcomp HoHV HoVH \<alpha>\<^sub>S\<^sub>B"
      using assoc_def \<alpha>.natural_transformation_axioms by auto

    interpretation \<alpha>: natural_transformation VVV.comp vcomp HoHV HoVH \<alpha>\<^sub>S\<^sub>B
      using natural_transformation_\<alpha> by simp

    interpretation \<alpha>: natural_isomorphism VVV.comp vcomp HoHV HoVH \<alpha>\<^sub>S\<^sub>B
    proof
      show "\<And>fgh. VVV.ide fgh \<Longrightarrow> iso (\<alpha>\<^sub>S\<^sub>B fgh)"
      proof -
        fix fgh
        assume fgh: "VVV.ide fgh"
        interpret f: arrow_of_spans C \<open>fst fgh\<close>
          using fgh VVV.ide_char VVV.arr_char arr_char by auto
        interpret g: arrow_of_spans C \<open>fst (snd fgh)\<close>
          using fgh VVV.ide_char VVV.arr_char VV.arr_char arr_char by auto
        interpret h: arrow_of_spans C \<open>snd (snd fgh)\<close>
          using fgh VVV.ide_char VVV.arr_char VV.arr_char arr_char by auto
        interpret fgh: three_composable_arrows_of_spans C prj0 prj1
                         \<open>fst fgh\<close> \<open>fst (snd fgh)\<close> \<open>snd (snd fgh)\<close>
          using fgh VVV.ide_char VVV.arr_char VV.arr_char arr_char
          by (unfold_locales, auto)
        interpret fgh: three_composable_identity_arrows_of_spans C prj0 prj1
                         \<open>fst fgh\<close> \<open>fst (snd fgh)\<close> \<open>snd (snd fgh)\<close>
          using fgh VVV.ide_char VV.ide_char ide_char
          apply unfold_locales
            apply blast
           apply blast
          by blast
        have 1: "arr (\<alpha>\<^sub>S\<^sub>B fgh)"
          using fgh \<alpha>.preserves_reflects_arr VVV.ideD(1) by blast
        have 2: "\<alpha>\<^sub>S\<^sub>B fgh = assoc\<^sub>S\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh))"
          using fgh assoc_def \<alpha>_ide [of "fst fgh" "fst (snd fgh)" "snd (snd fgh)"]
                VVV.ide_char VV.ide_char VVV.arr_char VV.arr_char
          by simp
        moreover have "iso ..."
          using 1 2 iso_char [of "assoc\<^sub>S\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh))"]
                fgh.chine_assoc_inverse by auto
        ultimately show "iso (\<alpha>\<^sub>S\<^sub>B fgh)" by argo
      qed
    qed

    lemma natural_isomorphism_\<alpha>:
    shows "natural_isomorphism VVV.comp vcomp HoHV HoVH \<alpha>\<^sub>S\<^sub>B"
      ..

  end

  locale four_composable_arrows_of_spans =
     span_bicategory +
  \<mu>: arrow_of_spans C \<mu> +
  \<nu>: arrow_of_spans C \<nu> +
  \<pi>: arrow_of_spans C \<pi> +
  \<rho>: arrow_of_spans C \<rho> +
  \<mu>\<nu>: two_composable_arrows_of_spans C prj0 prj1 \<mu> \<nu> +
  \<nu>\<pi>: two_composable_arrows_of_spans C prj0 prj1 \<nu> \<pi> +
  \<pi>\<rho>: two_composable_arrows_of_spans C prj0 prj1 \<pi> \<rho> +
  \<mu>\<nu>\<pi>: three_composable_arrows_of_spans C prj0 prj1 \<mu> \<nu> \<pi> +
  \<nu>\<pi>\<rho>: three_composable_arrows_of_spans C prj0 prj1 \<nu> \<pi> \<rho>
  for \<mu> (structure)
  and \<nu> (structure)
  and \<pi> (structure)
  and \<rho> (structure)

  locale four_composable_identity_arrows_of_spans =
    four_composable_arrows_of_spans +
  \<mu>: identity_arrow_of_spans C \<mu> +
  \<nu>: identity_arrow_of_spans C \<nu> +
  \<pi>: identity_arrow_of_spans C \<pi> +
  \<rho>: identity_arrow_of_spans C \<rho> +
  \<mu>\<nu>: two_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<nu> +
  \<nu>\<pi>: two_composable_identity_arrows_of_spans C prj0 prj1 \<nu> \<pi> +
  \<pi>\<rho>: two_composable_identity_arrows_of_spans C prj0 prj1 \<pi> \<rho> +
  \<mu>\<nu>\<pi>: three_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<nu> \<pi> +
  \<nu>\<pi>\<rho>: three_composable_identity_arrows_of_spans C prj0 prj1 \<nu> \<pi> \<rho>
  begin

    interpretation H: horizontal_composition vcomp hcomp src trg
      using has_horizontal_composition by auto

    text \<open>
      The following interpretations provide us with some systematic names
      for a lot of things.
    \<close>

    interpretation H\<mu>H\<nu>\<pi>: identity_arrow_of_spans C \<open>\<mu> \<star> \<nu> \<star> \<pi>\<close>
      using \<mu>\<nu>\<pi>.composites_are_identities ide_char' by auto
    interpretation HH\<mu>\<nu>\<pi>: identity_arrow_of_spans C \<open>(\<mu> \<star> \<nu>) \<star> \<pi>\<close>
      using \<mu>\<nu>\<pi>.composites_are_identities ide_char' by auto
    interpretation H\<nu>H\<pi>\<rho>: identity_arrow_of_spans C \<open>\<nu> \<star> \<pi> \<star> \<rho>\<close>
      using \<nu>\<pi>\<rho>.composites_are_identities ide_char' by auto
    interpretation HH\<nu>\<pi>\<rho>: identity_arrow_of_spans C \<open>(\<nu> \<star> \<pi>) \<star> \<rho>\<close>
      using \<nu>\<pi>\<rho>.composites_are_identities ide_char' by auto

    interpretation H\<mu>H\<nu>H\<pi>\<rho>: arrow_of_spans C \<open>\<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<close>
      using arrow_of_spans_hcomp \<mu>\<nu>.composable \<nu>\<pi>\<rho>.composites_are_arrows(1) by auto
    interpretation H\<mu>HH\<nu>\<pi>\<rho>: arrow_of_spans C \<open>\<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho>\<close>
      using arrow_of_spans_hcomp \<mu>\<nu>.composable \<nu>\<pi>\<rho>.composites_are_arrows(1) by auto
    interpretation HH\<mu>\<nu>H\<pi>\<rho>: arrow_of_spans C \<open>(\<mu> \<star> \<nu>) \<star> \<pi> \<star> \<rho>\<close>
      using hseq_char' match_4 \<mu>\<nu>\<pi>.composites_are_arrows(2) \<pi>\<rho>.composite_is_arrow arr_char
      by auto
    interpretation HH\<mu>H\<nu>\<pi>\<rho>: arrow_of_spans C \<open>(\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho>\<close>
      using arrow_of_spans_hcomp \<pi>\<rho>.composable \<mu>\<nu>\<pi>.composites_are_arrows(1) by auto
    interpretation HHH\<mu>\<nu>\<pi>\<rho>: arrow_of_spans C \<open>((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho>\<close>
      using arrow_of_spans_hcomp \<pi>\<rho>.composable \<mu>\<nu>\<pi>.composites_are_arrows(2) by auto

    interpretation assoc\<mu>\<nu>\<pi>: arrow_of_spans C \<open>assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>\<close>
      using arr_char \<mu>\<nu>.composable \<nu>\<pi>.composable assoc_simps(1) by auto
    interpretation assoc\<nu>\<pi>\<rho>: arrow_of_spans C \<open>assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>\<close>
      using arr_char \<nu>\<pi>.composable \<pi>\<rho>.composable assoc_simps(1) by auto

    interpretation \<mu>_\<nu>\<pi>: two_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<open>\<nu> \<star> \<pi>\<close>
      using \<mu>\<nu>.composable \<nu>\<pi>.composable by (unfold_locales, auto)
    interpretation \<mu>\<nu>_\<pi>: two_composable_identity_arrows_of_spans C prj0 prj1 \<open>\<mu> \<star> \<nu>\<close> \<pi>
      using \<mu>\<nu>.composable \<nu>\<pi>.composable by (unfold_locales, auto)
    interpretation \<nu>_\<pi>\<rho>: two_composable_identity_arrows_of_spans C prj0 prj1 \<nu> \<open>\<pi> \<star> \<rho>\<close>
      using \<nu>\<pi>.composable \<pi>\<rho>.composable by (unfold_locales, auto)
    interpretation \<nu>\<pi>_\<rho>: two_composable_identity_arrows_of_spans C prj0 prj1 \<open>\<nu> \<star> \<pi>\<close> \<rho>
      using \<nu>\<pi>.composable \<pi>\<rho>.composable by (unfold_locales, auto)
    (* The two other cases, \<mu>\<nu>\<pi> and \<nu>\<pi>\<rho>, are part of the locale assumptions. *)

    interpretation \<mu>_\<nu>\<pi>_\<rho>: three_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<open>\<nu> \<star> \<pi>\<close> \<rho> ..
    interpretation \<mu>_\<nu>_\<pi>\<rho>: three_composable_identity_arrows_of_spans C prj0 prj1 \<mu> \<nu> \<open>\<pi> \<star> \<rho>\<close> ..
    interpretation \<mu>\<nu>_\<pi>_\<rho>: three_composable_identity_arrows_of_spans C prj0 prj1 \<open>\<mu> \<star> \<nu>\<close> \<pi> \<rho> ..

    lemma chines_eq:
    shows "H\<mu>HH\<nu>\<pi>\<rho>.chine = \<mu>.leg0 \<down>\<down> HH\<nu>\<pi>\<rho>.leg1"
    and "HH\<mu>H\<nu>\<pi>\<rho>.chine = assoc\<mu>\<nu>\<pi>.cod.leg0 \<down>\<down> \<rho>.leg1"
    and "H\<mu>H\<nu>H\<pi>\<rho>.chine = \<mu>.leg0 \<down>\<down> H\<nu>H\<pi>\<rho>.leg1"
    proof -
      show "H\<mu>HH\<nu>\<pi>\<rho>.chine = \<mu>.leg0 \<down>\<down> HH\<nu>\<pi>\<rho>.leg1"
        using hcomp_def [of \<mu> "hcomp (hcomp \<nu> \<pi>) \<rho>"] chine_hcomp_ide_ide \<mu>\<nu>.composable
        by simp
      show "HH\<mu>H\<nu>\<pi>\<rho>.chine = assoc\<mu>\<nu>\<pi>.cod.leg0 \<down>\<down> \<rho>.leg1"
      proof -
        have "hseq \<nu> \<pi> \<and> arr \<mu> \<and> src \<mu> = trg (hcomp \<nu> \<pi>)"
          using \<mu>_\<nu>\<pi>.are_arrows(1) \<mu>_\<nu>\<pi>.composable \<nu>\<pi>.composite_is_arrow by blast
        then have "assoc\<mu>\<nu>\<pi>.cod.leg0 = \<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0"
          using \<nu>\<pi>.composable by (simp add: hcomp_def)
        then show ?thesis
          by (simp add: \<mu>_\<nu>\<pi>_\<rho>.chine_composite(1))
      qed
      show "H\<mu>H\<nu>H\<pi>\<rho>.chine = \<mu>.leg0 \<down>\<down> H\<nu>H\<pi>\<rho>.leg1"
        using hcomp_def [of \<mu> "hcomp \<nu> (hcomp \<pi> \<rho>)"] chine_hcomp_ide_ide \<mu>\<nu>.composable
        by simp
    qed

    lemma cospan_\<mu>0_H\<nu>H\<pi>\<rho>1:
    shows "C.cospan \<mu>.leg0 H\<nu>H\<pi>\<rho>.leg1"
    proof -
      have "H\<nu>H\<pi>\<rho>.leg1 = \<nu>.leg1 \<cdot> \<nu>\<pi>\<rho>.Prj\<^sub>1"
        using hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] \<nu>\<pi>.composable \<pi>\<rho>.composable
        apply auto
        by (auto simp add: hcomp_def)
      thus ?thesis
        using \<mu>\<nu>.legs_form_cospan \<nu>\<pi>.legs_form_cospan \<pi>\<rho>.legs_form_cospan by simp
    qed
 
    (* TODO: Better name for this. *)
    lemma assoc_in_homs:
    shows "\<guillemotleft>\<mu> \<star> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) : \<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho> \<Rightarrow> \<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<guillemotright>"
    and "\<guillemotleft>assoc\<^sub>S\<^sub>B \<mu> (\<nu> \<star> \<pi>) \<rho> : (\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho> \<Rightarrow> \<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho>\<guillemotright>"
    and "\<guillemotleft>assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi> \<star> \<rho> : ((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho> \<Rightarrow> (\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho>\<guillemotright>"
    and "\<guillemotleft>assoc\<^sub>S\<^sub>B \<mu> \<nu> (\<pi> \<star> \<rho>) : (\<mu> \<star> \<nu>) \<star> \<pi> \<star> \<rho> \<Rightarrow> \<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<guillemotright>"
    and "\<guillemotleft>assoc\<^sub>S\<^sub>B (\<mu> \<star> \<nu>) \<pi> \<rho> : ((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho> \<Rightarrow> (\<mu> \<star> \<nu>) \<star> \<pi> \<star> \<rho>\<guillemotright>"
    proof -
      show "\<guillemotleft>\<mu> \<star> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) : \<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho> \<Rightarrow> \<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<guillemotright>"
        using \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable by auto
      show "\<guillemotleft>assoc\<^sub>S\<^sub>B \<mu> (\<nu> \<star> \<pi>) \<rho> : (\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho> \<Rightarrow> \<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho>\<guillemotright>"
        using assoc_in_hom \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable by simp
      show "\<guillemotleft>assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi> \<star> \<rho> : ((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho> \<Rightarrow> (\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho>\<guillemotright>"
        using \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable by auto
      show "\<guillemotleft>assoc\<^sub>S\<^sub>B \<mu> \<nu> (\<pi> \<star> \<rho>) : (\<mu> \<star> \<nu>) \<star> \<pi> \<star> \<rho> \<Rightarrow> \<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<guillemotright>"
        using \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable
        by auto
      show "\<guillemotleft>assoc\<^sub>S\<^sub>B (\<mu> \<star> \<nu>) \<pi> \<rho> : ((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho> \<Rightarrow> (\<mu> \<star> \<nu>) \<star> \<pi> \<star> \<rho>\<guillemotright>"
        using \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable by auto
    qed

    lemma chine_composites:
    shows "Chn (\<mu> \<star> assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) = chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)"
    and "Chn (assoc\<^sub>S\<^sub>B \<mu> (\<nu> \<star> \<pi>) \<rho>) = \<mu>_\<nu>\<pi>_\<rho>.chine_assoc"
    and "Chn (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi> \<star> \<rho>) = chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
    and "Chn (assoc\<^sub>S\<^sub>B \<mu> \<nu> (\<pi> \<star> \<rho>)) = \<mu>_\<nu>_\<pi>\<rho>.chine_assoc"
    and "Chn (assoc\<^sub>S\<^sub>B (\<mu> \<star> \<nu>) \<pi> \<rho>) = \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
    proof -
      show "Chn (\<mu> \<star> assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) = chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)"
        using hcomp_def [of \<mu> "assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>"] chine_hcomp_def [of \<mu> "assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>"]
              \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable
        by auto
      show "Chn (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi> \<star> \<rho>) = chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
        using assoc_in_homs(2-3) hcomp_def
        by (metis arrI arrow_of_spans_data.select_convs(1) hseqE)
      show "Chn (assoc\<^sub>S\<^sub>B \<mu> (\<nu> \<star> \<pi>) \<rho>) = \<mu>_\<nu>\<pi>_\<rho>.chine_assoc"
        using hcomp_def
        by (meson arrow_of_spans_data.select_convs(1))
      show "Chn (assoc\<^sub>S\<^sub>B \<mu> \<nu> (\<pi> \<star> \<rho>)) = \<mu>_\<nu>_\<pi>\<rho>.chine_assoc"
        using hcomp_def
        by (meson arrow_of_spans_data.select_convs(1))
      show "Chn (assoc\<^sub>S\<^sub>B (\<mu> \<star> \<nu>) \<pi> \<rho>) = \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
        using hcomp_def
        by (meson arrow_of_spans_data.select_convs(1))
    qed

    lemma prj_in_homs [intro, simp]:
    shows "\<guillemotleft>\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] : H\<mu>HH\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<nu>\<pi>\<rho>.chine\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] : H\<mu>H\<nu>H\<pi>\<rho>.chine \<rightarrow>\<^sub>C \<mu>.apex\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.cod.leg0, \<rho>.cod.leg1] : HH\<mu>H\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>\<pi>.chine\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>0[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1] : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C \<rho>.chine\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1] : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>\<nu>\<pi>.chine\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>1[\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0, \<rho>.leg1] : HH\<mu>H\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>\<pi>.chine\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1] : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>\<nu>\<pi>.chine\<guillemotright>"
    and "\<guillemotleft>\<mu>_\<nu>\<pi>.prj\<^sub>0 : H\<mu>H\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<nu>\<pi>.apex\<guillemotright>"
    proof -
      show "\<guillemotleft>\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] : H\<mu>HH\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<nu>\<pi>\<rho>.chine\<guillemotright>"
      proof
        show "C.cospan \<mu>.leg0 HH\<nu>\<pi>\<rho>.leg1"
          using hcomp_def [of "hcomp \<nu> \<pi>" \<rho>] \<mu>_\<nu>\<pi>_\<rho>.cospan_\<mu>\<nu> \<pi>\<rho>.composable \<nu>\<pi>_\<rho>.legs_form_cospan
          by auto
        show "H\<mu>HH\<nu>\<pi>\<rho>.chine = \<mu>.leg0 \<down>\<down> HH\<nu>\<pi>\<rho>.leg1"
          using hcomp_def [of \<mu> "hcomp (hcomp \<nu> \<pi>) \<rho>"] chine_hcomp_ide_ide \<mu>\<nu>.composable
          by simp
        show "HH\<nu>\<pi>\<rho>.chine = C.dom HH\<nu>\<pi>\<rho>.leg1"
          by simp
      qed
      show "\<guillemotleft>\<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.cod.leg0, \<rho>.cod.leg1] : HH\<mu>H\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>\<pi>.chine\<guillemotright>"
      proof
        show "C.cospan assoc\<mu>\<nu>\<pi>.cod.leg0 \<rho>.cod.leg1"
          using hcomp_def [of \<mu> "hcomp \<nu> \<pi>"] hcomp_def [of \<nu> \<pi>]
          by (metis C.cod_comp H\<mu>H\<nu>\<pi>.cod.leg_simps(1) \<nu>\<pi>.cod_simps(2) \<mu>_\<nu>\<pi>.are_arrows(1)
              \<mu>_\<nu>\<pi>.composable \<mu>_\<nu>\<pi>_\<rho>.cospan_\<nu>\<pi> \<nu>\<pi>.composite_is_arrow \<rho>.cod_simps(3)
              arrow_of_spans_data.select_convs(3) span_data.select_convs(1))
        show "HH\<mu>H\<nu>\<pi>\<rho>.chine = assoc\<mu>\<nu>\<pi>.cod.leg0 \<down>\<down> \<rho>.cod.leg1"
          using chines_eq(2) by simp
        show "H\<mu>H\<nu>\<pi>.chine = C.dom assoc\<mu>\<nu>\<pi>.cod.leg0"
          by auto
      qed
      show "\<guillemotleft>\<p>\<^sub>0[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1] : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C \<rho>.chine\<guillemotright>"
      proof
        show "C.cospan HH\<mu>\<nu>\<pi>.leg0 \<rho>.leg1"
          using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable \<mu>\<nu>_\<pi>_\<rho>.cospan_\<mu>\<nu> \<nu>\<pi>\<rho>.cospan_\<nu>\<pi>
          by simp
        show "HHH\<mu>\<nu>\<pi>\<rho>.chine = HH\<mu>\<nu>\<pi>.leg0 \<down>\<down> \<rho>.leg1"
          using chine_hcomp_ide_ide hcomp_def [of "hcomp (hcomp \<mu> \<nu>) \<pi>" \<rho>] \<pi>\<rho>.composable
          by simp
        show "\<rho>.chine = C.dom \<rho>.leg1 " by simp
      qed
      show "\<guillemotleft>\<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1] : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>\<nu>\<pi>.chine\<guillemotright>"
      proof
        show "C.cospan HH\<mu>\<nu>\<pi>.leg0 \<rho>.leg1"
          using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable \<mu>\<nu>_\<pi>_\<rho>.cospan_\<mu>\<nu> \<nu>\<pi>\<rho>.cospan_\<nu>\<pi>
          by simp
        show "HHH\<mu>\<nu>\<pi>\<rho>.chine = HH\<mu>\<nu>\<pi>.leg0 \<down>\<down> \<rho>.leg1"
          using chine_hcomp_ide_ide hcomp_def [of "hcomp (hcomp \<mu> \<nu>) \<pi>" \<rho>] \<pi>\<rho>.composable
          by simp
        show "HH\<mu>\<nu>\<pi>.chine = C.dom HH\<mu>\<nu>\<pi>.leg0" by simp
      qed
      show "\<guillemotleft>\<p>\<^sub>1[\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0, \<rho>.leg1] : HH\<mu>H\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>\<pi>.chine\<guillemotright>"
      proof
        show "C.cospan (\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0) \<rho>.leg1"
          using \<mu>_\<nu>\<pi>.prj_in_hom(2) C.seqI' \<mu>_\<nu>\<pi>_\<rho>.cospan_\<nu>\<pi> by auto
        show "HH\<mu>H\<nu>\<pi>\<rho>.chine = \<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0 \<down>\<down> \<rho>.leg1"
          using chines_eq(2) hcomp_def [of \<mu> "hcomp \<nu> \<pi>"] \<mu>\<nu>.composable by simp
        show "H\<mu>H\<nu>\<pi>.chine = C.dom (\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0)"
          using \<mu>_\<nu>\<pi>.prj_in_hom(2) hcomp_def [of \<mu> "hcomp \<nu> \<pi>"] chine_hcomp_ide_ide \<mu>\<nu>.composable
          by auto
      qed
      show "\<guillemotleft>\<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1] : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>\<nu>\<pi>.chine\<guillemotright>"
      proof
        show "C.cospan assoc\<mu>\<nu>\<pi>.dom.leg0 \<rho>.leg1"
          using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable \<mu>\<nu>_\<pi>_\<rho>.cospan_\<mu>\<nu> \<nu>\<pi>\<rho>.cospan_\<nu>\<pi>
          by simp
        show "HHH\<mu>\<nu>\<pi>\<rho>.chine = assoc\<mu>\<nu>\<pi>.dom.leg0 \<down>\<down> \<rho>.leg1"
          using hcomp_def [of "hcomp (hcomp \<mu> \<nu>) \<pi>" \<rho>] chine_hcomp_ide_ide \<pi>\<rho>.composable
          by simp
        show "HH\<mu>\<nu>\<pi>.chine = C.dom assoc\<mu>\<nu>\<pi>.dom.leg0"
          using assoc\<mu>\<nu>\<pi>.dom.apex_def assoc\<mu>\<nu>\<pi>.chine_in_hom by fastforce
      qed
      show "\<guillemotleft>\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] : H\<mu>H\<nu>H\<pi>\<rho>.chine \<rightarrow>\<^sub>C \<mu>.apex\<guillemotright>"
        using cospan_\<mu>0_H\<nu>H\<pi>\<rho>1 chine_hcomp_ide_ide hcomp_def [of \<mu> "hcomp \<nu> (hcomp \<pi> \<rho>)"]
              \<mu>\<nu>.composable
        by auto
      show "\<guillemotleft>\<mu>_\<nu>\<pi>.prj\<^sub>0 : H\<mu>H\<nu>\<pi>.chine \<rightarrow>\<^sub>C \<nu>\<pi>.apex\<guillemotright>"
        using \<mu>_\<nu>\<pi>.prj_in_hom(2) chine_hcomp_ide_ide hcomp_def [of \<mu> "hcomp \<nu> \<pi>"] \<mu>\<nu>.composable
        by simp
    qed

    lemma chine_in_homs [intro, simp]:
    shows "\<guillemotleft>assoc\<mu>\<nu>\<pi>.chine : HH\<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>\<pi>.chine\<guillemotright>"
    and "\<guillemotleft>assoc\<nu>\<pi>\<rho>.chine : HH\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
    and "\<guillemotleft>chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) : H\<mu>HH\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
    and "\<guillemotleft>chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>H\<nu>\<pi>\<rho>.chine\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>assoc\<mu>\<nu>\<pi>.chine : HH\<mu>\<nu>\<pi>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>\<pi>.chine\<guillemotright>"
        using \<mu>\<nu>\<pi>.chine_assoc_in_hom by simp
      show "\<guillemotleft>assoc\<nu>\<pi>\<rho>.chine : HH\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
        using \<nu>\<pi>\<rho>.chine_assoc_in_hom by simp
      show "\<guillemotleft>chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) : H\<mu>HH\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<mu>H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
        using Chn_in_hom by (metis assoc_in_homs(1) chine_composites(1))
      show "\<guillemotleft>chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>H\<nu>\<pi>\<rho>.chine\<guillemotright>"
        using Chn_in_hom by (metis assoc_in_homs(3) chine_composites(3))
    qed

    lemma commutative_squares [intro, simp]:
    shows "C.commutative_square \<nu>\<pi>.leg0 \<rho>.leg1 \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0"
    and "C.commutative_square \<nu>.leg0 \<pi>\<rho>.leg1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
    and "C.commutative_square \<p>\<^sub>0[\<mu>.cod.leg0, assoc\<nu>\<pi>\<rho>.cod.leg1] assoc\<nu>\<pi>\<rho>.chine
            (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)) \<p>\<^sub>0[\<mu>.leg0, assoc\<nu>\<pi>\<rho>.dom.leg1]"
    and "C.commutative_square \<p>\<^sub>1[\<mu>.cod.leg0, assoc\<nu>\<pi>\<rho>.cod.leg1] \<mu>.chine
            (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)) \<p>\<^sub>1[\<mu>.leg0, assoc\<nu>\<pi>\<rho>.dom.leg1]"
    and "C.commutative_square assoc\<mu>\<nu>\<pi>.cod.leg0 \<rho>.cod.leg1
            (assoc\<mu>\<nu>\<pi>.chine \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1])
            (\<rho>.chine \<cdot> \<p>\<^sub>0[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1])"
    and "C.commutative_square \<mu>.leg0 (\<nu>\<pi>.leg1 \<cdot> \<nu>\<pi>_\<rho>.prj\<^sub>1) \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1
             \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
    and "C.commutative_square \<mu>.leg0 (\<nu>.leg1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>1) \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1
             \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
    proof -
      show 1: "C.commutative_square \<nu>\<pi>.leg0 \<rho>.leg1 \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0"
      proof -
        have 1: "C.arr \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0 \<and> C.dom \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0 = HH\<mu>H\<nu>\<pi>\<rho>.chine \<and>
                 C.cod \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0 = \<rho>.apex"
          by (meson C.in_homE \<mu>_\<nu>\<pi>_\<rho>.prj_in_hom(3))
        hence "(\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0) \<cdot> \<p>\<^sub>1[\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0, \<rho>.leg1] = \<rho>.leg1 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0"
          by (meson C.prj0_simps_arr C.pullback_commutes')
        thus ?thesis
          using 1 C.comp_assoc \<nu>\<pi>_\<rho>.legs_form_cospan(1) by simp
      qed
      show 2: "C.commutative_square \<nu>.leg0 \<pi>\<rho>.leg1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
      proof -
        have "\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0 \<cdot> \<p>\<^sub>1[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>\<rho>.leg1] =
              \<pi>\<rho>.leg1 \<cdot> \<p>\<^sub>0[\<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0, \<pi>\<rho>.leg1]"
          by (metis (no_types) C.category_axioms C.prj0_simps_arr C.pullback_commutes'
              category.comp_reduce \<mu>_\<nu>_\<pi>\<rho>.prj_simps(2) \<mu>_\<nu>_\<pi>\<rho>.prj_simps(3))
        thus ?thesis
          using C.commutative_square_def \<mu>_\<nu>_\<pi>\<rho>.cospan_\<nu>\<pi>
            \<mu>_\<nu>_\<pi>\<rho>.prj_simps(2) \<mu>_\<nu>_\<pi>\<rho>.prj_simps(3) \<mu>_\<nu>_\<pi>\<rho>.prj_simps(5) \<mu>_\<nu>_\<pi>\<rho>.prj_simps(6)
            \<mu>_\<nu>_\<pi>\<rho>.prj_simps(8) \<nu>.dom.apex_def
          by presburger
      qed
      show "C.commutative_square \<p>\<^sub>0[\<mu>.cod.leg0, assoc\<nu>\<pi>\<rho>.cod.leg1] assoc\<nu>\<pi>\<rho>.chine
                  (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)) \<p>\<^sub>0[\<mu>.leg0, assoc\<nu>\<pi>\<rho>.dom.leg1]"
        using assoc_in_homs(1) chine_hcomp_props(4) [of "assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>" \<mu>] hseq_char by blast
      show "C.commutative_square \<p>\<^sub>1[\<mu>.cod.leg0, assoc\<nu>\<pi>\<rho>.cod.leg1] \<mu>.chine
                  (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)) \<p>\<^sub>1[\<mu>.leg0, assoc\<nu>\<pi>\<rho>.dom.leg1]"
        using chine_hcomp_props(3) [of "assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>" \<mu>] hseq_char
              \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable
        by auto
      show "C.commutative_square assoc\<mu>\<nu>\<pi>.cod.leg0 \<rho>.cod.leg1
                  (assoc\<mu>\<nu>\<pi>.chine \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1])
                  (\<rho>.chine \<cdot> \<p>\<^sub>0[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1])"
        using assoc_in_homs(3) hseq_char chine_hcomp_props(2) by blast
      show "C.commutative_square \<mu>.leg0 (\<nu>\<pi>.leg1 \<cdot> \<nu>\<pi>_\<rho>.prj\<^sub>1) \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1
              \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
      proof
        show "C.cospan \<mu>.leg0 (\<nu>\<pi>.leg1 \<cdot> \<nu>\<pi>_\<rho>.prj\<^sub>1)"
          using HH\<nu>\<pi>\<rho>.dom.leg_simps(1) \<mu>_\<nu>\<pi>_\<rho>.cospan_\<mu>\<nu> C.arrI by fastforce
        show "C.span \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1 \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
          using 1 \<mu>_\<nu>\<pi>_\<rho>.prj_in_hom(1) by auto
        show "C.dom \<mu>.leg0 = C.cod \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
          by simp
        show "\<mu>.leg0 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1 =
              (\<nu>\<pi>.leg1 \<cdot> \<nu>\<pi>_\<rho>.prj\<^sub>1) \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
        proof -
          have "(\<nu>\<pi>.leg1 \<cdot> \<nu>\<pi>_\<rho>.prj\<^sub>1) \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> =
                \<nu>\<pi>.leg1 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1"
            using 1 C.comp_assoc by auto
          also have "... = \<mu>.leg0 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
            using hcomp_def [of \<nu> \<pi>]
            by (metis (no_types, lifting) C.comp_assoc C.prj1_simps_arr C.pullback_commutes'
                \<open>C.span \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1 \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>\<close> C.seqE)
          finally show ?thesis by auto
        qed
      qed
      show "C.commutative_square \<mu>.leg0 (\<nu>.leg1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>1) \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1
               \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
      proof
        show "C.cospan \<mu>.leg0 (\<nu>.leg1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>1)"
          using C.arrI \<mu>_\<nu>_\<pi>\<rho>.prj_in_hom(4) by auto
        show "C.span \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
          using 2 by fastforce
        thus "C.dom \<mu>.leg0 = C.cod \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1"
          using \<mu>_\<nu>_\<pi>\<rho>.cospan_\<mu>\<nu> by simp
        show "\<mu>.leg0 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1 =
              (\<nu>.leg1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>1) \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
        proof -
          have "(\<nu>.leg1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>1) \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> =
                \<nu>.leg1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
            using C.comp_assoc by auto
          also have "... = \<nu>.leg1 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1"
            using 2 by simp
          also have "... = \<mu>.leg0 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1"
            using C.pullback_commutes [of \<mu>.leg0 \<nu>.leg1]
            by (metis C.comp_assoc C.pullback_commutes' \<mu>_\<nu>_\<pi>\<rho>.cospan_\<mu>\<nu>)
          finally show ?thesis by simp
        qed
      qed

    qed

    lemma chine_pentagon:
    shows "Chn ((\<mu> \<star> assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) \<bullet> assoc\<^sub>S\<^sub>B \<mu> (\<nu> \<star> \<pi>) \<rho> \<bullet> (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi> \<star> \<rho>)) =
           Chn (assoc\<^sub>S\<^sub>B \<mu> \<nu> (\<pi> \<star> \<rho>) \<bullet> assoc\<^sub>S\<^sub>B (\<mu> \<star> \<nu>) \<pi> \<rho>)"
    proof -
      let ?LHS = "(\<mu> \<star> assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) \<bullet> assoc\<^sub>S\<^sub>B \<mu> (\<nu> \<star> \<pi>) \<rho> \<bullet> (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi> \<star> \<rho>)"
      let ?RHS = "assoc\<^sub>S\<^sub>B \<mu> \<nu> (\<pi> \<star> \<rho>) \<bullet> assoc\<^sub>S\<^sub>B (\<mu> \<star> \<nu>) \<pi> \<rho>"

      have LHS_in_hom: "\<guillemotleft>?LHS : ((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho> \<Rightarrow> \<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<guillemotright>"
        using \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable by auto
      have RHS_in_hom: "\<guillemotleft>?RHS : ((\<mu> \<star> \<nu>) \<star> \<pi>) \<star> \<rho> \<Rightarrow> \<mu> \<star> \<nu> \<star> \<pi> \<star> \<rho>\<guillemotright>"
        using \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable by auto

      have "arrow_of_spans (\<cdot>) ?LHS"
        using arr_char assoc_in_homs(1-3) by blast

      have L: "Chn ?LHS = chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                            chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
      proof -
        have "seq (\<mu> \<star> \<lparr>Chn = \<nu>\<pi>\<rho>.chine_assoc, Dom = Dom ((\<nu> \<star> \<pi>) \<star> \<rho>),
                        Cod = Cod (\<nu> \<star> \<pi> \<star> \<rho>)\<rparr>)
                  (\<lparr>Chn = \<mu>_\<nu>\<pi>_\<rho>.chine_assoc,
                    Dom = Dom ((\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho>), Cod = Cod (\<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho>)\<rparr> \<bullet>
                  (\<lparr>Chn = \<mu>\<nu>\<pi>.chine_assoc,
                    Dom = Dom ((\<mu> \<star> \<nu>) \<star> \<pi>), Cod = Cod (\<mu> \<star> \<nu> \<star> \<pi>)\<rparr> \<star> \<rho>))"
          by (meson LHS_in_hom arrI)
        moreover have "seq \<lparr>Chn = \<mu>_\<nu>\<pi>_\<rho>.chine_assoc,
                            Dom = Dom ((\<mu> \<star> \<nu> \<star> \<pi>) \<star> \<rho>), Cod = Cod (\<mu> \<star> (\<nu> \<star> \<pi>) \<star> \<rho>)\<rparr>
                       (\<lparr>Chn = \<mu>\<nu>\<pi>.chine_assoc,
                         Dom = Dom ((\<mu> \<star> \<nu>) \<star> \<pi>), Cod = Cod (\<mu> \<star> \<nu> \<star> \<pi>)\<rparr> \<star> \<rho>)"
          using assoc_in_homs(2) assoc_in_homs(3) by blast
        ultimately show ?thesis
          using Chn_vcomp chine_composites(1) chine_composites(2) chine_composites(3)
          by presburger
      qed
      have R: "Chn ?RHS = \<mu>_\<nu>_\<pi>\<rho>.chine_assoc \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
        using Chn_vcomp assoc_in_homs(4) assoc_in_homs(5) seqI' by auto

      text \<open>
        The outline of the proof is to show that the compositions of \<open>?LHS\<close>
        and \<open>?RHS\<close> with the two projections \<open>\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]\<close> and
        \<open>\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]\<close> are equal, and then apply \<open>\<nu>\<pi>\<rho>.prj'_joint_monic\<close>.
      \<close>

      text \<open>
        The case for projection \<open>\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]\<close> does not have subcases,
        so we'll dispatch that one first.
      \<close>

      have "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?LHS = \<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?RHS"
      proof -
        have "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?LHS = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
        proof -
          have "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?LHS =
                \<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                  chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            using L by simp
          also have "... = \<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                             chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
          proof -
            have "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) =
                  \<mu>.chine \<cdot> \<p>\<^sub>1[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]"
            proof -
              have "C.commutative_square \<p>\<^sub>1[\<mu>.cod.leg0, assoc\<nu>\<pi>\<rho>.cod.leg1] \<mu>.chine
                     (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)) \<p>\<^sub>1[\<mu>.leg0, assoc\<nu>\<pi>\<rho>.dom.leg1]"
                by blast
              thus ?thesis by auto
            qed
            thus ?thesis
            using C.comp_permute [of "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]" "chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)"
                                      \<mu>.chine "\<p>\<^sub>1[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]"
                                     "\<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"]
              by blast
          qed
          also have "... = \<mu>.chine \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            using C.comp_reduce [of "\<p>\<^sub>1[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]" \<mu>_\<nu>\<pi>_\<rho>.chine_assoc]
                  \<nu>\<pi>_\<rho>.leg1_composite
            by fastforce
          also have "... = \<mu>.chine \<cdot> \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
          proof -
            have "\<mu>.chine \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                  \<mu>.chine \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>1 \<cdot> \<p>\<^sub>1[\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0, \<rho>.leg1] \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using C.comp_assoc by simp
            also have "... = \<mu>.chine \<cdot> (\<mu>_\<nu>\<pi>.prj\<^sub>1 \<cdot> assoc\<mu>\<nu>\<pi>.chine) \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1]"
            proof -
              have "\<p>\<^sub>1[\<nu>\<pi>.leg0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0, \<rho>.leg1] \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                    assoc\<mu>\<nu>\<pi>.chine \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1]"
                using chine_hcomp_props(6) [of \<rho> "assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>"] hcomp_def [of \<mu> "hcomp \<nu> \<pi>"]
                      \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable
                      hseq_char assoc_in_homs(3)
                by auto
              thus ?thesis
                using C.comp_assoc by auto
            qed
            also have "... = \<mu>.chine \<cdot> \<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1 \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1]"
              using \<mu>\<nu>\<pi>.prj_chine_assoc(1) hcomp_def \<nu>\<pi>.composable by auto
            also have "... = \<mu>.chine \<cdot> \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
            proof -
              have "\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1 \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1] = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
              proof -
                have "\<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>1 \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1] =
                      (\<p>\<^sub>1[\<mu>.leg0, \<nu>.leg1] \<cdot> \<p>\<^sub>1[\<mu>\<nu>.leg0, \<pi>.leg1]) \<cdot> \<p>\<^sub>1[\<pi>.leg0 \<cdot> \<mu>\<nu>_\<pi>.prj\<^sub>0, \<rho>.leg1]"
                proof -
                  have "\<mu>\<nu>.leg0 = \<nu>.leg0 \<cdot> \<mu>\<nu>.prj\<^sub>0"
                    using hcomp_def \<mu>\<nu>.composable by simp
                  moreover have "assoc\<mu>\<nu>\<pi>.dom.leg0 = \<pi>.leg0 \<cdot> \<mu>\<nu>_\<pi>.prj\<^sub>0"
                    using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable by auto
                  ultimately show ?thesis by simp
                qed
                also have "... = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
                  using \<mu>\<nu>_\<pi>_\<rho>.prj_in_hom(1) C.comp_assoc by simp
                finally show ?thesis by blast
              qed
              thus ?thesis by simp
            qed
            finally show ?thesis by blast
          qed
          also have "... = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
            using \<mu>\<nu>_\<pi>_\<rho>.prj_in_hom(1) hcomp_def [of \<mu> \<nu>] chine_hcomp_ide_ide \<mu>\<nu>.cod.apex_def
                  \<mu>\<nu>.composable \<mu>_\<nu>_\<pi>\<rho>.cospan_\<mu>\<nu> C.comp_ide_arr
            by auto
          finally show ?thesis by blast
        qed
        also have "... = \<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?RHS"
        proof -
          have "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?RHS =
                \<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>_\<pi>\<rho>.chine_assoc \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
            using R by simp
          also have "... = \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
            using C.comp_reduce [of "\<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]" \<mu>_\<nu>_\<pi>\<rho>.chine_assoc]
                  hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] \<mu>_\<nu>_\<pi>\<rho>.chine_assoc_def \<nu>\<pi>.composable
            by fastforce
          also have "... = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
          proof -
            have "\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc = (\<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1) \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
              using hcomp_def [of \<mu> \<nu>] hcomp_def [of \<pi> \<rho>] \<mu>\<nu>.composable \<pi>\<rho>.composable
              by simp
            also have "... = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
              using \<mu>\<nu>.dom.apex_def \<mu>\<nu>.dom.leg_simps(1) hcomp_def \<mu>\<nu>.composable
                    \<mu>\<nu>.prj_in_hom(1) \<mu>\<nu>_\<pi>_\<rho>.prj_in_hom(4) C.comp_assoc
              by auto
            also have "... = \<mu>\<nu>.prj\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
              by simp
            finally show ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        finally show ?thesis by blast
      qed

      text \<open>
        Now for the case of \<open>\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]\<close>.
        We have to consider three sub-cases, involving the compositions with the projections
        \<open>\<nu>\<pi>\<rho>.Prj\<^sub>1\<close>, \<open>\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0\<close>, and \<open>\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0\<close>.
      \<close>

      moreover have "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?LHS =
                     \<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?RHS"
      proof -
        (* Facts common to the three sub-cases. *)
        have A: "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc =
                \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
          using \<mu>_\<nu>\<pi>_\<rho>.chine_assoc_def \<nu>\<pi>_\<rho>.leg1_composite by auto
        have B: "\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                 \<mu>_\<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine_assoc \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
        proof -
          have "\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                (\<mu>_\<nu>\<pi>.prj\<^sub>0 \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.cod.leg0, \<rho>.cod.leg1]) \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            using \<mu>_\<nu>\<pi>.composable \<nu>\<pi>.composite_is_arrow hcomp_def by auto
          also have "... = \<mu>_\<nu>\<pi>.prj\<^sub>0 \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.cod.leg0, \<rho>.cod.leg1] \<cdot>
                             chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            using C.comp_assoc by simp
          also have "... = \<mu>_\<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine_assoc \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
          proof -
            have "HH\<mu>\<nu>\<pi>.leg0 = assoc\<mu>\<nu>\<pi>.dom.leg0"
              using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] by simp
            moreover have "C.commutative_square assoc\<mu>\<nu>\<pi>.cod.leg0 \<rho>.cod.leg1
                               (assoc\<mu>\<nu>\<pi>.chine \<cdot> \<p>\<^sub>1[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1])
                               (\<rho>.chine \<cdot> \<p>\<^sub>0[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1])"
              by blast
            ultimately show ?thesis
              using chine_hcomp_def [of "assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>" \<rho>] by simp
          qed
          finally show ?thesis by blast
        qed
        have *: "assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                   chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                 \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
        proof -
          text \<open>Subcase \<open>\<nu>\<pi>\<rho>.Prj\<^sub>1\<close>:\<close>
          have "\<nu>\<pi>\<rho>.Prj\<^sub>1 \<cdot> assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                  chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                \<nu>\<pi>\<rho>.Prj\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
          proof -
            have "\<nu>\<pi>\<rho>.Prj\<^sub>1 \<cdot> assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                  \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using \<nu>\<pi>\<rho>.chine_assoc_props(1) C.prj0_in_hom [of \<mu>.leg0 HH\<nu>\<pi>\<rho>.leg1] cospan_\<mu>0_H\<nu>H\<pi>\<rho>1
                    C.comp_reduce [of \<nu>\<pi>\<rho>.Prj\<^sub>1 assoc\<nu>\<pi>\<rho>.chine \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>1
                                      "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                                         chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"]
              by auto
            also have "... = \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> \<cdot>
                              chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using A C.comp_reduce [of "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]" \<mu>_\<nu>\<pi>_\<rho>.chine_assoc]
              by fastforce
            also have "... = \<nu>\<pi>.prj\<^sub>1 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            proof -
              have "\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> = \<nu>\<pi>.prj\<^sub>1 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1"
              proof -
                have "\<nu>\<pi>.leg0 = \<pi>.leg0 \<cdot> \<nu>\<pi>.prj\<^sub>0"
                  using hcomp_def \<nu>\<pi>.composable by simp
                thus ?thesis
                  using commutative_squares(1) C.arrI \<mu>_\<nu>\<pi>_\<rho>.prj_in_hom(2) \<nu>\<pi>\<rho>.prj_in_hom(1)
                  by (simp add: C.comp_assoc)
              qed
              moreover have "C.seq \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>1 \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
                using chine_hcomp_ide_ide [of "hcomp \<nu> \<pi>" \<rho>] hcomp_def [of "hcomp \<nu> \<pi>" \<rho>]
                      \<pi>\<rho>.composable \<nu>\<pi>\<rho>.prj_in_hom(1)
                by auto
              moreover have "C.seq \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>
                                   (chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>)"
                by fastforce
              ultimately show ?thesis
                using C.comp_permute by blast
            qed
            also have "... = \<nu>\<pi>.prj\<^sub>1 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine_assoc \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
              using B by simp
            also have "... = \<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>1 \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
              using hcomp_def [of \<nu> \<pi>] \<nu>\<pi>.composable C.comp_assoc
                    C.comp_reduce [of \<mu>\<nu>\<pi>.Prj\<^sub>1\<^sub>0 \<mu>\<nu>\<pi>.chine_assoc \<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>1 "\<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"]
                    \<mu>\<nu>\<pi>.prj_in_hom(5) \<mu>\<nu>\<pi>.prj_chine_assoc(2)
              by auto
            also have "... = \<nu>\<pi>\<rho>.Prj\<^sub>1 \<cdot>
                             \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
            proof -
              have 1: "C.commutative_square \<nu>.leg0 \<pi>\<rho>.leg1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
                by blast
              hence 2: "\<guillemotleft>\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> :
                           HH\<mu>\<nu>H\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
                using hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] chine_hcomp_ide_ide \<nu>\<pi>.composable by auto
              have "\<nu>\<pi>\<rho>.Prj\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc =
                     \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
                using 1 2 \<pi>\<rho>.composable hcomp_def [of \<pi> \<rho>]
                      C.comp_reduce [of \<nu>\<pi>\<rho>.Prj\<^sub>1 "\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
                                        \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<mu>\<nu>_\<pi>_\<rho>.chine_assoc]
                by fastforce
              also have "... = \<mu>\<nu>.prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>1"
              proof -
                have "\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 = \<mu>\<nu>.prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1"
                  using hcomp_def \<mu>\<nu>.composable \<pi>\<rho>.composable by simp
                thus ?thesis
                  using C.comp_reduce C.comp_assoc by auto
              qed
              also have "... = \<mu>\<nu>.prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>.prj\<^sub>1 \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
                using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable by simp
              also have "... = \<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>1 \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
              proof -
                have 1: "\<mu>\<nu>.prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>.prj\<^sub>1 = \<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>1"
                  using hcomp_def \<mu>\<nu>.composable by simp
                moreover have 2: "C.seq \<mu>\<nu>.prj\<^sub>0 \<mu>\<nu>_\<pi>.prj\<^sub>1"
                  using 1 by fastforce
                moreover have "C.seq \<mu>\<nu>_\<pi>.prj\<^sub>1 \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
                  by (metis 1 2 C.match_1 C.seqI' \<mu>\<nu>\<pi>.prj_in_hom(2) prj_in_homs(5))
                ultimately show ?thesis
                  using C.comp_reduce by simp
              qed
              finally show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          moreover
          text \<open>Subcase \<open>\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0\<close>:\<close>
          have "\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                  chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
          proof -
            have "\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                  \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using C.comp_reduce [of \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 "assoc\<nu>\<pi>\<rho>.chine" \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>1
                                      "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                                         chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"]
              by auto
            also have "... = \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> \<cdot>
                              chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using A C.comp_reduce [of "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]" \<mu>_\<nu>\<pi>_\<rho>.chine_assoc]
              by fastforce
            also have "... = \<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            proof -
              have "\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> =
                    \<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1"
                using commutative_squares(1) C.arrI \<mu>_\<nu>\<pi>_\<rho>.prj_in_hom(2) \<nu>\<pi>\<rho>.prj_in_hom(2)
                      C.comp_assoc \<nu>\<pi>.leg0_composite
                by auto
              moreover have "C.seq \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
                using chine_hcomp_ide_ide [of "hcomp \<nu> \<pi>" \<rho>] hcomp_def [of "hcomp \<nu> \<pi>" \<rho>]
                      \<pi>\<rho>.composable \<nu>\<pi>\<rho>.prj_in_hom(2)
                by auto
              moreover have "C.seq \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>
                                   (chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>)"
                by fastforce
              ultimately show ?thesis
                using C.comp_permute by blast
            qed
            also have "... = \<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>_\<nu>\<pi>.prj\<^sub>0 \<cdot> \<mu>\<nu>\<pi>.chine_assoc \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
              using B by simp
            also have "... = \<mu>\<nu>\<pi>.Prj\<^sub>0 \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
              using hcomp_def [of \<nu> \<pi>] \<nu>\<pi>.composable \<mu>\<nu>\<pi>.prj_in_hom(6)
                    C.comp_reduce [of \<nu>\<pi>.prj\<^sub>0 \<mu>_\<nu>\<pi>.prj\<^sub>0 \<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0
                                      "\<mu>\<nu>\<pi>.chine_assoc \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"]
                    C.comp_reduce [of \<mu>\<nu>\<pi>.Prj\<^sub>0\<^sub>0 \<mu>\<nu>\<pi>.chine_assoc \<mu>\<nu>\<pi>.Prj\<^sub>0
                                      "\<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"]
              by fastforce
            also have "... = \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot>
                             \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
            proof -
              have 1: "C.commutative_square \<nu>.leg0 \<pi>\<rho>.leg1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
                by blast
              hence 2: "\<guillemotleft>\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> :
                            HH\<mu>\<nu>H\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
                using hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] chine_hcomp_ide_ide \<nu>\<pi>.composable by auto
              have "\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> = \<pi>\<rho>.prj\<^sub>1 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
              proof -
                have "\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> =
                      \<pi>\<rho>.prj\<^sub>1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
                proof -
                  have "\<pi>\<rho>.prj\<^sub>1 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>0 = \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0"
                    using hcomp_def [of \<pi> \<rho>] \<pi>\<rho>.composable by simp
                  moreover have "C.seq \<pi>\<rho>.prj\<^sub>1
                                       (\<nu>_\<pi>\<rho>.prj\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>)"
                    using 2 hcomp_def [of \<pi> \<rho>] \<nu>\<pi>\<rho>.chine_composite(2) \<nu>\<pi>\<rho>.prj_in_hom(5)
                          \<pi>\<rho>.composable
                    by auto
                  ultimately show ?thesis
                    using 2 C.comp_reduce [of \<pi>\<rho>.prj\<^sub>1 \<nu>_\<pi>\<rho>.prj\<^sub>0 \<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0
                                              "\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"]
                    by auto
                qed
                also have "... = \<pi>\<rho>.prj\<^sub>1 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
                  using 1 by simp
                finally show ?thesis by blast
              qed
              hence "\<nu>\<pi>\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot>
                       \<mu>\<nu>_\<pi>_\<rho>.chine_assoc =
                     \<pi>\<rho>.prj\<^sub>1 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
                using 2 C.comp_permute by blast
              also have "... = \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
             proof -
                have "\<pi>\<rho>.prj\<^sub>1 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0 = \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>0"
                  using hcomp_def \<mu>\<nu>.composable \<pi>\<rho>.composable by simp
                thus ?thesis
                  using 2 C.comp_reduce [of \<pi>\<rho>.prj\<^sub>1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0 \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>1\<^sub>0 \<mu>\<nu>_\<pi>_\<rho>.chine_assoc]
                  by auto
              qed
              also have "... = \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>0\<^sub>1"
                by simp
              also have "... = \<mu>\<nu>\<pi>.Prj\<^sub>0 \<cdot> \<p>\<^sub>1[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
                using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] hcomp_def [of \<mu> \<nu>] \<mu>\<nu>.composite_is_arrow
                      \<mu>\<nu>_\<pi>.composable
                by auto
              finally show ?thesis by simp
            qed
            finally show ?thesis by blast
          qed
          moreover
          text \<open>Subcase \<open>\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0\<close>:\<close>
          have "\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                  chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
          proof -
            have "\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> =
                  \<nu>\<pi>\<rho>.Prj\<^sub>0 \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                    chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using C.comp_reduce [of \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 assoc\<nu>\<pi>\<rho>.chine \<nu>\<pi>\<rho>.Prj\<^sub>0
                                      "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                                         chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"]
              by fastforce
            also have "... = \<nu>\<pi>\<rho>.Prj\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> \<cdot>
                              chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
              using A C.comp_reduce [of "\<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]" \<mu>_\<nu>\<pi>_\<rho>.chine_assoc]
              by fastforce
            also have "... = \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0 \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            proof -
              have "\<nu>\<pi>\<rho>.Prj\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle> = \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0"
              proof -
                have "\<nu>\<pi>\<rho>.Prj\<^sub>0 = \<nu>\<pi>_\<rho>.prj\<^sub>0"
                  using hcomp_def [of \<nu> \<pi>] \<nu>\<pi>.composable by simp
                thus ?thesis by simp
              qed
              thus ?thesis
                using chine_hcomp_ide_ide [of "hcomp \<nu> \<pi>" \<rho>] hcomp_def [of "hcomp \<nu> \<pi>" \<rho>]
                      \<pi>\<rho>.composable \<mu>_\<nu>\<pi>_\<rho>.prj_in_hom(3) calculation
                      C.comp_reduce [of \<nu>\<pi>\<rho>.Prj\<^sub>0 "\<langle>\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>\<pi>.leg0, \<rho>.leg1\<rbrakk> \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0\<rangle>"
                                        \<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0 "chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"]
                by fastforce
            qed
            also have "... = \<rho>.chine \<cdot> \<p>\<^sub>0[assoc\<mu>\<nu>\<pi>.dom.leg0, \<rho>.leg1]"
            proof -
              have "\<mu>_\<nu>\<pi>_\<rho>.Prj\<^sub>0 = \<p>\<^sub>0[assoc\<mu>\<nu>\<pi>.cod.leg0, \<rho>.cod.leg1]"
                using \<mu>_\<nu>\<pi>.composable \<nu>\<pi>.composite_is_arrow hcomp_def by auto
              thus ?thesis
                using chine_hcomp_props(5) [of \<rho> "assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>"]
                      \<mu>\<nu>.composable \<nu>\<pi>.composable \<pi>\<rho>.composable
                by simp
            qed
            also have "... = \<p>\<^sub>0[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
            proof -
              have "C.cospan HH\<mu>\<nu>\<pi>.leg0 \<rho>.leg1"
                using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable prj_in_homs(5) by blast
              hence "\<rho>.chine = C.cod \<p>\<^sub>0[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
                using C.prj0_simps [of HH\<mu>\<nu>\<pi>.leg0 \<rho>.leg1] by simp
              thus ?thesis
                using C.comp_cod_arr hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] \<nu>\<pi>.composable
                      HH\<mu>\<nu>\<pi>.dom.leg_simps(1) \<nu>\<pi>\<rho>.cospan_\<nu>\<pi>
                by simp
            qed
            also have "... = \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot>
                             \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
            proof -
              have 1: "C.commutative_square \<nu>.leg0 \<pi>\<rho>.leg1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
                by blast
              hence 2: "\<guillemotleft>\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> :
                           HH\<mu>\<nu>H\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
                using hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] chine_hcomp_ide_ide \<nu>\<pi>.composable by auto
              have
                "\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc =
                 \<pi>\<rho>.prj\<^sub>0 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
              proof -
                have "\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> =
                      \<pi>\<rho>.prj\<^sub>0 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
                proof -
                  have
                    "\<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> =
                     \<pi>\<rho>.prj\<^sub>0 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
                  proof -
                    have 3: "\<pi>\<rho>.prj\<^sub>0 \<cdot> \<nu>_\<pi>\<rho>.prj\<^sub>0 = \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0"
                      using hcomp_def [of \<pi> \<rho>] \<pi>\<rho>.composable by simp
                    moreover have "C.seq \<pi>\<rho>.prj\<^sub>0
                                         (\<nu>_\<pi>\<rho>.prj\<^sub>0 \<cdot> \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>)"
                      using 1 2 3 hcomp_def [of \<pi> \<rho>] \<nu>\<pi>\<rho>.chine_composite(2)
                            \<pi>\<rho>.composable
                      by (metis C.arrI C.match_4 C.prj_tuple(1) \<mu>_\<nu>_\<pi>\<rho>.prj_in_hom(3)
                          \<nu>\<pi>\<rho>.prj_in_hom(6))
                    ultimately show ?thesis
                      using 2 C.comp_reduce [of \<pi>\<rho>.prj\<^sub>0 \<nu>_\<pi>\<rho>.prj\<^sub>0 \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0
                                                "\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"]
                      by auto
                  qed
                  also have "... = \<pi>\<rho>.prj\<^sub>0 \<cdot> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0"
                    using 1 by simp
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using 2 C.comp_permute [of \<nu>\<pi>\<rho>.Prj\<^sub>0\<^sub>0 "\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
                                             \<pi>\<rho>.prj\<^sub>0 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0 \<mu>\<nu>_\<pi>_\<rho>.chine_assoc]
                  by blast
              qed
              also have "... = \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>0\<^sub>0 \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
                using hcomp_def \<mu>\<nu>.composable \<pi>\<rho>.composable C.comp_assoc \<nu>\<pi>\<rho>.cospan_\<nu>\<pi>
                      C.comp_reduce [of \<pi>\<rho>.prj\<^sub>0 \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0 \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>0\<^sub>0 \<mu>\<nu>_\<pi>_\<rho>.chine_assoc]
                by auto
              also have "... = \<mu>\<nu>_\<pi>_\<rho>.Prj\<^sub>0"
                by simp
              also have "... = \<p>\<^sub>0[HH\<mu>\<nu>\<pi>.leg0, \<rho>.leg1]"
                using hcomp_def [of "hcomp \<mu> \<nu>" \<pi>] hcomp_def [of \<mu> \<nu>]
                      \<mu>\<nu>.composite_is_arrow \<mu>\<nu>_\<pi>.composable
                by auto
              finally show ?thesis by simp
            qed
            finally show ?thesis by blast
          qed
          moreover have "\<guillemotleft>assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                            chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho> : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
            using \<nu>\<pi>\<rho>.chine_assoc_props(1) by fast
          moreover have "\<guillemotleft>\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc :
                            HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
          proof -
            have "\<guillemotleft>\<mu>\<nu>_\<pi>_\<rho>.chine_assoc : HHH\<mu>\<nu>\<pi>\<rho>.chine \<rightarrow>\<^sub>C HH\<mu>\<nu>H\<pi>\<rho>.chine\<guillemotright>"
              using \<mu>\<nu>_\<pi>_\<rho>.chine_assoc_props(1) by blast
            moreover have "\<guillemotleft>\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> :
                              HH\<mu>\<nu>H\<pi>\<rho>.chine \<rightarrow>\<^sub>C H\<nu>H\<pi>\<rho>.chine\<guillemotright>"
              using chine_hcomp_ide_ide hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] \<nu>\<pi>.composable by auto
            ultimately show ?thesis by blast
          qed
          ultimately show ?thesis
            using \<nu>\<pi>\<rho>.prj'_joint_monic
                    [of "assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                           chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
                        HHH\<mu>\<nu>\<pi>\<rho>.chine
                        "\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"]
            by simp
        qed

        text \<open>
          Now use fact \<open>*\<close> to finish off the \<open>\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]\<close> case.
        \<close>
        have "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?LHS =
              assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
        proof -
          have "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?LHS =
                \<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                  chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
            using L by simp
          also have "... = assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot>
                             chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>"
          proof -
            have "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>) =
                  assoc\<nu>\<pi>\<rho>.chine \<cdot> \<p>\<^sub>0[\<mu>.leg0, HH\<nu>\<pi>\<rho>.leg1]"
            proof -
              have "C.commutative_square \<p>\<^sub>0[\<mu>.cod.leg0, assoc\<nu>\<pi>\<rho>.cod.leg1] assoc\<nu>\<pi>\<rho>.chine
                      (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>)) \<p>\<^sub>0[\<mu>.leg0, assoc\<nu>\<pi>\<rho>.dom.leg1]"
                by blast
              thus ?thesis
                using \<nu>\<pi>\<rho>.chine_assoc_props(1) by auto
            qed
            moreover have "C.seq \<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>))"
              using cospan_\<mu>0_H\<nu>H\<pi>\<rho>1 prj_in_homs(2) by fastforce
            moreover have "C.seq (chine_hcomp \<mu> (assoc\<^sub>S\<^sub>B \<nu> \<pi> \<rho>))
                                 (\<mu>_\<nu>\<pi>_\<rho>.chine_assoc \<cdot> chine_hcomp (assoc\<^sub>S\<^sub>B \<mu> \<nu> \<pi>) \<rho>)"
              by blast
            ultimately show ?thesis
              using chine_hcomp_props(4) C.comp_permute by auto
          qed
          finally show ?thesis by blast
        qed
        also have "... = \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
          using * by simp
        also have "... = \<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?RHS"
        proof -
          have "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> Chn ?RHS =
                \<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>_\<pi>\<rho>.chine_assoc \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
            using R by simp
          also have "... = \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle> \<cdot> \<mu>\<nu>_\<pi>_\<rho>.chine_assoc"
          proof -
            have "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] \<cdot> \<mu>_\<nu>_\<pi>\<rho>.chine_assoc =
                  \<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
              using hcomp_def [of \<nu> "hcomp \<pi> \<rho>"] \<nu>\<pi>.composable \<mu>_\<nu>_\<pi>\<rho>.chine_assoc_def by auto
            thus ?thesis
              using C.comp_reduce [of "\<p>\<^sub>0[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1]" \<mu>_\<nu>_\<pi>\<rho>.chine_assoc
                                      "\<langle>\<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<^sub>1 \<lbrakk>\<nu>.leg0, \<pi>\<rho>.leg1\<rbrakk> \<mu>_\<nu>_\<pi>\<rho>.Prj\<^sub>0\<rangle>"
                                      \<mu>\<nu>_\<pi>_\<rho>.chine_assoc]
              by fastforce
          qed
          finally show ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
      moreover have "C.seq \<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] (Chn ?LHS)"
        using LHS_in_hom Chn_in_hom by blast
      moreover have "C.seq \<p>\<^sub>1[\<mu>.leg0, H\<nu>H\<pi>\<rho>.leg1] (Chn ?RHS)"
        using RHS_in_hom Chn_in_hom by blast
      ultimately show "Chn ?LHS = Chn ?RHS"
        using cospan_\<mu>0_H\<nu>H\<pi>\<rho>1 C.prj_joint_monic by blast
    qed

  end

  context span_bicategory
  begin

    interpretation VxV: product_category vcomp vcomp ..
    interpretation VV: subcategory VxV.comp \<open>\<lambda>\<nu>\<mu>. arr (fst \<nu>\<mu>) \<and> arr (snd \<nu>\<mu>) \<and>
                                                   src (fst \<nu>\<mu>) = trg (snd \<nu>\<mu>)\<close>
      by (unfold_locales, simp_all)
    interpretation VxVxV: product_category vcomp VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                          \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                 src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by auto

    interpretation H: horizontal_composition vcomp hcomp src trg
      using has_horizontal_composition by auto

    interpretation HoHV: "functor" VVV.comp vcomp HoHV
      using functor_HoHV by blast
    interpretation HoVH: "functor" VVV.comp vcomp HoVH
      using functor_HoVH by blast

    interpretation L: equivalence_functor vcomp vcomp L
      using equivalence_functor_L by auto
    interpretation R: equivalence_functor vcomp vcomp R
      using equivalence_functor_R by auto

    interpretation \<alpha>: natural_isomorphism VVV.comp vcomp HoHV HoVH \<alpha>\<^sub>S\<^sub>B
      using natural_isomorphism_\<alpha> by blast

    lemma pentagon:
    assumes "ide f" and "ide g" and "ide h" and "ide k"
    and "src f = trg g" and "src g = trg h" and "src h = trg k"
    shows "(f \<star> \<alpha>\<^sub>S\<^sub>B (g, h, k)) \<bullet> \<alpha>\<^sub>S\<^sub>B (f, g \<star> h, k) \<bullet> (\<alpha>\<^sub>S\<^sub>B (f, g, h) \<star> k) =
           \<alpha>\<^sub>S\<^sub>B (f, g, h \<star> k) \<bullet> \<alpha>\<^sub>S\<^sub>B (f \<star> g, h, k)"
    proof -
      interpret f: identity_arrow_of_spans C f
        using assms ide_char' by auto
      interpret g: identity_arrow_of_spans C g
        using assms ide_char' by auto
      interpret h: identity_arrow_of_spans C h
        using assms ide_char' by auto
      interpret k: identity_arrow_of_spans C k
        using assms ide_char' by auto

      interpret fghk: four_composable_identity_arrows_of_spans C prj0 prj1 f g h k
        using assms by (unfold_locales, auto)

      let ?LHS = "(f \<star> assoc\<^sub>S\<^sub>B g h k) \<bullet> (assoc\<^sub>S\<^sub>B f (g \<star> h) k) \<bullet> (assoc\<^sub>S\<^sub>B f g h \<star> k)"
      let ?RHS = "assoc\<^sub>S\<^sub>B f g (h \<star> k) \<bullet> assoc\<^sub>S\<^sub>B (f \<star> g) h k"

      have "(f \<star> \<alpha>\<^sub>S\<^sub>B (g, h, k)) \<bullet> \<alpha>\<^sub>S\<^sub>B (f, g \<star> h, k) \<bullet> (\<alpha>\<^sub>S\<^sub>B (f, g, h) \<star> k) = ?LHS"
        using assms \<alpha>_ide ide_hcomp src_hcomp trg_hcomp by simp
      also have "... = ?RHS"
        using fghk.\<mu>\<nu>.composable fghk.\<nu>\<pi>.composable fghk.\<pi>\<rho>.composable fghk.chine_pentagon
        by (intro arr_eqI, auto)
      also have "... = \<alpha>\<^sub>S\<^sub>B (f, g, h \<star> k) \<bullet> \<alpha>\<^sub>S\<^sub>B (f \<star> g, h, k)"
        using assms \<alpha>_ide ide_hcomp src_hcomp trg_hcomp by simp
      finally show ?thesis by blast
    qed

    lemma extends_to_bicategory:
    shows "bicategory vcomp hcomp assoc unit src trg"
      using unit_in_hom obj_char iso_unit assoc_def pentagon
      apply unfold_locales by auto

    sublocale bicategory vcomp hcomp assoc unit src trg
      using extends_to_bicategory by auto

  end

  subsection "Miscellaneous Formulas"

  context span_bicategory
  begin

    no_notation in_hom    ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation in_hom       ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")

    notation lunit        ("\<l>[_]")
    notation runit        ("\<r>[_]")
    notation lunit'       ("\<l>\<^sup>-\<^sup>1[_]")
    notation runit'       ("\<r>\<^sup>-\<^sup>1[_]")
    notation assoc        ("\<a>[_, _, _]")
    notation \<a>'           ("\<a>\<^sup>-\<^sup>1[_, _, _]")

    lemma \<alpha>'_ide:
    assumes "ide f" and "ide g" and "ide h"
    and "src f = trg g" and "src g = trg h"
    shows "\<alpha>' (f, g, h) = assoc'\<^sub>S\<^sub>B f g h"
    proof -
      have fgh: "VVV.ide (f, g, h)"
        using assms VVV.ide_char VVV.arr_char VV.arr_char by simp
      interpret f: arrow_of_spans C f
        using assms arr_char [of f] by auto
      interpret g: arrow_of_spans C g
        using assms arr_char [of g] by auto
      interpret h: arrow_of_spans C h
        using assms arr_char [of h] by auto
      interpret fgh: three_composable_arrows_of_spans C prj0 prj1 f g h
        using assms by (unfold_locales, auto)
      interpret fgh: three_composable_identity_arrows_of_spans C prj0 prj1 f g h
        using assms ide_char by (unfold_locales, auto)
      have "\<alpha>' (f, g, h) = inv (\<alpha> (f, g, h))"
        using fgh \<alpha>'.inverts_components
        by (simp add: \<alpha>_def)
      moreover have "inv (\<alpha> (f, g, h)) = \<lparr>Chn = C.inv (Chn (\<alpha> (f, g, h))),
                                          Dom = Cod (\<alpha> (f, g, h)),
                                          Cod = Dom (\<alpha> (f, g, h))\<rparr>"
        using fgh \<alpha>.components_are_iso inv_eq
        by (simp add: \<alpha>_def fgh.\<mu>\<nu>.composable fgh.\<nu>\<pi>.composable)
      moreover have "... = assoc'\<^sub>S\<^sub>B f g h"
        using assms fgh \<alpha>_ide [of f g h] fgh.chine_assoc_inverse C.inverse_unique
        by (simp add: \<alpha>_def)
      ultimately show ?thesis by simp
    qed

    text \<open>
      The following give explicit expressions for the unitors,
      derived from their characterizing properties and the definition of the associators.
    \<close>

    lemma runit_ide_eq:
    assumes "ide f"
    shows "\<r>[f] = \<lparr>Chn = \<p>\<^sub>1[Leg0 (Dom f), C.cod (Leg0 (Dom f))],
                   Dom = \<lparr>Leg0 = \<p>\<^sub>0[Leg0 (Dom f), C.cod (Leg0 (Dom f))],
                          Leg1 = Leg1 (Dom f) \<cdot> \<p>\<^sub>1[Leg0 (Dom f), C.cod (Leg0 (Dom f))]\<rparr>,
                   Cod = Cod f\<rparr>"
    proof -
      interpret f: identity_arrow_of_spans C f
        using assms ide_char' by auto
      interpret src: identity_arrow_of_spans C \<open>src f\<close>
        using assms ide_char' ide_src by auto
      interpret f_src: two_composable_identity_arrows_of_spans C prj0 prj1 f \<open>src f\<close>
        using assms by (unfold_locales, simp)
      interpret src_src: two_composable_identity_arrows_of_spans C prj0 prj1 \<open>src f\<close> \<open>src f\<close>
        by (unfold_locales, simp)
      interpret f_src_src: three_composable_identity_arrows_of_spans C prj0 prj1 f \<open>src f\<close> \<open>src f\<close>
        ..

      let ?rf = "\<lparr>Chn = \<p>\<^sub>1[f.leg0, f.dsrc],
                  Dom = \<lparr>Leg0 = \<p>\<^sub>0[f.leg0, f.dsrc], Leg1 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc]\<rparr>,
                  Cod = Cod f\<rparr>"
      have "?rf = \<r>[f]"
      proof (intro runit_eqI)
        show "ide f" by fact
        interpret rf: arrow_of_spans C ?rf
        proof -
          interpret dom_rf: span_in_category C
                              \<open>\<lparr>Leg0 = \<p>\<^sub>0[f.leg0, f.dsrc], Leg1 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc]\<rparr>\<close>
            by (unfold_locales, simp_all)
          show "arrow_of_spans C ?rf"
            using dom_rf.apex_def C.comp_cod_arr C.pullback_commutes [of f.leg0 f.dsrc]
            apply unfold_locales by auto
        qed
        show rf_in_hom: "\<guillemotleft>?rf : f \<star> src f \<Rightarrow> f\<guillemotright>"
        proof
          show "arr ?rf"
            using rf.arrow_of_spans_axioms arr_char by simp
          show "cod ?rf = f"
            using cod_char rf.arrow_of_spans_axioms arr_char by simp
          show "dom ?rf = f \<star> src f"
            using dom_char rf.arrow_of_spans_axioms src.arrow_of_spans_axioms arr_char hcomp_def
                  f.arrow_of_spans_axioms f_src.composable chine_hcomp_ide_ide src_def ide_char
                  C.comp_cod_arr rf.dom.apex_def
            by simp
        qed
        show "?rf \<star> src f = (f \<star> \<i>[src f]) \<bullet> \<a>[f, src f, src f]"
        proof (intro arr_eqI)
          show par: "par (?rf \<star> src f) ((f \<star> \<i>[src f]) \<bullet> \<a>[f, src f, src f])"
          proof -
            have "\<guillemotleft>?rf \<star> src f : (f \<star> src f) \<star> src f \<Rightarrow> f \<star> src f\<guillemotright>"
            proof -
              have "?rf \<star> src f = R ?rf"
                using assms rf_in_hom src_def trg_def arr_char rf.arrow_of_spans_axioms
                      f.arrow_of_spans_axioms
                by simp
              moreover have "\<guillemotleft>R ?rf : (f \<star> src f) \<star> src f \<Rightarrow> f \<star> src f\<guillemotright>"
                using rf_in_hom R.preserves_hom [of ?rf "f \<star> src f" f] by simp
              ultimately show ?thesis by auto
            qed
            thus ?thesis by auto
          qed
          show "Chn (?rf \<star> src f) = Chn ((f \<star> \<i>[src f]) \<bullet> \<a>[f, src f, src f])"
          proof -
            have "Chn (?rf \<star> src f) = \<langle>f_src_src.Prj\<^sub>1\<^sub>1 \<lbrakk>f.leg0, src.leg1\<rbrakk> f_src_src.Prj\<^sub>0\<^sub>1\<rangle>"
            proof -
              have "Chn (?rf \<star> src f) =
                    \<langle>f_src_src.Prj\<^sub>1\<^sub>1 \<lbrakk>f.leg0, src.leg1\<rbrakk> \<p>\<^sub>0[f_src.prj\<^sub>0, src.leg1]\<rangle>"
                using assms src_def trg_def hcomp_def arr_char ide_char
                      rf.arrow_of_spans_axioms src.identity_arrow_of_spans_axioms
                      chine_hcomp_arr_ide C.comp_cod_arr
                by (simp add: f.arrow_of_spans_axioms identity_arrow_of_spans_def)
              moreover have "\<p>\<^sub>0[f_src.prj\<^sub>0, src.leg1] = f_src_src.Prj\<^sub>0\<^sub>1"
              proof -
                have "src f = \<lparr>Chn = f.dsrc,
                               Dom = \<lparr>Leg0 = f.dsrc, Leg1 = f.dsrc\<rparr>,
                               Cod = \<lparr>Leg0 = f.dsrc, Leg1 = f.dsrc\<rparr>\<rparr>"
                  using assms src_def by simp
                thus ?thesis
                  by (simp add: C.comp_cod_arr C.pullback_commutes')
              qed
              ultimately show ?thesis by auto
            qed
            also have "... = Chn ((f \<star> \<i>[src f]) \<bullet> \<a>[f, src f, src f])"
            proof -
              have "Chn ((f \<star> \<i>[src f]) \<bullet> \<a>[f, src f, src f]) =
                    \<langle>f_src_src.Prj\<^sub>1 \<lbrakk>f.leg0, src.leg1\<rbrakk> f_src_src.Prj\<^sub>1\<^sub>0\<rangle> \<cdot> f_src_src.chine_assoc"
              proof -
                have "Chn ((f \<star> \<i>[src f]) \<bullet> \<a>[f, src f, src f]) =
                      Chn (f \<star> \<i>[src f]) \<cdot> Chn \<a>[f, src f, src f]"
                  using par vcomp_eq [of "f \<star> \<i>[src f]" "\<a>[f, src f, src f]"]
                  by simp
                moreover have "Chn (f \<star> \<i>[src f]) =
                               \<langle>f_src_src.Prj\<^sub>1 \<lbrakk>f.leg0, src.leg1\<rbrakk> f_src_src.Prj\<^sub>1\<^sub>0\<rangle>"
                proof -
                  have "\<i>[src f] = \<lparr>Chn = \<p>\<^sub>1[f.dsrc, f.dsrc],
                                   Dom = \<lparr>Leg0 = \<p>\<^sub>1[f.dsrc, f.dsrc], Leg1 = \<p>\<^sub>1[f.dsrc, f.dsrc]\<rparr>,
                                   Cod = \<lparr>Leg0 = f.dsrc, Leg1 = f.dsrc\<rparr>\<rparr>"
                    using unit_def src_def trg_def hcomp_def src.arrow_of_spans_axioms arr_char
                          f.arrow_of_spans_axioms C.comp_cod_arr
                    by simp
                  moreover have "arrow_of_spans C \<i>[src f]"
                    using assms arr_char [of "\<i>[src f]"] by simp
                  ultimately show ?thesis
                    using assms unit_def hcomp_def chine_hcomp_ide_arr
                          rf.arrow_of_spans_axioms src.arrow_of_spans_axioms
                          f.arrow_of_spans_axioms arr_char C.comp_cod_arr
                          src_def trg_def
                    by simp
                qed
                ultimately show ?thesis
                  using \<alpha>_ide by simp
              qed
              also have "... = \<langle>f_src_src.Prj\<^sub>1 \<cdot> f_src_src.chine_assoc
                                  \<lbrakk>f.leg0, src.leg1\<rbrakk>
                                f_src_src.Prj\<^sub>1\<^sub>0 \<cdot> f_src_src.chine_assoc\<rangle>"
              proof -
                have "C.commutative_square f.leg0 src.leg1 f_src_src.Prj\<^sub>1 f_src_src.Prj\<^sub>1\<^sub>0"
                proof
                  show "C.cospan f.leg0 src.leg1"
                    using f_src.legs_form_cospan(1) by auto
                  show "C.span f_src_src.Prj\<^sub>1 f_src_src.Prj\<^sub>1\<^sub>0"
                    using f_src_src.prj_in_hom(5) by auto
                  show "C.dom f.leg0 = C.cod f_src_src.Prj\<^sub>1"
                    by simp
                  show "f.leg0 \<cdot> f_src_src.Prj\<^sub>1 = src.leg1 \<cdot> f_src_src.Prj\<^sub>1\<^sub>0"
                    using C.pullback_commutes' \<open>C.span f_src_src.Prj\<^sub>1 f_src_src.Prj\<^sub>1\<^sub>0\<close>
                          C.comp_assoc
                    by auto
                qed
                moreover have "C.seq f_src_src.Prj\<^sub>1 f_src_src.chine_assoc"
                  by blast
                ultimately show ?thesis
                  using C.comp_tuple_arr by auto
              qed
              also have "... = \<langle>f_src_src.Prj\<^sub>1\<^sub>1 \<lbrakk>f.leg0, src.leg1\<rbrakk> f_src_src.Prj\<^sub>0\<^sub>1\<rangle>"
                by simp
              finally show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
        qed
      qed
      thus ?thesis by simp
    qed

    lemma lunit_ide_eq:
    assumes "ide f"
    shows "\<l>[f] = \<lparr>Chn = \<p>\<^sub>0[C.cod (Leg1 (Dom f)), Leg1 (Dom f)],
                   Dom = \<lparr>Leg0 = Leg0 (Dom f) \<cdot> \<p>\<^sub>0[C.cod (Leg1 (Dom f)), Leg1 (Dom f)],
                          Leg1 = \<p>\<^sub>1[C.cod (Leg1 (Dom f)), Leg1 (Dom f)]\<rparr>,
                   Cod = Cod f\<rparr>"
    proof -
      interpret f: identity_arrow_of_spans C f
        using assms ide_char' by auto
      interpret trg: identity_arrow_of_spans C \<open>trg f\<close>
        using assms ide_char' ide_trg by auto
      interpret trg_f: two_composable_identity_arrows_of_spans C prj0 prj1 \<open>trg f\<close> f
        using assms by (unfold_locales, simp)
      interpret trg_trg: two_composable_identity_arrows_of_spans C prj0 prj1 \<open>trg f\<close> \<open>trg f\<close>
        by (unfold_locales, simp)
      interpret trg_trg_f: three_composable_identity_arrows_of_spans C prj0 prj1 \<open>trg f\<close> \<open>trg f\<close> f
        ..

      let ?lf = "\<lparr>Chn = \<p>\<^sub>0[f.dtrg, f.leg1],
                  Dom = \<lparr>Leg0 = f.leg0 \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1], Leg1 = \<p>\<^sub>1[f.dtrg, f.leg1]\<rparr>,
                  Cod = Cod f\<rparr>"
      have "?lf = \<l>[f]"
      proof (intro lunit_eqI)
        show "ide f" by fact
        interpret lf: arrow_of_spans C ?lf
        proof -
          interpret dom_lf: span_in_category C
                              \<open>\<lparr>Leg0 = f.leg0 \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1], Leg1 = \<p>\<^sub>1[f.dtrg, f.leg1]\<rparr>\<close>
            by (unfold_locales, simp_all)
          show "arrow_of_spans C ?lf"
            using dom_lf.apex_def C.comp_cod_arr C.pullback_commutes [of f.dtrg f.leg1]
            apply unfold_locales by auto
        qed
        show lf_in_hom: "\<guillemotleft>?lf : trg f \<star> f \<Rightarrow> f\<guillemotright>"
        proof
          show "arr ?lf"
            using lf.arrow_of_spans_axioms arr_char by simp
          show "cod ?lf = f"
            using cod_char lf.arrow_of_spans_axioms arr_char by simp
          show "dom ?lf = trg f \<star> f"
            using dom_char lf.arrow_of_spans_axioms trg.arrow_of_spans_axioms arr_char hcomp_def
                  f.arrow_of_spans_axioms trg_f.composable chine_hcomp_ide_ide trg_def ide_char
                  C.comp_cod_arr lf.dom.apex_def
            by simp
        qed
        show "trg f \<star> ?lf = (\<i>[trg f] \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
        proof (intro arr_eqI)
          show par: "par (trg f \<star> ?lf) ((\<i>[trg f] \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[trg f, trg f, f])"
          proof -
            have "\<guillemotleft>trg f \<star> ?lf : trg f \<star> (trg f \<star> f) \<Rightarrow> trg f \<star> f\<guillemotright>"
            proof -
              have "trg f \<star> ?lf = L ?lf"
                using assms lf_in_hom src_def trg_def arr_char lf.arrow_of_spans_axioms
                      f.arrow_of_spans_axioms
                by simp
              moreover have "\<guillemotleft>L ?lf : trg f \<star> (trg f \<star> f) \<Rightarrow> trg f \<star> f\<guillemotright>"
                using lf_in_hom L.preserves_hom [of ?lf "trg f \<star> f" f] by simp
              ultimately show ?thesis by auto
            qed
            thus ?thesis by auto
          qed
          show "Chn (trg f \<star> ?lf) = Chn ((\<i>[trg f] \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[trg f, trg f, f])"
          proof -
            have "Chn (trg f \<star> ?lf) = \<langle>trg_trg_f.Prj\<^sub>1\<^sub>0 \<lbrakk>trg.leg0, f.leg1\<rbrakk> trg_trg_f.Prj\<^sub>0\<^sub>0\<rangle>"
            proof -
              have "Chn (trg f \<star> ?lf) =
                    \<langle>\<p>\<^sub>1[trg.leg0, trg_f.prj\<^sub>1] \<lbrakk>trg.leg0, f.leg1\<rbrakk> trg_trg_f.Prj\<^sub>0\<^sub>0\<rangle>"
                using assms src_def trg_def hcomp_def arr_char ide_char
                      lf.arrow_of_spans_axioms trg.identity_arrow_of_spans_axioms
                      chine_hcomp_ide_arr C.comp_cod_arr
                by (simp add: f.arrow_of_spans_axioms identity_arrow_of_spans_def)
              moreover have "\<p>\<^sub>1[trg.leg0, trg_f.prj\<^sub>1] = trg_trg_f.Prj\<^sub>1\<^sub>0"
              proof -
                have "trg f = \<lparr>Chn = f.dtrg,
                               Dom = \<lparr>Leg0 = f.dtrg, Leg1 = f.dtrg\<rparr>,
                               Cod = \<lparr>Leg0 = f.dtrg, Leg1 = f.dtrg\<rparr>\<rparr>"
                  using assms trg_def by simp
                thus ?thesis
                  apply (simp add: C.comp_cod_arr C.pullback_commutes')
                  by (metis C.comp_cod_arr C.pullback_commutes' select_convs(1) select_convs(2)
                      select_convs(3) f.cod_simps(3) lf.cod_trg_eq_dom_trg lf.dom.leg_simps(3)
                      span_data.select_convs(1) span_data.select_convs(2) trg.chine_eq_apex
                      trg_trg_f.cospan_\<nu>\<pi> trg_trg_f.prj_simps(10) trg_trg_f.prj_simps(16))
              qed
              ultimately show ?thesis by auto
            qed
            also have "... = Chn ((\<i>[trg f] \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[trg f, trg f, f])"
            proof -
              have "Chn ((\<i>[trg f] \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]) =
                    \<langle>trg_trg_f.Prj\<^sub>0\<^sub>1 \<lbrakk>trg.leg0, f.leg1\<rbrakk> trg_trg_f.Prj\<^sub>0\<rangle> \<cdot> trg_trg_f.chine_assoc'"
              proof -
                have "Chn ((\<i>[trg f] \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]) =
                      Chn (\<i>[trg f] \<star> f) \<cdot> Chn \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
                  using par vcomp_eq [of "\<i>[trg f] \<star> f" "\<a>\<^sup>-\<^sup>1[trg f, trg f, f]"]
                  by simp
                moreover have "Chn (\<i>[trg f] \<star> f) =
                               \<langle>trg_trg_f.Prj\<^sub>0\<^sub>1 \<lbrakk>trg.leg0, f.leg1\<rbrakk> trg_trg_f.Prj\<^sub>0\<rangle>"
                proof -
                  have "\<i>[trg f] = \<lparr>Chn = \<p>\<^sub>1[f.dtrg, f.dtrg],
                                   Dom = \<lparr>Leg0 = \<p>\<^sub>1[f.dtrg, f.dtrg], Leg1 = \<p>\<^sub>1[f.dtrg, f.dtrg]\<rparr>,
                                   Cod = \<lparr>Leg0 = f.dtrg, Leg1 = f.dtrg\<rparr>\<rparr>"
                    using unit_def src_def trg_def hcomp_def trg.arrow_of_spans_axioms arr_char
                          f.arrow_of_spans_axioms C.comp_cod_arr
                    by simp
                  moreover have "arrow_of_spans C \<i>[trg f]"
                    using assms arr_char [of "\<i>[trg f]"] by simp
                  ultimately show ?thesis
                    using assms unit_def hcomp_def chine_hcomp_arr_ide
                          lf.arrow_of_spans_axioms trg.arrow_of_spans_axioms
                          f.arrow_of_spans_axioms arr_char C.comp_cod_arr
                          src_def trg_def
                    by simp
                qed
                moreover have "Chn \<a>\<^sup>-\<^sup>1[trg f, trg f, f] = trg_trg_f.chine_assoc'"
                proof -
                  have "iso (\<alpha> (trg f, trg f, f))"
                  proof -
                    have "VVV.ide (trg f, trg f, f)"
                      using assms VVV.ide_char VVV.arr_char VV.ide_char VV.arr_char
                      by auto
                    thus ?thesis
                      using \<alpha>_def \<alpha>.components_are_iso [of "(trg f, trg f, f)"] by simp
                  qed
                  moreover have "C.inv trg_trg_f.chine_assoc = trg_trg_f.chine_assoc'"
                    using trg_trg_f.chine_assoc_inverse C.inv_is_inverse C.inverse_arrow_unique
                    by auto
                  ultimately show ?thesis
                    using assms by (simp add: \<a>'_def \<alpha>'_ide)
                qed
                ultimately show ?thesis
                  by simp
              qed
              also have "... = \<langle>trg_trg_f.Prj\<^sub>0\<^sub>1 \<cdot> trg_trg_f.chine_assoc'
                                  \<lbrakk>trg.leg0, f.leg1\<rbrakk>
                                trg_trg_f.Prj\<^sub>0 \<cdot> trg_trg_f.chine_assoc'\<rangle>"
              proof -
                have "C.commutative_square trg.leg0 f.leg1 trg_trg_f.Prj\<^sub>0\<^sub>1 trg_trg_f.Prj\<^sub>0"
                proof
                  show "C.cospan trg.leg0 f.leg1"
                    using trg_f.legs_form_cospan(1) by auto
                  show "C.span trg_trg_f.Prj\<^sub>0\<^sub>1 trg_trg_f.Prj\<^sub>0"
                    using trg_trg_f.prj_in_hom by auto
                  show "C.dom trg.leg0 = C.cod trg_trg_f.Prj\<^sub>0\<^sub>1"
                    by simp
                  show "trg.leg0 \<cdot> trg_trg_f.Prj\<^sub>0\<^sub>1 = f.leg1 \<cdot> trg_trg_f.Prj\<^sub>0"
                    by (metis C.comp_assoc C.prj0_simps_arr C.pullback_commutes'
                        \<open>C.span trg_trg_f.Prj\<^sub>0\<^sub>1 trg_trg_f.Prj\<^sub>0\<close>)
                qed
                moreover have "C.seq trg_trg_f.Prj\<^sub>0\<^sub>1 trg_trg_f.chine_assoc'"
                  by blast
                ultimately show ?thesis
                  using C.comp_tuple_arr [of trg.leg0 f.leg1 trg_trg_f.Prj\<^sub>0\<^sub>1 trg_trg_f.Prj\<^sub>0
                                             trg_trg_f.chine_assoc']
                  by auto
              qed
              also have "... = \<langle>trg_trg_f.Prj\<^sub>1\<^sub>0 \<lbrakk>trg.leg0, f.leg1\<rbrakk> trg_trg_f.Prj\<^sub>0\<^sub>0\<rangle>"
                by simp
              finally show ?thesis by simp
            qed
            finally show ?thesis by blast
          qed
        qed
      qed
      thus ?thesis by simp
    qed

    lemma runit'_ide_eq:
    assumes "ide f"
    shows "\<r>\<^sup>-\<^sup>1[f] = \<lparr>Chn = \<langle>Chn f \<lbrakk>Leg0 (Dom f), C.cod (Leg0 (Dom f))\<rbrakk> Leg0 (Dom f)\<rangle>,
                    Dom = Cod f,
                    Cod = \<lparr>Leg0 = \<p>\<^sub>0[Leg0 (Dom f), C.cod (Leg0 (Dom f))],
                           Leg1 = Leg1 (Dom f) \<cdot> \<p>\<^sub>1[Leg0 (Dom f), C.cod (Leg0 (Dom f))]\<rparr>\<rparr>"
    proof -
      interpret f: identity_arrow_of_spans C f
        using assms ide_char' by auto
      show "\<r>\<^sup>-\<^sup>1[f] = \<lparr>Chn = \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>, Dom = Cod f,
                     Cod = \<lparr>Leg0 = \<p>\<^sub>0[f.leg0, f.dsrc], Leg1 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc]\<rparr>\<rparr>"
      proof -
        have "C.inverse_arrows \<p>\<^sub>1[f.leg0, f.dsrc] \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
        proof
          show "C.ide (\<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle> \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc])"
          proof -
            have "\<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle> \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc] =
                  \<langle>f.chine \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc] \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0 \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc]\<rangle>"
              using assms C.comp_tuple_arr [of f.leg0 f.dsrc f.chine f.leg0 "\<p>\<^sub>1[f.leg0, f.dsrc]"]
                    C.comp_arr_dom C.comp_cod_arr
              by simp
            also have "... = \<langle>\<p>\<^sub>1[f.leg0, f.dsrc] \<lbrakk>f.leg0, f.dsrc\<rbrakk> \<p>\<^sub>0[f.leg0, f.dsrc]\<rangle>"
              using C.pullback_commutes [of f.leg0 f.dsrc] C.comp_cod_arr by auto
            also have "... = f.leg0 \<down>\<down> f.dsrc"
              by simp
            finally have "\<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle> \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc] = f.leg0 \<down>\<down> f.dsrc"
              by blast
            thus ?thesis by simp
          qed
          show "C.ide (\<p>\<^sub>1[f.leg0, f.dsrc] \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>)"
            using assms C.comp_arr_dom C.comp_cod_arr by auto
        qed
        hence "C.inv \<p>\<^sub>1[f.leg0, f.dsrc] = \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
          using C.inv_is_inverse C.inverse_arrow_unique by auto
        hence "\<r>\<^sup>-\<^sup>1[f] = \<lparr>Chn = \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>,
                        Dom = Cod \<r>[f], Cod = Dom \<r>[f]\<rparr>"
          using assms runit_ide_eq inv_eq [of "\<r>[f]"] iso_runit by simp
        thus ?thesis
          using assms runit_ide_eq by simp
      qed
    qed

    lemma lunit'_ide_eq:
    assumes "ide f"
    shows "\<l>\<^sup>-\<^sup>1[f] = \<lparr>Chn = \<langle>Leg1 (Dom f) \<lbrakk>C.cod (Leg1 (Dom f)), Leg1 (Dom f)\<rbrakk> Chn f\<rangle>,
                    Dom = Cod f,
                    Cod = \<lparr>Leg0 = Leg0 (Dom f) \<cdot> \<p>\<^sub>0[C.cod (Leg1 (Dom f)), Leg1 (Dom f)],
                           Leg1 = \<p>\<^sub>1[C.cod (Leg1 (Dom f)), Leg1 (Dom f)]\<rparr>\<rparr>"
    proof -
      interpret f: identity_arrow_of_spans C f
        using assms ide_char' by auto
      show "\<l>\<^sup>-\<^sup>1[f] = \<lparr>Chn = \<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle>, Dom = Cod f,
                     Cod = \<lparr>Leg0 = f.leg0 \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1], Leg1 = \<p>\<^sub>1[f.dtrg, f.leg1]\<rparr>\<rparr>"
      proof -
        have "C.inverse_arrows \<p>\<^sub>0[f.dtrg, f.leg1] \<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle>"
        proof
          show "C.ide (\<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle> \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1])"
          proof -
            have "\<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle> \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1] =
                  \<langle>f.leg1 \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1] \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1]\<rangle>"
              using assms C.comp_tuple_arr C.comp_arr_dom C.comp_cod_arr
              by simp
            also have "... = \<langle>\<p>\<^sub>1[f.dtrg, f.leg1] \<lbrakk>f.dtrg, f.leg1\<rbrakk> \<p>\<^sub>0[f.dtrg, f.leg1]\<rangle>"
            proof -
              have "f.leg1 \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1] = \<p>\<^sub>1[f.dtrg, f.leg1]"
                using C.pullback_commutes [of f.dtrg f.leg1] C.comp_cod_arr by auto
              thus ?thesis
                using C.comp_cod_arr by simp
            qed
            also have "... = f.dtrg \<down>\<down> f.leg1"
              by simp
            finally have "\<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle> \<cdot> \<p>\<^sub>0[f.dtrg, f.leg1] = f.dtrg \<down>\<down> f.leg1"
              by blast
            thus ?thesis by simp
          qed
          show "C.ide (\<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> \<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle>)"
            using assms C.comp_arr_dom C.comp_cod_arr by auto
        qed
        hence "C.inv \<p>\<^sub>0[f.dtrg, f.leg1] = \<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle>"
          using C.inv_is_inverse C.inverse_arrow_unique by auto
        hence "\<l>\<^sup>-\<^sup>1[f] = \<lparr>Chn = \<langle>f.leg1 \<lbrakk>f.dtrg, f.leg1\<rbrakk> f.chine\<rangle>,
                        Dom = Cod \<l>[f], Cod = Dom \<l>[f]\<rparr>"
          using assms lunit_ide_eq inv_eq [of "\<l>[f]"] iso_lunit by simp
        thus ?thesis
          using assms lunit_ide_eq by simp
      qed
    qed

  end

  locale adjunction_data_in_span_bicategory =
     span_bicategory C prj0 prj1 +
     adjunction_data_in_bicategory vcomp hcomp assoc unit src trg f g \<eta> \<epsilon>
  for C :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"         (infixr "\<cdot>" 55)
  and prj0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"      ("\<p>\<^sub>0[_, _]")
  and prj1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"      ("\<p>\<^sub>1[_, _]")
  and f :: "'a arrow_of_spans_data"
  and g :: "'a arrow_of_spans_data"
  and \<eta> :: "'a arrow_of_spans_data"
  and \<epsilon> :: "'a arrow_of_spans_data"
  begin

    interpretation f: identity_arrow_of_spans C f
      using ide_char' [of f] by auto
    interpretation g: identity_arrow_of_spans C g
      using ide_char' [of g] by auto

    interpretation gf: two_composable_identity_arrows_of_spans C prj0 prj1 g f
      using antipar by (unfold_locales, auto)
    interpretation fg: two_composable_identity_arrows_of_spans C prj0 prj1 f g
      using antipar by (unfold_locales, auto)

    interpretation fgf: three_composable_identity_arrows_of_spans C prj0 prj1 f g f ..
    interpretation gfg: three_composable_identity_arrows_of_spans C prj0 prj1 g f g ..

    interpretation \<eta>: arrow_of_spans C \<eta>
      using arr_char unit_in_hom by auto
    interpretation \<epsilon>: arrow_of_spans C \<epsilon>
      using arr_char counit_in_hom by auto

    lemma chine_unit_in_hom:
    shows "\<guillemotleft>\<eta>.chine : f.dsrc \<rightarrow>\<^sub>C g.leg0 \<down>\<down> f.leg1\<guillemotright>"
    proof -
      have "\<guillemotleft>\<eta>.chine : \<eta>.dom.apex \<rightarrow>\<^sub>C \<eta>.cod.apex\<guillemotright>"
        using \<eta>.chine_in_hom by simp
      moreover have "\<eta>.dom.apex = f.dsrc"
        using \<eta>.dom.apex_def dom_char unit_simps src_def by auto
      moreover have "\<eta>.cod.apex = g.leg0 \<down>\<down> f.leg1"
      proof -
        have "\<eta>.cod.apex = C.dom \<eta>.cod.leg0" by simp
        also have "... = C.dom (f.leg0 \<cdot> \<p>\<^sub>0[g.leg0, f.leg1])"
          using cod_char unit_simps hcomp_def gf.composable by simp
        also have "... = g.leg0 \<down>\<down> f.leg1"
          using fgf.cospan_\<nu>\<pi> by simp
        finally show ?thesis by blast
      qed
      ultimately show ?thesis by simp
    qed

    lemma chine_counit_in_hom:
    shows "\<guillemotleft>\<epsilon>.chine : f.leg0 \<down>\<down> g.leg1 \<rightarrow>\<^sub>C f.dtrg\<guillemotright>"
    proof -
      have "\<guillemotleft>\<epsilon>.chine : \<epsilon>.dom.apex \<rightarrow>\<^sub>C \<epsilon>.cod.apex\<guillemotright>"
        using \<epsilon>.chine_in_hom by simp
      moreover have "\<epsilon>.cod.apex = f.dtrg"
        using \<epsilon>.cod.apex_def cod_char counit_simps trg_def gf.composable by auto
      moreover have "\<epsilon>.dom.apex = f.leg0 \<down>\<down> g.leg1"
      proof -
        have "\<epsilon>.dom.apex = C.dom \<epsilon>.dom.leg0" by simp
        also have "... = C.dom (g.leg0 \<cdot> fg.prj\<^sub>0)"
          using dom_char counit_simps hcomp_def fg.composable by simp
        also have "... = f.leg0 \<down>\<down> g.leg1"
          using fg.prj_in_hom(2) by auto
        finally show ?thesis by blast
      qed
      ultimately show ?thesis by simp
    qed

    lemma \<eta>_leg_simps:
    shows "\<eta>.dom.leg0 = f.dsrc" and "\<eta>.dom.leg1 = f.dsrc"
    and "\<eta>.cod.leg0 = gf.leg0" and "\<eta>.cod.leg1 = gf.leg1"
    proof -
      show "\<eta>.dom.leg0 = f.dsrc"
        using dom_char unit_simps(2) src_def by auto
      show "\<eta>.dom.leg1 = f.dsrc"
        using dom_char unit_simps(2) src_def by auto
      show "\<eta>.cod.leg0 = gf.leg0"
        using cod_char unit_simps(1,3)
        by (metis (no_types, lifting) arrow_of_spans_data.select_convs(2))
      show "\<eta>.cod.leg1 = gf.leg1"
        using cod_char unit_simps(1,3)
        by (metis (no_types, lifting) arrow_of_spans_data.select_convs(2))
    qed

    lemma \<epsilon>_leg_simps:
    shows "\<epsilon>.cod.leg0 = f.dtrg" and "\<epsilon>.cod.leg1 = f.dtrg"
    and "\<epsilon>.dom.leg0 = fg.leg0" and "\<epsilon>.dom.leg1 = fg.leg1"
    proof -
      show "\<epsilon>.cod.leg0 = f.dtrg"
        using cod_char counit_simps(3) trg_def gf.composable by auto
      show "\<epsilon>.cod.leg1 = f.dtrg"
        using cod_char counit_simps(3) trg_def gf.composable by auto
      show "\<epsilon>.dom.leg0 = fg.leg0"
        using dom_char counit_simps hcomp_def fg.composable by simp
      show "\<epsilon>.dom.leg1 = fg.leg1"
        using dom_char counit_simps hcomp_def fg.composable by simp
    qed

    lemma Chn_triangle_eq:
    shows "Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) = gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> f.leg0"
    and "Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) = gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> g.leg1"
    proof -
      have "Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) =
            \<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> chine_hcomp \<epsilon> f \<cdot> fgf.chine_assoc' \<cdot> chine_hcomp f \<eta> \<cdot>
              \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
      proof -
        have "Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) =
              Chn \<l>[f] \<cdot> Chn (\<epsilon> \<star> f) \<cdot> Chn \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> Chn (f \<star> \<eta>) \<cdot> Chn \<r>\<^sup>-\<^sup>1[f]"
          using antipar Chn_vcomp by auto
        also have "... = \<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> chine_hcomp \<epsilon> f \<cdot> fgf.chine_assoc' \<cdot>
                           chine_hcomp f \<eta> \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
          using \<alpha>_ide fg.composable gf.composable fgf.chine_assoc_inverse
                C.inverse_unique inv_eq iso_assoc lunit_ide_eq hcomp_def [of \<epsilon> f]
                gf.composable hcomp_def [of f \<eta>] fg.composable runit'_ide_eq
          by simp
        finally show ?thesis by blast
      qed
      moreover have "C.arr (Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]))"
      proof -
        have "\<guillemotleft>\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f] : f \<Rightarrow> f\<guillemotright>"
          using ide_left ide_right antipar triangle_in_hom(1) by blast
        thus ?thesis
          using Chn_in_hom by blast
      qed
      ultimately have *: "C.arr (\<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> chine_hcomp \<epsilon> f \<cdot> fgf.chine_assoc' \<cdot>
                                   chine_hcomp f \<eta> \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>)"
        by simp

      have "Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) =
               \<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> chine_hcomp \<epsilon> f \<cdot> fgf.chine_assoc' \<cdot> chine_hcomp f \<eta> \<cdot>
                 \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
        by fact
      also have
        1: "... = fgf.Prj\<^sub>0 \<cdot> fgf.chine_assoc' \<cdot> chine_hcomp f \<eta> \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
      proof -
        have "\<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> chine_hcomp \<epsilon> f = \<p>\<^sub>0[\<epsilon>.dom.leg0, f.leg1]"
        proof -
          have "chine_hcomp \<epsilon> f = \<langle>\<epsilon>.chine \<cdot> \<p>\<^sub>1[\<epsilon>.dom.leg0, f.leg1]
                                   \<lbrakk>\<epsilon>.cod.leg0, f.leg1\<rbrakk>
                                 \<p>\<^sub>0[\<epsilon>.dom.leg0, f.leg1]\<rangle>"
            using chine_hcomp_arr_ide gf.composable by simp
          moreover have 1: "f.dtrg = \<epsilon>.cod.leg0"
            using cod_char trg_def counit_simps gf.composable by simp
          moreover have "C.commutative_square f.dtrg f.leg1
                           (\<epsilon>.chine \<cdot> \<p>\<^sub>1[\<epsilon>.dom.leg0, f.leg1]) \<p>\<^sub>0[\<epsilon>.dom.leg0, f.leg1]"
          proof
            show "C.cospan f.dtrg f.leg1" by simp
            show 2: "C.span (\<epsilon>.chine \<cdot> \<p>\<^sub>1[\<epsilon>.dom.leg0, f.leg1]) \<p>\<^sub>0[\<epsilon>.dom.leg0, f.leg1]"
              using 1 \<open>C.cospan f.dtrg f.leg1\<close> chine_counit_in_hom by simp
            show 3: "C.dom f.dtrg = C.cod (\<epsilon>.chine \<cdot> \<p>\<^sub>1[\<epsilon>.dom.leg0, f.leg1])"
              using 1 2 dom_char counit_simps by simp
            show "f.dtrg \<cdot> \<epsilon>.chine \<cdot> \<p>\<^sub>1[\<epsilon>.dom.leg0, f.leg1] = f.leg1 \<cdot> \<p>\<^sub>0[\<epsilon>.dom.leg0, f.leg1]"
              using 1 2 3 C.comp_cod_arr dom_char counit_simps C.pullback_commutes'
              by (metis (no_types, lifting) C.prj1_simps_arr C.seqE \<epsilon>.leg0_commutes)
          qed
          ultimately show ?thesis by simp
        qed
        also have "... = fgf.Prj\<^sub>0"
          using dom_char counit_simps hcomp_def fg.composable by simp
        finally have "\<p>\<^sub>0[f.dtrg, f.leg1] \<cdot> chine_hcomp \<epsilon> f = fgf.Prj\<^sub>0"
          by simp
        moreover have "C.seq \<p>\<^sub>0[f.dtrg, f.leg1] (chine_hcomp \<epsilon> f)"
          using chine_hcomp_props(1) fg.composable calculation(1) fgf.prj_in_hom(3)
          by auto
        moreover have "C.seq (chine_hcomp \<epsilon> f)
                             (fgf.chine_assoc' \<cdot> chine_hcomp f \<eta> \<cdot>
                                \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>)"
          using chine_hcomp_props(1) fg.composable by (metis "*" C.seqE)
        ultimately show ?thesis
          using C.comp_reduce by simp
      qed
      also have 3: "... = fgf.Prj\<^sub>0\<^sub>0 \<cdot> chine_hcomp f \<eta> \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
        using C.comp_reduce [of fgf.Prj\<^sub>0 fgf.chine_assoc' fgf.Prj\<^sub>0\<^sub>0
                                "chine_hcomp f \<eta> \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"]
              * fgf.prj_chine_assoc'(3)
        by blast
      also have 4: "... = (gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]) \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
      proof -
        have "fgf.Prj\<^sub>0\<^sub>0 \<cdot> chine_hcomp f \<eta> = gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]"
        proof -
          have "fgf.Prj\<^sub>0\<^sub>0 \<cdot> chine_hcomp f \<eta> =
                (gf.prj\<^sub>0 \<cdot> \<p>\<^sub>0[f.leg0, gf.leg1]) \<cdot>
                   \<langle>\<p>\<^sub>1[f.leg0, f.dsrc] \<lbrakk>f.leg0, gf.leg1\<rbrakk> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]\<rangle>"
            using hcomp_def fg.composable gf.composable chine_hcomp_ide_arr \<eta>_leg_simps by auto
          also have "... = gf.prj\<^sub>0 \<cdot> \<p>\<^sub>0[f.leg0, gf.leg1] \<cdot>
                             \<langle>\<p>\<^sub>1[f.leg0, f.dsrc] \<lbrakk>f.leg0, gf.leg1\<rbrakk> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]\<rangle>"
            using C.comp_assoc by simp
          also have "... = gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]"
          proof -
            have "C.commutative_square f.leg0 gf.leg1 \<p>\<^sub>1[f.leg0, f.dsrc] (\<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc])"
            proof
              show "C.cospan f.leg0 gf.leg1"
                using hcomp_def gf.composable fgf.prj_in_hom(5) by auto
              show "C.span \<p>\<^sub>1[f.leg0, f.dsrc] (\<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc])"
                using chine_unit_in_hom by auto
              show "C.dom f.leg0 = C.cod \<p>\<^sub>1[f.leg0, f.dsrc]" by simp
              show "f.leg0 \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc] = gf.leg1 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]"
              proof -
                have "f.leg0 \<cdot> \<p>\<^sub>1[f.leg0, f.dsrc] = \<p>\<^sub>0[f.leg0, f.dsrc]"
                  using C.comp_cod_arr C.pullback_commutes [of f.leg0 f.dsrc] by auto
                also have "... = gf.leg1 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc]"
                  using unit_simps cod_char hcomp_def gf.composable \<eta>.leg1_commutes \<eta>_leg_simps
                        C.comp_cod_arr chine_unit_in_hom C.comp_reduce
                  by auto
                finally show ?thesis by blast
              qed
            qed
            thus ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        moreover have "C.seq fgf.Prj\<^sub>0\<^sub>0 (chine_hcomp f \<eta>)"
          using chine_hcomp_props(1) by (metis "*" 1 3 C.match_2 C.seqE)
        moreover have "C.seq (chine_hcomp f \<eta>) \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
          using chine_hcomp_props(1) by (metis "*" C.seqE)
        ultimately show ?thesis
          using C.comp_reduce by simp
      qed
      also have "... = gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>0[f.leg0, f.dsrc] \<cdot> \<langle>f.chine \<lbrakk>f.leg0, f.dsrc\<rbrakk> f.leg0\<rangle>"
        using C.comp_assoc by simp
      also have "... = gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> f.leg0"
        using C.comp_cod_arr f.leg0_commutes by simp
      finally show "Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) = gf.prj\<^sub>0 \<cdot> \<eta>.chine \<cdot> f.leg0"
        by simp

      have "Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) =
            \<p>\<^sub>1[g.leg0, g.dsrc] \<cdot> chine_hcomp g \<epsilon> \<cdot> gfg.chine_assoc \<cdot> chine_hcomp \<eta> g \<cdot>
              \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
      proof -
        have "Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) =
              Chn \<r>[g] \<cdot> Chn (g \<star> \<epsilon>) \<cdot> Chn \<a>[g, f, g] \<cdot> Chn (\<eta> \<star> g) \<cdot> Chn \<l>\<^sup>-\<^sup>1[g]"
          using antipar Chn_vcomp by auto
        also have "... = \<p>\<^sub>1[g.leg0, g.dsrc] \<cdot> chine_hcomp g \<epsilon> \<cdot> gfg.chine_assoc \<cdot> chine_hcomp \<eta> g \<cdot>
                           \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
          using \<alpha>_ide gf.composable fg.composable runit_ide_eq hcomp_def [of g \<epsilon>]
                fg.composable hcomp_def [of \<eta> g] gf.composable lunit'_ide_eq
          by simp
        finally show ?thesis by blast
      qed
      moreover have "C.arr (Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]))"
      proof -
        have "\<guillemotleft>\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g] : g \<Rightarrow> g\<guillemotright>"
          using ide_left ide_right antipar triangle_in_hom(2) by blast
        thus ?thesis
          using Chn_in_hom by blast
      qed
      ultimately have *: "C.arr (\<p>\<^sub>1[g.leg0, g.dsrc] \<cdot> chine_hcomp g \<epsilon> \<cdot> gfg.chine_assoc \<cdot> chine_hcomp \<eta> g \<cdot>
                                   \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>)"
        by simp

      have "Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) =
            \<p>\<^sub>1[g.leg0, g.dsrc] \<cdot> chine_hcomp g \<epsilon> \<cdot> gfg.chine_assoc \<cdot> chine_hcomp \<eta> g \<cdot>
              \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
        by fact
      also have
        1: "... = gfg.Prj\<^sub>1 \<cdot> gfg.chine_assoc \<cdot> chine_hcomp \<eta> g \<cdot> \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
      proof -
        have "\<p>\<^sub>1[g.leg0, g.dsrc] \<cdot> chine_hcomp g \<epsilon> = \<p>\<^sub>1[g.leg0, \<epsilon>.dom.leg1]"
        proof -
          have "chine_hcomp g \<epsilon> = \<langle>\<p>\<^sub>1[g.leg0, \<epsilon>.dom.leg1]
                                   \<lbrakk>g.leg0, \<epsilon>.cod.leg1\<rbrakk>
                                 \<epsilon>.chine \<cdot> \<p>\<^sub>0[g.leg0, \<epsilon>.dom.leg1]\<rangle>"
            using chine_hcomp_ide_arr gf.composable by simp
          moreover have 1: "g.dsrc = \<epsilon>.cod.leg1"
            using gfg.cospan_\<mu>\<nu> by (simp add: \<epsilon>_leg_simps(2))
          moreover have "C.commutative_square g.leg0 g.dsrc \<p>\<^sub>1[g.leg0, \<epsilon>.dom.leg1]
                             (\<epsilon>.chine \<cdot> \<p>\<^sub>0[g.leg0, \<epsilon>.dom.leg1])"
          proof
            show "C.cospan g.leg0 g.dsrc" by simp
            show 2: "C.span \<p>\<^sub>1[g.leg0, \<epsilon>.dom.leg1] (\<epsilon>.chine \<cdot> \<p>\<^sub>0[g.leg0, \<epsilon>.dom.leg1])"
              using 1 \<open>C.cospan g.leg0 g.dsrc\<close> chine_counit_in_hom by simp
            show 3: "C.dom g.leg0 = C.cod \<p>\<^sub>1[g.leg0, \<epsilon>.dom.leg1]"
              using 1 2 dom_char counit_simps by simp
            show "g.leg0 \<cdot> \<p>\<^sub>1[g.leg0, \<epsilon>.dom.leg1] = g.dsrc \<cdot> \<epsilon>.chine \<cdot> \<p>\<^sub>0[g.leg0, \<epsilon>.dom.leg1]"
              using 1 2 3 C.comp_cod_arr dom_char counit_simps C.pullback_commutes'
              by (metis (no_types, lifting) C.cod_comp C.prj0_simps_arr C.seqE \<epsilon>.leg1_commutes)
          qed
          ultimately show ?thesis by simp
        qed
        also have "... = gfg.Prj\<^sub>1"
          using dom_char counit_simps hcomp_def fg.composable by simp
        finally have "\<p>\<^sub>1[g.leg0, g.dsrc] \<cdot> chine_hcomp g \<epsilon> = gfg.Prj\<^sub>1"
          by simp
        moreover have "C.seq \<p>\<^sub>1[g.leg0, g.dsrc] (chine_hcomp g \<epsilon>)"
          using chine_hcomp_props(1) [of g \<epsilon>] gf.composable calculation gfg.prj_in_hom(4)
          by auto
        moreover have "C.seq (chine_hcomp g \<epsilon>)
                             (gfg.chine_assoc \<cdot> chine_hcomp \<eta> g \<cdot> \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>)"
          using chine_hcomp_props(1) gf.composable * by (metis C.seqE)
        ultimately show ?thesis
          using C.comp_reduce by simp
      qed
      also have 3: "... = gfg.Prj\<^sub>1\<^sub>1 \<cdot> chine_hcomp \<eta> g \<cdot> \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
        using C.comp_reduce [of gfg.Prj\<^sub>1 gfg.chine_assoc gfg.Prj\<^sub>1\<^sub>1
                                "chine_hcomp \<eta> g \<cdot> \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"]
              * gfg.prj_chine_assoc(1)
        by blast
      also have 4: "... = (gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]) \<cdot> \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
      proof -
        have "gfg.Prj\<^sub>1\<^sub>1 \<cdot> chine_hcomp \<eta> g = gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]"
        proof -
          have "gfg.Prj\<^sub>1\<^sub>1 \<cdot> chine_hcomp \<eta> g =
                (gf.prj\<^sub>1 \<cdot> \<p>\<^sub>1[gf.leg0, g.leg1]) \<cdot>
                   \<langle>\<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1] \<lbrakk>gf.leg0, g.leg1\<rbrakk> \<p>\<^sub>0[g.dtrg, g.leg1]\<rangle>"
            using hcomp_def fg.composable gf.composable chine_hcomp_arr_ide trg_def unit_simps(5)
                  \<eta>_leg_simps
            by auto
          also have "... = gf.prj\<^sub>1 \<cdot> \<p>\<^sub>1[gf.leg0, g.leg1] \<cdot>
                             \<langle>\<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1] \<lbrakk>gf.leg0, g.leg1\<rbrakk> \<p>\<^sub>0[g.dtrg, g.leg1]\<rangle>"
            using C.comp_assoc by simp
          also have "... = gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]"
          proof -
            have "C.commutative_square gf.leg0 g.leg1 (\<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]) \<p>\<^sub>0[g.dtrg, g.leg1]"
            proof
              show "C.cospan gf.leg0 g.leg1"
                using hcomp_def [of g f] gf.composable gfg.prj_in_hom(3) by auto
              show "C.span (\<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]) \<p>\<^sub>0[g.dtrg, g.leg1]"
                using chine_unit_in_hom fg.composable src_def trg_def by auto
              show "C.dom gf.leg0 = C.cod (\<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1])"
                using chine_unit_in_hom \<eta>_leg_simps
                by (simp add: \<eta>.cod.apex_def
                    \<open>C.span (\<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]) \<p>\<^sub>0[g.dtrg, g.leg1]\<close>)
              show "gf.leg0 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1] = g.leg1 \<cdot> \<p>\<^sub>0[g.dtrg, g.leg1]"
              proof -
                have "g.leg1 \<cdot> \<p>\<^sub>0[g.dtrg, g.leg1] = \<p>\<^sub>1[g.dtrg, g.leg1]"
                  using C.comp_cod_arr C.pullback_commutes [of g.dtrg g.leg1] by auto
                also have "... = gf.leg0 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1]"
                proof -
                  have "gf.leg0 \<cdot> \<eta>.chine = g.dtrg"
                    using unit_simps cod_char hcomp_def gf.composable \<eta>.leg0_commutes
                          dom_char trg_def fg.composable
                    by simp
                  moreover have "C.seq \<eta>.chine \<p>\<^sub>1[g.dtrg, g.leg1]"
                    using chine_unit_in_hom fg.composable src_def trg_def by auto
                  ultimately show ?thesis
                    using C.comp_cod_arr C.comp_reduce by auto
                qed
                finally show ?thesis by simp
              qed
            qed
            thus ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        moreover have "C.seq gfg.Prj\<^sub>1\<^sub>1 (chine_hcomp \<eta> g)"
          using chine_hcomp_props(1) [of \<eta> g] by (metis "*" 1 "3" C.match_2 C.seqE)
        moreover have "C.seq (chine_hcomp \<eta> g) \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
          using chine_hcomp_props(1) by (metis "*" C.seqE)
        ultimately show ?thesis
          using C.comp_reduce by simp
      qed
      also have "... = gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> \<p>\<^sub>1[g.dtrg, g.leg1] \<cdot> \<langle>g.leg1 \<lbrakk>g.dtrg, g.leg1\<rbrakk> g.chine\<rangle>"
        using C.comp_assoc by simp
      also have "... = gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> g.leg1"
        using C.comp_cod_arr g.leg1_commutes by simp
      finally show "Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) = gf.prj\<^sub>1 \<cdot> \<eta>.chine \<cdot> g.leg1"
        by simp
    qed

  end

  subsection "Maps in Span(C)"

  text \<open>
    In this section, we chararacterize the maps (\emph{i.e}~the left adjoints)
    in a span bicategory.  This is Proposition 2 of \cite{carboni-et-al}.
  \<close>

  context span_bicategory
  begin

    abbreviation adjoint_of_map
    where "adjoint_of_map f \<equiv> \<lparr>Chn = Chn f,
                               Dom = \<lparr>Leg0 = Leg1 (Dom f), Leg1 = Leg0 (Dom f)\<rparr>,
                               Cod = \<lparr>Leg0 = Leg1 (Dom f), Leg1 = Leg0 (Dom f)\<rparr>\<rparr>"

    abbreviation unit_for_map
    where "unit_for_map f \<equiv> \<lparr>Chn = \<langle>C.inv (Leg0 (Dom f))
                                      \<lbrakk>Leg1 (Dom f), Leg1 (Dom f)\<rbrakk>
                                    C.inv (Leg0 (Dom f))\<rangle>,
                             Dom = Dom (src f),
                             Cod = Dom (hcomp (adjoint_of_map f) f)\<rparr>"

    abbreviation counit_for_map
    where "counit_for_map f \<equiv> \<lparr>Chn = Leg1 (Dom f) \<cdot> \<p>\<^sub>0[Leg0 (Dom f), Leg0 (Dom f)],
                               Dom = Dom (hcomp f (adjoint_of_map f)),
                               Cod = Dom (trg f)\<rparr>"

    lemma is_left_adjoint_char:
    shows "is_left_adjoint f \<longleftrightarrow> ide f \<and> C.iso (Leg0 (Dom f))"
    and "is_left_adjoint f \<Longrightarrow>
           adjunction_in_bicategory vcomp hcomp assoc unit src trg f
              (adjoint_of_map f) (unit_for_map f) (counit_for_map f)"
    proof
      show 1: "is_left_adjoint f \<Longrightarrow> ide f \<and> C.iso (Leg0 (Dom f))"
      proof
        assume f: "is_left_adjoint f"
        obtain g \<eta> \<epsilon> where adj: "adjunction_in_bicategory vcomp hcomp assoc unit src trg f g \<eta> \<epsilon>"
          using f adjoint_pair_def by blast
        interpret adjunction_in_bicategory vcomp hcomp assoc unit src trg f g \<eta> \<epsilon>
          using adj by auto
        show "ide f" by simp

        interpret f: identity_arrow_of_spans C f
          using ide_char' [of f] by auto
        interpret g: identity_arrow_of_spans C g
          using ide_char' [of g] by auto

        interpret gf: two_composable_identity_arrows_of_spans C prj0 prj1 g f
          using antipar by (unfold_locales, auto)
        interpret fg: two_composable_identity_arrows_of_spans C prj0 prj1 f g
          using antipar by (unfold_locales, auto)

        interpret fgf: three_composable_identity_arrows_of_spans C prj0 prj1 f g f ..

        interpret src_f: arrow_of_spans C \<open>src f\<close>
          using arr_char gf.are_arrows(2) by blast
        interpret src_f: identity_arrow_of_spans C \<open>src f\<close>
          using ide_char ide_src src_def by (unfold_locales, simp)

        interpret \<eta>: arrow_of_spans C \<eta>
          using arr_char unit_in_hom by auto
        interpret \<epsilon>: arrow_of_spans C \<epsilon>
          using arr_char counit_in_hom by auto

        interpret adjunction_data_in_span_bicategory C prj0 prj1 f g \<eta> \<epsilon>
          ..
        show "C.iso f.leg0"
        proof -
          have "C.section f.leg0"
          proof -
            have "f.chine = (gf.prj\<^sub>0 \<cdot> \<eta>.chine) \<cdot> f.leg0"
              using triangle_left' Chn_triangle_eq(1) C.comp_assoc by simp
            thus ?thesis
              using f.chine_is_identity by auto
          qed
          moreover have "C.retraction f.leg0"
            using C.retractionI [of f.leg0 "gf.prj\<^sub>0 \<cdot> \<eta>.chine"] hcomp_def C.comp_assoc
                  \<eta>.leg0_commutes gf.leg0_composite \<eta>_leg_simps
            by auto
          ultimately show ?thesis
            by (simp add: C.iso_iff_section_and_retraction)
        qed
      qed
      have 2: "ide f \<and> C.iso (Leg0 (Dom f)) \<Longrightarrow>
                 adjunction_in_bicategory vcomp hcomp assoc unit src trg f
                   (adjoint_of_map f) (unit_for_map f) (counit_for_map f)"

        text \<open>
          The right adjoint \<open>g\<close> is obtained by exchanging the legs of \<open>f\<close>.
          The unit is obtained by tupling \<open>C.inv f.leg0\<close> with itself,
          via the pullback of \<open>f.leg1\<close> with itself.
          The counit is given by the legs of \<open>f \<star> g\<close>, which are equal,
          because the two legs of a pullback of the isomorphism \<open>f.leg0\<close>
          with itself must be equal.
          It then remains to verify the triangle identities.
      \<close>

      proof -
        assume f: "ide f \<and> C.iso (Leg0 (Dom f))"
        interpret f: identity_arrow_of_spans C f
          using f ide_char' by auto
        interpret Dom_src: span_in_category C \<open>\<lparr>Leg0 = f.dsrc, Leg1 = f.dsrc\<rparr>\<close>
          using f by (unfold_locales, auto)
        interpret Dom_trg: span_in_category C \<open>\<lparr>Leg0 = f.dtrg, Leg1 = f.dtrg\<rparr>\<close>
          using f by (unfold_locales, auto)

        define g where "g = adjoint_of_map f"
        interpret Dom_g: span_in_category C \<open>\<lparr>Leg0 = f.leg1, Leg1 = f.leg0\<rparr>\<close>
          by (unfold_locales, simp)
        interpret g: arrow_of_spans C g
          unfolding g_def
          using Dom_g.apex_def f.leg0_commutes f.leg1_commutes
          by (unfold_locales, auto)
        interpret g: identity_arrow_of_spans C g
          using g_def
          by (unfold_locales, auto)
        have ide_g: "ide g"
          using f ide_char g.arrow_of_spans_axioms by simp

        interpret fg: two_composable_arrows_of_spans C prj0 prj1 f g
          apply unfold_locales
          using g_def src_def trg_def arr_char f.arrow_of_spans_axioms g.arrow_of_spans_axioms
          by auto
        interpret fg: two_composable_identity_arrows_of_spans C prj0 prj1 f g
          ..
        interpret gf: two_composable_arrows_of_spans C prj0 prj1 g f
          apply unfold_locales
          using g_def src_def trg_def arr_char f.arrow_of_spans_axioms g.arrow_of_spans_axioms
          by auto
        interpret gf: two_composable_identity_arrows_of_spans C prj0 prj1 g f
          ..
        have hcomp_fg_eq: "hcomp f g = \<lparr>Chn = f.leg0 \<down>\<down> f.leg0,
                                         Dom = \<lparr>Leg0 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.leg0],
                                                Leg1 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.leg0]\<rparr>,
                                         Cod = \<lparr>Leg0 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.leg0],
                                                Leg1 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.leg0]\<rparr>\<rparr>"
          using f g_def hcomp_def fg.composable src_def trg_def arr_char f.arrow_of_spans_axioms
                g.arrow_of_spans_axioms chine_hcomp_def gf.are_identities(1) chine_hcomp_ide_ide
                C.pullback_iso_self
          by auto
        have hcomp_gf_eq: "hcomp g f = \<lparr>Chn = f.leg1 \<down>\<down> f.leg1,
                                         Dom = \<lparr>Leg0 = f.leg0 \<cdot> \<p>\<^sub>0[f.leg1, f.leg1],
                                                Leg1 = f.leg0 \<cdot> \<p>\<^sub>1[f.leg1, f.leg1]\<rparr>,
                                         Cod = \<lparr>Leg0 = f.leg0 \<cdot> \<p>\<^sub>0[f.leg1, f.leg1],
                                                Leg1 = f.leg0 \<cdot> \<p>\<^sub>1[f.leg1, f.leg1]\<rparr>\<rparr>"
          using g_def hcomp_def gf.composable src_def trg_def chine_hcomp_ide_ide
                arr_char f.arrow_of_spans_axioms g.arrow_of_spans_axioms ide_char
          by simp

        define \<eta> where "\<eta> = unit_for_map f"
        interpret Dom_gf: span_in_category C \<open>\<lparr>Leg0 = f.leg0 \<cdot> \<p>\<^sub>0[f.leg1, f.leg1],
                                               Leg1 = f.leg0 \<cdot> \<p>\<^sub>1[f.leg1, f.leg1]\<rparr>\<close>
          by (unfold_locales, simp_all)
        interpret \<eta>: arrow_of_spans C \<eta>
          using f g_def \<eta>_def hcomp_def src_def trg_def f.arrow_of_spans_axioms
                g.arrow_of_spans_axioms arr_char C.comp_arr_inv'
                C.tuple_in_hom [of f.leg1 f.leg1 "C.inv f.leg0" "C.inv f.leg0"]
                Dom_src.apex_def Dom_gf.apex_def
          apply unfold_locales by (simp_all add: C.comp_assoc)
        have unit_in_hom: "\<guillemotleft>\<eta> : src f \<Rightarrow> hcomp g f\<guillemotright>"
        proof
          show 1: "arr \<eta>"
            using arr_char \<eta>.arrow_of_spans_axioms by simp
          show "dom \<eta> = src f"
            using 1 \<eta>_def dom_char src_def Dom_src.apex_def by simp
          show "cod \<eta> = hcomp g f"
            using 1 \<eta>_def g_def cod_char hcomp_gf_eq Dom_gf.apex_def by simp
        qed

        define \<epsilon> where "\<epsilon> = counit_for_map f"
        interpret Dom_fg: span_in_category C \<open>\<lparr>Leg0 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.leg0],
                                               Leg1 = f.leg1 \<cdot> \<p>\<^sub>1[f.leg0, f.leg0]\<rparr>\<close>
          by (unfold_locales, simp_all)
        interpret \<epsilon>: arrow_of_spans C \<epsilon>
          using f g_def \<epsilon>_def hcomp_def src_def trg_def f.arrow_of_spans_axioms
                g.arrow_of_spans_axioms arr_char C.comp_cod_arr C.pullback_iso_self
                Dom_trg.apex_def Dom_fg.apex_def
          apply unfold_locales by auto
        have counit_in_hom: "\<guillemotleft>\<epsilon> : hcomp f g \<Rightarrow> trg f\<guillemotright>"
        proof
          show 1: "arr \<epsilon>"
            using arr_char \<epsilon>.arrow_of_spans_axioms by simp
          show "cod \<epsilon> = trg f"
            using 1 \<epsilon>_def cod_char trg_def Dom_trg.apex_def by simp
          show "dom \<epsilon> = hcomp f g"
            using 1 g_def \<epsilon>_def dom_char hcomp_fg_eq Dom_fg.apex_def by simp
        qed
        interpret adj: adjunction_data_in_bicategory vcomp hcomp assoc unit src trg f g \<eta> \<epsilon>
          using f ide_g unit_in_hom counit_in_hom gf.composable
          by (unfold_locales, simp_all)
        interpret adjunction_data_in_span_bicategory C prj0 prj1 f g \<eta> \<epsilon>
          ..
        have triangle_left: "(\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<bullet> \<r>[f]"
        proof -
          have "\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f] = f"
          proof (intro arr_eqI)
            show "par (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) f"
              using f ide_in_hom [of f] adj.triangle_in_hom(3)
              by (metis (no_types, lifting) in_homE)
            show "Chn (\<l>[f] \<bullet> (\<epsilon> \<star> f) \<bullet> \<a>\<^sup>-\<^sup>1[f, g, f] \<bullet> (f \<star> \<eta>) \<bullet> \<r>\<^sup>-\<^sup>1[f]) = f.chine"
              using f g_def \<eta>_def Chn_triangle_eq(1) C.comp_tuple_arr C.comp_inv_arr' by simp
          qed
          thus ?thesis
            using adj.triangle_equiv_form by simp
        qed
        have triangle_right: "(g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<bullet> \<l>[g]"
        proof -
          have "\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g] = g"
          proof (intro arr_eqI)
            show "par (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) g"
              using adj.ide_right ide_in_hom [of g] adj.triangle_in_hom(4)
              by (metis (no_types, lifting) in_homE)
            show "Chn (\<r>[g] \<bullet> (g \<star> \<epsilon>) \<bullet> \<a>[g, f, g] \<bullet> (\<eta> \<star> g) \<bullet> \<l>\<^sup>-\<^sup>1[g]) = g.chine"
              using f g_def \<eta>_def Chn_triangle_eq(2) C.comp_tuple_arr C.comp_inv_arr' by simp
          qed
          thus ?thesis
            using adj.triangle_equiv_form by simp
        qed
        interpret adj: adjunction_in_bicategory vcomp hcomp assoc unit src trg f g \<eta> \<epsilon>
          using triangle_left triangle_right by (unfold_locales, simp_all)
        show "adjunction_in_bicategory vcomp hcomp assoc unit src trg f g \<eta> \<epsilon>" ..
      qed
      show "ide f \<and> C.iso (Leg0 (Dom f)) \<Longrightarrow> is_left_adjoint f"
        using 2 adjoint_pair_def by blast
      show "is_left_adjoint f \<Longrightarrow> adjunction_in_bicategory vcomp hcomp assoc unit src trg f
              (adjoint_of_map f) (unit_for_map f) (counit_for_map f)"
        using 1 2 by blast
    qed

  end

end
