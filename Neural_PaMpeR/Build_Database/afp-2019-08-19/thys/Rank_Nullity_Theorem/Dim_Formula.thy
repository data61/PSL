(*  
    Title:      Dim_Formula.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section "Rank Nullity Theorem of Linear Algebra"

theory Dim_Formula
  imports Fundamental_Subspaces
begin

context vector_space
begin

subsection\<open>Previous results\<close>

text\<open>Linear dependency is a monotone property, based on the 
  monotonocity of linear independence:\<close>

lemma dependent_mono:
  assumes d:"dependent A"
  and A_in_B: "A \<subseteq> B"
  shows  "dependent B"
  using independent_mono [OF _ A_in_B] d by auto

text\<open>Given a finite independent set, a linear combination of its 
  elements equal to zero is possible only if every coefficient is zero:\<close>

lemma scalars_zero_if_independent:
  assumes fin_A: "finite A"
  and ind: "independent A"
  and sum: "(\<Sum>x\<in>A. scale (f x) x) = 0"
  shows "\<forall>x \<in> A. f x = 0"
  using fin_A ind local.dependent_finite sum by blast

end

context finite_dimensional_vector_space
begin

text\<open>In an finite dimensional vector space, every independent set is finite, and 
  thus @{thm [display ]scalars_zero_if_independent [no_vars]} holds:\<close>

corollary scalars_zero_if_independent_euclidean:
  assumes ind: "independent A"
    and sum: "(\<Sum>x\<in>A. scale (f x) x) = 0"
  shows "\<forall>x \<in> A. f x = 0"
  using finiteI_independent ind scalars_zero_if_independent sum by blast

end

text\<open>The following lemma states that every linear form is injective over the 
  elements which define the basis of the range of the linear form. 
  This property is applied later over the elements of an arbitrary 
  basis which are not in the basis of the nullifier or kernel set 
  (\emph{i.e.}, the candidates to be the basis of the range space 
  of the linear form).\<close>

text\<open>Thanks to this result, it can be concluded that the cardinal 
  of the elements of a basis which do not belong to the kernel 
  of a linear form @{term "f::'a => 'b"} is equal to the cardinal 
  of the set obtained when applying @{term "f::'a => 'b"} to such elements.\<close>

text\<open>The application of this lemma is not usually found in the pencil and paper 
  proofs of the ``rank nullity theorem'', but will be crucial to know that,
  being @{term "f::'a => 'b"} a linear form from a finite dimensional
  vector space @{term "V"} to a vector space @{term "V'"}, 
  and given a basis @{term "B::'a set"} of @{term "ker f"}, 
  when @{term "B"} is completed up to a basis of @{term "V::'a set"}
  with a set @{term "W::'a set"}, the cardinal of this set is
  equal to the cardinal of its range set:\<close>
  
context vector_space
begin

lemma inj_on_extended:
  assumes lf: "Vector_Spaces.linear scaleB scaleC f"
  and f: "finite C"
  and ind_C: "independent C"
  and C_eq: "C = B \<union> W"
  and disj_set: "B \<inter> W = {}"
  and span_B: "{x. f x = 0} \<subseteq> span B"
  shows "inj_on f W"
  \<comment> \<open>The proof is carried out by reductio ad absurdum\<close>
proof (unfold inj_on_def, rule+, rule ccontr)
  interpret lf: Vector_Spaces.linear scaleB scaleC f using lf by simp
  \<comment> \<open>Some previous consequences of the premises that are used later:\<close>
  have fin_B: "finite B" using finite_subset [OF _ f] C_eq by simp  
  have ind_B: "independent B" and ind_W: "independent W" 
    using independent_mono[OF ind_C] C_eq by simp_all
  \<comment> \<open>The proof starts here; we assume that there exist two different elements\<close>
  \<comment> \<open>with the same image:\<close>
  fix x::'b and y::'b
  assume x: "x \<in> W" and y: "y \<in> W" and f_eq: "f x = f y" and x_not_y: "x \<noteq> y"
  have fin_yB: "finite (insert y B)" using fin_B by simp
  have "f (x - y) = 0" by (metis diff_self f_eq lf.diff)
  hence "x - y \<in> {x. f x = 0}" by simp
  hence "\<exists>g. (\<Sum>v\<in>B. scale (g v) v) = (x - y)" using span_B
    unfolding span_finite [OF fin_B] by force
  then obtain g where sum: "(\<Sum>v\<in>B. scale (g v) v) = (x - y)" by blast
  \<comment> \<open>We define one of the elements as a linear combination of the second 
      element and the ones in $B$\<close>
  define h :: "'b \<Rightarrow> 'a" where "h a = (if a = y then 1 else g a)" for a
  have "x = y + (\<Sum>v\<in>B. scale (g v) v)" using sum by auto
  also have "... = scale (h y) y  + (\<Sum>v\<in>B. scale (g v) v)" unfolding h_def by simp
  also have "... = scale (h y) y + (\<Sum>v\<in>B. scale (h v) v)"
    apply (unfold add_left_cancel, rule sum.cong) 
    using y h_def empty_iff disj_set by auto   
  also have "... = (\<Sum>v\<in>(insert y B). scale (h v) v)"
    by (rule sum.insert[symmetric], rule fin_B)
       (metis (lifting) IntI disj_set empty_iff y)
  finally have x_in_span_yB: "x \<in> span (insert y B)"
    unfolding span_finite[OF fin_yB] by auto
  \<comment> \<open>We have that a subset of elements of $C$ is linearly dependent\<close>
  have dep: "dependent (insert x (insert y B))" 
    by (unfold dependent_def, rule bexI [of _ x])
       (metis Diff_insert_absorb Int_iff disj_set empty_iff insert_iff 
         x x_in_span_yB x_not_y, simp)
  \<comment> \<open>Therefore, the set $C$ is also dependent:\<close>
  hence "dependent C" using C_eq x y
    by (metis Un_commute Un_upper2 dependent_mono insert_absorb insert_subset)
  \<comment> \<open>This yields the contradiction, since $C$ is independent:\<close>
  thus False using ind_C by contradiction
qed
end

subsection\<open>The proof\<close>

text\<open>Now the rank nullity theorem can be proved; given any linear form 
  @{term "f::'a => 'b"}, the sum of the dimensions of its kernel and 
  range subspaces is equal to the dimension of the source vector space.\<close>

text\<open>The statement of the ``rank nullity theorem for linear algebra'', as 
  well as its proof, follow the ones on~\cite{AX97}. The proof is the 
  traditional one found in the literature. The theorem is also named 
  ``fundamental theorem of linear algebra'' in some texts (for instance,
  in~\cite{GO10}).\<close>

context finite_dimensional_vector_space
begin

theorem rank_nullity_theorem:
  assumes l: "Vector_Spaces.linear scale scaleC f"
  shows "dimension = dim {x. f x = 0} + vector_space.dim scaleC (range f)"
proof -
  \<comment> \<open>For convenience we define abbreviations for the universe set, $V$, 
    and the kernel of $f$\<close>
  interpret l: Vector_Spaces.linear scale scaleC f by fact
  define V :: "'b set" where "V = UNIV"
  define ker_f where "ker_f = {x. f x = 0}"
  \<comment> \<open>The kernel is a proper subspace:\<close>
  have sub_ker: "subspace {x. f x = 0}" using l.subspace_kernel .
  \<comment> \<open>The kernel has its proper basis, $B$:\<close>
  obtain B where B_in_ker: "B \<subseteq> {x. f x = 0}"
    and independent_B: "independent B"
    and ker_in_span:"{x. f x = 0} \<subseteq> span B"
    and card_B: "card B = dim {x. f x = 0}" using basis_exists by blast
  \<comment> \<open>The space $V$ has a (finite dimensional) basis, $C$:\<close>
  obtain C where B_in_C: "B \<subseteq> C" and C_in_V: "C \<subseteq> V" 
    and independent_C: "independent C"
    and span_C: "V = span C"
    unfolding V_def
    by (metis independent_B extend_basis_superset independent_extend_basis span_extend_basis span_superset)
  \<comment> \<open>The basis of $V$, $C$, can be decomposed in the disjoint union of the 
      basis of the kernel, $B$, and its complementary set, $C - B$\<close>
  have C_eq: "C = B \<union> (C - B)" by (rule Diff_partition [OF B_in_C, symmetric])
  have eq_fC: "f ` C = f ` B \<union> f ` (C - B)" 
    by (subst C_eq, unfold image_Un, simp) 
  \<comment> \<open>The basis $C$, and its image, are finite, since $V$ is finite-dimensional\<close>
  have finite_C: "finite C"
    using finiteI_independent[OF independent_C] .
  have finite_fC: "finite (f ` C)" by (rule finite_imageI [OF finite_C])
  \<comment> \<open>The basis $B$ of the kernel of $f$, and its image, are also finite\<close>
  have finite_B: "finite B" by (rule rev_finite_subset [OF finite_C B_in_C])
  have finite_fB: "finite (f ` B)" by (rule finite_imageI[OF finite_B])
  \<comment> \<open>The set $C - B$ is also finite\<close>
  have finite_CB: "finite (C - B)" by (rule finite_Diff [OF finite_C, of B])
  have dim_ker_le_dim_V:"dim (ker_f) \<le> dim V" 
    using dim_subset [of ker_f V] unfolding V_def by simp
  \<comment> \<open>Here it starts the proof of the theorem: the sets $B$ and 
      $C - B$ must be proven to be bases, respectively, of the kernel 
      of $f$ and its range\<close>
  show ?thesis
  proof -
    have "dimension = dim V" unfolding V_def dim_UNIV dimension_def
      by (metis basis_card_eq_dim dimension_def independent_Basis span_Basis top_greatest)
    also have "dim V = dim C" unfolding span_C dim_span ..
    also have "... = card C"
      using basis_card_eq_dim [of C C, OF _ span_superset independent_C] by simp
    also have "... = card (B \<union> (C - B))" using C_eq by simp
    also have "... = card B + card (C-B)"
      by (rule card_Un_disjoint[OF finite_B finite_CB], fast)
    also have "... = dim ker_f + card (C-B)" unfolding ker_f_def card_B ..
    \<comment> \<open>Now it has to be proved that the elements of $C - B$ are a basis of 
      the range of $f$\<close>
    also have "... = dim ker_f + l.vs2.dim (range f)"
    proof (unfold add_left_cancel)
      define W where "W = C - B"
      have finite_W: "finite W" unfolding W_def using finite_CB .
      have finite_fW: "finite (f ` W)" using finite_imageI[OF finite_W] .
      have "card W = card (f ` W)" 
        by (rule card_image [symmetric], rule inj_on_extended[OF l, of C B], rule finite_C)
          (rule independent_C,unfold W_def, subst C_eq, rule refl, simp, rule ker_in_span)
      also have "... = l.vs2.dim (range f)"
        \<comment> \<open>The image set of $W$ is independent and its span contains the range 
             of $f$, so it is a basis of the range:\<close>
      proof (rule l.vs2.basis_card_eq_dim)
        \<comment> \<open>1. The image set of $W$ generates the range of $f$:\<close>
        show "range f \<subseteq> l.vs2.span (f ` W)"
        proof (unfold l.vs2.span_finite [OF finite_fW], auto)
          \<comment> \<open>Given any element $v$ in $V$, its image can be expressed as a 
            linear combination of elements of the image by $f$ of $C$:\<close>
          fix v :: 'b
          have fV_span: "f ` V \<subseteq> l.vs2.span  (f ` C)"
            by (simp add: span_C l.span_image)
          have "\<exists>g. (\<Sum>x\<in>f`C. scaleC (g x) x) = f v"
            using fV_span unfolding V_def
            using l.vs2.span_finite[OF finite_fC]
            by (metis (no_types, lifting) V_def rangeE rangeI span_C l.span_image)
          then obtain g where fv: "f v = (\<Sum>x\<in>f ` C. scaleC (g x) x)" by metis
              \<comment> \<open>We recall that $C$ is equal to $B$ union $(C - B)$, and $B$ 
            is the basis of the kernel; thus, the image of the elements of 
            $B$ will be equal to zero:\<close>
          have zero_fB: "(\<Sum>x\<in>f ` B. scaleC (g x) x) = 0"
            using B_in_ker by (auto intro!: sum.neutral)
          have zero_inter: "(\<Sum>x\<in>(f ` B \<inter> f ` W). scaleC (g x) x) = 0"
            using B_in_ker by (auto intro!: sum.neutral)
          have "f v = (\<Sum>x\<in>f ` C. scaleC (g x) x)" using fv .
          also have "... = (\<Sum>x\<in>(f ` B \<union> f ` W).  scaleC (g x) x)" 
            using eq_fC W_def by simp
          also have "... = 
              (\<Sum>x\<in>f ` B. scaleC (g x) x) + (\<Sum>x\<in>f ` W. scaleC (g x) x) 
                - (\<Sum>x\<in>(f ` B \<inter> f ` W). scaleC (g x) x)" 
            using sum_Un [OF finite_fB finite_fW] by simp
          also have "... = (\<Sum>x\<in>f ` W. scaleC (g x) x)" 
            unfolding zero_fB zero_inter by simp
              \<comment> \<open>We have proved that the image set of $W$ is a generating set 
              of the range of $f$\<close>
          finally show "f v \<in> range (\<lambda>u. \<Sum>v\<in>f ` W. scaleC (u v) v)" by auto
        qed
          \<comment> \<open>2. The image set of $W$ is linearly independent:\<close>
        show "l.vs2.independent (f ` W)"
          using finite_fW
        proof (rule l.vs2.independent_if_scalars_zero)
          \<comment> \<open>Every linear combination (given by $g x$) of the elements of 
           the image set of $W$ equal to zero, requires every coefficient to 
           be zero:\<close>
          fix g :: "'c => 'a" and w :: 'c
          assume sum: "(\<Sum>x\<in>f ` W. scaleC (g x) x) = 0" and w: "w \<in> f ` W"
          have "0 = (\<Sum>x\<in>f ` W. scaleC (g x) x)" using sum by simp
          also have "... = sum ((\<lambda>x. scaleC (g x) x) \<circ> f) W"
            by (rule sum.reindex, rule inj_on_extended[OF l, of C B])
              (unfold W_def, rule finite_C, rule independent_C, rule C_eq, simp, 
                rule ker_in_span)
          also have "... = (\<Sum>x\<in>W. scaleC ((g \<circ> f) x) (f x))" unfolding o_def ..
          also have "... = f (\<Sum>x\<in>W. scale ((g \<circ> f) x) x)"
            unfolding l.sum[symmetric] l.scale[symmetric] by simp
          finally have f_sum_zero:"f (\<Sum>x\<in>W. scale ((g \<circ> f) x) x) = 0" by (rule sym)
          hence "(\<Sum>x\<in>W. scale ((g \<circ> f) x) x) \<in> ker_f" unfolding ker_f_def by simp
          hence "\<exists>h. (\<Sum>v\<in>B. scale (h v) v) = (\<Sum>x\<in>W. scale ((g \<circ> f) x) x)"
            using span_finite[OF finite_B] using ker_in_span
            unfolding ker_f_def by force
          then obtain h where 
            sum_h: "(\<Sum>v\<in>B. scale (h v) v) = (\<Sum>x\<in>W. scale ((g \<circ> f) x) x)" by blast
          define t where "t a = (if a \<in> B then h a else - ((g \<circ> f) a))" for a
          have "0 = (\<Sum>v\<in>B. scale (h v) v) + - (\<Sum>x\<in>W. scale ((g \<circ> f) x) x)" 
            using sum_h by simp
          also have "... =  (\<Sum>v\<in>B. scale (h v) v) + (\<Sum>x\<in>W. - (scale ((g \<circ> f) x) x))" 
            unfolding sum_negf ..
          also have "... = (\<Sum>v\<in>B. scale (t v) v) + (\<Sum>x\<in>W. -(scale((g \<circ> f) x) x))" 
            unfolding add_right_cancel unfolding t_def by simp
          also have "... =  (\<Sum>v\<in>B. scale (t v) v) + (\<Sum>x\<in>W. scale (t x) x)"
            by (unfold add_left_cancel t_def W_def, rule sum.cong) simp+
          also have "... = (\<Sum>v\<in>B \<union> W. scale (t v) v)"
            by (rule sum.union_inter_neutral [symmetric], rule finite_B, rule finite_W) 
              (simp add: W_def)
          finally have "(\<Sum>v\<in>B \<union> W. scale (t v) v) = 0" by simp
          hence coef_zero: "\<forall>x\<in>B \<union> W. t x = 0"
            using C_eq scalars_zero_if_independent [OF finite_C independent_C]
            unfolding W_def by simp
          obtain y where w_fy: "w = f y " and y_in_W: "y \<in> W" using w by fast
          have "- g w = t y" 
            unfolding t_def w_fy using y_in_W unfolding W_def by simp
          also have "... = 0" using coef_zero y_in_W unfolding W_def by simp
          finally show "g w = 0" by simp
        qed
      qed auto
      finally show "card (C - B) = l.vs2.dim (range f)" unfolding W_def .
    qed
    finally show ?thesis unfolding V_def ker_f_def unfolding dim_UNIV .
  qed
qed

end

subsection\<open>The rank nullity theorem for matrices\<close>

text\<open>The proof of the theorem for matrices
  is direct, as a consequence of the ``rank nullity theorem''.\<close>

lemma rank_nullity_theorem_matrices:
  fixes A::"'a::{field}^'cols::{finite, wellorder}^'rows"
  shows "ncols A = vec.dim (null_space A) + vec.dim (col_space A)"
  using vec.rank_nullity_theorem[OF matrix_vector_mul_linear_gen, of A]
  apply (subst (2 3) matrix_of_matrix_vector_mul [of A, symmetric])
  unfolding null_space_eq_ker[OF matrix_vector_mul_linear_gen]
  unfolding col_space_eq_range [OF matrix_vector_mul_linear_gen]
  unfolding vec.dimension_def ncols_def card_cart_basis
  by simp

end
