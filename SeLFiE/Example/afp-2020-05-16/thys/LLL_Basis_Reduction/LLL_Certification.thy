(*
    Authors:    René Thiemann
                BSD
*)

section \<open>Certification of External LLL Invocations\<close>

text \<open>Instead of using a fully verified algorithm, we also provide a technique to invoke
an external LLL solver. In order to check its result, we not only need the reduced basic,
but also the matrices which translate between the input basis and the reduced basis. 
Then we can easily check whether the resulting lattices are indeed identical and just have
to start the verified algorithm on the already reduced basis.
This invocation will then usually just require one computation of Gram--Schmidt in order
to check that the basis is already reduced. Alternatively, one could also throw an error
message in case the basis is not reduced.\<close>

subsection \<open>Checking Results of External LLL Solvers\<close>

theory LLL_Certification
  imports
    LLL_Impl
    Jordan_Normal_Form.Show_Matrix
begin


definition "gauss_jordan_integer_inverse n A B I = (case gauss_jordan A B of
   (C,D) \<Rightarrow> C = I \<and> list_all is_int_rat (concat (mat_to_list D)))" 

definition "integer_equivalent n fs gs = (let 
  fs' = map_mat rat_of_int (mat_of_cols n fs);
  gs' = map_mat rat_of_int (mat_of_cols n gs);
  I = 1\<^sub>m n
  in gauss_jordan_integer_inverse n fs' gs' I \<and> gauss_jordan_integer_inverse n gs' fs' I)" 

context vec_module
begin

lemma mat_mult_sub_lattice: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and gs: "set gs \<subseteq> carrier_vec n" 
  and A: "A \<in> carrier_mat (length fs) (length gs)" 
  and prod: "mat_of_rows n fs = map_mat of_int A * mat_of_rows n gs" 
  shows "lattice_of fs \<subseteq> lattice_of gs" 
proof 
  let ?m = "length fs"
  let ?m' = "length gs" 
  let ?i = "of_int :: int \<Rightarrow> 'a" 
  let ?I = "map_mat ?i" 
  let ?A = "?I A" 
  have gsC: "mat_of_rows n gs \<in> carrier_mat ?m' n" by auto
  from A have A: "?A \<in> carrier_mat ?m ?m'" by auto
  from fs have fsi[simp]: "\<And> i. i < ?m \<Longrightarrow> fs ! i \<in> carrier_vec n" by auto
  hence fsi'[simp]: "\<And> i. i < ?m \<Longrightarrow> dim_vec (fs ! i) = n" by simp
  from gs have fsi[simp]: "\<And> i. i < ?m' \<Longrightarrow> gs ! i \<in> carrier_vec n" by auto
  hence gsi'[simp]: "\<And> i. i < ?m' \<Longrightarrow> dim_vec (gs ! i) = n" by simp
  fix v
  assume "v \<in> lattice_of fs" 
  from in_latticeE[OF this]
  obtain c where v: "v = M.sumlist (map (\<lambda>i. ?i (c i) \<cdot>\<^sub>v fs ! i) [0..<?m])" by auto
  let ?c = "vec ?m (\<lambda> i. ?i (c i))" 
  let ?d = "A\<^sup>T *\<^sub>v vec ?m c" 
  note v
  also have "\<dots> = mat_of_cols n fs *\<^sub>v ?c" 
    by (rule eq_vecI, auto intro!: dim_sumlist sum.cong 
      simp: sumlist_nth scalar_prod_def mat_of_cols_def)
  also have "mat_of_cols n fs = (mat_of_rows n fs)\<^sup>T" 
    by (simp add: transpose_mat_of_rows)
  also have "\<dots> = (?A * mat_of_rows n gs)\<^sup>T" unfolding prod ..
  also have "\<dots> = (mat_of_rows n gs)\<^sup>T * ?A\<^sup>T" 
    by (rule transpose_mult[OF A gsC])
  also have "(mat_of_rows n gs)\<^sup>T = mat_of_cols n gs" 
    by (simp add: transpose_mat_of_rows)
  finally have "v = (mat_of_cols n gs * ?A\<^sup>T) *\<^sub>v ?c" .
  also have "\<dots> = mat_of_cols n gs *\<^sub>v (?A\<^sup>T *\<^sub>v ?c)" 
    by (rule assoc_mult_mat_vec, insert A, auto)
  also have "?A\<^sup>T = ?I (A\<^sup>T)" by fastforce
  also have "?c = map_vec ?i (vec ?m c)" by auto
  also have "?I (A\<^sup>T) *\<^sub>v \<dots> = map_vec ?i ?d" 
    using A by (simp add: of_int_hom.mult_mat_vec_hom)
  finally have "v = mat_of_cols n gs *\<^sub>v map_vec ?i ?d" .
  define d where "d = ?d" 
  have d: "d \<in> carrier_vec ?m'" unfolding d_def using A by auto
  have "v = mat_of_cols n gs *\<^sub>v map_vec ?i d" unfolding d_def by fact
  also have "\<dots> =  M.sumlist (map (\<lambda>i. ?i (d $ i) \<cdot>\<^sub>v gs ! i) [0..<?m'])" 
    by (rule sym, rule eq_vecI, insert d, auto intro!: dim_sumlist sum.cong 
      simp: sumlist_nth scalar_prod_def mat_of_cols_def)
  finally show "v \<in> lattice_of gs" 
    by (intro in_latticeI, auto)
qed
end

context LLL_with_assms
begin

lemma mult_left_identity:
  defines "B \<equiv> (map_mat rat_of_int (mat_of_rows n fs_init))"
  assumes P_carrier[simp]: "P \<in> carrier_mat m m" 
  and PB: "P * B = B"  
shows "P = 1\<^sub>m m" 
proof -
  let ?set_rows = "set (rows B)"
  let ?hom = "of_int_hom.vec_hom :: int vec \<Rightarrow> rat vec"
  have set_rows_carrier: "?set_rows \<subseteq> (carrier_vec n)" by (auto simp add: rows_def B_def)
  have set_rows_eq: "?set_rows = set (map of_int_hom.vec_hom fs_init)"
  proof -
    have "x \<in> of_int_hom.vec_hom ` set fs_init" if x: "x \<in> set (rows B)" for x
      using x unfolding B_def 
      by (metis cof_vec_space.lin_indpt_list_def fs_init image_set 
          lin_dep mat_of_rows_map rows_mat_of_rows)
    moreover have "of_int_hom.vec_hom xa \<in> set (rows B)" if xa: "xa \<in> set fs_init" for xa
    proof -
      obtain i where xa: "xa = fs_init ! i" and i: "i<m"
        by (metis in_set_conv_nth len xa)
      have "?hom (fs_init ! i) = row B i" unfolding B_def
        by (metis i cof_vec_space.lin_indpt_list_def fs_init index_map_mat(2) len lin_dep 
            mat_of_rows_carrier(2) mat_of_rows_map nth_map nth_rows rows_mat_of_rows)
      thus ?thesis
        by (metis B_def xa i cof_vec_space.lin_indpt_list_def fs_init index_map_mat(2) len 
            length_rows lin_dep mat_of_rows_map nth_map nth_mem rows_mat_of_rows)
    qed
    ultimately show ?thesis by auto
  qed
  have ind_set_rows: "gs.lin_indpt ?set_rows"
    using lin_dep set_rows_eq unfolding gs.lin_indpt_list_def by auto
  have inj_on_rowB: "inj_on (row B) {0..<m}" 
  proof -
    have "x = y" if x: "x < m" and y: "y < m" and row_xy: "row B x = row B y" for x y
    proof (rule ccontr)
      assume xy: "x \<noteq> y"
      have 1: "?hom (fs_init ! x) = row B x" unfolding B_def
        by (metis fs_init index_map_mat(2) len local.set_rows_carrier mat_of_rows_carrier(2) 
            mat_of_rows_map nth_map nth_rows rows_mat_of_rows set_rows_eq that(1))
      moreover have 2: "?hom (fs_init ! y) = row B y" unfolding B_def
        by (metis fs_init index_map_mat(2) len local.set_rows_carrier mat_of_rows_carrier(2) 
            mat_of_rows_map nth_map nth_rows rows_mat_of_rows set_rows_eq that(2))
      ultimately have "?hom (fs_init ! x) = ?hom (fs_init ! y)" using row_xy by auto
      thus False using lin_dep x y row_xy unfolding gs.lin_indpt_list_def 
        using xy x y len unfolding distinct_conv_nth by auto
    qed
    thus ?thesis unfolding inj_on_def by auto
  qed
  have the_x: "(THE k. k < m \<and> row B x = row B k) = x" if x: "x < m" for x
  proof (rule theI2)
    show "x < m \<and> row B x = row B x" using x by auto
    fix xa assume xa: "xa < m \<and> row B x = row B xa" 
    show "xa = x" using xa inj_on_rowB x unfolding inj_on_def by auto
    thus "xa = x" .
  qed
  let ?h= "row B"
  show ?thesis
  proof (rule eq_matI, unfold one_mat_def, auto)
    fix j assume j: "j < m"
    let ?f = "(\<lambda>v. P $$ (j, THE k. k < m \<and> v = row B k))"
    let ?g = "\<lambda>v. if v = row B j then (?f v) - 1 else ?f v"
    have finsum_closed[simp]: 
       "finsum_vec TYPE(rat) n (\<lambda>k. P $$ (j, k) \<cdot>\<^sub>v row B k) {0..<m} \<in> carrier_vec n" 
      by (rule finsum_vec_closed, insert len B_def, auto)
    have B_carrier[simp]: "B \<in> carrier_mat m n" using len fs_init B_def by auto
    define v where "v \<equiv> row B j"
    have v_set_rows: "v \<in> set (rows B)" using nth_rows j unfolding v_def
      by (metis B_carrier carrier_matD(1) length_rows nth_mem)
    have [simp]: "mat_of_rows n fs_init \<in> carrier_mat m n" using len fs_init by auto
    have "B = P*B" using PB by auto
    also have "... = mat\<^sub>r m n (\<lambda>i. finsum_vec TYPE(rat) n (\<lambda>k. P $$ (i, k) \<cdot>\<^sub>v row B k) {0..<m})"
      by (rule mat_mul_finsum_alt, auto)
    also have "row (...) j = finsum_vec TYPE(rat) n (\<lambda>k. P $$ (j, k) \<cdot>\<^sub>v row B k) {0..<m}"
      by (rule row_mat_of_row_fun[OF j], simp)
    also have "... = finsum_vec TYPE(rat) n (\<lambda>v.  ?f v \<cdot>\<^sub>v v) ?set_rows"  (is "?lhs = ?rhs")
    proof (rule eq_vecI)
      have rhs_carrier: "?rhs \<in> carrier_vec n" 
        by (rule finsum_vec_closed, insert set_rows_carrier, auto)
      have "dim_vec ?lhs = n" using vec_space.finsum_dim by simp
      also have dim_rhs: "... = dim_vec ?rhs" using rhs_carrier by auto
      finally show "dim_vec ?lhs = dim_vec ?rhs" .
      fix i assume i: "i < dim_vec ?rhs"
      have i_n: "i < n" using i dim_rhs by auto
      let ?g = "\<lambda>v. (?f v \<cdot>\<^sub>v v) $ i"
      have image_h: "?h `{0..<m} = ?set_rows" by (auto simp add: B_def len rows_def)      
      have "?lhs $ i = (\<Sum>k\<in>{0..<m}. (P $$ (j, k) \<cdot>\<^sub>v row B k) $ i)" 
        by (rule index_finsum_vec[OF _ i_n], auto)
      also have "... = sum (?g \<circ> ?h) {0..<m}" unfolding o_def 
        by (rule sum.cong, insert the_x, auto)
      also have "... = sum (\<lambda>v. (?f v \<cdot>\<^sub>v v) $ i) (?h `{0..<m})" 
        by (rule sum.reindex[symmetric, OF inj_on_rowB])
      also have "... =  (\<Sum>v\<in>?set_rows. (?f v \<cdot>\<^sub>v v) $ i)" using image_h by auto
      also have "... = ?rhs $ i" 
        by (rule index_finsum_vec[symmetric, OF _ i_n], insert set_rows_carrier, auto)
      finally show "?lhs $ i = ?rhs $ i" by auto    
    qed
    also have "... = (\<Oplus>\<^bsub>gs.V\<^esub>v\<in>?set_rows. ?f v \<cdot>\<^sub>v v)" unfolding vec_space.finsum_vec ..  
    also have "... = gs.lincomb ?f ?set_rows" unfolding gs.lincomb_def by auto
    finally have lincomb_rowBj: "gs.lincomb ?f ?set_rows = row B j" ..
    have lincomb_0: "gs.lincomb ?g (?set_rows) = 0\<^sub>v n"
    proof -
      have v_closed[simp]: "v \<in> Rn" unfolding v_def using j by auto
      have lincomb_f_closed[simp]: "gs.lincomb ?f (?set_rows-{v}) \<in> Rn" 
        by (rule gs.lincomb_closed, insert set_rows_carrier, auto)
      have fv_v_closed[simp]: "?f v \<cdot>\<^sub>v v \<in> Rn" by auto
      have lincomb_f: "gs.lincomb ?f ?set_rows = ?f v \<cdot>\<^sub>v v + gs.lincomb ?f (?set_rows-{v})"
        by (rule gs.lincomb_del2, insert set_rows_carrier v_set_rows, auto) 
      have fvv_gvv: "?f v \<cdot>\<^sub>v v - v = ?g v \<cdot>\<^sub>v v" unfolding v_def 
        by (rule eq_vecI, auto, simp add: left_diff_distrib)
      have lincomb_fg: "gs.lincomb ?f (?set_rows-{v}) = gs.lincomb ?g (?set_rows-{v})" 
        (is "?lhs = ?rhs")
      proof (rule eq_vecI)
        show dim_vec_eq: "dim_vec ?lhs = dim_vec ?rhs"
          by (smt DiffE carrier_vecD gs.lincomb_closed local.set_rows_carrier subsetCE subsetI)
        fix i assume i: "i<dim_vec ?rhs"
        hence i_n: "i<n" using dim_vec_eq lincomb_f_closed by auto
        have "?lhs $ i =  (\<Sum>x\<in>(?set_rows-{v}). ?f x * x $ i)" 
          by (rule gs.lincomb_index[OF i_n], insert set_rows_carrier, auto)
        also have "... = (\<Sum>x\<in>(?set_rows-{v}). ?g x * x $ i)"
          by (rule sum.cong, auto simp add: v_def)
        also have "... = ?rhs $ i"
          by (rule gs.lincomb_index[symmetric, OF i_n], insert set_rows_carrier, auto)
        finally show "?lhs $ i = ?rhs $ i" .
      qed
      have "0\<^sub>v n = gs.lincomb ?f ?set_rows - v" using lincomb_rowBj unfolding v_def B_def by auto
      also have "... = ?f v \<cdot>\<^sub>v v + gs.lincomb ?f (?set_rows-{v}) - v" using lincomb_f by auto
      also have "... = (gs.lincomb ?f (?set_rows-{v}) + ?f v \<cdot>\<^sub>v v) + - v" 
        unfolding gs.M.a_comm[OF lincomb_f_closed fv_v_closed] by auto
      also have "... = gs.lincomb ?f (?set_rows-{v}) + (?f v \<cdot>\<^sub>v v + - v)" 
        by (rule gs.M.a_assoc, auto)
      also have "... = gs.lincomb ?f (?set_rows-{v}) + (?f v \<cdot>\<^sub>v v - v)" by auto
      also have "... = gs.lincomb ?g (?set_rows-{v}) + (?g v \<cdot>\<^sub>v v)" 
        unfolding lincomb_fg fvv_gvv by auto
      also have "... = (?g v \<cdot>\<^sub>v v) + gs.lincomb ?g (?set_rows-{v})" 
        by (rule gs.M.a_comm, auto, rule gs.lincomb_closed, insert set_rows_carrier, auto)
      also have "... = gs.lincomb ?g (?set_rows)" 
        by (rule gs.lincomb_del2[symmetric], insert v_set_rows set_rows_carrier, auto)
      finally show ?thesis ..
    qed
    have g0: "?g \<in> ?set_rows \<rightarrow> {0}" 
      by (rule gs.not_lindepD[of ?set_rows, OF ind_set_rows _ _ _ lincomb_0], auto)  
    hence "?g (row B j) = 0" using v_set_rows unfolding v_def Pi_def by blast
    hence "?f (row B j) - 1 = 0" by auto
    hence "P $$ (j,j) - 1 = 0" using the_x j by auto
    thus "P$$(j,j) = 1" by auto
    fix i assume i: "i < m" and ji: "j \<noteq> i"
    have row_ij: "row B i \<noteq> row B j" using inj_on_rowB ji i j unfolding inj_on_def by fastforce
    have "row B i \<in> ?set_rows" using nth_rows i
      by (metis B_carrier carrier_matD(1) length_rows nth_mem)
    hence "?g (row B i) = 0" using g0 unfolding Pi_def by blast
    hence "?f (row B i) = 0" using row_ij by auto
    thus "P $$ (j, i) = 0" using the_x i by auto
  next
     show "dim_row P = m" and "dim_col P = m" using P_carrier unfolding carrier_mat_def by auto
   qed
qed



text \<open>This is the key lemma. It permits to change from the initial basis
@{term fs_init} to an arbitrary @{term gs} that has been computed by some
external tool. Here, two change-of-basis matrices U1 and U2 are required 
to certify the change via the conditions prod1 and prod2.\<close>


lemma LLL_change_basis: assumes gs: "set gs \<subseteq> carrier_vec n" 
  and len': "length gs = m" 
  and U1: "U1 \<in> carrier_mat m m" 
  and U2: "U2 \<in> carrier_mat m m" 
  and prod1: "mat_of_rows n fs_init = U1 * mat_of_rows n gs" 
  and prod2: "mat_of_rows n gs = U2 * mat_of_rows n fs_init" 
shows "lattice_of gs = lattice_of fs_init" "LLL_with_assms n m gs \<alpha>" 
proof -
  let ?i = "of_int :: int \<Rightarrow> int" 
  have "U1 = map_mat ?i U1" by (intro eq_matI, auto)
  with prod1 have prod1: "mat_of_rows n fs_init = map_mat ?i U1 * mat_of_rows n gs" by simp
  have "U2 = map_mat ?i U2" by (intro eq_matI, auto)
  with prod2 have prod2: "mat_of_rows n gs = map_mat ?i U2 * mat_of_rows n fs_init" by simp
  have "lattice_of gs \<subseteq> lattice_of fs_init" 
    by (rule mat_mult_sub_lattice[OF gs fs_init _ prod2], auto simp: U2 len len')
  moreover have "lattice_of gs \<supseteq> lattice_of fs_init"
    by (rule mat_mult_sub_lattice[OF fs_init gs _ prod1], auto simp: U1 len len')
  ultimately show "lattice_of gs = lattice_of fs_init" by blast
  show "LLL_with_assms n m gs \<alpha>"
  proof
    show "4/3 \<le> \<alpha>" by (rule \<alpha>)
    show "length gs = m" by fact
    show "lin_indep gs"
    proof -
      let ?fs = "map_mat rat_of_int (mat_of_rows n fs_init)"
      let ?gs = "map_mat rat_of_int (mat_of_rows n gs)"
      let ?U1 = "map_mat rat_of_int U1"
      let ?U2 = "map_mat rat_of_int U2"
      let ?P = "?U1 * ?U2"
      have rows_gs_eq: "rows ?gs = map of_int_hom.vec_hom gs"
      proof (rule nth_equalityI)        
        fix i assume i: "i < length (rows ?gs)"
        have "rows ?gs ! i = row ?gs i" by (rule nth_rows, insert i, auto)
        also have "... = of_int_hom.vec_hom (gs ! i)"
          by (metis (mono_tags, lifting) gs i index_map_mat(2) length_map length_rows map_carrier_vec 
              mat_of_rows_map mat_of_rows_row nth_map nth_mem rows_mat_of_rows subset_code(1))
        also have "... = map of_int_hom.vec_hom gs ! i" 
          by (rule nth_map[symmetric], insert i, auto)        
        finally show "rows ?gs ! i = map of_int_hom.vec_hom gs ! i" .
      qed (simp)
      have fs_hom: "?fs \<in> carrier_mat m n" unfolding carrier_mat_def using len by auto
      have gs_hom: "?gs \<in> carrier_mat m n" unfolding carrier_mat_def using len' by auto    
      have U1U2: "U1 * U2 \<in> carrier_mat m m" by (meson assms(3) assms(4) mult_carrier_mat)
      have U1_hom: "?U1 \<in> carrier_mat m m" by (simp add: U1)
      have U2_hom: "?U2 \<in> carrier_mat m m" by (simp add: U2)
      have U1U2_hom: "?U1 * ?U2 \<in> carrier_mat m m" using U1 U2 by auto
      have Gs_U2Fs: "?gs = ?U2 * ?fs" using prod2
        by (metis U2 assms(6) len mat_of_rows_carrier(1) of_int_hom.mat_hom_mult)
      have fs_hom_eq: "?fs = ?P * ?fs"
        by (smt U1 U1U2 U2 assms(5) assms(6) assoc_mult_mat fs_hom 
            map_carrier_mat of_int_hom.mat_hom_mult)
      have P_id: "?P = 1\<^sub>m m" by (rule mult_left_identity[OF U1U2_hom fs_hom_eq[symmetric]])
      hence "det (?U1) * det (?U2) = 1" by (smt U1_hom U2_hom det_mult det_one of_int_hom.hom_det)
      hence det_U2: "det ?U2 \<noteq> 0" and det_U1: "det ?U1 \<noteq> 0" by auto    
      from det_non_zero_imp_unit[OF U2_hom det_U2, unfolded Units_def, of "()"] 
      have inv_U2: "invertible_mat ?U2"
        using U1_hom U2_hom
        unfolding invertible_mat_def inverts_mat_def by (auto simp: ring_mat_def)
      interpret Rs: vectorspace class_ring "(gs.vs (gs.row_space ?gs))" 
        by (rule gs.vector_space_row_space[OF gs_hom])
      interpret RS_fs: vectorspace class_ring "(gs.vs (gs.row_space (?fs)))"
        by (rule gs.vector_space_row_space[OF fs_hom])
      have submoduleGS: "submodule class_ring (gs.row_space ?gs) gs.V"
        and submoduleFS: "submodule class_ring (gs.row_space ?fs) gs.V" 
        by (metis gs.row_space_def gs.span_is_submodule index_map_mat(3) 
            mat_of_rows_carrier(3) rows_carrier)+
      have set_rows_fs_in: "set (rows ?fs) \<subseteq> gs.row_space ?fs" 
        and rows_gs_row_space: "set (rows ?gs) \<subseteq> gs.row_space ?gs" 
        unfolding gs.row_space_def      
        by (metis gs.in_own_span index_map_mat(3) mat_of_rows_carrier(3) rows_carrier)+
      have Rs_fs_dim: "RS_fs.dim = m"
      proof -
        have "RS_fs.dim = card (set (rows ?fs))"
        proof (rule RS_fs.dim_basis)
          have "RS_fs.span (set (rows ?fs)) = gs.span (set (rows ?fs))" 
            by (rule gs.span_li_not_depend[OF _ submoduleFS], simp add: set_rows_fs_in)
          also have "... = carrier (gs.vs (gs.row_space ?fs))"
           unfolding gs.row_space_def unfolding gs.carrier_vs_is_self by auto
          finally have "RS_fs.gen_set (set (rows ?fs))" by auto
          moreover have "RS_fs.lin_indpt (set (rows ?fs))"
          proof -
            have "module.lin_dep class_ring (gs.vs (gs.row_space ?fs)) (set (rows ?fs)) 
              = gs.lin_dep (set (rows ?fs))"
              by (rule gs.span_li_not_depend[OF _ submoduleFS], simp add: set_rows_fs_in) 
            thus ?thesis using lin_dep unfolding gs.lin_indpt_list_def
              by (metis fs_init mat_of_rows_map rows_mat_of_rows)
          qed
          moreover have "set (rows ?fs) \<subseteq> carrier (gs.vs (gs.row_space ?fs))"
            by (simp add: set_rows_fs_in)
          ultimately show "RS_fs.basis (set (rows ?fs))" unfolding RS_fs.basis_def by simp
        qed (simp)
        also have "... = m"
          by (metis cof_vec_space.lin_indpt_list_def distinct_card fs_init len 
              length_map lin_dep mat_of_rows_map rows_mat_of_rows)
        finally show ?thesis .
      qed
      have "gs.row_space ?fs = gs.row_space (?U2*?fs)" 
        by (rule gs.row_space_is_preserved[symmetric, OF inv_U2 U2_hom fs_hom])
      also have "... = gs.row_space ?gs" using Gs_U2Fs by auto
      finally have "gs.row_space ?fs = gs.row_space ?gs" by auto
      hence "vectorspace.dim class_ring (gs.vs (gs.row_space ?gs)) = m"
        using Rs_fs_dim fs_hom_eq by auto
      hence Rs_dim_is_m: "Rs.dim = m" by blast
      have card_set_rows: "card (set (rows ?gs)) \<le> m"
        by (metis assms(2) card_length length_map rows_gs_eq)     
      have Rs_basis: "Rs.basis (set (rows ?gs))" 
      proof (rule Rs.dim_gen_is_basis)        
        show "card (set (rows ?gs)) \<le> Rs.dim" using card_set_rows Rs_dim_is_m by auto
        have "Rs.span (set (rows ?gs)) = gs.span (set (rows ?gs))" 
          by (rule gs.span_li_not_depend[OF rows_gs_row_space submoduleGS])
        also have "... = carrier (gs.vs (gs.row_space ?gs))"
           unfolding gs.row_space_def unfolding gs.carrier_vs_is_self by auto
        finally show "Rs.gen_set (set (rows ?gs))" by auto
        show "set (rows ?gs) \<subseteq> carrier (gs.vs (gs.row_space ?gs))" using rows_gs_row_space by auto
      qed (simp)      
      hence indpt_Rs: "Rs.lin_indpt (set (rows ?gs))" unfolding Rs.basis_def by auto
      have gs_lin_indpt_rows: "gs.lin_indpt (set (rows ?gs))" 
        (*Is there any automatic way to prove this?*) 
        (*TODO: via gs.span_li_not_depend*)
      proof 
        define N where "N \<equiv> (gs.row_space ?gs)"
        assume "gs.lin_dep (set (rows ?gs))"
        from this obtain A f v where A1: "finite A" and A2: "A \<subseteq> set (rows ?gs)"
          and lc_gs: "gs.lincomb f A = 0\<^sub>v n" and v: "v \<in> A" and fv: "f v \<noteq> 0" 
          unfolding gs.lin_dep_def by blast
        have "gs.lincomb f A = module.lincomb (gs.vs N) f A" 
          by (rule gs.lincomb_not_depend, insert submoduleGS A1 A2 gs.row_space_def 
              rows_gs_row_space, auto simp add: N_def gs.row_space_def)          
        also have "... = Rs.lincomb f A" using N_def by blast
        finally have "Rs.lin_dep (set (rows ?gs))" 
          unfolding Rs.lin_dep_def using A1 A2 v fv lc_gs by auto
        thus False using indpt_Rs by auto
      qed
      have "card (set (rows ?gs)) \<ge> Rs.dim" 
        by (rule Rs.gen_ge_dim, insert rows_gs_row_space Rs_basis, auto simp add: Rs.basis_def)
      hence card_m: "card (set (rows ?gs)) = m" using card_set_rows Rs_dim_is_m by auto      
      have "distinct (map (of_int_hom.vec_hom::int vec \<Rightarrow> rat vec) gs)" 
        using rows_gs_eq assms(2) card_m card_distinct by force
      moreover have "set (map of_int_hom.vec_hom gs) \<subseteq> Rn" using gs by auto
      ultimately show "gs.lin_indpt_list (map of_int_hom.vec_hom gs)"
        using gs_lin_indpt_rows
        unfolding rows_gs_eq gs.lin_indpt_list_def
        by auto      
    qed
  qed
qed

lemma gauss_jordan_integer_inverse: fixes fs gs :: "int vec list" 
  assumes gs: "set gs \<subseteq> carrier_vec n"
  and len_gs: "length gs = n" 
  and fs: "set fs \<subseteq> carrier_vec n" 
  and len_fs: "length fs = n" 
  and gauss: "gauss_jordan_integer_inverse n (map_mat rat_of_int (mat_of_cols n fs)) 
    (map_mat rat_of_int (mat_of_cols n gs)) (1\<^sub>m n)" (is "gauss_jordan_integer_inverse _ ?fs ?gs _")
shows "\<exists> U. U \<in> carrier_mat n n \<and> mat_of_rows n gs = U * mat_of_rows n fs" 
proof -
  have fs': "?fs \<in> carrier_mat n n" using fs len_fs by auto
  have gs': "?gs \<in> carrier_mat n n" using gs len_gs by auto
  note gauss = gauss[unfolded gauss_jordan_integer_inverse_def]
  from gauss obtain A where gauss: "gauss_jordan ?fs ?gs = (1\<^sub>m n, A)"
   and int: "list_all is_int_rat (concat (mat_to_list A))" by auto
  note gauss = gauss_jordan[OF fs' gs' gauss]
  note A = gauss(4)
  let ?A = "map_mat int_of_rat A" 
  from gauss(2)[OF A] A
  have id: "?fs * A = ?gs" by auto
  let ?U = "(map_mat int_of_rat A)\<^sup>T" 
  from A have U: "?U \<in> carrier_mat n n" by auto
  have "A = map_mat of_int ?A" using int[unfolded list_all_iff] A
    by (intro eq_matI, auto simp: mat_to_list_def)
  with id have "?gs = ?fs * map_mat of_int ?A" by auto
  also have "\<dots> = map_mat of_int (mat_of_cols n fs * ?A)" 
    by (rule of_int_hom.mat_hom_mult[symmetric], insert fs' A, auto)
  finally have "mat_of_cols n fs * ?A = mat_of_cols n gs"
    using of_int_hom.mat_hom_inj by fastforce
  hence "(mat_of_cols n gs)\<^sup>T = (mat_of_cols n fs * ?A)\<^sup>T" by simp
  also have "\<dots> = ?U * (mat_of_cols n fs)\<^sup>T" 
    by (rule transpose_mult, insert fs' A, auto)
  also have "(mat_of_cols n fs)\<^sup>T = mat_of_rows n fs" 
    using fs len_fs unfolding mat_of_rows_def mat_of_cols_def
    by (intro eq_matI, auto)
  also have "(mat_of_cols n gs)\<^sup>T = mat_of_rows n gs" 
    using gs len_gs unfolding mat_of_rows_def mat_of_cols_def
    by (intro eq_matI, auto)
  finally show ?thesis using U by blast
qed 
  

lemma LLL_change_basis_mat_inverse: assumes gs: "set gs \<subseteq> carrier_vec n" 
  and len': "length gs = n" 
  and "m = n" 
  and eq: "integer_equivalent n fs_init gs" 
shows "lattice_of gs = lattice_of fs_init" "LLL_with_assms n m gs \<alpha>" 
proof -
  from eq[unfolded integer_equivalent_def Let_def]
  have 1: "gauss_jordan_integer_inverse n (of_int_hom.mat_hom (mat_of_cols n fs_init))
   (of_int_hom.mat_hom (mat_of_cols n gs)) (1\<^sub>m n)" 
    and 2: "gauss_jordan_integer_inverse n (of_int_hom.mat_hom (mat_of_cols n gs))
     (of_int_hom.mat_hom (mat_of_cols n fs_init)) (1\<^sub>m n)" 
    by auto
  note len = len[unfolded \<open>m = n\<close>]
  from gauss_jordan_integer_inverse[OF gs len' fs_init len 1] \<open>m = n\<close>
  obtain U where U: "U \<in> carrier_mat m m" "mat_of_rows n gs = U * mat_of_rows n fs_init" by auto
  from gauss_jordan_integer_inverse[OF fs_init len gs len' 2] \<open>m = n\<close>
  obtain V where V: "V \<in> carrier_mat m m" "mat_of_rows n fs_init = V * mat_of_rows n gs" by auto
  from LLL_change_basis[OF gs len'[folded \<open>m = n\<close>] V(1) U(1) V(2) U(2)]
  show "lattice_of gs = lattice_of fs_init" "LLL_with_assms n m gs \<alpha>" by blast+
qed

end

text \<open>External solvers must deliver a reduced basis and optionally two
  matrices to convert between the input and the reduced basis. These two
  matrices are mandatory if the input matrix is not a square matrix.\<close>
consts external_lll_solver :: "integer \<times> integer \<Rightarrow> integer list list \<Rightarrow> 
  integer list list \<times> (integer list list \<times> integer list list)option" 

definition reduce_basis_external :: "rat \<Rightarrow> int vec list \<Rightarrow> int vec list" where
  "reduce_basis_external \<alpha> fs = (case fs of Nil \<Rightarrow> [] | Cons f _ \<Rightarrow> (let 
    rb = reduce_basis \<alpha>;
    fsi = map (map integer_of_int o list_of_vec) fs;
    n = dim_vec f;
    m = length fs in 
  case external_lll_solver (map_prod integer_of_int integer_of_int (quotient_of \<alpha>)) fsi of 
    (gsi, co) \<Rightarrow>
    let gs = (map (vec_of_list o map int_of_integer) gsi) in
    if \<not> (length gs = m \<and> (\<forall> gi \<in> set gs. dim_vec gi = n)) then
      Code.abort (STR ''error in external LLL invocation: dimensions of reduced basis do not fit\<newline>input to external solver: ''
        + String.implode (show fs) + STR ''\<newline>\<newline>'') (\<lambda> _. rb fs)
     else 
       case co of Some (u1i, u2i) \<Rightarrow> (let 
         u1 = mat_of_rows_list m (map (map int_of_integer) u1i);
         u2 = mat_of_rows_list m (map (map int_of_integer) u2i);
         gs = (map (vec_of_list o map int_of_integer) gsi);
         Fs = mat_of_rows n fs;
         Gs = mat_of_rows n gs in 
         if (dim_row u1 = m \<and> dim_col u1 = m \<and> dim_row u2 = m \<and> dim_col u2 = m 
             \<and> Fs = u1 * Gs \<and> Gs = u2 * Fs)
          then rb gs
          else Code.abort (STR ''error in external lll invocation\<newline>f,g,u1,u2 are as follows\<newline>''
            + String.implode (show Fs) + STR ''\<newline>\<newline>''
            + String.implode (show Gs) + STR ''\<newline>\<newline>''
            + String.implode (show u1) + STR ''\<newline>\<newline>''
            + String.implode (show u2) + STR ''\<newline>\<newline>''
            ) (\<lambda> _. rb fs))
   | None \<Rightarrow> (if (n = m \<and> integer_equivalent n fs gs) then
       rb gs
      else Code.abort (STR ''error in external LLL invocation:\<newline>'' +
        (if n = m then STR ''reduced matrix does not span same lattice'' else 
          STR ''no certificate only allowed for square matrices'')) (\<lambda> _. rb fs))
    ))" 

definition short_vector_external :: "rat \<Rightarrow> int vec list \<Rightarrow> int vec" where
  "short_vector_external \<alpha> fs = (hd (reduce_basis_external \<alpha> fs))" 

instance bool :: prime_card
  by (standard, auto)

context LLL_with_assms
begin

lemma reduce_basis_external: assumes res: "reduce_basis_external \<alpha> fs_init = fs" 
  shows "reduced fs m" "LLL_invariant True m fs" 
  (* "lattice_of fs = lattice_of fs_init" is part of LLL_invariant *)
proof (atomize(full), goal_cases)
  case 1
  show ?case
  proof (cases "LLL_Impl.reduce_basis \<alpha> fs_init = fs")
    case True
    from reduce_basis[OF this] show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases fs_init)
      case Nil
      with res have "fs = []" unfolding reduce_basis_external_def by auto
      with False Nil have False by (simp add: LLL_Impl.reduce_basis_def)
      thus ?thesis ..
    next
      case (Cons f rest)
      from Cons fs_init len have dim_fs_n: "dim_vec f = n" by auto
      let ?ext = "external_lll_solver (map_prod integer_of_int integer_of_int (quotient_of \<alpha>)) 
        (map (map integer_of_int \<circ> list_of_vec) fs_init)" 
      note res = res[unfolded reduce_basis_external_def Cons Let_def list.case Code.abort_def dim_fs_n,
          folded Cons]
      from res False obtain gsi co where ext: "?ext = (gsi, co)" by (cases ?ext, auto)
      define gs where "gs = map (vec_of_list o map int_of_integer) gsi" 
      note res = res[unfolded ext option.simps split len dim_fs_n, folded gs_def]
      from res False have not: "(\<not> (length gs = m \<and> (\<forall>gi\<in>set gs. dim_vec gi = n))) = False" 
        by (auto split: if_splits)
      note res = res[unfolded this if_False]
      from not have gs: "set gs \<subseteq> carrier_vec n" 
         and len_gs: "length gs = m" by auto
      have "lattice_of gs = lattice_of fs_init \<and> LLL_with_assms n m gs \<alpha> \<and> LLL_Impl.reduce_basis \<alpha> gs = fs" 
      proof (cases co)
        case (Some pair)
        from res Some obtain u1i u2i where co: "co = Some (u1i, u2i)" by (cases co, auto)
        define u1 where "u1 = mat_of_rows_list m (map (map int_of_integer) u1i)"
        define u2 where "u2 = mat_of_rows_list m (map (map int_of_integer) u2i)" 
        note res = res[unfolded co option.simps split len dim_fs_n, folded u1_def u2_def gs_def]
        from res False 
        have u1: "u1 \<in> carrier_mat m m" 
          and u2: "u2 \<in> carrier_mat m m" 
          and prod1: "mat_of_rows n fs_init = u1 * mat_of_rows n gs" 
          and prod2: "mat_of_rows n gs = u2 * mat_of_rows n fs_init" 
          and gs_v: "LLL_Impl.reduce_basis \<alpha> gs = fs" 
          by (auto split: if_splits)
        from LLL_change_basis[OF gs len_gs u1 u2 prod1 prod2] gs_v
        show ?thesis by auto
      next
        case None
        from res[unfolded None option.simps] False
        have id: "fs = LLL_Impl.reduce_basis \<alpha> gs" and nm: "n = m" 
          and equiv: "integer_equivalent n fs_init gs" 
          by (auto split: if_splits)
        from LLL_change_basis_mat_inverse[OF gs len_gs[folded nm] nm[symmetric] equiv] id
        show ?thesis by auto
      qed
      hence id: "lattice_of gs = lattice_of fs_init" 
         and assms: "LLL_with_assms n m gs \<alpha>"
         and gs_fs: "LLL_Impl.reduce_basis \<alpha> gs = fs"  by auto
      from LLL_with_assms.reduce_basis[OF assms gs_fs]
      have red: "reduced fs m" and inv: "LLL.LLL_invariant n m gs \<alpha> True m fs" by auto
      from inv[unfolded LLL.LLL_invariant_def LLL.L_def id]
      have lattice: "lattice_of fs = lattice_of fs_init" by auto
      show ?thesis
      proof (intro conjI red lattice)
        show "LLL_invariant True m fs" using inv unfolding LLL.LLL_invariant_def LLL.L_def id .
      qed
    qed
  qed 
qed

lemma short_vector_external: assumes res: "short_vector_external \<alpha> fs_init = v"
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)"
  "v \<noteq> 0\<^sub>v j"
proof (atomize(full), goal_cases)
  case 1
  obtain fs where red: "reduce_basis_external \<alpha> fs_init = fs" by blast
  from res[unfolded short_vector_external_def red] have v: "v = hd fs" by auto
  from reduce_basis_external[OF red] 
  have red: "reduced fs m" and inv: "LLL_invariant True m fs" by blast+
  from basis_reduction_short_vector[OF inv v m0]
  show ?case by blast
qed
end

text \<open>Unspecified constant to easily enable/disable external lll solver in generated code\<close>

consts enable_external_lll_solver :: bool

definition short_vector_hybrid :: "rat \<Rightarrow> int vec list \<Rightarrow> int vec" where
  "short_vector_hybrid = (if enable_external_lll_solver then short_vector_external else short_vector)" 

definition reduce_basis_hybrid :: "rat \<Rightarrow> int vec list \<Rightarrow> int vec list" where
  "reduce_basis_hybrid = (if enable_external_lll_solver then reduce_basis_external else reduce_basis)" 


context LLL_with_assms
begin
lemma short_vector_hybrid: assumes res: "short_vector_hybrid \<alpha> fs_init = v"
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)"
  "v \<noteq> 0\<^sub>v j"
  using short_vector[of v, OF _ m0] short_vector_external[of v, OF _ m0]
    res[unfolded short_vector_hybrid_def]
  by (auto split: if_splits)

lemma reduce_basis_hybrid: assumes res: "reduce_basis_hybrid \<alpha> fs_init = fs" 
  shows "reduced fs m" "LLL_invariant True m fs" 
  using reduce_basis_external[of fs] reduce_basis[of fs] res[unfolded reduce_basis_hybrid_def]
  by (auto split: if_splits)
end



lemma lll_oracle_default_code[code]: 
  "external_lll_solver x = Code.abort (STR ''no implementation of external_lll_solver specified'') (\<lambda> _. external_lll_solver x)" 
  by simp

text \<open>By default, external solvers are disabled.
  For enabling an external solver, load it via a separate theory like \<^file>\<open>FPLLL_Solver.thy\<close>\<close>

overloading enable_external_lll_solver \<equiv> enable_external_lll_solver
begin
  definition enable_external_lll_solver where "enable_external_lll_solver = False"
end

definition "short_vector_test_hybrid xs = 
  (let ys = map (vec_of_list o map int_of_integer) xs
   in integer_of_int (sq_norm (short_vector_hybrid (3/2) ys)))" 
 
(* export_code short_vector_test_hybrid in Haskell module_name LLL *)
end
