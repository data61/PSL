signature ORDER_GENERATOR =
sig
  (* 1. pair of result creates the rhs for the < operator, idx 0 results in < *)
  (* 2. pair of result contains list of arguments for recursor, each indexed by
        first the constructor number
        second the index number
  *)
  (*                          dtyp_info            order   idx        *)
  val mk_less_idx : theory -> Old_Datatype_Aux.info -> sort -> (int -> term) * (term * int * int) list;

  (* given an idx, x, and y, it creates x <= y *)
  (*                             dtyp_info            order   idx     x       y   *)
  val mk_less_eq_idx : theory -> Old_Datatype_Aux.info -> sort -> (int -> term -> term -> term);

  (* proves the transitivity theorems (for \<le> and < ) *)
  val mk_transitivity_thms : theory -> Old_Datatype_Aux.info -> thm * thm;

  (* proves the theorem (x < y) = (x \<le> y \<and> \<not> y \<le> x) *)
  val mk_less_le_not_le_thm : theory -> Old_Datatype_Aux.info -> thm

  (* proves the theorem (x \<le> x) *)
  val mk_le_refl_thm : theory -> Old_Datatype_Aux.info -> thm

  (* proves the theorem (x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y) *)
  (* takes as input the transitivity thm for < and the less_le_not_le thm *)
  val mk_antisym_thm : theory -> Old_Datatype_Aux.info -> thm -> thm -> thm

  (* proves the theorem (x \<le> y \<or> y \<le> x) *)
  val mk_linear_thm : theory -> Old_Datatype_Aux.info -> thm

  (* proves all four theorems which are required for orders: trans, refl, antisym, less_le_not_le *)
  val mk_order_thms : theory -> Old_Datatype_Aux.info -> thm list

  (* creates and registers (0 = ord, 1 = order, 2 = linear-order) for datatype *)
  val derive : int -> string -> string -> theory -> theory
end


structure Order_Generator : ORDER_GENERATOR =
struct

open Derive_Aux

val less_name = @{const_name "Orderings.less"}

(* construct free variable x_i *)
fun mk_free_tysubst_i typ_subst x i ty = Free (x ^ string_of_int i, ty |> typ_subst)

fun mk_less_idx thy info sort =
  let
    val typ_subst = typ_subst_for_sort thy info sort
    val descr = #descr info
    fun typ_of dty = Old_Datatype_Aux.typ_of_dtyp descr dty |> typ_subst
    val rec_names = #rec_names info
    val mk_free_i = mk_free_tysubst_i typ_subst
    fun rec_idx i dtys = dt_number_recs (take i dtys) |> fst
    fun mk_rhss (idx,(ty_name,_,cons)) =
      let
        val ty = typ_of (Old_Datatype_Aux.DtRec idx)
        val linfo = BNF_LFP_Compat.the_info thy [] ty_name
        val case_name = #case_name linfo
        fun mk_rhs (i,(_,dtysi)) =
          let
            val lvars = map_index (fn (i,dty) => mk_free_i "x_" i (typ_of dty)) dtysi
            fun res_var (i,oc) = mk_free_i "res_" oc (typ_of (Old_Datatype_Aux.DtRec i) --> @{typ bool});
            val res_vars = dt_number_recs dtysi
                     |> snd
                     |> map res_var
            fun mk_case (j,(_,dtysj)) =
              let
                val rvars = map_index (fn (i,dty) => mk_free_i "y_" i (typ_of dty)) dtysj
                val x = nth lvars
                val y = nth rvars
                fun combine_dts [] = @{term False}
                  | combine_dts ((_,c) :: []) = c
                  | combine_dts ((i,c) :: ics) = HOLogic.mk_disj (c, HOLogic.mk_conj (HOLogic.mk_eq (x i, y i), combine_dts ics))
                fun less_of_dty (i,Old_Datatype_Aux.DtRec j) = res_var (j,rec_idx i dtysj) $ y i
                  | less_of_dty (i,_) =
                      let
                        val xi = x i
                        val ty = Term.type_of xi
                        val less = Const (less_name, ty --> ty --> @{typ bool})
                      in less $ xi $ y i end
                val rhs =
                  if i < j then @{term True}
                  else if i > j then @{term False}
                  else map_index less_of_dty dtysi
                    |> map_index I
                    |> combine_dts
                val lam_rhs = fold lambda (rev rvars) rhs
              in lam_rhs end
            val cases = map_index mk_case cons
            val case_ty = (map type_of cases @ [ty]) ---> @{typ bool}
            val rhs_case = list_comb (Const (case_name, case_ty), cases)
            val rhs = fold lambda (rev (lvars @ res_vars)) rhs_case
          in rhs end
        val rec_args = map_index (fn (i,c) => (mk_rhs (i,c),i,idx)) cons
      in rec_args end
    val nrec_args = maps mk_rhss descr
    val rec_args = map #1 nrec_args
    fun mk_rec i =
      let
        val ty = typ_of (Old_Datatype_Aux.DtRec i)
        val rec_ty = map type_of rec_args @ [ty,ty] ---> @{typ bool}
        val rec_name = nth rec_names i
        val rhs = list_comb (Const (rec_name, rec_ty), rec_args)
      in rhs end
  in (mk_rec,nrec_args) end

fun mk_less_eq_idx thy info sort idx x y =
  mk_less_idx thy info sort
  |> fst
  |> (fn less => HOLogic.mk_disj (less idx $ x $ y, HOLogic.mk_eq (x,y)))

fun mk_prop_trm thy info sort
  (gen : (int -> term) -> (term -> term -> term)list -> term list * term list) =
  let
    fun main idx =
      let
        val xs = mk_xs thy info sort idx
        fun less a b = (mk_less_idx thy info sort |> fst) idx $ a $ b
        val less_eq = mk_less_eq_idx thy info sort idx
      in gen xs [less, less_eq] end
  in #descr info
    |> map (fst #> main)
  end

fun mk_prop_major_trm thy info sort gen =
  mk_prop_trm thy info sort gen |> prop_trm_to_major_imp


fun mk_trans_thm_trm thy info =
  mk_prop_trm thy info @{sort "order"}
  (fn xs => fn [less,_] =>
    let val (x,y,z) = (xs 1, xs 2, xs 3)
    in ([less x y, less y z, less x z], [x,y,z]) end)

fun mk_trans_eq_thm_trm thy info =
  mk_prop_major_trm thy info @{sort "order"}
  (fn xs => fn [_, lesseq] =>
    let val (x,y,z) = (xs 1, xs 2, xs 3)
    in ([lesseq x y, lesseq y z, lesseq x z], [x,y,z]) end)

fun mk_less_disj mk_less px py dtys =
  let
    fun build_disj [] _ _ = @{term False}
      | build_disj (px :: xs) (py :: ys) (dty :: dtys) =
          HOLogic.mk_disj (mk_less dty px py, HOLogic.mk_conj (HOLogic.mk_eq (px,py),build_disj xs ys dtys))
  in
    HOLogic.mk_Trueprop (build_disj px py dtys)
  end;

fun simps_of_info info = #case_rewrites info @ #rec_rewrites info @ #inject info @ #distinct info

fun mk_transitivity_thms thy (info : Old_Datatype_Aux.info) =
  let
    val ctxt = Proof_Context.init_global thy
    (* first prove transitivity of < *)
    val trans_props = mk_trans_thm_trm thy info
    val sort = @{sort "order"}
    val (mk_rec,nrec_args) = mk_less_idx thy info sort
    val typ_subst = typ_subst_for_sort thy info sort
    val descr = #descr info
    fun typ_of dty = Old_Datatype_Aux.typ_of_dtyp descr dty |> typ_subst
    fun mk_less_term (Old_Datatype_Aux.DtRec i) = mk_rec i
      | mk_less_term dty =
          let
            val ty = typ_of dty
          in Const (less_name, ty --> ty --> @{typ bool}) end;
    fun mk_less dty x y = mk_less_term dty $ x $ y;
    val ind_thm = #induct info
    val trans_thm_of_tac = inductive_thm thy trans_props ind_thm sort
    fun ind_case_tac ctxt i hyps [xy,yz] params_x [y,z] =
      let
        val (j,idx) = nth nrec_args i |> (fn (_,j,idx) => (j,idx))
        val linfo = nth descr idx |> (fn (_,(ty_name,_,_)) => ty_name)
          |> BNF_LFP_Compat.the_info thy []
        fun solve_with_tac ctxt thms =
          let
            val simp_ctxt =
              (ctxt
                |> Context_Position.set_visible false
                |> put_simpset my_simp_set)
                addsimps (simps_of_info info @ simps_of_info linfo @ thms)
          in mk_solve_with_tac simp_ctxt thms (asm_full_simp_tac simp_ctxt 1) end

        fun case_tac ctxt y_z = mk_case_tac ctxt [[SOME y_z]] (#exhaust linfo)
        fun sub_case_tac (ctxt,k,prems,iparams_y) =
          let
            val case_hyp_y = hd prems
            fun sub_sub_case_tac (ctxt,l,prems,iparams_z) =
              let
                val case_hyp_z = hd prems
                val comp_eq = [case_hyp_z, case_hyp_y, xy, yz]
              in
                (if not (j = l andalso l = k)
                then
                  K (solve_with_tac ctxt comp_eq)
                else
                  let
                    val params_y = map (snd #> Thm.term_of) iparams_y
                    val params_z = map (snd #> Thm.term_of) iparams_z
                    val c_info = nth descr idx |> snd |> (fn (_,_,info) => nth info j)
                    val pdtys = snd c_info
                    val build_disj = mk_less_disj mk_less
                    val xy' = build_disj params_x params_y pdtys
                    val yz' = build_disj params_y params_z pdtys
                    fun disj_thm t = Goal.prove_future ctxt [] [] t (K (solve_with_tac ctxt comp_eq))
                    val xy_disj = disj_thm xy'
                    val yz_disj = disj_thm yz'
                    fun solve_tac xy _ [] _ _ _ _ _ = K (solve_with_tac ctxt [xy])
                      | solve_tac xy yz (px :: pxs) (py :: pys) (pz :: pzs) (dty :: dtys) eqs ihyps =
                          let
                            fun case_tac_disj ctxt disj tac =
                              mk_case_tac ctxt [] (@{thm disjE} OF [disj]) (fn (ctxt,ii,hyps,_) => tac ii ctxt (List.last hyps))
                            fun yz_case_tac ctxt = case_tac_disj ctxt yz
                            val rec_type = (fn Old_Datatype_Aux.DtRec _ => true | _ => false) dty
                            fun xy_tac ii ctxt hyp_xy =
                              if ii = 1 (* right branch, px = py and pxs < pys *)
                              then
                                let
                                  val eq_term = HOLogic.mk_eq (px,py) |> HOLogic.mk_Trueprop
                                  val eq_xy_thm = Goal.prove_future ctxt [] [] eq_term (K (solve_with_tac ctxt [hyp_xy]))
                                  val xy'_thm = Goal.prove_future ctxt [] [] (build_disj pxs pys dtys) (K (solve_with_tac ctxt [hyp_xy]))
                                  fun yz_tac jj ctxt hyp_yz =
                                  if jj = 1 (* right branch, py = pz and pys < pzs *)
                                    (* = and = *)
                                  then
                                    let
                                      val eq_term = HOLogic.mk_eq (px,pz) |> HOLogic.mk_Trueprop
                                      val eq_thm  = Goal.prove_future ctxt [] [] eq_term (K (solve_with_tac ctxt [eq_xy_thm,hyp_yz]))
                                      val yz'_thm = Goal.prove_future ctxt [] [] (build_disj pys pzs dtys) (K (solve_with_tac ctxt [hyp_yz]))
                                      val drop_hyps = if rec_type then tl else I
                                    in
                                      solve_tac xy'_thm yz'_thm pxs pys pzs dtys (eq_thm :: eqs) (drop_hyps ihyps) 1
                                    end
                                  else (* left branch, py < pz *)
                                    (* = and < *)
                                    let
                                      val xz_term = mk_less dty px pz |> HOLogic.mk_Trueprop
                                      val xz_thm  = Goal.prove_future ctxt [] [] xz_term (K (solve_with_tac ctxt [hyp_xy,hyp_yz]))
                                    in
                                      solve_with_tac ctxt (xz_thm :: case_hyp_z :: eqs)
                                    end
                                in
                                  yz_case_tac ctxt yz_tac
                                end
                              else (* left branch, px < py *)
                                let
                                  val xz_term = mk_less dty px pz |> HOLogic.mk_Trueprop
                                  fun yz_tac jj ctxt hyp_yz =
                                    if jj = 1 (* right branch, py = pz *)
                                      (* < and = *)
                                    then
                                      let
                                        val xz_thm = Goal.prove_future ctxt [] [] xz_term (K (solve_with_tac ctxt [hyp_xy,hyp_yz]))
                                      in
                                        solve_with_tac ctxt (xz_thm :: case_hyp_z :: eqs)
                                      end
                                    else (* left branch, py < pz *)
                                      (* < and < *)
                                      let
                                        val trans_thm = if rec_type then hd ihyps else @{thm less_trans}
                                        val tac = resolve_tac ctxt [trans_thm OF [hyp_xy,hyp_yz]] 1
                                        val xz_thm = Goal.prove_future ctxt [] [] xz_term (K tac)
                                      in
                                        solve_with_tac ctxt (xz_thm :: case_hyp_z :: eqs)
                                      end
                                in
                                  yz_case_tac ctxt yz_tac
                                end;
                            val xy_case_tac = case_tac_disj ctxt xy xy_tac
                          in
                            K (my_print_tac ctxt ("another case: ") THEN xy_case_tac)
                          end
                  in
                    K (my_print_tac ctxt "recursive case: ")
                    THEN' solve_tac xy_disj yz_disj params_x params_y params_z pdtys [] hyps
                  end
                ) 1
              end
          in
            my_print_tac ctxt ("consider constructor " ^ string_of_int k) THEN
            (if k >= j then case_tac ctxt z sub_sub_case_tac else
               solve_with_tac ctxt [case_hyp_y,xy])
          end (* end sub_case tac *)
      in
        my_print_tac ctxt ("start induct " ^ string_of_int i) THEN case_tac ctxt y sub_case_tac
      end (* end ind_case tac *)
    val trans_thm =  trans_thm_of_tac ind_case_tac
    val (trans_eq_trm,vars) = mk_trans_eq_thm_trm thy info
    val inst_trans = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) vars) trans_thm
    val trans_eq_vars_string = map (dest_Free #> fst) vars
    fun tac_to_eq_thm tac = Goal.prove_global_future thy trans_eq_vars_string [] trans_eq_trm (K tac)
    val eq_tac = mk_solve_with_tac ctxt [inst_trans] (blast_tac ctxt 1)
    val trans_eq_thm = tac_to_eq_thm eq_tac
  in
    (trans_thm,trans_eq_thm)
  end

val mk_binary_less_thm = mk_binary_thm mk_prop_trm mk_less_idx less_name

fun mk_less_le_not_le_thm thy info =
  let
    val sort = @{sort "order"}
    (* main property: x < y \<Longrightarrow> \<not> y \<le> x *)
    fun prop_gen xs [less,lesseq] =
      let
        val (x,y) = (xs 1, xs 2)
      in ([less x y, lesseq y x |> HOLogic.mk_not], [x,y]) end
    fun main_tac ctxt ih_hyps ih_prems y_prem solve_with_tac _ params_x params_y c_info mk_less =
      let
        val pdtys = snd c_info
        val comp_eq = y_prem :: ih_prems
        val build_disj = mk_less_disj mk_less
        val xy' = build_disj params_x params_y pdtys
        val xy_disj = Goal.prove_future ctxt [] [] xy' (K (solve_with_tac ctxt comp_eq))
        fun solve_tac ctxt xy [] _ _ _ _ = solve_with_tac ctxt [xy]
          | solve_tac ctxt xy (px :: pxs) (py :: pys) (dty :: dtys) eqs ihyps =
              let
                val xs_ys = build_disj pxs pys dtys
                val x_eq_y = HOLogic.mk_eq (px,py)
                val x_less_y = mk_less dty px py
                val disj2 =
                  HOLogic.mk_disj (x_less_y, HOLogic.mk_conj (HOLogic.mk_not x_less_y, HOLogic.mk_conj( x_eq_y, HOLogic.dest_Trueprop xs_ys)))
                  |> HOLogic.mk_Trueprop
                val disj2_thm = Goal.prove_future ctxt [] [] disj2 (K (Method.insert_tac ctxt [xy] 1 THEN blast_tac ctxt 1))
                fun case_tac_disj disj tac =
                  mk_case_tac ctxt [] (@{thm disjE} OF [disj]) (fn (ctxt,ii,hyps,_) => tac ii ctxt (List.last hyps))
                val rec_type = (fn Old_Datatype_Aux.DtRec _ => true | _ => false) dty
                fun xy_tac ii ctxt hyp_xy =
                  if ii = 1
                  then (* right branch, px = py and \<not> px < py and pxs < pys *)
                    let
                      val eq_term = x_eq_y |> HOLogic.mk_Trueprop
                      val eq_xy_thm = Goal.prove_future ctxt [] [] eq_term (K (solve_with_tac ctxt [hyp_xy]))
                      val xy'_thm = Goal.prove_future ctxt [] [] xs_ys (K (solve_with_tac ctxt [hyp_xy]))
                      val yx_thm =
                        Goal.prove_future ctxt [] [] (mk_less dty py px |> HOLogic.mk_not |> HOLogic.mk_Trueprop)
                        (K (solve_with_tac ctxt [hyp_xy]))
                      val ihyps' = if rec_type then tl ihyps else ihyps
                      val solve_rec = solve_tac ctxt xy'_thm pxs pys dtys (eq_xy_thm :: yx_thm :: eqs) ihyps'
                    in
                      solve_rec
                    end
                  else (* left branch, px < py *)
                       (* hence \<not> py \<le> px (yx_thm) *)
                    let
                      val yx = HOLogic.mk_disj (mk_less dty py px, HOLogic.mk_eq (py,px)) |> HOLogic.mk_not |> HOLogic.mk_Trueprop
                      val tac = if rec_type then solve_with_tac ctxt [hd ihyps OF [hyp_xy]] else solve_with_tac ctxt [hyp_xy]
                      val yx_thm = Goal.prove_future ctxt [] [] yx (K tac)
                    in
                      solve_with_tac ctxt (yx_thm :: y_prem :: eqs)
                    end;
              in
                case_tac_disj disj2_thm xy_tac
              end (* end solve tac *)
      in
        (solve_tac ctxt xy_disj params_x params_y pdtys [] ih_hyps : tactic)
      end (* end main_tac *)
    val main_thm = mk_binary_less_thm thy info prop_gen sort main_tac
    val ctxt = Proof_Context.init_global thy
    val (thm_trm,vars) = mk_prop_major_trm thy info sort (fn xs => fn [less,lesseq] =>
      let val (x,y) = (xs 1, xs 2)
      in
        ([HOLogic.mk_eq (less x y,HOLogic.mk_conj (lesseq x y, lesseq y x |> HOLogic.mk_not))], [x,y])
      end)
    val inst_thm = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) vars) main_thm
    val vars_strings = map (dest_Free #> fst) vars
    val thm =
      Goal.prove_future ctxt vars_strings [] thm_trm
        (K (Method.insert_tac ctxt [inst_thm] 1 THEN blast_tac ctxt 1))
  in
    thm
  end

fun mk_le_refl_thm thy info =
  let
    val sort = @{sort "order"}
    (* x \<le> x *)
    val ctxt = Proof_Context.init_global thy
    val (thm_trm,vars) = mk_prop_major_trm thy info sort (fn xs => fn [_,lesseq] =>
      let val x = xs 1
      in
        ([lesseq x x],[x])
      end)
    val vars_strings = map (dest_Free #> fst) vars
  in
    Goal.prove_future ctxt vars_strings [] thm_trm (K (blast_tac ctxt 1))
  end

fun mk_antisym_thm thy info trans_thm less_thm =
  let
    val sort = @{sort "order"}
    (* x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y *)
    val ctxt = Proof_Context.init_global thy
    val (thm_trm,vars) = mk_prop_major_trm thy info sort (fn xs => fn [_,lesseq] =>
      let val (x,y) = (xs 1, xs 2)
      in
        ([lesseq x y, lesseq y x, HOLogic.mk_eq (x,y)],[x,y])
      end)
    val vars_strings = map (dest_Free #> fst) vars
    val tvars = vars @ [hd vars]
    val lvars = [hd vars,hd vars]
    fun inst_thm vars thm = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) vars) thm
    val inst_trans = inst_thm tvars trans_thm
    val inst_less = inst_thm lvars less_thm
    val res =
      Goal.prove_future ctxt vars_strings [] thm_trm
        (K (Method.insert_tac ctxt [inst_trans,inst_less] 1 THEN blast_tac ctxt 1))
  in
    res
  end

fun mk_order_thms thy info =
  let
    val (trans,trans_eq) = mk_transitivity_thms thy info
    val less = mk_less_le_not_le_thm thy info
    val refl = mk_le_refl_thm thy info
    val antisym = mk_antisym_thm thy info trans less
  in
    [trans_eq,less,refl,antisym]
  end


fun mk_linear_thm thy info =
  let
    val sort = @{sort "linorder"}
    (* main property: x = y \<or> x < y \<or> y < x *)
    fun prop_gen xs [less,_] =
      let val (x,y) = (xs 1, xs 2)
      in
        ([HOLogic.mk_disj (HOLogic.mk_eq (x,y),HOLogic.mk_disj(less x y, less y x))],[x,y])
      end
    fun main_tac ctxt ih_hyps _ y_prem solve_with_tac _ params_x params_y c_info mk_less =
      let
        val pdtys = snd c_info
        fun solve_tac [] _ _ eqs _ = solve_with_tac ctxt eqs
          | solve_tac (px :: pxs) (py :: pys) (dty :: dtys) eqs ihyps =
              let
                val less = mk_less dty
                val x_eq_y = HOLogic.mk_eq (px,py)
                val disj_trm = HOLogic.mk_disj (x_eq_y,HOLogic.mk_disj(less px py, less py px)) |> HOLogic.mk_Trueprop
                val rec_type = (fn Old_Datatype_Aux.DtRec _ => true | _ => false) dty
                val disj_thm' = if rec_type then hd ihyps else @{thm linear_cases}
                val disj_tac = resolve_tac ctxt [disj_thm'] 1
                val disj_thm = Goal.prove_future ctxt [] [] disj_trm (K (disj_tac))
                fun case_tac_disj disj tac =
                  mk_case_tac ctxt [] (@{thm disjE} OF [disj]) (fn (ctxt,ii,hyps,_) => tac ii ctxt (List.last hyps))
                fun eq_less_less_tac ii _ eq_less =
                  if ii = 0
                  then (* left branch, px = py *)
                    let
                      val ihyps' = if rec_type then tl ihyps else ihyps
                      val solve_rec = solve_tac pxs pys dtys (eq_less :: eqs) ihyps'
                    in
                      solve_rec
                    end
                  else (* right branch, px < py \<or> py < px *)
                    let
                      fun less_tac _ _ less = solve_with_tac ctxt (less :: eqs)
                    in
                      case_tac_disj eq_less less_tac
                    end;
              in
                case_tac_disj disj_thm eq_less_less_tac
              end (* end solve tac *)
      in
        (solve_tac params_x params_y pdtys [y_prem] ih_hyps : tactic)
      end (* end main tac *)
    val main_thm = mk_binary_less_thm thy info prop_gen sort main_tac
    val ctxt = Proof_Context.init_global thy
    (* x \<le> y \<or> y \<le> x *)
    val (thm_trm,vars) = mk_prop_major_trm thy info sort (fn xs => fn [_,lesseq] =>
      let val (x,y) = (xs 1, xs 2)
      in
        ([HOLogic.mk_disj (lesseq x y,lesseq y x)],[x,y])
      end)
    val inst_thm = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) vars) main_thm
    val vars_strings = map (dest_Free #> fst) vars
    val thm =
      Goal.prove_future ctxt vars_strings [] thm_trm
        (K (Method.insert_tac ctxt [inst_thm] 1 THEN blast_tac ctxt 1))
  in
    thm
  end

fun derive kind dtyp_name _ thy =
  let
    val tyco = dtyp_name

    (* first register in class ord *)
    val base_name = Long_Name.base_name tyco
    val _ = writeln ("creating orders for datatype " ^ base_name)
    val sort = @{sort ord}
    val info = BNF_LFP_Compat.the_info thy [] tyco
    val vs_of_sort =
      let val i = BNF_LFP_Compat.the_spec thy tyco |> #1
      in fn sort => map (fn (n,_) => (n, sort)) i end
    val vs = vs_of_sort sort
    val less_rhs = mk_less_idx thy info sort |> fst |> (fn x => x 0)
    val ty = Term.fastype_of less_rhs |> Term.dest_Type |> snd |> hd
    fun mk_binrel_def T = mk_def (T --> T --> HOLogic.boolT)
    val less_def = mk_binrel_def ty @{const_name less} less_rhs
    val x = Free ("x",ty)
    val y = Free ("y",ty)
    val less_eq_rhs = lambda x (lambda y (HOLogic.mk_disj (less_rhs $ x $ y, HOLogic.mk_eq (x,y))))
    val less_eq_def = mk_binrel_def ty @{const_name less_eq} less_eq_rhs
    val ((less_thm,less_eq_thm),lthy) = Class.instantiation ([tyco],vs,sort) thy
      |> define_overloaded ("less_" ^ base_name ^ "_def", less_def)
      ||>> define_overloaded ("less_eq_" ^ base_name ^ "_def", less_eq_def)
    val less_thms = [less_thm, less_eq_thm]

    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt []) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class ord")

    (* next register in class order *)
    val thy'' =
      if kind < 1 then thy'
      else
        let
          val sort = @{sort order}
          val vs = vs_of_sort sort
          val [trans_eq,less,refl,antisym] = mk_order_thms thy info
          val lthy = Class.instantiation ([tyco],vs,sort) thy'

          fun order_tac ctxt =
            my_print_tac ctxt "enter order" THEN
            unfold_tac ctxt less_thms THEN
            my_print_tac ctxt "after unfolding" THEN
            resolve_tac ctxt [less] 1 THEN
            my_print_tac ctxt "after less" THEN
            resolve_tac ctxt [refl] 1 THEN
            my_print_tac ctxt "after refl" THEN
            resolve_tac ctxt [trans_eq] 1 THEN assume_tac ctxt 1 THEN assume_tac ctxt 1 THEN
            my_print_tac ctxt "after trans" THEN
            resolve_tac ctxt [antisym] 1 THEN assume_tac ctxt 1 THEN assume_tac ctxt 1
          val thy'' =
            Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [] THEN order_tac ctxt) lthy
          val _ = writeln ("registered " ^ base_name ^ " in class order")
        in thy'' end

    (* next register in class linorder *)
    val thy''' =
      if kind < 2 then thy''
      else
        let
          val sort = @{sort linorder}
          val vs = vs_of_sort sort
          val lthy = Class.instantiation ([tyco],vs,sort) thy''
          val linear = mk_linear_thm thy info
          fun order_tac ctxt =
            unfold_tac ctxt less_thms THEN
            resolve_tac ctxt [linear] 1
          val thy''' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [] THEN order_tac ctxt) lthy
          val _ = writeln ("registered " ^ base_name ^ " in class linorder")
        in thy''' end

  in thy''' end

val _ =
  Theory.setup
   (Derive_Manager.register_derive "ord" "derives ord for a datatype" (derive 0) #>
    Derive_Manager.register_derive "order" "derives an order for a datatype" (derive 1) #>
    Derive_Manager.register_derive "linorder" "derives a linear order for a datatype" (derive 2))

end
