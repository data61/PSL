(* Algebraic manipulations on matrices *)

(* Debugging: trace list of terms *)
fun string_of_terms ctxt ts =
    ts |> map (Syntax.pretty_term ctxt)
       |> Pretty.commas |> Pretty.block |> Pretty.string_of

(* Debugging: print term *)
fun trace_t ctxt s t =
    tracing (s ^ " " ^ (Syntax.string_of_term ctxt t))

(* Debugging: trace full theorem *)
fun trace_fullthm ctxt s th =
    tracing (s ^ " [" ^ (Thm.hyps_of th |> string_of_terms ctxt) ^
             "] ==> " ^ (Thm.prop_of th |> Syntax.string_of_term ctxt))

(* nat type *)
val natT = HOLogic.natT

(* Whether t is of the form a * b *)
fun is_times t =
  case t of
    Const (@{const_name times}, _) $ _ $ _ => true
  | _ => false

(* Whether t is of the form a + b *)
fun is_plus t =
  case t of
    Const (@{const_name plus}, _) $ _ $ _ => true
  | _ => false

(* Whether t is of the form a - b *)
fun is_minus t =
  case t of
    Const (@{const_name minus}, _) $ _ $ _ => true
  | _ => false

(* Whether t is of the form - a *)
fun is_uminus t =
  case t of
    Const (@{const_name uminus}, _) $ _ => true
  | _ => false

(* Given t of the form a (op) b, return the pair (a, b) *)
fun dest_binop t =
  case t of
    _ $ a $ b => (a, b)
  | _ => raise Fail "dest_binop"

(* Given t of the form f $ x, return the term x. *)
fun dest_arg t =
  case t of
    _ $ x => x
  | _ => raise Fail "dest_arg"

(* Return the first of two arguments of t. *)
fun dest_arg1 t =
  case t of
    _ $ arg1 $ _ => arg1
  | _ => raise Fail "dest_arg1"

(* Whether t is a matrix. *)
fun is_mat_type t =
  is_Type (fastype_of t) andalso
  (fastype_of t |> dest_Type |> fst) = "Matrix.mat"

(* Whether t is of the form c . A *)
fun is_smult_mat t =
  case t of
    Const (@{const_name smult_mat}, _) $ _ $ _ => true
  | _ => false

(* Whether t is of the form adjoint a *)
fun is_adjoint t =
  case t of
    Const (@{const_name mat_adjoint}, _) $ _ => true
  | _ => false

(* Whether t is of the form 1_m n *)
fun is_id_mat t =
  case t of
    Const (@{const_name one_mat}, _) $ _ => true
  | _ => false

(* Whether t is of the form 0_m n n *)
fun is_zero_mat t =
  case t of
    Const (@{const_name zero_mat}, _) $ _ $ _ => true
  | _ => false

(* Given a product in normal form, return the atomic components.
  E.g. strip_times (a * b * c * d) = [a, b, c, d]. *)
fun strip_times t =
  if is_times t then
    strip_times (dest_arg1 t) @ [dest_arg t]
  else
    [t]

(* Returns the term "carrier_mat n n", where t is a matrix providing the type. *)
fun carrier_mat n t =
  let
    val T = fastype_of t  (* 'a mat *)
    val Tset = HOLogic.mk_setT T  (* 'a mat set *)
  in
    Const (@{const_name carrier_mat}, natT --> natT --> Tset) $ n $ n
  end

(* Given n and t, returns the term "t : carrier n n" *)
fun mk_mem_carrier n t =
  HOLogic.mk_mem (t, carrier_mat n t)

(* Given n and t, returns the theorem [t : carrier n n]. t : carrier n n *)
fun assume_carrier ctxt n t =
  Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_mem_carrier n t)))

(* Given a term t, return t : carrier n n under the assumptions that the
  atomic components of t are in carrier n n.
  E.g. given t = a * b * c, returns
    [a : carrier n n, b : carrier n n, c : carrier n n]. a * b * c : carrier n n. *)
fun prod_in_carrier ctxt n t =
  if is_times t then
    let
      val (a, b) = dest_binop t
      val th1 = prod_in_carrier ctxt n a
      val th2 = prod_in_carrier ctxt n b
    in
      [th1, th2] MRS @{thm mult_carrier_mat}
    end
  else if is_plus t then
    let
      val (a, b) = dest_binop t
      val th1 = prod_in_carrier ctxt n a
      val th2 = prod_in_carrier ctxt n b
    in
      [th1, th2] MRS @{thm add_carrier_mat'}
    end
  else if is_uminus t then
    let
      val a = dest_arg t
      val th = prod_in_carrier ctxt n a
    in
      th RS @{thm uminus_carrier_mat}
    end
  else if is_minus t then
    let
      val (a, b) = dest_binop t
      val th1 = prod_in_carrier ctxt n a
      val th2 = prod_in_carrier ctxt n b
    in
      [th1, th2] MRS @{thm minus_carrier_mat'}
    end
  else if is_adjoint t then
    let
      val a = dest_arg t
      val th = prod_in_carrier ctxt n a
    in
      th RS @{thm adjoint_dim}
    end
  else if is_smult_mat t then
    let
      val a = dest_arg t
      val th = prod_in_carrier ctxt n a
    in
      th RS @{thm smult_carrier_mat}
    end
  else
    assume_carrier ctxt n t

(* Given theorem a = b, return theorem b = a *)
fun obj_sym th =
  th RS @{thm HOL.sym}

(* Given theorem a = b, return theorem a == b *)
fun to_meta_eq th =
  th RS @{thm HOL.eq_reflection}

(* Given theorem a == b, return theorem a = b *)
fun to_obj_eq th =
  th RS @{thm HOL.meta_eq_to_obj_eq}

fun rewr_cv ctxt n th ct =
  let
    val th = to_meta_eq th
    val pat = th |> Thm.concl_of |> dest_arg1 |> Thm.cterm_of ctxt
    val inst = Thm.match (pat, ct)
    val th = Thm.instantiate inst th
    val prems = map (fn prem => prod_in_carrier ctxt n (prem |> dest_arg |> dest_arg1))
                    (Thm.prems_of th)
  in
    prems MRS th
  end
  handle THM _ => let val _ = trace_fullthm ctxt "here" th in raise Fail "THM" end
     | Pattern.MATCH => let val _ = trace_fullthm ctxt "here" th in raise Fail "MATCH" end
  
(* Normalize (a_1 * ... * a_n) * (b_1 * ... * b_n) *)
fun assoc_times_norm ctxt n ct =
  let
    val t = Thm.term_of ct
    val (a, b) = dest_binop t
  in
    if is_smult_mat a then
      Conv.every_conv [
        rewr_cv ctxt n @{thm mult_smult_assoc_mat},
        Conv.arg_conv (assoc_times_norm ctxt n)] ct
    else if is_smult_mat b then
      Conv.every_conv [
        rewr_cv ctxt n @{thm mult_smult_distrib},
        Conv.arg_conv (assoc_times_norm ctxt n)] ct
    else if is_times b then
      Conv.every_conv [
        rewr_cv ctxt n (obj_sym @{thm assoc_mult_mat}),
        Conv.arg1_conv (assoc_times_norm ctxt n)] ct
    else if is_id_mat a then
      rewr_cv ctxt n @{thm left_mult_one_mat} ct
    else if is_id_mat b then
      rewr_cv ctxt n @{thm right_mult_one_mat} ct
    else
      Conv.all_conv ct
  end

(* Normalize (a_1 + ... + a_n) + b *)
fun assoc_plus_one_norm ctxt n ct =
  let
    val t = Thm.term_of ct
    val (a, b) = dest_binop t
  in
    if not (is_mat_type t) then
      Conv.all_conv ct
    else if is_plus a then
      if Term_Ord.term_ord (dest_arg a, b) = GREATER then
        Conv.every_conv [
          rewr_cv ctxt n @{thm swap_plus_mat},
          Conv.arg1_conv (assoc_plus_one_norm ctxt n)] ct
      else
        Conv.all_conv ct
    else
      if Term_Ord.term_ord (a, b) = GREATER then
        rewr_cv ctxt n @{thm comm_add_mat} ct
      else
        Conv.all_conv ct
  end

(* Normalize (a_1 + ... + a_n) + (b_1 + ... + b_n) *)
fun assoc_plus_norm ctxt n ct =
  let
    val t = Thm.term_of ct
    val (a, b) = dest_binop t
  in
    if not (is_mat_type t) then
      Conv.all_conv ct
    else if is_plus b then
      Conv.every_conv [
        rewr_cv ctxt n (obj_sym @{thm assoc_add_mat}),
        Conv.arg1_conv (assoc_plus_norm ctxt n),
        assoc_plus_one_norm ctxt n] ct
    else if is_zero_mat a then
      rewr_cv ctxt n @{thm left_add_zero_mat} ct
    else if is_zero_mat b then
      rewr_cv ctxt n @{thm right_add_zero_mat} ct
    else
      assoc_plus_one_norm ctxt n ct
  end

(* Normalization of c . (a_1 + ... + a_n) *)
fun smult_plus_norm ctxt n ct =
  let
    val t = Thm.term_of ct
  in
    if is_plus (dest_arg t) then
      Conv.every_conv [
        rewr_cv ctxt n @{thm add_smult_distrib_left_mat},
        Conv.arg1_conv (smult_plus_norm ctxt n)] ct
    else
      Conv.all_conv ct
  end

(* Normalize (a_1 + ... + a_n) * b *)
fun norm_mult_poly_monomial ctxt n ct =
  let
    val t = Thm.term_of ct
  in
    if is_plus (dest_arg1 t) then
      Conv.every_conv [
        rewr_cv ctxt n @{thm add_mult_distrib_mat},
        Conv.arg1_conv (norm_mult_poly_monomial ctxt n),
        Conv.arg_conv (assoc_times_norm ctxt n),
        assoc_plus_norm ctxt n] ct
    else
      assoc_times_norm ctxt n ct
  end

(* Normalize (a_1 + ... + a_n) * (b_1 + ... + b_n) *)
fun norm_mult_polynomials ctxt n ct =
  let
    val t = Thm.term_of ct
  in
    if is_plus (dest_arg t) then
      Conv.every_conv [
        rewr_cv ctxt n @{thm mult_add_distrib_mat},
        Conv.arg1_conv (norm_mult_polynomials ctxt n),
        Conv.arg_conv (norm_mult_poly_monomial ctxt n),
        assoc_plus_norm ctxt n] ct
    else
      norm_mult_poly_monomial ctxt n ct
  end   

fun is_trace t =
  case t of
    Const (@{const_name trace}, _) $ _ => true
  | _ => false

(* Normalize trace (a_1 * ... * a_n) *)
fun norm_trace_times ctxt n ct =
  let
    val tt = Thm.term_of ct
    val t = dest_arg tt
    val ts = strip_times t
    val (rest, last) = split_last ts
  in
    if exists (fn t' => Term_Ord.term_ord (last, t') = LESS) rest then
      Conv.every_conv [
        rewr_cv ctxt n @{thm trace_comm},
        Conv.arg_conv (assoc_times_norm ctxt n),
        norm_trace_times ctxt n] ct
    else
      Conv.all_conv ct
  end

(* Normalize trace (a_1 + ... + a_n) *)
fun norm_trace_plus ctxt n ct =
  let
    val tt = Thm.term_of ct
    val t = dest_arg tt
  in
    if is_plus t then
      Conv.every_conv [
        rewr_cv ctxt n @{thm trace_add_linear},
        Conv.arg1_conv (norm_trace_plus ctxt n),
        Conv.arg_conv (norm_trace_times ctxt n)] ct
    else
      norm_trace_times ctxt n ct
  end

(* Normalize with respect to associativity. *)
fun assoc_norm ctxt n ct =
  let
    val t = Thm.term_of ct
  in
    if is_times t then
      Conv.every_conv [
        Conv.binop_conv (assoc_norm ctxt n),
        norm_mult_polynomials ctxt n] ct
    else if is_plus t then
      Conv.every_conv [
        Conv.binop_conv (assoc_norm ctxt n),
        assoc_plus_norm ctxt n] ct
    else if is_smult_mat t then
      Conv.every_conv [
        Conv.arg_conv (assoc_norm ctxt n),
        smult_plus_norm ctxt n] ct
    else if is_minus t then
      Conv.every_conv [
        rewr_cv ctxt n @{thm minus_add_uminus_mat},
        assoc_norm ctxt n] ct
    else if is_uminus t then
      Conv.every_conv [
        rewr_cv ctxt n @{thm uminus_mat},
        assoc_norm ctxt n] ct
    else if is_adjoint t then
      if is_times (dest_arg t) then
        Conv.every_conv [
          rewr_cv ctxt n @{thm adjoint_mult},
          assoc_norm ctxt n] ct
      else if is_adjoint (dest_arg t) then
        Conv.every_conv [
          Conv.rewr_conv (to_meta_eq @{thm adjoint_adjoint}),
          assoc_norm ctxt n] ct
      else
        Conv.all_conv ct
    else if is_trace t then
      Conv.every_conv [
        Conv.arg_conv (assoc_norm ctxt n),
        norm_trace_plus ctxt n] ct
    else
      Conv.all_conv ct
  end

(* Given equality between two products of matrices, attempt to prove
  the equality by normalization.
  Example: given A * (B * C) = (A * B) * C, return the theorem stating
  the equality, with hypothesis A, B, C : carrier_mat n. *)
fun prove_by_assoc_norm ctxt n t =
  let
    val _ = trace_t ctxt "To show equation:" t
    val (a, b) = dest_binop t
    val norm1 = assoc_norm ctxt n (Thm.cterm_of ctxt a)
    val norm2 = assoc_norm ctxt n (Thm.cterm_of ctxt b)
  in
    if Thm.rhs_of norm1 aconvc Thm.rhs_of norm2 then
      let
        val res = Thm.transitive norm1 (Thm.symmetric norm2)
      in
        res |> to_obj_eq
      end
    else
      let
        val _ = trace_t ctxt "Left side is:" (Thm.term_of (Thm.rhs_of norm1))
        val _ = trace_t ctxt "Right side is:" (Thm.term_of (Thm.rhs_of norm2))
      in
        raise Fail "Normalization are not equal."
      end
  end

fun prove_by_assoc_norm_tac n ctxt state =
  let
    val n = Syntax.read_term ctxt n
    val subgoals = Thm.prems_of state
  in
    if null subgoals then Seq.empty else
      let
        (* Subgoal to be proved, in the form [A1, ..., An] ==> s = t *)
        val subgoal = state |> Drule.cprems_of |> hd
        val (cprems, cconcl) = (Drule.strip_imp_prems subgoal, Drule.strip_imp_concl subgoal)
        val concl = HOLogic.dest_Trueprop (Thm.term_of cconcl)

        (* Theorem A1 ==> ... ==> An ==> s = t, but possibly with addtional
           assumptions in Thm.hyps_of subgoal_th *)
        val subgoal_th = fold Thm.implies_intr (rev cprems) (prove_by_assoc_norm ctxt n concl)

        val chyps = Thm.chyps_of subgoal_th
        val res = Thm.implies_elim state subgoal_th
      in
        Seq.single (fold Thm.implies_intr chyps res)
      end
  end

val mat_assoc_method : (Proof.context -> Method.method) context_parser =
  Scan.lift Parse.term >> (fn n => fn ctxt => (SIMPLE_METHOD (prove_by_assoc_norm_tac n ctxt)))
