signature HOL_DATATYPE = sig
  val mk_typ: bool -> typ -> term
  val mk_dt_def: Proof.context -> string -> term
end

structure HOL_Datatype : HOL_DATATYPE = struct

fun check_sort [@{class type}] = ()
  | check_sort _ = error "non-standard sorts are not supported"

fun mk_tvar ((name, idx), sort) =
  (check_sort sort; mk_name (name ^ "." ^ Value.print_int idx))

fun mk_tfree (name, sort) =
  (check_sort sort; mk_name name)

fun mk_typ schematic t =
  let
    fun aux (Type (typ, args)) =
          @{const TApp} $ mk_name typ $ HOLogic.mk_list @{typ typ} (map aux args)
      | aux (TVar tvar) =
          if schematic then
            @{const TVar} $ mk_tvar tvar
          else
            error "schematic type variables are not supported"
      | aux (TFree tfree) =
          if schematic then
            error "free type variables are not supported"
          else
            @{const TVar} $ mk_tfree tfree
  in aux t end

fun mk_dt_def ctxt typ =
  let
    val {ctrs, T, ...} = the (Ctr_Sugar.ctr_sugar_of ctxt typ)

    val tparams =
      dest_Type T |> snd
      |> map (mk_tvar o dest_TVar)
      |> HOLogic.mk_list @{typ name}

    fun mk_ctr ctr =
      let
        val (name, typ) = dest_Const ctr
        val params = strip_type typ |> fst |> map (mk_typ true) |> HOLogic.mk_list @{typ typ}
      in (mk_name name, params) end

    val ctrs =
      map mk_ctr ctrs
      |> mk_fmap (@{typ name}, @{typ "typ list"})
  in
    @{const make_dt_def} $ tparams $ ctrs
  end

end