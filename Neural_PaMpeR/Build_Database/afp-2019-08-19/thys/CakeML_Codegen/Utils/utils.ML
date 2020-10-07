fun repeat1_conv cv = cv then_conv Conv.repeat_conv cv

fun init [] = error "empty list"
  | init [_] = []
  | init (x :: xs) = x :: init xs

fun last [] = error "empty list"
  | last [x] = x
  | last (_ :: xs) = last xs

val unvarify_typ =
  let
    fun aux (TVar ((name, idx), sort)) = TFree (name ^ Value.print_int idx, sort)
      | aux t = t
  in map_atyps aux end

fun all_consts (Const (name, typ)) = [(name, typ)]
  | all_consts (t $ u) = union (op =) (all_consts t) (all_consts u)
  | all_consts (Abs (_, _, t)) = all_consts t
  | all_consts _ = []

fun induct_of_bnf_const ctxt const =
  let
    open Dict_Construction_Util

    val (name, _) = dest_Const const

    fun cmp {T, ...} (Const (name', _)) = if name = name' then SOME T else NONE
      | cmp _ _ = NONE

    fun is_disc_or_sel (sugar as {discs, selss, ...}) =
      maps (map (cmp sugar)) selss @ map (cmp sugar) discs

    val Ts =
      Ctr_Sugar.ctr_sugars_of ctxt
      |> maps is_disc_or_sel
      |> cat_options
  in
    case Ts of
      (Type (typ_name, _) :: _) =>
        BNF_FP_Def_Sugar.fp_sugar_of ctxt typ_name
        |> Option.mapPartial #fp_co_induct_sugar
        |> Option.map #co_inducts
    | _ => NONE
  end