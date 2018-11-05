(*  Title:      PSL.thy
    Author:     Yutaka Nagashima, Data61, CSIRO

Import this file to install PSL. That is all you need to do to install PSL.
See ./Example.thy for examples.
*)

theory PSL
imports "src/Try_Hard"
begin

text{* Uncomment the following to unleash the power parallelism. *}

ML{* Multithreading.max_threads_update 28 *}
ML{* Multithreading.parallel_proofs := 0; *}
ML{*
Term.Const;
Term.add_consts;
@{term "f x"};
Term.add_frees @{term "f x"} [] |> rev |> hd |> snd |> Term.dest_Type;
Term.add_frees @{term "x"} []  |> hd |> snd |> Term.dest_TFree;
Term.exists_type: (typ -> bool) -> term -> bool;

fun is_fun_typ (Type (typ_name, _):typ) = typ_name = "fun"
  | is_fun_typ  _                       = false;

fun trm_has_fun_typ (trm:term) = Term.exists_type is_fun_typ trm: bool;

trm_has_fun_typ @{term "f x"};
trm_has_fun_typ @{term "True"};
trm_has_fun_typ @{term "x"};
*}ML{*
fun trm_to_funs (trm:term) =
  let
    val vars       = Term.add_vars trm []        : (indexname * typ) list;
    val frees      = Term.add_frees trm []       : (string * typ) list;
    val consts     = Term.add_consts trm []      : (string * typ) list;
    val result =
      {vars   = map Term.Var vars     |> filter trm_has_fun_typ,
       frees  = map Term.Free frees   |> filter trm_has_fun_typ,
       consts = map Term.Const consts |> filter trm_has_fun_typ};
  in
    result:{consts: term list, frees: term list, vars: term list}
  end;

@{term "f x"} |> trm_to_funs |> #frees |> map (fst o Term.dest_Free);

fun trm_to_fun_free_names (trm:term) = trm |> trm_to_funs |> #frees |> map (fst o Term.dest_Free);
*}

end