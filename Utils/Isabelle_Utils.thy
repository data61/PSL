(* This file provides utility functions that are specific to Isabelle/HOL. *)
theory Isabelle_Utils
imports Utils
begin

ML{* signature ISABELLE_UTILS =
sig
  val get_1st_subg                  : thm -> term option;
  val flatten_trm                   : term -> term list;
  val get_trms_in_thm               : thm -> term list;
  val get_typ_names_in_trm          : term -> string list;
  val get_const_names_in_thm        : thm -> string list;
  val get_const_names_in_1st_subg   : thm -> string list;
  val get_abs_names_in_trm          : term -> string list;
  val get_abs_names_in_thm          : thm -> string list;
  val get_abs_name_in_1st_subg      : thm -> string list;
  val get_typ_names_in_thm          : thm -> string list;
  val get_typ_names_in_1st_subg     : thm -> string list;
  val get_free_var_names_in_trms    : term list -> string list;
  val get_free_var_names_in_thm     : thm -> string list;
  val get_free_var_names_in_1st_subg: thm -> string list;
  val get_all_var_names_in_1st_subg : thm -> string list;
  val proof_state_to_thm            : Proof.state -> thm;
  val mk_proof_obligation           : Proof.context -> string -> thm;
end;
*}

ML{* structure Isabelle_Utils : ISABELLE_UTILS  =
struct
  fun get_1st_subg (goal:thm) = (SOME o hd) (Thm.prems_of goal) handle Empty => NONE : term option;

  fun flatten_trm (trm1 $ trm2) = flat [flatten_trm trm1, flatten_trm trm2]
    | flatten_trm trm = [trm];

  fun get_trms_in_thm (thm:thm) = Thm.cprop_of thm |> Thm.term_of |> flatten_trm;

  fun get_const_names_in_thm thm = thm
    |> Thm.cprop_of
    |> Thm.term_of
    |> (fn subg:term => Term.add_const_names subg []);

  fun get_const_names_in_1st_subg (goal:thm) = goal
    |> get_1st_subg
    |> Option.map (fn subg:term => Term.add_const_names subg [])
    |> these;

  fun get_typs_in_trm (Const (_ ,T))    = [T]
   |  get_typs_in_trm (Free (_, T))     = [T]
   |  get_typs_in_trm (Var (_, T))      = [T]
   |  get_typs_in_trm (Bound _)         = []
   |  get_typs_in_trm (Abs (_, T, trm)) = T :: get_typs_in_trm trm
   |  get_typs_in_trm (trm1 $ trm2)     = get_typs_in_trm trm1 @ get_typs_in_trm trm2;

  local
    fun get_typ_names' (Type (name, typs)) = name :: flat (map get_typ_names' typs)
     |  get_typ_names' (TFree (name, _))   = [name]
     |  get_typ_names' (TVar (_, _))       = [];
  in
    fun get_typs_names (typs:typ list) = map get_typ_names' typs |> flat;
  end;

  fun get_abs_names_in_trm (Abs (name, _, trm)) =
        name :: (trm |> flatten_trm |> map get_abs_names_in_trm |> flat)
   |  get_abs_names_in_trm (trm1 $ trm2) = get_abs_names_in_trm trm1 @ get_abs_names_in_trm trm2
   |  get_abs_names_in_trm _ = [];

  fun get_abs_names_in_thm thm = thm |> Thm.cprop_of |> Thm.term_of |> get_abs_names_in_trm;

  fun get_abs_name_in_1st_subg (goal:thm) = goal
    |> get_1st_subg
    |> Option.map get_abs_names_in_trm
    |> these
    |> map Utils.remove__s;

  fun get_typ_names_in_trm trm = trm 
    |> get_typs_in_trm
    |> get_typs_names
    |> duplicates (op =)
    |> map Utils.remove__s;

  fun get_typ_names_in_thm thm = thm 
    |> get_trms_in_thm
    |> map get_typ_names_in_trm
    |> flat
    |> duplicates (op =)
    |> map Utils.remove__s;

  fun get_typ_names_in_1st_subg (goal:thm) = goal
    |> get_1st_subg
    |> Option.map get_typ_names_in_trm
    |> these
    |> map Utils.remove__s;

  fun get_free_var_names_in trm = if Term.is_Free trm 
    then [Term.dest_Free trm |> fst |> Utils.remove__s] else [];

  fun get_free_var_names_in_trms trms = trms
    |> map get_free_var_names_in
    |> List.concat
    |> distinct (op =);

  fun get_free_var_names_in_thm thm = thm
    |> get_trms_in_thm
    |> get_free_var_names_in_trms;

  fun get_free_var_names_in_1st_subg (goal:thm) = goal
    |> get_1st_subg
    |> Option.map (fn subg:term => Term.add_frees subg [])
    |> Option.map (map fst)
    |> these
    |> map Utils.remove__s;

  fun get_all_var_names_in_1st_subg (goal:thm) =
      Option.map (map fst o strip_all_vars) (get_1st_subg goal)
    |> these
    |> map Utils.remove__s : string list;

  val proof_state_to_thm = #goal o Proof.goal;

  fun mk_proof_obligation ctxt (prop_str:string) = 
    Syntax.read_prop ctxt prop_str
    |> Thm.cterm_of ctxt
    |> Thm.trivial
end;
*}

end