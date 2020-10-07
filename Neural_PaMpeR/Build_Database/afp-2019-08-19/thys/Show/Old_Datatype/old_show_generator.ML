(*
Copyright 2009-2014 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
signature SHOW_GENERATOR = 
sig 
  (*creates the shows function (ignores precedence)*)
  val mk_shows_idx : theory -> Old_Datatype_Aux.info -> (int -> term) * (term * int * int) list;
  (*creates the shows_list function*)
  val mk_shows_list : typ -> term;
  (*creates and registers show-functions for datatypes*)
  val derive : string -> string -> theory -> theory
end

structure Show_Generator : SHOW_GENERATOR =
struct

open Derive_Aux

val shows_prec_name = @{const_name "shows_prec"}

val shows_ty = @{typ "shows"}
val string_ty = @{typ "string"}
val nat_ty = @{typ "nat"}
val sort = @{sort show}
val append = @{term "append :: string \<Rightarrow> shows"}
val default_prec = @{term "0 :: nat"}

(*construct free variable x_i*)
fun mk_free_tysubst_i typ_subst x i ty = Free (x ^ string_of_int i, ty |> typ_subst)

fun mk_shows_idx thy info =
  let
    val typ_subst = typ_subst_for_sort thy info sort 
    val descr = #descr info
    fun mk_shows s = append $ HOLogic.mk_string s
    fun typ_of dty = Old_Datatype_Aux.typ_of_dtyp descr dty |> typ_subst
    val rec_names = #rec_names info
    val mk_free_i = mk_free_tysubst_i typ_subst
    fun rec_idx i dtys = dt_number_recs (take i dtys) |> fst
    fun mk_rhss (idx, (_, _, cons)) = 
      let
        fun mk_rhs (_, (cname, dtysi)) = 
          let
            val lvars = map_index (fn (i, dty) => mk_free_i "x_" i (typ_of dty)) dtysi
            fun res_var (_, oc) = mk_free_i "res_" oc shows_ty;
            val res_vars = dt_number_recs dtysi |> snd |> map res_var
            val x = nth lvars
            val show_cname = mk_shows (Long_Name.base_name cname)
            fun combine_dts C e [] = C e
              | combine_dts C e ((_, c) :: ics) = 
                  combine_dts (fn e' => C (@{term "(+@+)"} $ e $ e')) c ics
            fun parenthise t = @{term shows_sep_paren} $ t
            fun shows_of_dty (i, Old_Datatype_Aux.DtRec j) =
                  res_var (j, rec_idx i dtysi) |> parenthise
              | shows_of_dty (i, _) = 
                  let
                    val xi = x i
                    val ty = Term.type_of xi
                    val shows = Const (shows_prec_name, nat_ty --> ty --> shows_ty) $ default_prec $ xi
                  in shows |> parenthise end
            val pre_rhs = map_index shows_of_dty dtysi
              |> map_index I
              |> combine_dts I show_cname
            val rhs = fold lambda (rev (lvars @ res_vars)) pre_rhs
          in rhs end
        val rec_args = map_index (fn (i, c) => (mk_rhs (i, c), i, idx)) cons 
      in rec_args end
    val nrec_args = flat (map mk_rhss descr)
    val rec_args = map #1 nrec_args
    fun mk_rec i = 
      let
        val ty = typ_of (Old_Datatype_Aux.DtRec i)
        val rec_ty = map type_of rec_args @ [ty] ---> shows_ty
        val rec_name = nth rec_names i
        val rhs = list_comb (Const (rec_name, rec_ty), rec_args)
      in rhs end
  in (mk_rec, nrec_args) end

fun mk_shows_list ty =
  let
    val list_ty = Type (@{type_name "list"}, [ty])
    val shows = Abs ("x", ty, Const (shows_prec_name, nat_ty --> ty --> shows_ty) $ default_prec $ Bound 0) 
    val shows_list_aux = Const (@{const_name shows_list_aux}, (ty --> shows_ty) --> list_ty --> shows_ty)
    val rhs = shows_list_aux $ shows
  in rhs end

fun mk_prop_trm thy info 
  (gen : (int -> term) -> (term -> term) -> term list * term list) = 
  let 
    fun main idx = 
      let
        val xs = mk_xs thy info sort idx
        val shows = fn a => fst (mk_shows_idx thy info) idx $ a
      in gen xs shows  end
  in
    #descr info
    |> map (fst #> main)
  end  

val r_var = Free ("r", string_ty)
val s_var = Free ("s", string_ty)

fun mk_assoc_thm_trm thy info =
  mk_prop_trm thy info (fn xs => fn show => 
    let val x = xs 1
    in
      ([HOLogic.mk_eq (append $ (show x $ r_var) $ s_var, show x $ (append $ r_var $ s_var))],
        [x, r_var, s_var])
    end)

fun simps_of_info (info : Old_Datatype_Aux.info) = #rec_rewrites info

fun mk_assoc_thm thy info =
  let 
    val assoc_props = mk_assoc_thm_trm thy info
    val ind_thm = #induct info
    val simp_that = simps_of_info info
    val assoc_thm_of_tac = inductive_thm thy assoc_props ind_thm sort
    val nrec_args = mk_shows_idx thy info |> snd
    val descr = #descr info

    fun ind_tac ctxt i ihs _ _ _ =
      let
        val (_, j, idx) = nth nrec_args i 
        val c_info = nth descr idx |> snd |> (fn (_, _, info) => nth info j)
        val pdtys = snd c_info
        fun sub_case_tac [] [] = all_tac
          | sub_case_tac (dty :: pdtys) ihs =
              let
                (*for recursive arguments, use IH, otherwise use thm from shows_class*)
                val (thm, ihs') = (case dty of Old_Datatype_Aux.DtRec _ => (hd ihs, tl ihs) | _ => (@{thm assoc(1)}, ihs))
              in
                (*handle separator*)
                resolve_tac ctxt
                  [case pdtys of [] => @{thm shows_sep_paren_final} | _ => @{thm shows_sep_paren}] 1
                (*handle argument*)
                THEN resolve_tac ctxt [thm] 1
                (*recurse*)
                THEN sub_case_tac pdtys ihs'
              end
          | sub_case_tac _ _ = error "internal error in show_generator"
      in
        (*unfold recursor*)
        unfold_tac ctxt simp_that 
        (*handle constructor*)
        THEN resolve_tac ctxt
          [case pdtys of [] => @{thm append_assoc} | _ => @{thm append_assoc_trans}] 1
        (*handle arguments*)
        THEN sub_case_tac pdtys ihs
      end
  in assoc_thm_of_tac ind_tac end


fun derive dtyp_name _ thy = 
  let
    val tyco = dtyp_name
    val base_name = Long_Name.base_name tyco
    val _ = writeln ("creating show-functions for data type " ^ base_name)
    val info = BNF_LFP_Compat.the_info thy [] tyco
    val vs =
      let val i = BNF_LFP_Compat.the_spec thy tyco |> fst
      in map (fn (n, _) => (n, sort)) i end
    val shows_rhs = fst (mk_shows_idx thy info) 0
    val shows_prec_rhs = lambda  (Free ("p", nat_ty)) shows_rhs
    val ty = Term.fastype_of shows_rhs |> Term.dest_Type |> snd |> hd
    val shows_list_rhs = mk_shows_list ty
    
    val shows_prec_def = mk_def (nat_ty --> ty --> shows_ty) @{const_name shows_prec} shows_prec_rhs
    val shows_list_def = mk_def (Type (@{type_name list}, [ty]) --> shows_ty) @{const_name shows_list} shows_list_rhs
    val ((shows_prec_thm, shows_list_thm), lthy) = Class.instantiation ([tyco], vs, sort) thy
      |> define_overloaded ("shows_prec_" ^ base_name ^ "_def", shows_prec_def)
      ||>> define_overloaded ("shows_list_" ^ base_name ^ "_def", shows_list_def) 

    val assoc_thm = mk_assoc_thm thy info;
    fun assoc_tac ctxt = unfold_tac ctxt [shows_prec_thm]
      THEN resolve_tac ctxt [assoc_thm] 1;

    val thy' = Class.prove_instantiation_exit (fn ctxt =>
        Class.intro_classes_tac ctxt []
        THEN assoc_tac ctxt
        THEN unfold_tac ctxt [shows_list_thm] 
        THEN resolve_tac ctxt @{thms shows_list_aux_assoc} 1
        THEN resolve_tac ctxt @{thms ballI} 1
        THEN assoc_tac ctxt
      ) lthy;
    val _ = writeln ("registered " ^ base_name ^ " in class show")
  
  in thy' end

val _ =
  Theory.setup
    (Derive_Manager.register_derive "show" "derives a show function for a datatype" derive)

end
