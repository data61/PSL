signature HASH_GENERATOR =
sig
  (* creates the hash function (possible bounded by some parameter) *)
  (*                          dtyp_info                *)
  val mk_hash : theory -> Old_Datatype_Aux.info -> term;

  (* creates and registers hash-functions for datatype *)
  val derive : string -> string -> theory -> theory
end

structure Hash_Generator : HASH_GENERATOR =
struct

open Derive_Aux

val max_int = 2147483648 (* 2 ^^ 31 *)

fun int_of_string s = fold
  (fn c => fn i => (1792318057 * i + Char.ord c) mod max_int)
  (String.explode s)
  0

(* all numbers in int_of_string and create_factors are primes (31-bit) *)

fun create_factor ty_name con_name idx i j =
  (1444315237 * int_of_string ty_name +
  1336760419 * int_of_string con_name +
  2044890737 * (idx + 1) +
  1622892797 * (i+1) +
  2140823281 * (j+1)) mod max_int

fun create_def_size _ = 10

val hash_name = @{const_name "hashcode"}

(* construct free variable x_i *)
fun mk_free_tysubst_i typ_subst x i ty = Free (x ^ string_of_int i, ty |> typ_subst)

fun mk_hash thy info =
  let
    val sort = @{sort hashable}
    val typ_subst = typ_subst_for_sort thy info sort
    val descr = #descr info
    val ty_name = info |> #descr |> hd |> snd |> #1
    val cons_hash = create_factor ty_name
    val mk_num = HOLogic.mk_number @{typ hashcode}
    fun typ_of dty = Old_Datatype_Aux.typ_of_dtyp descr dty |> typ_subst
    val rec_names = #rec_names info
    val mk_free_i = mk_free_tysubst_i typ_subst
    fun rec_idx i dtys = dt_number_recs (take i dtys) |> fst
    fun mk_rhss (idx,(_,_,cons)) =
      let
        fun mk_rhs (i,(cname,dtysi)) =
          let
            val lvars = map_index (fn (i,dty) => mk_free_i "x_" i (typ_of dty)) dtysi
            fun res_var (_,oc) = mk_free_i "res_" oc (@{typ hashcode});
            val res_vars = dt_number_recs dtysi
              |> snd
              |> map res_var
            val x = nth lvars
            fun combine_dts [] = mk_num (cons_hash cname idx i 0)
              | combine_dts ((_,c) :: ics) = @{term "(+) :: hashcode => hashcode => hashcode"} $ c $ combine_dts ics
            fun multiply j t =
              let
                val mult = mk_num (cons_hash cname idx i (j+1))
              in @{term "(*) :: hashcode => hashcode => hashcode"} $ mult $ t end
            fun hash_of_dty (i,Old_Datatype_Aux.DtRec j) = res_var (j,rec_idx i dtysi) |> multiply i
              | hash_of_dty (i,_) =
                  let
                    val xi = x i
                    val ty = Term.type_of xi
                    val hash = Const (hash_name, ty --> @{typ hashcode}) $ xi
                  in hash |> multiply i end
            val pre_rhs = map_index hash_of_dty dtysi
              |> map_index I
              |> combine_dts
            val rhs = fold lambda (rev (lvars @ res_vars)) pre_rhs
          in rhs end
        val rec_args = map_index (fn (i,c) => (mk_rhs (i,c),i,idx)) cons
      in rec_args end
    val nrec_args = maps mk_rhss descr
    val rec_args = map #1 nrec_args
    fun mk_rec i =
      let
        val ty = typ_of (Old_Datatype_Aux.DtRec i)
        val rec_ty = map type_of rec_args @ [ty] ---> @{typ hashcode}
        val rec_name = nth rec_names i
        val rhs = list_comb (Const (rec_name, rec_ty), rec_args)
      in rhs end
  in mk_rec 0 end


fun derive dtyp_name _ thy =
  let
    val tyco = dtyp_name

    val base_name = Long_Name.base_name tyco
    val _ = writeln ("creating hashcode for datatype " ^ base_name)
    val sort = @{sort hashable}
    val info = BNF_LFP_Compat.the_info thy [] tyco
    val vs_of_sort =
      let val i = BNF_LFP_Compat.the_spec thy tyco |> #1
      in fn sort => map (fn (n,_) => (n, sort)) i end
    val vs = vs_of_sort sort
    val hash_rhs = mk_hash thy info
    val ty = Term.fastype_of hash_rhs |> Term.dest_Type |> snd |> hd
    val ty_it = Type (@{type_name itself}, [ty])
    val hashs_rhs = lambda (Free ("x",ty_it)) (HOLogic.mk_number @{typ nat} (create_def_size ty))

    val hash_def = mk_def (ty --> @{typ hashcode}) @{const_name hashcode} hash_rhs
    val hashs_def = mk_def (ty_it --> @{typ nat}) @{const_name def_hashmap_size} hashs_rhs

    val ((hash_thm , hashs_thm),lthy) = Class.instantiation ([tyco],vs,sort) thy
      |> define_overloaded ("hashcode_" ^ base_name ^ "_def", hash_def)
      ||>> define_overloaded ("def_hashmap_size_" ^ base_name ^ "_def", hashs_def)
    val hash_thms = [hash_thm, hashs_thm]

    fun hash_tac ctxt =
      my_print_tac ctxt "enter hash " THEN
      unfold_tac ctxt hash_thms THEN
      my_print_tac ctxt "after unfolding" THEN
      simp_tac ctxt 1
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [] THEN hash_tac ctxt) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class hashable")

  in thy' end

val _ =
  Theory.setup
    (Derive_Manager.register_derive "hashable" "derives a hash function for a datatype" derive)

end
