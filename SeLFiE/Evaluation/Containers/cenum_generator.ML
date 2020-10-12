(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)

signature CENUM_GENERATOR = 
sig 
  
  (* derives a trivial instance (None) for class enum and any type *)
  val derive_no_cenum : string -> theory -> theory

end

structure Cenum_Generator : CENUM_GENERATOR = 
struct
open Containers_Generator;

fun mk_none_cenum ty =
  let 
    val lty = Type (@{type_name list}, [ty])
    val fty = (ty --> @{typ bool}) --> @{typ bool}
    val oty = Type (@{type_name option},[
      Type (@{type_name prod},[lty, Type (@{type_name prod},[fty,fty])])])
    val res = Const (@{const_name None}, oty)
  in res
end

val derive_no_cenum = 
  derive_none @{const_name cEnum} @{sort cenum} mk_none_cenum

fun derive_cenum typ_name param thy = 
  let
    val _ = if (param = "no") then false else  
      error "currently only parameter 'no' is accepted for class cenum"
    in derive_no_cenum typ_name thy 
  end

val _ = Theory.setup  
  (Derive_Manager.register_derive "cenum" "use (no) enumeration for class cenum" derive_cenum) 
end
