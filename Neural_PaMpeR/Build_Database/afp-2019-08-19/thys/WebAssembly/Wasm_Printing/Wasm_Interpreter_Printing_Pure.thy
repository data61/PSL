theory Wasm_Interpreter_Printing_Pure imports "../Wasm_Interpreter_Properties" Wasm_Type_Abs_Printing "HOL-Library.Code_Target_Nat" (* "Native_Word.Code_Target_Bits_Int" *) begin

axiomatization where
  mem_grow_impl_is[code]: "mem_grow_impl m n = Some (mem_grow m n)"

definition "run = run_v (2^63) 300"

code_printing
  constant host_apply_impl \<rightharpoonup> (OCaml) "ImplWrapper.host'_apply'_impl"

declare Rep_bytes_inverse[code abstype]
declare Rep_mem_inverse[code abstype]

declare write_bytes.rep_eq[code abstract]
and read_bytes.rep_eq[code abstract]
and mem_append.rep_eq[code abstract]

lemma bytes_takefill_rep_eq[code abstract]:
  "Rep_bytes (bytes_takefill b n bs) = takefill b n (Rep_bytes bs)"
  using bytes_takefill.rep_eq Rep_uint8_inverse
  by simp

lemma bytes_replicate_rep_eq[code abstract]:
  "Rep_bytes (bytes_replicate n b) = replicate n b"
  using bytes_replicate.rep_eq Rep_uint8_inverse
  by simp

export_code open run in OCaml

end
