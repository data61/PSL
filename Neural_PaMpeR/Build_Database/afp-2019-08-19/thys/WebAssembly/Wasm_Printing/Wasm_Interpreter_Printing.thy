theory Wasm_Interpreter_Printing imports "../Wasm_Interpreter_Properties" begin

definition "run = run_v (2^63) 300"

code_printing
  constant host_apply_impl \<rightharpoonup> (OCaml) "ImplWrapper.host'_apply'_impl"
| constant mem_grow_impl \<rightharpoonup> (OCaml) "ImplWrapper.mem'_grow'_impl"

(* memory *)

declare Rep_bytes_inverse[code abstype]
declare Rep_mem_inverse[code abstype]

code_printing
  type_constructor bytes \<rightharpoonup> (OCaml) "Int64.t"
| type_constructor mem \<rightharpoonup> (OCaml) "ImplWrapperTypes.memory"

code_printing
  constant mem_size \<rightharpoonup> (OCaml) "ImplWrapper.size"
(* | constant mem_grow \<rightharpoonup> (OCaml) "ImplWrapper.grow" *)
| constant load \<rightharpoonup> (OCaml) "ImplWrapper.load"
| constant store \<rightharpoonup> (OCaml) "ImplWrapper.store"
| constant load_packed \<rightharpoonup> (OCaml) "ImplWrapper.load'_packed"
| constant store_packed \<rightharpoonup> (OCaml) "ImplWrapper.store'_packed"

declare mem_size_def[code del]
declare store_def[code del]
declare load_def[code del]
declare store_packed_def[code del]
declare load_packed_def[code del]

end
