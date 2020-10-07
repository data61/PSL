theory Test_Datatypes
imports
  Lazy_Case.Lazy_Case
  "../Preproc/Embed"
  "../Preproc/Eval_Instances"
  "../Backend/CakeML_Setup"
  "../Compiler/Compiler"
  CakeML.CakeML_Compiler
begin

fun app where
"app [] xs = xs" |
"app (y # ys) xs = y # app ys xs"

embed app' is app .
print_theorems

declare app'.C_info_def[code]

(* FIXME code_simp doesn't work for the below cakeml invocation *)

lemma [code_unfold]:
  "app'.cake_dt_prelude =
   (Dtype (make_locn 0 0 0, make_locn 0 0 0)
     [([[CHR 0x27, CHR ''a'', CHR ''_'', CHR ''0'']], ''List_list'',
       [(''List_list_Cons'', [Tvar [CHR 0x27, CHR ''a'', CHR ''_'', CHR ''0''], Tapp [Tvar [CHR 0x27, CHR ''a'', CHR ''_'', CHR ''0'']] (TC_name (Short ''List_list''))]), (''List_list_Nil'', [])])])"
  by eval

lemma [code_unfold]:
  "Compiler.compile app'.C_info app' = [Tdec
   (Dletrec (make_locn 0 0 0, make_locn 0 0 0)
     [(''Test__Datatypes_app'', ''Test__Datatypes_app_'',
       Mat (Var (Short ''Test__Datatypes_app_''))
        [(Pcon (Some (Short ''List_list_Nil'')) [], Fun ''Test__Datatypes_app_'' (Mat (Var (Short ''Test__Datatypes_app_'')) [(pat.Pvar ''xs_0'', Var (Short ''xs_0''))])),
         (Pcon (Some (Short ''List_list_Cons'')) [pat.Pvar ''y_0'', pat.Pvar ''ys_0''],
          Fun ''ys_0_''
           (Mat (Var (Short ''ys_0_''))
             [(pat.Pvar ''xs_0'', Con (Some (Short ''List_list_Cons'')) [Var (Short ''y_0''), exp0.App Opapp [exp0.App Opapp [Var (Short ''Test__Datatypes_app''), Var (Short ''ys_0'')], Var (Short ''xs_0'')]])]))])])]"
  by eval

cakeml (prog) \<open>
  Ast.Tdec app'.cake_dt_prelude # Compiler.compile app'.C_info app'
\<close>

end
