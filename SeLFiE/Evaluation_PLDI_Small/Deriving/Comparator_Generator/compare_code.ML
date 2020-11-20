signature COMPARE_CODE =
sig
  
  (* changes the code equations of some constant such that
     two consecutive comparisons via <=, <, or = are turned into one
     invocation of the comparator. 
     The difference to a standard code_unfold is that here we change the code-equations
     where an additional sort-constraint on compare_order can be added. Otherwise, there would
     be no compare-function. *)
  val change_compare_code : 
    term                      (* the constant *) 
    -> string list     (* the list of type parameters which should be constraint to @{sort compare_order} *) 
    -> local_theory -> local_theory

end

structure Compare_Code : COMPARE_CODE =
struct

fun drop_leading_qmark s = 
  if String.isPrefix "?" s then String.substring (s,1,String.size s - 1) else s

fun change_compare_code const inst_names lthy = 
  let
    val inst_names = map drop_leading_qmark inst_names
    val const_string = quote (Pretty.string_of (Syntax.pretty_term lthy const))
    val cname = (case const of Const (cname,_) => cname | _ => 
      error ("expected constant as input, but got " ^ const_string))
    val cert = Code.get_cert lthy [] cname
    val code_eqs = cert |> Code.equations_of_cert (Proof_Context.theory_of lthy)
    |> snd |> these |> map (fst o snd) |> map_filter I
    val _ = if null code_eqs then error "could not find code equations" else ()

    (* adding sort-constraint compare_order within code equations*)
    val const' = hd code_eqs |> Thm.concl_of |> Logic.dest_equals |> fst |> strip_comb |> fst
    val types = Term.add_tvars const' []
    val ctyp_of = TVar #> Thm.ctyp_of lthy
    fun filt s = not (member (op =) (@{sort ord} @ @{sort linorder} @ @{sort order}) s)
    val map_types = maps (fn ty => if List.exists (fn tn => tn = (fst o fst) ty) inst_names then 
      [(ty, ctyp_of (apsnd (fn ss => filter filt ss @ @{sort compare_order}) ty))] else 
      []) types
    val code_eqs = map (Thm.instantiate (map_types, [])) code_eqs 

    (* replace comparisons and register code eqns *)
    val new_code_eqs = map (Local_Defs.unfold lthy @{thms two_comparisons_into_compare}) code_eqs
    val _ = if map Thm.prop_of new_code_eqs = map Thm.prop_of code_eqs then
      warning ("Code equations for " ^ const_string ^ " did not change\n" ^
      "Perhaps you have to provide some type variables which should be restricted to compare_order\n" ^
      (@{make_string} (map TVar types ~~ map snd types, const', code_eqs))) 
      else ()
    val lthy = Local_Theory.note (
      (Binding.name (Long_Name.base_name cname ^ "_compare_code"), @{attributes [code]}), new_code_eqs) lthy 
      |> snd    
  in
    lthy
  end
  
fun change_compare_code_cmd const tnames_option lthy = 
  change_compare_code (Syntax.read_term lthy const) tnames_option lthy

val _ =
  Outer_Syntax.local_theory @{command_keyword compare_code} 
    "turn comparisons via <= and < into compare within code-equations"
    (Scan.optional (@{keyword "("} |-- (Parse.list Parse.string) --| @{keyword ")"}) [] --
      Parse.term >> (fn (inst, c) => change_compare_code_cmd c inst))

end
