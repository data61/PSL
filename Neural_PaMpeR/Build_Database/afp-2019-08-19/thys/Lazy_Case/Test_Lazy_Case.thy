section \<open>Usage\<close>

theory Test_Lazy_Case
imports Lazy_Case
begin

text \<open>
  This entry provides a @{command datatype} plugin and a separate command.
  The plugin runs by default on all defined datatypes, but it can be disabled individually:
\<close>

datatype (plugins del: lazy_case) 'a tree = Node | Fork 'a "'a tree list"

context begin

text \<open>
  The @{command lazify} command can be used to add lazy constants if the plugin has been disabled
  during datatype definition.
\<close>

lazify tree

end

text \<open>Nested and mutual recursion are supported.\<close>

datatype
  'a mlist1 = MNil1 | MCons1 'a "'a mlist2" and
  'a mlist2 = MNil2 | MCons2 'a "'a mlist1"

text \<open>Records are supported.\<close>

record meep =
  x1 :: nat
  x2 :: int

section \<open>Examples\<close>

definition test where
"test x \<longleftrightarrow> (if x then True else False)"

definition test' where
"test' = case_bool True False"

definition test'' where
"test'' xs = (case xs of [] \<Rightarrow> False | _ \<Rightarrow> True)"

fun fac :: "nat \<Rightarrow> nat" where
"fac n = (if n \<le> 1 then 1 else n * fac (n - 1))"

lemma map_tree[code]:
  "map_tree f t = (case t of Node \<Rightarrow> Node | Fork x ts \<Rightarrow> Fork (f x) (map (map_tree f) ts))"
by (induction t) auto

text \<open>The generated code uses neither target-language \texttt{if-then-else} nor match expressions.\<close>

export_code test test' test'' fac map_tree in SML

(*<*)

ML\<open>
fun get_code_eqs ctxt const =
  let
    val thy = Proof_Context.theory_of ctxt
    val graph = #eqngr (Code_Preproc.obtain true { ctxt = ctxt, consts = [const], terms = [] })
    fun mk_eqs name = name
      |> Code_Preproc.cert graph
      |> Code.equations_of_cert thy ||> these
      |> pair name
  in
    AList.lookup (=) (maps (map mk_eqs) (rev (Graph.strong_conn graph))) const
    |> the |> snd
    |> map (fst o snd)
    |> map_filter I
  end

fun check_absence ctxt const =
  let
    val forbidden =
      @{const_name HOL.If} :: map (fst o dest_Const o #casex) (Ctr_Sugar.ctr_sugars_of ctxt)
    val check = exists_subterm (fn Const (c, _) => member (=) forbidden c | _ => false)
  in
    get_code_eqs ctxt const
    |> map Thm.prop_of
    |> forall (not o check)
    |> @{assert}
  end
\<close>

ML_val\<open>check_absence @{context} @{const_name fac}: unit\<close>
ML_val\<open>check_absence @{context} @{const_name test}: unit\<close>
ML_val\<open>check_absence @{context} @{const_name test'}: unit\<close>
ML_val\<open>check_absence @{context} @{const_name test''}: unit\<close>
ML_val\<open>check_absence @{context} @{const_name map_tree}: unit\<close>

(*>*)

end