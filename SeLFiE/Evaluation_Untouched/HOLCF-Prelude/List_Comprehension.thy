section \<open>List Comprehension\<close>

theory List_Comprehension
  imports Data_List
begin

no_notation
  disj (infixr "|" 30)

nonterminal llc_qual and llc_quals

syntax
  "_llc" :: "'a \<Rightarrow> llc_qual \<Rightarrow> llc_quals \<Rightarrow> ['a]" ("[_ | __")
  "_llc_gen" :: "'a \<Rightarrow> ['a] \<Rightarrow> llc_qual" ("_ <- _")
  "_llc_guard" :: "tr \<Rightarrow> llc_qual" ("_")
  "_llc_let" :: "letbinds \<Rightarrow> llc_qual" ("let _")
  "_llc_quals" :: "llc_qual \<Rightarrow> llc_quals \<Rightarrow> llc_quals" (", __")
  "_llc_end" :: "llc_quals" ("]")
  "_llc_abs" :: "'a \<Rightarrow> ['a] \<Rightarrow> ['a]"

translations
  "[e | p <- xs]" => "CONST concatMap\<cdot>(_llc_abs p [e])\<cdot>xs"
  "_llc e (_llc_gen p xs) (_llc_quals q qs)"
    => "CONST concatMap\<cdot>(_llc_abs p (_llc e q qs))\<cdot>xs"
  "[e | b]" => "If b then [e] else []"
  "_llc e (_llc_guard b) (_llc_quals q qs)"
    => "If b then (_llc e q qs) else []"
  "_llc e (_llc_let b) (_llc_quals q qs)"
    => "_Let b (_llc e q qs)"

parse_translation \<open>
let open HOLCF_Library in
  let
    val NilC = Syntax.const @{const_syntax "Nil"};

    fun Lam x = Syntax.const @{const_syntax "Abs_cfun"} $ x;

    fun fresh_var ts ctxt =
      let
        val ctxt' = fold Variable.declare_term ts ctxt
      in
        singleton (Variable.variant_frees ctxt' []) ("x", dummyT)
      end

    fun pat_tr ctxt p e = (* %x. case x of p => e | _ => [] *)
      let
        val x = Free (fresh_var [p, e] ctxt);
        val case1 = Syntax.const @{syntax_const "_case1"} $ p $ e;
        val case2 =
          Syntax.const @{syntax_const "_case1"} $
            Syntax.const @{const_syntax Pure.dummy_pattern} $ NilC;
        val cs = Syntax.const @{syntax_const "_case2"} $ case1 $ case2;
      in
        (* FIXME: handle HOLCF patterns correctly *)
        Syntax_Trans.abs_tr [x, Case_Translation.case_tr false ctxt [x, cs]]
        |> Lam
      end

    fun abs_tr ctxt [p, e] =
      (case Term_Position.strip_positions p of
        Free (s, T) => Lam (Syntax_Trans.abs_tr [p, e])
      | _ => pat_tr ctxt p e)

  in [(@{syntax_const "_llc_abs"}, abs_tr)] end
end
\<close>

lemma concatMap_singleton [simp]:
  "concatMap\<cdot>(\<Lambda> x. [f\<cdot>x])\<cdot>xs = map\<cdot>f\<cdot>xs"
  by (induct xs) simp_all

lemma listcompr_filter [simp]:
  "[x | x <- xs, P\<cdot>x] = filter\<cdot>P\<cdot>xs"
proof (induct xs)
  case (Cons a xs)
  then show ?case by (cases "P\<cdot>a"; simp)
qed simp_all

lemma "[y | let y = x*2; z = y, x <- xs] = A"
  apply simp
  oops

end
