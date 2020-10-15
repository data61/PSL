(*  Title:       Executable Transitive Closures of Finite Relations
    Author:      Christian Sternagel <c.sternagel@gmail.com>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

section \<open>Computing Images of Finite Transitive Closures\<close>

theory Finite_Transitive_Closure_Simprocs
imports Transitive_Closure_List_Impl
begin

lemma rtrancl_Image_eq:
  assumes "r = set r'" and "x = set x'"
  shows "r\<^sup>* `` x = set (rtrancl_list_impl r' x')"
  using assms by (auto simp: rtrancl_list_impl)

lemma trancl_Image_eq:
  assumes "r = set r'" and "x = set x'"
  shows "r\<^sup>+ `` x = set (trancl_list_impl r' x')"
  using assms by (auto simp: trancl_list_impl)


subsection \<open>A Simproc for Computing the Images of Finite Transitive Closures\<close>

ML \<open>
signature FINITE_TRANCL_IMAGE =
sig
  val trancl_simproc : Proof.context -> cterm -> thm option
  val rtrancl_simproc : Proof.context -> cterm -> thm option
end

structure Finite_Trancl_Image : FINITE_TRANCL_IMAGE =
struct

fun eval_tac ctxt =
  let val conv = Code_Runtime.dynamic_holds_conv ctxt
  in CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN' resolve_tac ctxt [TrueI] end

fun mk_rtrancl T = Const (@{const_name rtrancl_list_impl}, T);

fun mk_trancl T = Const (@{const_name trancl_list_impl}, T);

fun dest_rtrancl_Image
      (Const (@{const_name Image}, T) $ (Const (@{const_name rtrancl}, _) $ r) $ x) = (T, r, x)
  | dest_rtrancl_Image _ = raise Match

fun dest_trancl_Image
      (Const (@{const_name Image}, T) $ (Const (@{const_name trancl}, _) $ r) $ x) = (T, r, x)
  | dest_trancl_Image _ = raise Match

fun gen_simproc dest mk_const eq_thm ctxt ct =
  let
    val t = Thm.term_of ct;
    val (T, r, x) = t |> dest;
  in
    (*make sure that the relation as well as the given domain are finite sets*)
    (case (try HOLogic.dest_set r, try HOLogic.dest_set x) of
      (SOME xs, SOME ys) =>
        let
          (*types*)
          val setT = T |> dest_funT |> snd |> dest_funT |> fst;
          val eltT = setT |> HOLogic.dest_setT;
          val prodT = HOLogic.mk_prodT (eltT, eltT);
          val prod_listT = HOLogic.listT prodT;
          val listT = HOLogic.listT eltT;

          (*terms*)
          val set = Const (@{const_name List.set}, listT --> setT);
          val const = mk_const (prod_listT --> listT --> listT);
          val r' = HOLogic.mk_list prodT xs;
          val x' = HOLogic.mk_list eltT ys;
          val t' = set $ (const $ r' $ x')
          val u = Value_Command.value ctxt t';
          val eval = (t', u) |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;

          val maybe_rule =
            try (Goal.prove ctxt [] [] eval) (fn {context, ...} => eval_tac context 1);
        in
          (case maybe_rule of
            SOME rule =>
            let
              val conv = (t, t') |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;
              val eq_thm' = Goal.prove ctxt [] [] conv (fn {context = ctxt', ...} =>
                resolve_tac ctxt' [eq_thm] 1 THEN REPEAT (simp_tac ctxt' 1));
            in
              SOME (@{thm HOL.trans} OF [eq_thm', rule] RS @{thm eq_reflection})
            end
          | NONE => NONE)
        end
    | _ => NONE)
  end


val rtrancl_simproc = gen_simproc dest_rtrancl_Image mk_rtrancl @{thm rtrancl_Image_eq}
val trancl_simproc = gen_simproc dest_trancl_Image mk_trancl @{thm trancl_Image_eq}

end
\<close>

simproc_setup rtrancl_Image ("r\<^sup>* `` x") = \<open>K Finite_Trancl_Image.rtrancl_simproc\<close>
simproc_setup trancl_Image  ("r\<^sup>+ `` x") = \<open>K Finite_Trancl_Image.trancl_simproc\<close>

subsection \<open>Example\<close>

text \<open>
  The images of (reflexive) transitive closures are computed by evaluation.
\<close>
lemma
  "{(1::nat, 2), (2, 3), (3, 4), (4, 5)}\<^sup>* `` {1} = {1, 2, 3, 4, 5}"
  "{(1::nat, 2), (2, 3), (3, 4), (4, 5)}\<^sup>+ `` {1} = {2, 3, 4, 5}"
  apply simp_all
  apply auto
done

text \<open>
  Evaluation does not allow for free variables and thus fails in their presence.
\<close>
lemma
  "{(x, y)}\<^sup>* `` {x} = {x, y}"
  oops

end

