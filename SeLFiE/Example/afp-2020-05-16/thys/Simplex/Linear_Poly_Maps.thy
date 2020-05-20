(* Authors: F. Maric, M. Spasic, R. Thiemann *)
theory Linear_Poly_Maps
  imports Abstract_Linear_Poly
    "HOL-Library.Finite_Map"
    "HOL-Library.Monad_Syntax"
begin

(* ************************************************************************** *)
(* Executable implementation                                                  *)
(* ************************************************************************** *)
definition get_var_coeff :: "(var, rat) fmap \<Rightarrow> var \<Rightarrow> rat" where
  "get_var_coeff lp v == case fmlookup lp v of None \<Rightarrow> 0 | Some c \<Rightarrow> c"

definition set_var_coeff :: "var \<Rightarrow> rat \<Rightarrow> (var, rat) fmap \<Rightarrow> (var, rat) fmap" where
  "set_var_coeff v c lp ==
      if c = 0 then fmdrop v lp else fmupd v c lp"

lift_definition LinearPoly :: "(var, rat) fmap \<Rightarrow> linear_poly" is get_var_coeff
proof -
  fix fmap
  show "inv (get_var_coeff fmap)" unfolding inv_def
    by (rule finite_subset[OF _ dom_fmlookup_finite[of fmap]],
        auto intro: fmdom'I simp: get_var_coeff_def split: option.splits)
qed

definition ordered_keys :: "('a :: linorder, 'b)fmap \<Rightarrow> 'a list" where
  "ordered_keys m = sorted_list_of_set (fset (fmdom m))"

context includes fmap.lifting lifting_syntax
begin

lemma [transfer_rule]: "(((=) ===> (=)) ===> pcr_linear_poly ===> (=)) (=) pcr_linear_poly"
  by(standard,auto simp: pcr_linear_poly_def cr_linear_poly_def rel_fun_def OO_def)

lemma [transfer_rule]: "(pcr_fmap (=) (=) ===> pcr_linear_poly) (\<lambda> f x. case f x of None \<Rightarrow> 0 | Some x \<Rightarrow> x) LinearPoly"
  by (standard, transfer, auto simp:get_var_coeff_def fmap.pcr_cr_eq cr_fmap_def)

lift_definition linear_poly_map :: "linear_poly \<Rightarrow> (var, rat) fmap" is
  "\<lambda> lp x. if lp x = 0 then None else Some (lp x)" by (auto simp: dom_def)

lemma certificate[code abstype]:
  "LinearPoly (linear_poly_map lp) = lp"
  by (transfer, auto)

text\<open>Zero\<close>
definition zero :: "(var, rat)fmap" where "zero = fmempty"

lemma [code abstract]:
  "linear_poly_map 0 = zero" unfolding zero_def
  by (transfer, auto)

text\<open>Addition\<close>

definition add_monom :: "rat \<Rightarrow> var \<Rightarrow> (var, rat) fmap \<Rightarrow> (var, rat) fmap" where
  "add_monom c v lp == set_var_coeff v (c + get_var_coeff lp v) lp"

definition add :: "(var, rat) fmap \<Rightarrow> (var, rat) fmap \<Rightarrow> (var, rat) fmap" where
  "add lp1 lp2 = foldl (\<lambda> lp v. add_monom (get_var_coeff lp1 v) v lp) lp2 (ordered_keys lp1)"

lemma lookup_add_monom:
  "get_var_coeff lp v + c \<noteq> 0 \<Longrightarrow>
    fmlookup (add_monom c v lp) v = Some (get_var_coeff lp v + c)"
  "get_var_coeff lp v + c = 0 \<Longrightarrow>
    fmlookup (add_monom c v lp) v = None"
  "x \<noteq> v \<Longrightarrow> fmlookup (add_monom c v lp) x = fmlookup lp x"
  unfolding add_monom_def get_var_coeff_def set_var_coeff_def
  by auto

lemma fmlookup_fold_not_mem: "x \<notin> set k1 \<Longrightarrow>
  fmlookup (foldl (\<lambda>lp v. add_monom (get_var_coeff P1 v) v lp) P2 k1) x
    = fmlookup P2 x"
  by (induct k1 arbitrary: P2, auto simp: lookup_add_monom)

lemma [code abstract]:
  "linear_poly_map (p1 + p2) = add (linear_poly_map p1) (linear_poly_map p2)"
proof (rule fmap_ext)
  fix x :: nat (* index *)
  let ?p1 = "fmlookup (linear_poly_map p1) x"
  let ?p2 = "fmlookup (linear_poly_map p2) x"
  define P1 where "P1 = linear_poly_map p1"
  define P2 where "P2 = linear_poly_map p2"
  define k1 where "k1 = ordered_keys P1"
  have k1: "distinct k1 \<and> fset (fmdom P1) = set k1" unfolding k1_def P1_def ordered_keys_def
    by auto
  have id: "fmlookup (linear_poly_map (p1 + p2)) x = (case ?p1 of None \<Rightarrow> ?p2 | Some y1 \<Rightarrow>
    (case ?p2 of None \<Rightarrow> Some y1 | Some y2 \<Rightarrow> if y1 + y2 = 0 then None else Some (y1 + y2)))"
    by (transfer, auto)
  show "fmlookup (linear_poly_map (p1 + p2)) x = fmlookup (add (linear_poly_map p1) (linear_poly_map p2)) x"
  proof (cases "fmlookup P1 x")
    case None
    from fmdom_notI[OF None] have "x \<notin> fset (fmdom P1)" by (meson notin_fset)
    with k1 have x: "x \<notin> set k1" by auto
    show ?thesis unfolding id P1_def[symmetric] P2_def[symmetric] None
      unfolding add_def k1_def[symmetric] fmlookup_fold_not_mem[OF x] by auto
  next
    case (Some y1)
    from fmdomI[OF this] have "x \<in> fset (fmdom P1)" by (meson notin_fset)
    with k1 have "x \<in> set k1" by auto
    from split_list[OF this] obtain bef aft where k1_id: "k1 = bef @ x # aft" by auto
    with k1 have x: "x \<notin> set bef" "x \<notin> set aft" by auto
    have xy1: "get_var_coeff P1 x = y1" using Some unfolding get_var_coeff_def by auto
    let ?P = "foldl (\<lambda>lp v. add_monom (get_var_coeff P1 v) v lp) P2 bef"
    show ?thesis unfolding id P1_def[symmetric] P2_def[symmetric] Some option.simps
      unfolding add_def k1_def[symmetric] k1_id foldl_append foldl_Cons
      unfolding fmlookup_fold_not_mem[OF x(2)] xy1
    proof -
      show "(case fmlookup P2 x of None \<Rightarrow> Some y1 | Some y2 \<Rightarrow> if y1 + y2 = 0 then None else Some (y1 + y2))
        = fmlookup (add_monom y1 x ?P) x"
      proof (cases "get_var_coeff ?P x + y1 = 0")
        case True
        from Some[unfolded P1_def] have y1: "y1 \<noteq> 0"
          by (transfer, auto split: if_splits)
        then show ?thesis unfolding lookup_add_monom(2)[OF True] using True
          unfolding get_var_coeff_def[of _ x] fmlookup_fold_not_mem[OF x(1)]
          by (auto split: option.splits)
      next
        case False
        show ?thesis unfolding lookup_add_monom(1)[OF False] using False
          unfolding get_var_coeff_def[of _ x] fmlookup_fold_not_mem[OF x(1)]
          by (auto split: option.splits)
      qed
    qed
  qed
qed


text\<open>Scaling\<close>
definition scale :: "rat \<Rightarrow> (var, rat) fmap \<Rightarrow> (var, rat) fmap" where
  "scale r lp = (if r = 0 then fmempty else (fmmap ((*) r) lp))"

lemma [code abstract]:
  "linear_poly_map (r *R p) = scale r (linear_poly_map p)"
proof (cases "r = 0")
  case True
  then have *: "(r = 0) = True" by simp
  show ?thesis unfolding scale_def * if_True using True
    by (transfer, auto)
next
  case False
  then have *: "(r = 0) = False" by simp
  show ?thesis unfolding scale_def * if_False using False
    by (transfer, auto)
qed


(* Coeff *)
lemma coeff_code [code]:
  "coeff lp = get_var_coeff (linear_poly_map lp)"
  by (rule ext, unfold get_var_coeff_def, transfer, auto)

(* Var *)
lemma Var_code[code abstract]:
  "linear_poly_map (Var x) = set_var_coeff x 1 fmempty"
  unfolding set_var_coeff_def
  by (transfer, auto split: if_splits simp: fun_eq_iff map_upd_def)

(* vars *)
lemma vars_code[code]: "vars lp = fset (fmdom (linear_poly_map lp))"
  by (transfer, auto simp: Transfer.Rel_def rel_fun_def pcr_fset_def cr_fset_def)

(* vars_list *)
lemma vars_list_code[code]: "vars_list lp = ordered_keys (linear_poly_map lp)"
  unfolding ordered_keys_def vars_code[symmetric]
  by (transfer, auto)

(* valuate *)
lemma valuate_code[code]:  "valuate lp val = (
  let lpm = linear_poly_map lp
  in sum_list (map (\<lambda> x. (the (fmlookup lpm x)) *R (val x)) (vars_list lp)))"
  unfolding Let_def
proof (subst sum_list_distinct_conv_sum_set)
  show "distinct (vars_list lp)"
    by (transfer, auto)
next
  show "lp \<lbrace> val \<rbrace> =
        (\<Sum>x\<in>set (vars_list lp). the (fmlookup (linear_poly_map lp) x) *R val x)"
    unfolding set_vars_list
    by (transfer, auto)
qed

end

lemma lp_monom_code[code]: "linear_poly_map (lp_monom c x) = (if c = 0 then fmempty else fmupd x c fmempty)"
proof (rule fmap_ext, goal_cases)
  case (1 y)
  include fmap.lifting
  show ?case by (cases "c = 0", (transfer, auto)+)
qed

instantiation linear_poly :: equal
begin

definition "equal_linear_poly x y = (linear_poly_map x = linear_poly_map y)"

instance
proof (standard, unfold equal_linear_poly_def, standard)
  fix x y
  assume "linear_poly_map x = linear_poly_map y"
  from arg_cong[OF this, of LinearPoly, unfolded certificate]
  show "x = y" .
qed auto
end

end