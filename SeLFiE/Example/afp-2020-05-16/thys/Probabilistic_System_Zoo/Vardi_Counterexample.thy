section \<open>Vardi Systems Are Not a BNF\<close>

(*<*)
theory Vardi_Counterexample
imports
  Vardi
begin
(*>*)

text \<open>Do not import this theory. It contains an inconsistent axiomatization.
The point is to exhibit the particular inconsistency.\<close>

(*<*)
text \<open>

Let V = (P + D) / ~ be the Vardi functor
  (P - powerset functor, 
   D - probability distribution functor,
   ~ - relation identifying singleton sets with Dirac distributions).

Lemma: V does not preserve weak pullbacks

By contradiction. Let X = {a, b}, C = {a}, f : X -> C with f(x) = a. Consider the cospan

X --f-> C <-f-- X,

which has the pullback Q = {(a, a), (a, b), (b, a), (b, b)}.

Then let VQ be a pullback of the cospan

V X --V f-> V C <-V f--V X.

Now pick x = L {a, b} : V X and y = R [a -> 0.5, b -> 0.5] : V X (L and R are the sum's injections).

We have V f x = L {a} = R [a -> 1] = V f y.

Therefore the pullback VQ must contain an element z s.t. V fst z = {a, b} and V snd z = [a -> 0.5, b -> 0.5]
 where fst (x, y) = x and snd (x, y) = y are the standard projections. There is however no such element z.
\<close>
(*>*)

text \<open>
We axiomatize the relator commutation property and show that we can deduce @{term False} from it.

We cannot do this with a locale, since we need the fully polymorphic version of the following axiom.
\<close>

axiomatization where
  inconsistent: "rel_var R1 S1 OO rel_var R2 S2 \<le> rel_var (R1 OO R2) (S1 OO S2)"

bnf "('a, 'b, 'k) var"
  map: map_var
  sets: set1_var set2_var
  bd: "bd_pre_var0 :: 'k var0_pre_var0_bdT rel"
  rel: rel_var
proof (standard, goal_cases)
  case 1 then show ?case
    by transfer (auto simp add: var0.map_id)
next
  case 2 then show ?case
    apply (rule ext)
    apply transfer
    apply (auto simp add: var0.map_comp)
    done
next
  case 3 then show ?case
    apply transfer
    apply (subst var0.map_cong0)
    apply assumption
    apply assumption
    apply auto
    done
next
  case 4 then show ?case
    apply (rule ext)
    apply transfer
    apply (simp add: var0.set_map0)
    done
next
  case 5 then show ?case
    apply (rule ext)
    apply transfer
    apply (simp add: var0.set_map0)
    done
next
  case 6 then show ?case by (rule var0.bd_card_order)
next
  case 7 then show ?case
    by (simp add: var0.bd_cinfinite)
next
  case (8 x) then show ?case
    unfolding subset_eq set1_var_def by (simp add: var0.set_bd(1)) 
next
  case (9 x) then show ?case
    unfolding subset_eq set2_var_def by (simp add: var0.set_bd(2)) 
next
  case 10 then show ?case by (rule inconsistent) \<comment> \<open>BAAAAAMMMM\<close>
next
  case 11 then show ?case
      unfolding rel_var.simps[abs_def] by (auto simp: fun_eq_iff)
qed

lift_definition X :: "(bool, 'b, 'k) var" is "BPS (binsert (True, undefined) (binsert (False, undefined) bempty))".

lift_definition Y :: "(bool, 'b, 'k) var" is "PMF (pmf_of_set {(True, undefined), (False, undefined)})".

lift_definition Z :: "(bool, 'b, 'k) var" is "PMF (return_pmf (True, undefined))".

lift_definition Z' :: "(bool, 'b, 'k) var" is "BPS (bsingleton (True, undefined))".

lift_definition C :: "(bool\<times>bool, 'b\<times>'b, 'k) var" is
  "BPS (binsert ((True, True), (undefined, undefined)) (binsert ((False, True), (undefined, undefined)) bempty))".

lift_definition C' :: "(bool\<times>bool, 'b\<times>'b, 'k) var" is
  "PMF (map_pmf (\<lambda>((a, b), (c, d)). ((a,c), (b,d))) (pair_pmf (return_pmf (True, undefined)) (pmf_of_set {(True, undefined), (False, undefined)})))".

lemma Z_eq_Z': "Z = Z'"
  by transfer auto

lemma False
proof -
  have [simp]: "\<And>x. pmf_of_set {(True, undefined), (False, undefined)} \<noteq> return_pmf x"
    by (auto simp: pmf_eq_iff split: split_indicator)
  have [simp]: "\<And>x. binsert (True, undefined) (binsert (False, undefined) bempty) \<noteq> bsingleton x"
    unfolding bsingleton_def by transfer auto

  define R where "R a b = b" for a b :: bool
  have "rel_var R (=) X Z'"
    unfolding R_def var.in_rel mem_Collect_eq subset_eq
    apply (intro exI[of _ C])
    apply transfer
    apply (auto simp: set_bset binsert.rep_eq fsts.simps snds.simps bempty.rep_eq bsingleton_def)
    done
  moreover
  define S where "S a b = a" for a b :: bool
  have "rel_var S (=) Z Y"
    unfolding S_def var.in_rel mem_Collect_eq subset_eq
    apply (intro exI[of _ C'])
    apply transfer
    apply (auto simp: fsts.simps snds.simps pmf.map_comp comp_def split_beta map_fst_pair_pmf map_snd_pair_pmf)
    done
  ultimately have "rel_var (R OO S) ((=) OO (=)) X Y" (is "rel_var ?R ?S X Y")
    unfolding var.rel_compp unfolding Z_eq_Z' by blast
  moreover have "\<not> rel_var ?R ?S X Y"
    unfolding var.in_rel mem_Collect_eq subset_eq
    apply (auto simp: split_beta)
    apply transfer'
    apply (auto elim!: var_eq.cases)
    apply (case_tac [!] z)
    apply (auto simp add: snds.simps)
    done
  ultimately show False
    by auto
qed

(*<*)
end
(*>*)
