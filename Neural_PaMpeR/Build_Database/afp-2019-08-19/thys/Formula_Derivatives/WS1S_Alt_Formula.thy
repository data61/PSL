section \<open>Concrete Atomic WS1S Formulas (Singleton Semantics for FO Variables)\<close>

(*<*)
theory WS1S_Alt_Formula
imports
  Abstract_Formula
  WS1S_Prelim
begin
(*>*)

datatype (FOV0: 'fo, SOV0: 'so) atomic =
  Fo 'fo |
  Z 'fo |
  Less 'fo 'fo |
  In 'fo 'so

derive linorder atomic

type_synonym fo = nat
type_synonym so = nat
type_synonym ws1s = "(fo, so) atomic"
type_synonym formula = "(ws1s, order) aformula"

primrec wf0 where
  "wf0 idx (Fo m) = LESS FO m idx"
| "wf0 idx (Z m) = LESS FO m idx"
| "wf0 idx (Less m1 m2) = (LESS FO m1 idx \<and> LESS FO m2 idx)"
| "wf0 idx (In m M) = (LESS FO m idx \<and> LESS SO M idx)"

inductive lformula0 where
  "lformula0 (Fo m)"
| "lformula0 (Z m)"
| "lformula0 (Less m1 m2)"
| "lformula0 (In m M)"

code_pred lformula0 .

declare lformula0.intros[simp]

inductive_cases lformula0E[elim]: "lformula0 a"

abbreviation "FV0 \<equiv> case_order FOV0 SOV0"

fun find0 where
  "find0 FO i (Fo m) = (i = m)"
| "find0 FO i (Z m) = (i = m)"
| "find0 FO i (Less m1 m2) = (i = m1 \<or> i = m2)"
| "find0 FO i (In m _) = (i = m)"
| "find0 SO i (In _ M) = (i = M)"
| "find0 _ _ _ = False"

abbreviation "decr0 ord k \<equiv> map_atomic (case_order (dec k) id ord) (case_order id (dec k) ord)"

primrec satisfies0 where
  "satisfies0 \<AA> (Fo m) = (\<exists>x. m\<^bsup>\<AA>\<^esup>FO = {|x|})"
| "satisfies0 \<AA> (Z m) = (m\<^bsup>\<AA>\<^esup>FO = {||})"
| "satisfies0 \<AA> (Less m1 m2) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in if \<not>(\<exists>x. P1 = {|x|}) \<or> \<not>(\<exists>x. P2 = {|x|})
   then False
   else fthe_elem P1 < fthe_elem P2)"
| "satisfies0 \<AA> (In m M) =
   (let P = m\<^bsup>\<AA>\<^esup>FO in if \<not>(\<exists>x. P = {|x|}) then False else fMin P |\<in>| M\<^bsup>\<AA>\<^esup>SO)"

fun lderiv0 where
  "lderiv0 (bs1, bs2) (Fo m) = (if bs1 ! m then FBase (Z m) else FBase (Fo m))"
| "lderiv0 (bs1, bs2) (Z m) = (if bs1 ! m then FBool False else FBase (Z m))"
| "lderiv0 (bs1, bs2) (Less m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (Less m1 m2)
  | (True, False) \<Rightarrow> FAnd (FBase (Z m1)) (FBase (Fo m2))
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (In m M) = (case (bs1 ! m, bs2 ! M) of
    (False, _) \<Rightarrow> FBase (In m M)
  | (True, True) \<Rightarrow> FBase (Z m)
  | _ \<Rightarrow> FBool False)"

primrec rev where
  "rev (Fo m) = Fo m"
| "rev (Z m) = Z m"
| "rev (Less m1 m2) = Less m2 m1"
| "rev (In m M) = In m M"

abbreviation "rderiv0 v \<equiv> map_aformula rev id o lderiv0 v o rev"

primrec nullable0 where
  "nullable0 (Fo m) = False"
| "nullable0 (Z m) = True"
| "nullable0 (Less m1 m2) = False"
| "nullable0 (In m M) = False"

lemma fimage_Suc_fsubset0[simp]: "Suc |`| A |\<subseteq>| {|0|} \<longleftrightarrow> A = {||}"
  by blast

lemma fsubset_singleton_iff: "A |\<subseteq>| {|x|} \<longleftrightarrow> A = {||} \<or> A = {|x|}"
  by blast

definition "restrict ord P = (case ord of FO \<Rightarrow> \<exists>x. P = {|x|} | SO \<Rightarrow> True)"
definition "Restrict ord i = (case ord of FO \<Rightarrow> FBase (Fo i) | SO \<Rightarrow> FBool True)"

declare [[goals_limit = 50]]


global_interpretation WS1S_Alt: Formula SUC LESS assigns nvars Extend CONS SNOC Length
  extend size_atom zero \<sigma> eval downshift upshift finsert cut len restrict Restrict
  lformula0 FV0 find0 wf0 decr0 satisfies0 nullable0 lderiv0 rderiv0 undefined
  defines norm = "Formula_Operations.norm find0 decr0"
  and nFOr = "Formula_Operations.nFOr :: formula \<Rightarrow> _"
  and nFAnd = "Formula_Operations.nFAnd :: formula \<Rightarrow> _"
  and nFNot = "Formula_Operations.nFNot find0 decr0 :: formula \<Rightarrow> _"
  and nFEx = "Formula_Operations.nFEx find0 decr0"
  and nFAll = "Formula_Operations.nFAll find0 decr0"
  and decr = "Formula_Operations.decr decr0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and find = "Formula_Operations.find find0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and FV = "Formula_Operations.FV FV0"
  and RESTR = "Formula_Operations.RESTR Restrict :: _ \<Rightarrow> formula"
  and RESTRICT = "Formula_Operations.RESTRICT Restrict FV0"
  and deriv = "\<lambda>d0 (a :: atom) (\<phi> :: formula). Formula_Operations.deriv extend d0 a \<phi>"
  and nullable = "\<lambda>\<phi> :: formula. Formula_Operations.nullable nullable0 \<phi>"
  and fut_default = "Formula.fut_default extend zero rderiv0"
  and fut = "Formula.fut extend zero find0 decr0 rderiv0"
  and finalize = "Formula.finalize SUC extend zero find0 decr0 rderiv0"
  and final = "Formula.final SUC extend zero find0 decr0
     nullable0 rderiv0 :: idx \<Rightarrow> formula \<Rightarrow> _"
  and ws1s_wf = "Formula_Operations.wf SUC (wf0 :: idx \<Rightarrow> ws1s \<Rightarrow> _)"
  and ws1s_lformula = "Formula_Operations.lformula lformula0 :: formula \<Rightarrow> _"
  and check_eqv = "\<lambda>idx. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>) (=)"
  and bounded_check_eqv = "\<lambda>idx. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>) (=)"
  and automaton = "DA.automaton
    (\<lambda>a \<phi>. norm (deriv lderiv0 (a :: atom) \<phi> :: formula))"
proof
  fix k idx and a :: ws1s and l assume "wf0 (SUC k idx) a" "LESS k l (SUC k idx)" "\<not> find0 k l a"
  then show "wf0 idx (decr0 k l a)"
    by (induct a) (unfold wf0.simps atomic.map find0.simps,
     (transfer, force simp: dec_def split: if_splits order.splits)+) \<comment> \<open>slow\<close>
next
  fix k and a :: ws1s and l assume "lformula0 a"
  then show "lformula0 (decr0 k l a)" by (induct a) auto
next
  fix i k and a :: ws1s and \<AA> :: interp and P assume *: "\<not> find0 k i a" "LESS k i (SUC k (#\<^sub>V \<AA>))"
    and disj: "lformula0 a \<or> len P \<le> Length \<AA>"
  from disj show "satisfies0 (Extend k i \<AA> P) a = satisfies0 \<AA> (decr0 k i a)"
  proof
    assume "lformula0 a"
    then show ?thesis using *
      by (induct a)
        (auto simp: dec_def split: if_splits order.split option.splits bool.splits) \<comment> \<open>slow\<close>
  next
    assume "len P \<le> Length \<AA>"
    with * show ?thesis
    proof (induct a)
      case Fo then show ?case by (cases k) (auto simp: dec_def)
    next
      case Z then show ?case by (cases k) (auto simp: dec_def)
    next
      case Less then show ?case by (cases k) (auto simp: dec_def)
    next
      case In then show ?case by (cases k) (auto simp: dec_def)
    qed
  qed
next
  fix idx and a :: ws1s and x assume "lformula0 a" "wf0 idx a"
  then show "Formula_Operations.wf SUC wf0 idx (lderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.wf.simps Let_def split: bool.splits order.splits)
next
  fix a :: ws1s and x assume "lformula0 a"
  then show "Formula_Operations.lformula lformula0 (lderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.lformula.simps split: bool.splits)
next
  fix idx and a :: ws1s and x assume "wf0 idx a"
  then show "Formula_Operations.wf SUC wf0 idx (rderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.wf.simps Let_def sorted_append
        split: bool.splits order.splits nat.splits)
next
  fix \<AA> :: interp and a :: ws1s
  note fmember.rep_eq[symmetric, simp]
  assume "Length \<AA> = 0"
  then show "nullable0 a = satisfies0 \<AA> a"
    by (induct a, unfold wf0.simps nullable0.simps satisfies0.simps Let_def)
      (transfer, (auto 0 3 dest: MSB_greater split: prod.splits if_splits option.splits bool.splits nat.splits) [])+  \<comment> \<open>slow\<close>
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp] upshift_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "lformula0 a" "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies Extend Length satisfies0 \<AA> (lderiv0 x a) =
     satisfies0 (CONS x \<AA>) a"
   proof (induct a)
   qed (auto split: prod.splits bool.splits)
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp] upshift_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "lformula0 a" "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies_bounded Extend Length len satisfies0 \<AA> (lderiv0 x a) =
     satisfies0 (CONS x \<AA>) a"
     by (induct a) (auto split: prod.splits bool.splits)
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies_bounded Extend Length len satisfies0 \<AA> (rderiv0 x a) =
     satisfies0 (SNOC x \<AA>) a"
   proof (induct a)
     case Less then show ?case
       apply (auto 2 0 split: prod.splits option.splits bool.splits)
       apply (auto simp add: fsubset_singleton_iff)
       apply (metis assigns_less_Length finsertCI less_not_sym)
       apply force
       apply (metis assigns_less_Length finsertCI less_not_sym)
       apply force
       done
   next
     case In then show ?case by (force split: prod.splits)
   qed (auto split: prod.splits)
next
   fix a :: ws1s and \<AA> \<BB> :: interp
   assume "wf0 (#\<^sub>V \<BB>) a" "#\<^sub>V \<AA> = #\<^sub>V \<BB>" "(\<And>m k. LESS k m (#\<^sub>V \<BB>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k)" "lformula0 a"
   then show "satisfies0 \<AA> a \<longleftrightarrow> satisfies0 \<BB> a" by (induct a) auto
next
   fix a :: ws1s
   assume "lformula0 a"
   moreover
   define d where "d = Formula_Operations.deriv extend lderiv0"
   define \<Phi> :: "_ \<Rightarrow> (ws1s, order) aformula set"
     where "\<Phi> a =
       (case a of
         Fo m \<Rightarrow> {FBase (Fo m), FBase (Z m), FBool False}
       | Z m \<Rightarrow> {FBase (Z m), FBool False}
       | Less m1 m2 \<Rightarrow> {FBase (Less m1 m2),
          FAnd (FBase (Z m1)) (FBase (Fo m2)),
          FAnd (FBase (Z m1)) (FBase (Z m2)),
          FAnd (FBase (Z m1)) (FBool False),
          FAnd (FBool False) (FBase (Fo m2)),
          FAnd (FBool False) (FBase (Z m2)),
          FAnd (FBool False) (FBool False),
         FBool False}
       | In i I \<Rightarrow> {FBase (In i I),  FBase (Z i), FBool False})" for a
   { fix xs
     note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
     from \<open>lformula0 a\<close> have "FBase a \<in> \<Phi> a" by (cases a) auto
     moreover have "\<And>x \<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> d x \<phi> \<in> \<Phi> a"
       by (auto simp: d_def split: atomic.splits list.splits bool.splits if_splits option.splits)
     then have "\<And>\<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> fold d xs \<phi> \<in> \<Phi> a" by (induct xs) auto
     ultimately have "fold d xs (FBase a) \<in> \<Phi> a" by blast
   }
   moreover have "finite (\<Phi> a)" using \<open>lformula0 a\<close> unfolding \<Phi>_def by (auto split: atomic.splits)
   ultimately show "finite {fold d xs (FBase a) | xs. True}" by (blast intro: finite_subset)
next
   fix a :: ws1s
   define d where "d = Formula_Operations.deriv extend rderiv0"
   define \<Phi> :: "_ \<Rightarrow> (ws1s, order) aformula set"
     where "\<Phi> a =
       (case a of
         Fo m \<Rightarrow> {FBase (Fo m), FBase (Z m), FBool False}
       | Z m \<Rightarrow> {FBase (Z m), FBool False}
       | Less m1 m2 \<Rightarrow> {FBase (Less m1 m2),
          FAnd (FBase (Z m2)) (FBase (Fo m1)) ,
          FAnd (FBase (Z m2)) (FBase (Z m1)),
          FAnd (FBase (Z m2)) (FBool False),
          FAnd (FBool False) (FBase (Fo m1)),
          FAnd (FBool False) (FBase (Z m1)),
          FAnd (FBool False) (FBool False),
         FBool False}
       | In i I \<Rightarrow> {FBase (In i I),  FBase (Z i), FBool False})" for a
   { fix xs
     note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
     then have "FBase a \<in> \<Phi> a" by (auto split: atomic.splits option.splits)
     moreover have "\<And>x \<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> d x \<phi> \<in> \<Phi> a"
       by (auto simp add: d_def Let_def not_le gr0_conv_Suc
         split: atomic.splits list.splits bool.splits if_splits option.splits nat.splits)
     then have "\<And>\<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> fold d xs \<phi> \<in> \<Phi> a"
       by (induct xs) auto
     ultimately have "fold d xs (FBase a) \<in> \<Phi> a" by blast
   }
   moreover have "finite (\<Phi> a)" unfolding \<Phi>_def using [[simproc add: finite_Collect]]
     by (auto split: atomic.splits)
   ultimately show "finite {fold d xs (FBase a) | xs. True}" by (blast intro: finite_subset)
next
  fix k l and a :: ws1s
  show "find0 k l a \<longleftrightarrow> l \<in> FV0 k a" by (induct a rule: find0.induct) auto
next
  fix a :: ws1s and k :: order
  show "finite (FV0 k a)" by (cases k) (induct a, auto)+
next
  fix idx a k v
  assume "wf0 idx a" "v \<in> FV0 k a"
  then show "LESS k v idx" by (cases k) (induct a, auto)+
next
  fix idx k i
  assume "LESS k i idx"
  then show "Formula_Operations.wf SUC wf0 idx (Restrict k i)"
     unfolding Restrict_def by (cases k) (auto simp: Formula_Operations.wf.simps)
next
  fix k and i :: nat
  show "Formula_Operations.lformula lformula0 (Restrict k i)"
    unfolding Restrict_def by (cases k) (auto simp: Formula_Operations.lformula.simps)
next
  fix i \<AA> k P r
  assume "i\<^bsup>\<AA>\<^esup>k = P"
  then show "restrict k P \<longleftrightarrow>
    Formula_Operations.satisfies_gen Extend Length satisfies0 r \<AA> (Restrict k i)"
    unfolding restrict_def Restrict_def
    by (cases k) (auto simp: Formula_Operations.satisfies_gen.simps)
qed (auto simp: Extend_commute_unsafe downshift_def upshift_def fimage_iff Suc_le_eq len_def
  dec_def eval_def cut_def len_downshift_helper CONS_inj dest!: CONS_surj
  dest: fMax_ge fMax_ffilter_less fMax_boundedD fsubset_fsingletonD
  split: order.splits if_splits)

(*Workaround for code generation*)
lemma check_eqv_code[code]: "check_eqv idx r s =
  ((ws1s_wf idx r \<and> ws1s_lformula r) \<and> (ws1s_wf idx s \<and> ws1s_lformula s) \<and>
  (case rtrancl_while (\<lambda>(p, q). final idx p = final idx q)
    (\<lambda>(p, q). map (\<lambda>a. (norm (deriv lderiv0 a p), norm (deriv lderiv0 a q))) (\<sigma> idx))
    (norm (RESTRICT r), norm (RESTRICT s)) of
    None \<Rightarrow> False
  | Some ([], x) \<Rightarrow> True
  | Some (a # list, x) \<Rightarrow> False))"
  unfolding check_eqv_def WS1S_Alt.check_eqv_def WS1S_Alt.step_alt ..

definition while where [code del, code_abbrev]: "while idx \<phi> = while_default (fut_default idx \<phi>)"
declare while_default_code[of "fut_default idx \<phi>" for idx \<phi>, folded while_def, code]

lemma check_eqv_sound: 
  "\<lbrakk>#\<^sub>V \<AA> = idx; check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (WS1S_Alt.sat \<AA> \<phi> \<longleftrightarrow> WS1S_Alt.sat \<AA> \<psi>)"
  unfolding check_eqv_def by (rule WS1S_Alt.check_eqv_soundness)

lemma bounded_check_eqv_sound:
  "\<lbrakk>#\<^sub>V \<AA> = idx; bounded_check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (WS1S_Alt.sat\<^sub>b \<AA> \<phi> \<longleftrightarrow> WS1S_Alt.sat\<^sub>b \<AA> \<psi>)"
  unfolding bounded_check_eqv_def by (rule WS1S_Alt.bounded_check_eqv_soundness)

method_setup check_equiv = \<open>
  let
    fun tac ctxt =
      let
        val conv = @{computation_check terms: Trueprop
          "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
          "plus :: nat \<Rightarrow> _" "minus :: nat \<Rightarrow> _"
          "times :: nat \<Rightarrow> _" "divide :: nat \<Rightarrow> _" "modulo :: nat \<Rightarrow> _"
          "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
          check_eqv datatypes: formula "int list" integer idx
          "nat \<times> nat" "nat option" "bool option"} ctxt
      in
        CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    Scan.succeed (SIMPLE_METHOD' o tac)
  end
\<close>

end
