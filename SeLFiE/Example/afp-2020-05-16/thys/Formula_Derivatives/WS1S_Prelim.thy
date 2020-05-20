section \<open>WS1S Interpretations\<close>

(*<*)
theory WS1S_Prelim
imports
  FSet_More
  Deriving.Compare_Instances
  "List-Index.List_Index"
begin

hide_const (open) cut
(*>*)

definition "eval P x = (x |\<in>| P)"
definition "downshift P = (\<lambda>x. x - Suc 0) |`| (P |-| {|0|})"
definition "upshift P = Suc |`| P"
definition "lift bs i P = (if bs ! i then finsert 0 (upshift P) else upshift P)"
definition "snoc n bs i P = (if bs ! i then finsert n P else P)"
definition "cut n P = ffilter (\<lambda>i. i < n) P"
definition "len P = (if P = {||} then 0 else Suc (fMax P))"

datatype order = FO | SO
derive linorder order
instantiation order :: enum begin
  definition "enum_order = [FO, SO]"
  definition "enum_all_order P = (P FO \<and> P SO)"
  definition "enum_ex_order P = (P FO \<or> P SO)"
  lemmas enum_defs = enum_order_def enum_all_order_def enum_ex_order_def
  instance proof qed (auto simp: enum_defs, (metis (full_types) order.exhaust)+)
end

typedef idx = "UNIV :: (nat \<times> nat) set" by (rule UNIV_witness)

setup_lifting type_definition_idx

lift_definition SUC :: "order \<Rightarrow> idx \<Rightarrow> idx" is
  "\<lambda>ord (m, n). case ord of FO \<Rightarrow> (Suc m, n) | SO \<Rightarrow> (m, Suc n)" .
lift_definition LESS :: "order \<Rightarrow> nat \<Rightarrow> idx \<Rightarrow> bool" is
  "\<lambda>ord l (m, n). case ord of FO \<Rightarrow> l < m | SO \<Rightarrow> l < n" .
abbreviation "LEQ ord l idx \<equiv> LESS ord l (SUC ord idx)"

definition "MSB Is \<equiv>
  if \<forall>P \<in> set Is. P = {||} then 0 else Suc (Max (\<Union>P \<in> set Is. fset P))"

lemma MSB_Nil[simp]: "MSB [] = 0"
  unfolding MSB_def by simp

lemma MSB_Cons[simp]: "MSB (I # Is) = max (if I = {||} then 0 else Suc (fMax I)) (MSB Is)"
  unfolding MSB_def including fset.lifting
  by transfer (auto simp: Max_Un list_all_iff Sup_bot_conv(2)[symmetric] simp del: Sup_bot_conv(2))

lemma MSB_append[simp]: "MSB (I1 @ I2) = max (MSB I1) (MSB I2)"
  by (induct I1) auto

lemma MSB_insert_nth[simp]:
  "MSB (insert_nth n P Is) = max (if P = {||} then 0 else Suc (fMax P)) (MSB Is)"
  by (subst (2) append_take_drop_id[of n Is, symmetric])
    (simp only: insert_nth_take_drop MSB_append MSB_Cons MSB_Nil)

lemma MSB_greater:
  "\<lbrakk>i < length Is; p |\<in>| Is ! i\<rbrakk> \<Longrightarrow> p < MSB Is"
  unfolding MSB_def by (fastforce simp: Bex_def in_set_conv_nth less_Suc_eq_le intro: Max_ge)

lemma MSB_mono: "set I1 \<subseteq> set I2 \<Longrightarrow> MSB I1 \<le> MSB I2"
  unfolding MSB_def including fset.lifting
  by transfer (auto simp: list_all_iff intro!: Max_ge)

lemma MSB_map_index'_CONS[simp]:
  "MSB (map_index' i (lift bs) Is) =
  (if MSB Is = 0 \<and> (\<forall>i \<in> {i ..< i + length Is}. \<not> bs ! i) then 0 else Suc (MSB Is))"
  by (induct Is arbitrary: i)
   (auto split: if_splits simp: mono_fMax_commute[where f = Suc, symmetric] mono_def
    lift_def upshift_def,
    metis atLeastLessThan_iff le_antisym not_less_eq_eq)

lemma MSB_map_index'_SNOC[simp]:
  "MSB Is \<le> n \<Longrightarrow> MSB (map_index' i (snoc n bs) Is) =
  (if (\<forall>i \<in> {i ..< i + length Is}. \<not> bs ! i) then MSB Is else Suc n)"
  by (induct Is arbitrary: i)
    (auto split: if_splits simp: mono_fMax_commute[where f = Suc, symmetric] mono_def
    snoc_def, (metis atLeastLessThan_iff le_antisym not_less_eq_eq)+)

lemma MSB_replicate[simp]: "MSB (replicate n P) = (if P = {||} \<or> n = 0 then 0 else Suc (fMax P))"
  by (induct n) auto

typedef interp =
  "{(n :: nat, I1 :: nat fset list, I2  :: nat fset list) | n I1 I2. MSB (I1 @ I2) \<le> n}"
  by auto

setup_lifting type_definition_interp

lift_definition assigns :: "nat \<Rightarrow> interp \<Rightarrow> order \<Rightarrow> nat fset" ("_\<^bsup>_\<^esup>_" [900, 999, 999] 999)
  is "\<lambda>n (_, I1, I2) ord. case ord of FO \<Rightarrow> if n < length I1 then I1 ! n else {||}
    | SO \<Rightarrow> if n < length I2 then I2 ! n else {||}" .
lift_definition nvars :: "interp \<Rightarrow> idx" ("#\<^sub>V _" [1000] 900)
  is "\<lambda>(_, I1, I2). (length I1, length I2)" .
lift_definition Length :: "interp \<Rightarrow> nat"
  is "\<lambda>(n, _, _). n" .
lift_definition Extend :: "order \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> nat fset \<Rightarrow> interp"
  is "\<lambda>ord i (n, I1, I2) P. case ord of
      FO \<Rightarrow> (max n (if P = {||} then 0 else Suc (fMax P)), insert_nth i P I1, I2)
    | SO \<Rightarrow> (max n (if P = {||} then 0 else Suc (fMax P)), I1, insert_nth i P I2)"
  using MSB_mono by (auto simp del: insert_nth_take_drop split: order.splits)

lift_definition CONS :: "(bool list \<times> bool list) \<Rightarrow> interp \<Rightarrow> interp"
  is "\<lambda>(bs1, bs2) (n, I1, I2).
   (Suc n, map_index (lift bs1) I1, map_index (lift bs2) I2)"
  by auto

lift_definition SNOC :: "(bool list \<times> bool list) \<Rightarrow> interp \<Rightarrow> interp"
  is "\<lambda>(bs1, bs2) (n, I1, I2).
   (Suc n, map_index (snoc n bs1) I1, map_index (snoc n bs2) I2)"
  by (auto simp: Let_def)

type_synonym atom = "bool list \<times> bool list"

lift_definition zero :: "idx \<Rightarrow> atom"
  is "\<lambda>(m, n). (replicate m False, replicate n False)" .

definition "extend ord b \<equiv>
  \<lambda>(bs1, bs2). case ord of FO \<Rightarrow> (b # bs1, bs2) | SO \<Rightarrow> (bs1, b # bs2)"
lift_definition size_atom :: "bool list \<times> bool list \<Rightarrow> idx"
  is "\<lambda>(bs1, bs2). (length bs1, length bs2)" .

lift_definition \<sigma> :: "idx \<Rightarrow> atom list"
  is "(\<lambda>(n, N). map (\<lambda>bs. (take n bs, drop n bs)) (List.n_lists (n + N) [True, False]))" .

lemma fMin_fimage_Suc[simp]: "x |\<in>| A \<Longrightarrow> fMin (Suc |`| A) = Suc (fMin A)"
  by (rule fMin_eqI) (auto intro: fMin_in)

lemma fMin_eq_0[simp]: "0 |\<in>| A \<Longrightarrow> fMin A = (0 :: nat)"
  by (rule fMin_eqI) auto

lemma insert_nth_Cons[simp]:
  "insert_nth i x (y # xs) = (case i of 0 \<Rightarrow> x # y # xs | Suc i \<Rightarrow> y # insert_nth i x xs)"
  by (cases i) simp_all

lemma insert_nth_commute[simp]:
  assumes "j \<le> i" "i \<le> length xs"
  shows "insert_nth j y (insert_nth i x xs) = insert_nth (Suc i) x (insert_nth j y xs)"
  using assms by (induct xs arbitrary: i j) (auto simp del: insert_nth_take_drop split: nat.splits)

lemma SUC_SUC[simp]: "SUC ord (SUC ord' idx) = SUC ord' (SUC ord idx)"
  by transfer (auto split: order.splits)

lemma LESS_SUC[simp]:
  "LESS ord 0 (SUC ord idx)"
  "LESS ord (Suc l) (SUC ord idx) = LESS ord l idx"
  "ord \<noteq> ord' \<Longrightarrow> LESS ord l (SUC ord' idx) = LESS ord l idx"
  "LESS ord l idx \<Longrightarrow> LESS ord l (SUC ord' idx)"
  by (transfer, force split: order.splits)+

lemma nvars_Extend[simp]:
  "#\<^sub>V (Extend ord i \<AA> P) = SUC ord (#\<^sub>V \<AA>)"
  by (transfer, force split: order.splits)

lemma Length_Extend[simp]:
  "Length (Extend k i \<AA> P) = max (Length \<AA>) (if P = {||} then 0 else Suc (fMax P))"
  unfolding max_def by (split if_splits, transfer) (force split: order.splits)

lemma assigns_Extend[simp]:
  "LEQ ord i (#\<^sub>V \<AA>) \<Longrightarrow>m\<^bsup>Extend ord i \<AA> P\<^esup>ord = (if m = i then P else (if m > i then m - Suc 0 else m)\<^bsup>\<AA>\<^esup>ord)"
  "ord \<noteq> ord' \<Longrightarrow> m\<^bsup>Extend ord i \<AA> P\<^esup>ord' = m\<^bsup>\<AA>\<^esup>ord'"
  by (transfer, force simp: min_def nth_append split: order.splits)+

lemma Extend_commute_safe[simp]:
  "\<lbrakk>j \<le> i; LEQ ord i (#\<^sub>V \<AA>)\<rbrakk> \<Longrightarrow>
    Extend ord j (Extend ord i \<AA> P1) P2 = Extend ord (Suc i) (Extend ord j \<AA> P2) P1"
  by (transfer,
    force simp del: insert_nth_take_drop simp: replicate_add[symmetric] split: order.splits)

lemma Extend_commute_unsafe:
  "ord \<noteq> ord' \<Longrightarrow> Extend ord j (Extend ord' i \<AA> P1) P2 = Extend ord' i (Extend ord j \<AA> P2) P1"
  by (transfer, force simp: replicate_add[symmetric] split: order.splits)

lemma Length_CONS[simp]:
  "Length (CONS x \<AA>) = Suc (Length \<AA>)"
  by (transfer, force split: order.splits)

lemma Length_SNOC[simp]:
  "Length (SNOC x \<AA>) = Suc (Length \<AA>)"
  by (transfer, force simp: Let_def split: order.splits)

lemma nvars_CONS[simp]:
  "#\<^sub>V (CONS x \<AA>) = #\<^sub>V \<AA>"
  by (transfer, force)

lemma nvars_SNOC[simp]:
  "#\<^sub>V (SNOC x \<AA>) = #\<^sub>V \<AA>"
  by (transfer, force simp: Let_def)

lemma assigns_CONS[simp]:
  assumes "#\<^sub>V \<AA> = size_atom bs1_bs2"
  shows "LESS ord x (#\<^sub>V \<AA>) \<Longrightarrow> x\<^bsup>CONS bs1_bs2 \<AA>\<^esup>ord =
    (if case_prod case_order bs1_bs2 ord ! x then finsert 0 (upshift (x\<^bsup>\<AA>\<^esup>ord)) else upshift (x\<^bsup>\<AA>\<^esup>ord))"
  by (insert assms, transfer) (auto simp: lift_def split: order.splits)

lemma assigns_SNOC[simp]:
  assumes "#\<^sub>V \<AA> = size_atom bs1_bs2"
  shows "LESS ord x (#\<^sub>V \<AA>) \<Longrightarrow> x\<^bsup>SNOC bs1_bs2 \<AA>\<^esup>ord =
    (if case_prod case_order bs1_bs2 ord ! x then finsert (Length \<AA>) (x\<^bsup>\<AA>\<^esup>ord) else x\<^bsup>\<AA>\<^esup>ord)"
  by (insert assms, transfer) (force simp: snoc_def Let_def split: order.splits)

lemma map_index'_eq_conv[simp]:
  "map_index' i f xs = map_index' j g xs = (\<forall>k < length xs. f (i + k) (xs ! k) = g (j + k) (xs ! k))"
proof (induct xs arbitrary: i j)
  case Cons from Cons(1)[of "Suc i" "Suc j"] show ?case by (auto simp: nth_Cons split: nat.splits)
qed simp

lemma fMax_Diff_0[simp]: "Suc m |\<in>| P \<Longrightarrow> fMax (P |-| {|0|}) = fMax P"
  by (rule fMax_eqI) (auto intro: fMax_in dest: fMax_ge)

lemma Suc_fMax_pred_fimage[simp]:
  assumes "Suc p |\<in>| P" "0 |\<notin>| P"
  shows "Suc (fMax ((\<lambda>x. x - Suc 0) |`| P)) = fMax P"
  using assms by (subst mono_fMax_commute[of Suc, unfolded mono_def, simplified]) (auto simp: o_def)

lemma Extend_CONS[simp]: "#\<^sub>V \<AA> = size_atom x \<Longrightarrow> Extend ord 0 (CONS x \<AA>) P =
  CONS (extend ord (eval P 0) x) (Extend ord 0 \<AA> (downshift P))"
  by transfer (auto simp: extend_def o_def gr0_conv_Suc
    mono_fMax_commute[of Suc, symmetric, unfolded mono_def, simplified]
    lift_def upshift_def downshift_def eval_def
    dest!: fsubset_fsingletonD split: order.splits)

lemma size_atom_extend[simp]:
  "size_atom (extend ord b x) = SUC ord (size_atom x)"
  unfolding extend_def by transfer (simp split: prod.splits order.splits)

lemma size_atom_zero[simp]:
  "size_atom (zero idx) = idx"
  unfolding extend_def by transfer (simp split: prod.splits order.splits)

lemma interp_eqI:
  "\<lbrakk>Length \<AA> = Length \<BB>; #\<^sub>V \<AA> = #\<^sub>V \<BB>; \<And>m k. LESS k m (#\<^sub>V \<AA>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k\<rbrakk> \<Longrightarrow> \<AA> = \<BB>"
  by transfer (force split: order.splits intro!: nth_equalityI)

lemma Extend_SNOC_cut[unfolded eval_def cut_def Length_SNOC, simp]:
  "\<lbrakk>len P \<le> Length (SNOC x \<AA>); #\<^sub>V \<AA> = size_atom x\<rbrakk> \<Longrightarrow>
  Extend ord 0 (SNOC x \<AA>) P =
    SNOC (extend ord (if eval P (Length \<AA>) then True else False) x) (Extend ord 0 \<AA> (cut (Length \<AA>) P))"
  by transfer (fastforce simp: extend_def len_def cut_def ffilter_eq_fempty_iff snoc_def eval_def
    split: if_splits order.splits dest: fMax_ge fMax_boundedD intro: fMax_in)

lemma nth_replicate_simp: "replicate m x ! i = (if i < m then x else [] ! (i - m))"
  by (induct m arbitrary: i) (auto simp: nth_Cons')

lemma MSB_eq_SucD: "MSB Is = Suc x \<Longrightarrow> \<exists>P\<in>set Is. x |\<in>| P"
  using Max_in[of "\<Union>x\<in>set Is. fset x"]
  unfolding MSB_def by (force simp: fmember_def split: if_splits)

lemma append_replicate_inj:
  assumes "xs \<noteq> [] \<Longrightarrow> last xs \<noteq> x" and "ys \<noteq> [] \<Longrightarrow> last ys \<noteq> x"
  shows "xs @ replicate m x = ys @ replicate n x \<longleftrightarrow> (xs = ys \<and> m = n)"
proof safe
  from assms have assms': "xs \<noteq> [] \<Longrightarrow> rev xs ! 0 \<noteq> x" "ys \<noteq> [] \<Longrightarrow> rev ys ! 0 \<noteq> x"
    by (auto simp: hd_rev hd_conv_nth[symmetric])
  assume *: "xs @ replicate m x = ys @ replicate n x"
  then have "rev (xs @ replicate m x) = rev (ys @ replicate n x)" ..
  then have "replicate m x @ rev xs = replicate n x @ rev ys" by simp
  then have "take (max m n) (replicate m x @ rev xs) = take (max m n) (replicate n x @ rev ys)" by simp
  then have "replicate m x @ take (max m n - m) (rev xs) =
    replicate n x @ take (max m n - n) (rev ys)" by (auto simp: min_def max_def split: if_splits)
  then have "(replicate m x @ take (max m n - m) (rev xs)) ! min m n =
    (replicate n x @ take (max m n - n) (rev ys)) ! min m n" by simp
  with arg_cong[OF *, of length, simplified] assms' show "m = n"
    by (cases "xs = []" "ys = []" rule: bool.exhaust[case_product bool.exhaust])
      (auto simp: min_def nth_append split: if_splits)
  with * show "xs = ys" by auto
qed

lemma fin_lift[simp]: "m |\<in>| lift bs i (I ! i) \<longleftrightarrow> (case m of 0 \<Rightarrow> bs ! i | Suc m \<Rightarrow> m |\<in>| I ! i)"
  unfolding lift_def upshift_def by (auto split: nat.splits)

lemma ex_Length_0[simp]:
  "\<exists>\<AA>. Length \<AA> = 0 \<and> #\<^sub>V \<AA> = idx"
  by transfer (auto intro!: exI[of _ "replicate m {||}" for m])

lemma is_empty_inj[simp]: "\<lbrakk>Length \<AA> = 0; Length \<BB> = 0; #\<^sub>V \<AA> = #\<^sub>V \<BB>\<rbrakk> \<Longrightarrow> \<AA> = \<BB>"
  by transfer (simp add: list_eq_iff_nth_eq split: prod.splits,
    metis MSB_greater fMax_in less_nat_zero_code)

lemma set_\<sigma>_length_atom[simp]: "(x \<in> set (\<sigma> idx)) \<longleftrightarrow> idx = size_atom x"
  by transfer (auto simp: set_n_lists enum_UNIV image_iff intro!: exI[of _ "I1 @ I2" for I1 I2])

lemma distinct_\<sigma>[simp]: "distinct (\<sigma> idx)"
  by transfer (auto 0 4 simp: distinct_map distinct_n_lists set_n_lists inj_on_def
    intro: iffD2[OF append_eq_append_conv]
      box_equals[OF _ append_take_drop_id append_take_drop_id, of n _ n for n])

lemma fMin_less_Length[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> fMin (m1\<^bsup>\<AA>\<^esup>k) < Length \<AA>"
  by transfer
    (force elim: order.strict_trans2[OF MSB_greater, rotated -1] intro: fMin_in split: order.splits)

lemma fMax_less_Length[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> fMax (m1\<^bsup>\<AA>\<^esup>k) < Length \<AA>"
  by transfer
    (force elim: order.strict_trans2[OF MSB_greater, rotated -1] intro: fMax_in split: order.splits)

lemma min_Length_fMin[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> min (Length \<AA>) (fMin (m1\<^bsup>\<AA>\<^esup>k)) = fMin (m1\<^bsup>\<AA>\<^esup>k)"
  using fMin_less_Length[of x m1 \<AA> k] unfolding fMin_def by auto

lemma max_Length_fMin[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> max (Length \<AA>) (fMin (m1\<^bsup>\<AA>\<^esup>k)) = Length \<AA>"
  using fMin_less_Length[of x m1 \<AA> k] unfolding fMin_def by auto

lemma min_Length_fMax[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> min (Length \<AA>) (fMax (m1\<^bsup>\<AA>\<^esup>k)) = fMax (m1\<^bsup>\<AA>\<^esup>k)"
  using fMax_less_Length[of x m1 \<AA> k] unfolding fMax_def by auto

lemma max_Length_fMax[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> max (Length \<AA>) (fMax (m1\<^bsup>\<AA>\<^esup>k)) = Length \<AA>"
  using fMax_less_Length[of x m1 \<AA> k] unfolding fMax_def by auto

lemma assigns_less_Length[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> x < Length \<AA>"
  by transfer (force dest: MSB_greater split: order.splits if_splits)

lemma Length_notin_assigns[simp]: "Length \<AA> |\<notin>| m\<^bsup>\<AA>\<^esup>k"
  by (metis assigns_less_Length less_not_refl)

lemma nth_zero[simp]: "LESS ord m (#\<^sub>V \<AA>) \<Longrightarrow> \<not> case_prod case_order (zero (#\<^sub>V \<AA>)) ord ! m"
  by transfer (auto split: order.splits)

lemma in_fimage_Suc[simp]: "x |\<in>| Suc |`| A \<longleftrightarrow> (\<exists>y. y |\<in>| A \<and> x = Suc y)"
  by blast

lemma fimage_Suc_inj[simp]: "Suc |`| A = Suc |`| B \<longleftrightarrow> A = B"
  by blast

lemma MSB_eq0_D: "MSB I = 0 \<Longrightarrow> x < length I \<Longrightarrow> I ! x = {||}"
  unfolding MSB_def by (auto split: if_splits)

lemma Suc_in_fimage_Suc: "Suc x |\<in>| Suc |`| X \<longleftrightarrow> x |\<in>| X"
  by auto

lemma Suc_in_fimage_Suc_o_Suc[simp]: "Suc x |\<in>| (Suc \<circ> Suc) |`| X \<longleftrightarrow> x |\<in>| Suc |`| X"
  by auto

lemma finsert_same_eq_iff[simp]: "finsert k X = finsert k Y \<longleftrightarrow> X |-| {|k|} = Y |-| {|k|}"
  by auto


lemma fimage_Suc_o_Suc_eq_fimage_Suc_iff[simp]:
  "((Suc \<circ> Suc) |`| X = Suc |`| Y) \<longleftrightarrow> (Suc |`| X = Y)"
  by (metis fimage_Suc_inj fset.map_comp)

lemma fMax_image_Suc[simp]: "x |\<in>| P \<Longrightarrow> fMax (Suc |`| P) = Suc (fMax P)"
  by (rule fMax_eqI) (metis Suc_le_mono fMax_ge fimageE, metis fimageI fempty_iff fMax_in)

lemma fimage_Suc_eq_singleton[simp]: "(fimage Suc Z = {|y|}) \<longleftrightarrow> (\<exists>x. Z = {|x|} \<and> Suc x = y)"
  by (cases y) auto

lemma len_downshift_helper:
  "x |\<in>| P \<Longrightarrow> Suc (fMax ((\<lambda>x. x - Suc 0) |`| (P |-| {|0|}))) \<noteq> fMax P \<Longrightarrow> xa |\<in>| P \<Longrightarrow> xa = 0"
proof -
  assume a1: "xa |\<in>| P"
  assume a2: "Suc (fMax ((\<lambda>x. x - Suc 0) |`| (P |-| {|0|}))) \<noteq> fMax P"
  have "xa |\<in>| {|0|} \<longrightarrow> xa = 0" by fastforce
  moreover
  { assume "xa |\<notin>| {|0|}"
    hence "0 |\<notin>| P |-| {|0|} \<and> xa |\<notin>| {|0|}" by blast
    then obtain esk1\<^sub>1 :: "nat \<Rightarrow> nat" where "xa = 0" using a1 a2 by (metis Suc_fMax_pred_fimage fMax_Diff_0 fminus_iff not0_implies_Suc) }
  ultimately show "xa = 0" by blast
qed

lemma CONS_inj[simp]: "size_atom x = #\<^sub>V \<AA> \<Longrightarrow> size_atom y = #\<^sub>V \<AA> \<Longrightarrow> #\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow>
  CONS x \<AA> = CONS y \<BB> \<longleftrightarrow> (x = y \<and> \<AA> = \<BB>)"
  by transfer (auto simp: list_eq_iff_nth_eq lift_def upshift_def split: if_splits; blast)

lemma Suc_minus1: "Suc (x - Suc 0) = (if x = 0 then Suc 0 else x)"
  by auto

lemma fset_eq_empty_iff: "(fset X = {}) = (X = {||})"
  by (metis bot_fset.rep_eq fset_inverse)

lemma fset_le_singleton_iff: "(fset X \<subseteq> {x}) = (X = {||} \<or> X = {|x|})"
  by (metis finsert.rep_eq fset_eq_empty_iff fset_inject order_refl singleton_insert_inj_eq subset_singletonD)

lemma MSB_decreases:
  "MSB I \<le> Suc m \<Longrightarrow> MSB (map (\<lambda>X. (\<lambda>I1. I1 - Suc 0) |`| (X |-| {|0|})) I) \<le> m"
  unfolding MSB_def
  by (auto simp add: not_le less_Suc_eq_le fset_eq_empty_iff fset_le_singleton_iff
    split: if_splits dest!: iffD1[OF Max_le_iff, rotated -1] iffD1[OF Max_ge_iff, rotated -1]; force)

lemma CONS_surj[dest]: "Length \<AA> > 0 \<Longrightarrow>
  \<exists>x \<BB>. \<AA> = CONS x \<BB> \<and> #\<^sub>V \<BB> = #\<^sub>V \<AA> \<and> size_atom x = #\<^sub>V \<AA>"
  by transfer (auto simp: gr0_conv_Suc list_eq_iff_nth_eq lift_def upshift_def split: if_splits
    intro!: exI[of _ "map (\<lambda>X. 0 |\<in>| X) _"] exI[of _ "map (\<lambda>X. (\<lambda>x. x - Suc 0) |`| (X |-| {|0|})) _"],
    auto simp: MSB_decreases upshift_def Suc_minus1 fimage_iff intro: rev_fBexI split: if_splits)
 
(*<*)
end
(*>*)
