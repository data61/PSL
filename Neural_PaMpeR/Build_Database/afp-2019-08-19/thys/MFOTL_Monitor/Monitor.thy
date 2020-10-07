(*<*)
theory Monitor
  imports Abstract_Monitor Table
begin
(*>*)

section \<open>Concrete Monitor\<close>

subsection \<open>Monitorable Formulas\<close>

definition "mmonitorable \<phi> \<longleftrightarrow> safe_formula \<phi> \<and> MFOTL.future_reach \<phi> \<noteq> \<infinity>"

fun mmonitorable_exec :: "'a MFOTL.formula \<Rightarrow> bool" where
  "mmonitorable_exec (MFOTL.Eq t1 t2) = (MFOTL.is_Const t1 \<or> MFOTL.is_Const t2)"
| "mmonitorable_exec (MFOTL.Neg (MFOTL.Eq (MFOTL.Const x) (MFOTL.Const y))) = True"
| "mmonitorable_exec (MFOTL.Neg (MFOTL.Eq (MFOTL.Var x) (MFOTL.Var y))) = (x = y)"
| "mmonitorable_exec (MFOTL.Pred e ts) = True"
| "mmonitorable_exec (MFOTL.Neg (MFOTL.Or (MFOTL.Neg \<phi>) \<psi>)) = (mmonitorable_exec \<phi> \<and>
    (mmonitorable_exec \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<or> (case \<psi> of MFOTL.Neg \<psi>' \<Rightarrow> mmonitorable_exec \<psi>' | _ \<Rightarrow> False)))"
| "mmonitorable_exec (MFOTL.Or \<phi> \<psi>) = (MFOTL.fv \<psi> = MFOTL.fv \<phi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (MFOTL.Exists \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (MFOTL.Prev I \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (MFOTL.Next I \<phi>) = (mmonitorable_exec \<phi> \<and> right I \<noteq> \<infinity>)"
| "mmonitorable_exec (MFOTL.Since \<phi> I \<psi>) = (MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (MFOTL.Until \<phi> I \<psi>) = (MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<and> right I \<noteq> \<infinity> \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec _ = False"

lemma plus_eq_enat_iff: "a + b = enat i \<longleftrightarrow> (\<exists>j k. a = enat j \<and> b = enat k \<and> j + k = i)"
  by (cases a; cases b) auto

lemma minus_eq_enat_iff: "a - enat k = enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j - k = i)"
  by (cases a) auto

lemma safe_formula_mmonitorable_exec: "safe_formula \<phi> \<Longrightarrow> MFOTL.future_reach \<phi> \<noteq> \<infinity> \<Longrightarrow> mmonitorable_exec \<phi>"
proof (induct \<phi> rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce split: formula.splits)
next
  case (6 \<phi> \<psi>)
  then show ?case 
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce split: formula.splits)
next
  case (10 \<phi> I \<psi>)
  then show ?case 
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce split: formula.splits)
next
  case (11 \<phi> I \<psi>)
  then show ?case 
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce simp: plus_eq_enat_iff split: formula.splits)
qed (auto simp add: plus_eq_enat_iff minus_eq_enat_iff)

lemma mmonitorable_exec_mmonitorable: "mmonitorable_exec \<phi> \<Longrightarrow> mmonitorable \<phi>"
proof (induct \<phi> rule: mmonitorable_exec.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce split: formula.splits)
next
  case (10 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce split: formula.splits)
next
  case (11 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce simp: one_enat_def split: formula.splits)
qed (auto simp add: mmonitorable_def one_enat_def)

lemma monitorable_formula_code[code]: "mmonitorable \<phi> = mmonitorable_exec \<phi>"
  using mmonitorable_exec_mmonitorable safe_formula_mmonitorable_exec mmonitorable_def
  by blast



subsection \<open>The Executable Monitor\<close>

type_synonym ts = nat

type_synonym 'a mbuf2 = "'a table list \<times> 'a table list"
type_synonym 'a msaux = "(ts \<times> 'a table) list"
type_synonym 'a muaux = "(ts \<times> 'a table \<times> 'a table) list"

datatype 'a mformula =
    MRel "'a table"
  | MPred MFOTL.name "'a MFOTL.trm list"
  | MAnd "'a mformula" bool "'a mformula" "'a mbuf2"
  | MOr "'a mformula" "'a mformula" "'a mbuf2"
  | MExists "'a mformula"
  | MPrev \<I> "'a mformula" bool "'a table list" "ts list"
  | MNext \<I> "'a mformula" bool "ts list"
  | MSince bool "'a mformula" \<I> "'a mformula" "'a mbuf2" "ts list" "'a msaux"
  | MUntil bool "'a mformula" \<I> "'a mformula" "'a mbuf2" "ts list" "'a muaux"

record 'a mstate =
  mstate_i :: nat
  mstate_m :: "'a mformula"
  mstate_n :: nat

fun eq_rel :: "nat \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a table" where
  "eq_rel n (MFOTL.Const x) (MFOTL.Const y) = (if x = y then unit_table n else empty_table)"
| "eq_rel n (MFOTL.Var x) (MFOTL.Const y) = singleton_table n x y"
| "eq_rel n (MFOTL.Const x) (MFOTL.Var y) = singleton_table n y x"
| "eq_rel n (MFOTL.Var x) (MFOTL.Var y) = undefined"

fun neq_rel :: "nat \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a table" where
  "neq_rel n (MFOTL.Const x) (MFOTL.Const y) = (if x = y then empty_table else unit_table n)"
| "neq_rel n (MFOTL.Var x) (MFOTL.Var y) = (if x = y then empty_table else undefined)"
| "neq_rel _ _ _ = undefined"

fun minit0 :: "nat \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a mformula" where
  "minit0 n (MFOTL.Neg \<phi>) = (case \<phi> of
    MFOTL.Eq t1 t2 \<Rightarrow> MRel (neq_rel n t1 t2)
  | MFOTL.Or (MFOTL.Neg \<phi>) \<psi> \<Rightarrow> (if safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi>
      then MAnd (minit0 n \<phi>) False (minit0 n \<psi>) ([], [])
      else (case \<psi> of MFOTL.Neg \<psi> \<Rightarrow> MAnd (minit0 n \<phi>) True (minit0 n \<psi>) ([], []) | _ \<Rightarrow> undefined))
  | _ \<Rightarrow> undefined)"
| "minit0 n (MFOTL.Eq t1 t2) = MRel (eq_rel n t1 t2)"
| "minit0 n (MFOTL.Pred e ts) = MPred e ts"
| "minit0 n (MFOTL.Or \<phi> \<psi>) = MOr (minit0 n \<phi>) (minit0 n \<psi>) ([], [])"
| "minit0 n (MFOTL.Exists \<phi>) = MExists (minit0 (Suc n) \<phi>)"
| "minit0 n (MFOTL.Prev I \<phi>) = MPrev I (minit0 n \<phi>) True [] []"
| "minit0 n (MFOTL.Next I \<phi>) = MNext I (minit0 n \<phi>) True []"
| "minit0 n (MFOTL.Since \<phi> I \<psi>) = (if safe_formula \<phi>
    then MSince True (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    else (case \<phi> of
      MFOTL.Neg \<phi> \<Rightarrow> MSince False (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    | _ \<Rightarrow> undefined))"
| "minit0 n (MFOTL.Until \<phi> I \<psi>) = (if safe_formula \<phi>
    then MUntil True (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    else (case \<phi> of
      MFOTL.Neg \<phi> \<Rightarrow> MUntil False (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    | _ \<Rightarrow> undefined))"

definition minit :: "'a MFOTL.formula \<Rightarrow> 'a mstate" where
  "minit \<phi> = (let n = MFOTL.nfv \<phi> in \<lparr>mstate_i = 0, mstate_m = minit0 n \<phi>, mstate_n = n\<rparr>)"

fun mprev_next :: "\<I> \<Rightarrow> 'a table list \<Rightarrow> ts list \<Rightarrow> 'a table list \<times> 'a table list \<times> ts list" where
  "mprev_next I [] ts = ([], [], ts)"
| "mprev_next I xs [] = ([], xs, [])"
| "mprev_next I xs [t] = ([], xs, [t])"
| "mprev_next I (x # xs) (t # t' # ts) = (let (ys, zs) = mprev_next I xs (t' # ts)
    in ((if mem (t' - t) I then x else empty_table) # ys, zs))"

fun mbuf2_add :: "'a table list \<Rightarrow> 'a table list \<Rightarrow> 'a mbuf2 \<Rightarrow> 'a mbuf2" where
 "mbuf2_add xs' ys' (xs, ys) = (xs @ xs', ys @ ys')"

fun mbuf2_take :: "('a table \<Rightarrow> 'a table \<Rightarrow> 'b) \<Rightarrow> 'a mbuf2 \<Rightarrow> 'b list \<times> 'a mbuf2" where
  "mbuf2_take f (x # xs, y # ys) = (let (zs, buf) = mbuf2_take f (xs, ys) in (f x y # zs, buf))"
| "mbuf2_take f (xs, ys) = ([], (xs, ys))"

fun mbuf2t_take :: "('a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
  'a mbuf2 \<Rightarrow> ts list \<Rightarrow> 'b \<times> 'a mbuf2 \<times> ts list" where
  "mbuf2t_take f z (x # xs, y # ys) (t # ts) = mbuf2t_take f (f x y t z) (xs, ys) ts"
| "mbuf2t_take f z (xs, ys) ts = (z, (xs, ys), ts)"

fun match :: "'a MFOTL.trm list \<Rightarrow> 'a list \<Rightarrow> (nat \<rightharpoonup> 'a) option" where
  "match [] [] = Some Map.empty"
| "match (MFOTL.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (MFOTL.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

definition update_since :: "\<I> \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow>
  'a msaux \<Rightarrow> 'a table \<times> 'a msaux" where
  "update_since I pos rel1 rel2 nt aux =
    (let aux = (case [(t, join rel pos rel1). (t, rel) \<leftarrow> aux, nt - t \<le> right I] of
        [] \<Rightarrow> [(nt, rel2)]
      | x # aux' \<Rightarrow> (if fst x = nt then (fst x, snd x \<union> rel2) # aux' else (nt, rel2) # x # aux'))
    in (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, left I \<le> nt - t] {}, aux))"

definition update_until :: "\<I> \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow> 'a muaux \<Rightarrow> 'a muaux" where
  "update_until I pos rel1 rel2 nt aux =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem (nt - t) I then a2 \<union> join rel2 pos a1 else a2)) aux) @
    [(nt, rel1, if left I = 0 then rel2 else empty_table)]"

fun eval_until :: "\<I> \<Rightarrow> ts \<Rightarrow> 'a muaux \<Rightarrow> 'a table list \<times> 'a muaux" where
  "eval_until I nt [] = ([], [])"
| "eval_until I nt ((t, a1, a2) # aux) = (if t + right I < nt then
    (let (xs, aux) = eval_until I nt aux in (a2 # xs, aux)) else ([], (t, a1, a2) # aux))"

primrec meval :: "nat \<Rightarrow> ts \<Rightarrow> 'a MFOTL.database \<Rightarrow> 'a mformula \<Rightarrow> 'a table list \<times> 'a mformula" where
  "meval n t db (MRel rel) = ([rel], MRel rel)"
| "meval n t db (MPred e ts) = ([(\<lambda>f. tabulate f 0 n) ` Option.these
    (match ts ` (\<Union>(e', x)\<in>db. if e = e' then {x} else {}))], MPred e ts)"
| "meval n t db (MAnd \<phi> pos \<psi> buf) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>r1 r2. join r1 pos r2) (mbuf2_add xs ys buf)
    in (zs, MAnd \<phi> pos \<psi> buf))"
| "meval n t db (MOr \<phi> \<psi> buf) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add xs ys buf)
    in (zs, MOr \<phi> \<psi> buf))"
| "meval n t db (MExists \<phi>) =
    (let (xs, \<phi>) = meval (Suc n) t db \<phi> in (map (\<lambda>r. tl ` r) xs, MExists \<phi>))"
| "meval n t db (MPrev I \<phi> first buf nts) =
    (let (xs, \<phi>) = meval n t db \<phi>;
      (zs, buf, nts) = mprev_next I (buf @ xs) (nts @ [t])
    in (if first then empty_table # zs else zs, MPrev I \<phi> False buf nts))"
| "meval n t db (MNext I \<phi> first nts) =
    (let (xs, \<phi>) = meval n t db \<phi>;
      (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
      (zs, _, nts) = mprev_next I xs (nts @ [t])
    in (zs, MNext I \<phi> first nts))"
| "meval n t db (MSince pos \<phi> I \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      ((zs, aux), buf, nts) = mbuf2t_take (\<lambda>r1 r2 t (zs, aux).
        let (z, aux) = update_since I pos r1 r2 t aux
        in (zs @ [z], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ [t])
    in (zs, MSince pos \<phi> I \<psi> buf nts aux))"
| "meval n t db (MUntil pos \<phi> I \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      (aux, buf, nts) = mbuf2t_take (update_until I pos) aux (mbuf2_add xs ys buf) (nts @ [t]);
      (zs, aux) = eval_until I (case nts of [] \<Rightarrow> t | nt # _ \<Rightarrow> nt) aux
    in (zs, MUntil pos \<phi> I \<psi> buf nts aux))"

definition mstep :: "'a MFOTL.database \<times> ts \<Rightarrow> 'a mstate \<Rightarrow> (nat \<times> 'a tuple) set \<times> 'a mstate" where
  "mstep tdb st =
     (let (xs, m) = meval (mstate_n st) (snd tdb) (fst tdb) (mstate_m st)
     in (\<Union> (set (map (\<lambda>(i, X). (\<lambda>v. (i, v)) ` X) (List.enumerate (mstate_i st) xs))),
      \<lparr>mstate_i = mstate_i st + length xs, mstate_m = m, mstate_n = mstate_n st\<rparr>))"

lemma mstep_alt: "mstep tdb st =
     (let (xs, m) = meval (mstate_n st) (snd tdb) (fst tdb) (mstate_m st)
     in (\<Union>(i, X) \<in> set (List.enumerate (mstate_i st) xs). \<Union>v \<in> X. {(i,v)},
      \<lparr>mstate_i = mstate_i st + length xs, mstate_m = m, mstate_n = mstate_n st\<rparr>))"
  unfolding mstep_def
  by (auto split: prod.split)


subsection \<open>Verdict Delay\<close>

primrec progress :: "'a MFOTL.trace \<Rightarrow> 'a MFOTL.formula \<Rightarrow> nat \<Rightarrow> nat" where
  "progress \<sigma> (MFOTL.Pred e ts) j = j"
| "progress \<sigma> (MFOTL.Eq t1 t2) j = j"
| "progress \<sigma> (MFOTL.Neg \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Or \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Exists \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress \<sigma> \<phi> j)) j)"
| "progress \<sigma> (MFOTL.Next I \<phi>) j = progress \<sigma> \<phi> j - 1"
| "progress \<sigma> (MFOTL.Since \<phi> I \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> \<tau> \<sigma> i + right I \<ge> \<tau> \<sigma> k}"

lemma progress_And[simp]: "progress \<sigma> (MFOTL.And \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
  unfolding MFOTL.And_def by simp

lemma progress_And_Not[simp]: "progress \<sigma> (MFOTL.And_Not \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
  unfolding MFOTL.And_Not_def by simp

lemma progress_mono: "j \<le> j' \<Longrightarrow> progress \<sigma> \<phi> j \<le> progress \<sigma> \<phi> j'"
proof (induction \<phi>)
  case (Until \<phi> I \<psi>)
  then show ?case
    by (cases "right I")
      (auto dest: trans_le_add1[OF \<tau>_mono] intro!: cInf_superset_mono)
qed auto

lemma progress_le: "progress \<sigma> \<phi> j \<le> j"
proof (induction \<phi>)
  case (Until \<phi> I \<psi>)
  then show ?case
    by (cases "right I")
      (auto intro: trans_le_add1[OF \<tau>_mono] intro!: cInf_lower)
qed auto

lemma progress_0[simp]: "progress \<sigma> \<phi> 0 = 0"
  using progress_le by auto

lemma progress_ge: "MFOTL.future_reach \<phi> \<noteq> \<infinity> \<Longrightarrow> \<exists>j. i \<le> progress \<sigma> \<phi> j"
proof (induction \<phi> arbitrary: i)
  case (Pred e ts)
  then show ?case by auto
next
  case (Eq t1 t2)
  then show ?case by auto
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  from Or.prems have "MFOTL.future_reach \<phi>1 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>1") (auto)
  moreover from Or.prems have "MFOTL.future_reach \<phi>2 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>2") (auto)
  ultimately obtain j1 j2 where "i \<le> progress \<sigma> \<phi>1 j1" and "i \<le> progress \<sigma> \<phi>2 j2"
    using Or.IH[of i] by blast
  then have "i \<le> progress \<sigma> (MFOTL.Or \<phi>1 \<phi>2) (max j1 j2)"
    by (cases "j1 \<le> j2") (auto elim!: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (Exists \<phi>)
  then show ?case by simp
next
  case (Prev I \<phi>)
  from Prev.prems have "MFOTL.future_reach \<phi> \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>") (auto)
  then obtain j where "i \<le> progress \<sigma> \<phi> j"
    using Prev.IH[of i] by blast
  then show ?case by (auto intro!: exI[of _ j] elim!: order.trans[OF _ progress_le])
next
  case (Next I \<phi>)
  from Next.prems have "MFOTL.future_reach \<phi> \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>") (auto)
  then obtain j where "Suc i \<le> progress \<sigma> \<phi> j"
    using Next.IH[of "Suc i"] by blast
  then show ?case by (auto intro!: exI[of _ j])
next
  case (Since \<phi>1 I \<phi>2)
  from Since.prems have "MFOTL.future_reach \<phi>1 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>1") (auto)
  moreover from Since.prems have "MFOTL.future_reach \<phi>2 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>2") (auto)
  ultimately obtain j1 j2 where "i \<le> progress \<sigma> \<phi>1 j1" and "i \<le> progress \<sigma> \<phi>2 j2"
    using Since.IH[of i] by blast
  then have "i \<le> progress \<sigma> (MFOTL.Since \<phi>1 I \<phi>2) (max j1 j2)"
    by (cases "j1 \<le> j2") (auto elim!: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems obtain b where [simp]: "right I = enat b"
    by (cases "right I") (auto)
  obtain i' where "i < i'" and "\<tau> \<sigma> i + b + 1 \<le> \<tau> \<sigma> i'"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + b + 1"] by (auto simp add: less_eq_Suc_le)
  then have 1: "\<tau> \<sigma> i + b < \<tau> \<sigma> i'" by simp
  from Until.prems have "MFOTL.future_reach \<phi>1 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>1") (auto)
  moreover from Until.prems have "MFOTL.future_reach \<phi>2 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>2") (auto)
  ultimately obtain j1 j2 where "Suc i' \<le> progress \<sigma> \<phi>1 j1" and "Suc i' \<le> progress \<sigma> \<phi>2 j2"
    using Until.IH[of "Suc i'"] by blast
  then have "i \<le> progress \<sigma> (MFOTL.Until \<phi>1 I \<phi>2) (max j1 j2)"
    unfolding progress.simps
  proof (intro cInf_greatest, goal_cases nonempty greatest)
    case nonempty
    then show ?case
      by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
  next
    case (greatest x)
    with \<open>i < i'\<close> 1 show ?case
      by (cases "j1 \<le> j2")
        (auto dest!: spec[of _ i'] simp: max_absorb1 max_absorb2 less_eq_Suc_le
          elim: order.trans[OF _ progress_le] order.trans[OF _ progress_mono, rotated]
          dest!: not_le_imp_less[THEN less_imp_le] intro!: less_\<tau>D[THEN less_imp_le, of \<sigma> i x])
  qed
  then show ?case by blast
qed

lemma cInf_restrict_nat:
  fixes x :: nat
  assumes "x \<in> A"
  shows "Inf A = Inf {y \<in> A. y \<le> x}"
  using assms by (auto intro!: antisym intro: cInf_greatest cInf_lower Inf_nat_def1)

lemma progress_time_conv:
  assumes "\<forall>i<j. \<tau> \<sigma> i = \<tau> \<sigma>' i"
  shows "progress \<sigma> \<phi> j = progress \<sigma>' \<phi> j"
proof (induction \<phi>)
  case (Until \<phi>1 I \<phi>2)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with Until show ?case
  proof (cases "right I")
    case (enat b)
    then show ?thesis
    proof (cases "j")
      case (Suc n)
      with enat * Until show ?thesis
        using assms \<tau>_mono[THEN trans_le_add1]
        by (auto 6 0
          intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x=n] cInf_restrict_nat[symmetric, where x=n]])
    qed simp
  qed simp
qed simp_all

lemma Inf_UNIV_nat: "(Inf UNIV :: nat) = 0"
  by (simp add: cInf_eq_minimum)

lemma progress_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "progress \<sigma> \<phi> (plen \<pi>) = progress \<sigma>' \<phi> (plen \<pi>)"
  using assms by (auto intro: progress_time_conv \<tau>_prefix_conv)

lemma sat_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'" and "i < progress \<sigma> \<phi> (plen \<pi>)"
  shows "MFOTL.sat \<sigma> v i \<phi> \<longleftrightarrow> MFOTL.sat \<sigma>' v i \<phi>"
using assms(3) proof (induction \<phi> arbitrary: v i)
  case (Pred e ts)
  with \<Gamma>_prefix_conv[OF assms(1,2)] show ?case by simp
next
  case (Eq t1 t2)
  show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms(1,2)] show ?case
    by (cases i) (auto split: if_splits)
next
  case (Next I \<phi>)
  then have "Suc i < plen \<pi>"
    by (auto intro: order.strict_trans2[OF _ progress_le[of \<sigma> \<phi>]])
  with Next \<tau>_prefix_conv[OF assms(1,2)] show ?case by simp
next
  case (Since \<phi>1 I \<phi>2)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le])
  with Since \<tau>_prefix_conv[OF assms(1,2)] show ?case by auto
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems obtain b where [simp]: "right I = enat b"
    by (cases "right I") (auto simp add: Inf_UNIV_nat)
  from Until.prems obtain j where "\<tau> \<sigma> i + b + 1 \<le> \<tau> \<sigma> j"
    "j \<le> progress \<sigma> \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma> \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 1: "k < progress \<sigma> \<phi>1 (plen \<pi>)" and 2: "k < progress \<sigma> \<phi>2 (plen \<pi>)"
    if "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + b" for k
    using that by (fastforce elim!: order.strict_trans2[rotated] intro: less_\<tau>D[of \<sigma>])+
  have 3: "k < plen \<pi>" if "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + b" for k
    using 1[OF that] by (simp add: less_eq_Suc_le order.trans[OF _ progress_le])

  from Until.prems have "i < progress \<sigma>' (MFOTL.Until \<phi>1 I \<phi>2) (plen \<pi>)"
    unfolding progress_prefix_conv[OF assms(1,2)] .
  then obtain j where "\<tau> \<sigma>' i + b + 1 \<le> \<tau> \<sigma>' j"
    "j \<le> progress \<sigma>' \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma>' \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 11: "k < progress \<sigma> \<phi>1 (plen \<pi>)" and 21: "k < progress \<sigma> \<phi>2 (plen \<pi>)"
    if "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' i + b" for k
    unfolding progress_prefix_conv[OF assms(1,2)]
    using that by (fastforce elim!: order.strict_trans2[rotated] intro: less_\<tau>D[of \<sigma>'])+
  have 31: "k < plen \<pi>" if "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' i + b" for k
    using 11[OF that] by (simp add: less_eq_Suc_le order.trans[OF _ progress_le])

  show ?case unfolding sat.simps
  proof ((intro ex_cong iffI; elim conjE), goal_cases LR RL)
    case (LR j)
    with Until.IH(1)[OF 1] Until.IH(2)[OF 2] \<tau>_prefix_conv[OF assms(1,2) 3] show ?case
      by (auto 0 4 simp: le_diff_conv add.commute dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  next
    case (RL j)
    with Until.IH(1)[OF 11] Until.IH(2)[OF 21] \<tau>_prefix_conv[OF assms(1,2) 31] show ?case
      by (auto 0 4 simp: le_diff_conv add.commute dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  qed
qed

interpretation verimon: monitor_timed_progress "\<lambda>\<phi>. MFOTL.future_reach \<phi> \<noteq> \<infinity>" progress
  by (unfold_locales, (fact progress_mono progress_le progress_time_conv sat_prefix_conv |
        simp add: mmonitorable_def progress_ge)+)

abbreviation "mverdicts \<equiv> verimon.verdicts"


subsection \<open>Correctness\<close>

subsubsection \<open>Invariants\<close>

definition wf_mbuf2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a table \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a table \<Rightarrow> bool) \<Rightarrow>
  'a mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2 i ja jb P Q buf \<longleftrightarrow> i \<le> ja \<and> i \<le> jb \<and> (case buf of (xs, ys) \<Rightarrow>
    list_all2 P [i..<ja] xs \<and> list_all2 Q [i..<jb] ys)"

definition wf_mbuf2' :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow>
  'a MFOTL.formula \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j))
    (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)
    (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
    (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>)) buf"

lemma wf_mbuf2'_UNIV_alt: "wf_mbuf2' \<sigma> j n UNIV \<phi> \<psi> buf \<longleftrightarrow> (case buf of (xs, ys) \<Rightarrow>
  list_all2 (\<lambda>i. wf_table n (MFOTL.fv \<phi>) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
    [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) ..< (progress \<sigma> \<phi> j)] xs \<and>
  list_all2 (\<lambda>i. wf_table n (MFOTL.fv \<psi>) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
    [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) ..< (progress \<sigma> \<psi> j)] ys)"
  unfolding wf_mbuf2'_def wf_mbuf2_def
  by (simp add: mem_restr_UNIV[THEN eqTrueI, abs_def] split: prod.split)

definition wf_ts :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a MFOTL.formula \<Rightarrow> ts list \<Rightarrow> bool" where
  "wf_ts \<sigma> j \<phi> \<psi> ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<j] ts"

abbreviation "Sincep pos \<phi> I \<psi> \<equiv> MFOTL.Since (if pos then \<phi> else MFOTL.Neg \<phi>) I \<psi>"

definition wf_since_aux :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow> bool \<Rightarrow>
    'a MFOTL.formula \<Rightarrow> \<I> \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a msaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>)) X) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"

lemma qtable_mem_restr_UNIV: "qtable n A (mem_restr UNIV) Q X = wf_table n A Q X"
  unfolding qtable_def by auto

lemma wf_since_aux_UNIV_alt:
  "wf_since_aux \<sigma> n UNIV pos \<phi> I \<psi> aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      wf_table n (MFOTL.fv \<psi>)
          (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>)) X) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"
  unfolding wf_since_aux_def qtable_mem_restr_UNIV ..

definition wf_until_aux :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow> bool \<Rightarrow>
    'a MFOTL.formula \<Rightarrow> \<I> \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_aux \<sigma> n R pos \<phi> I \<psi> aux ne \<longleftrightarrow> list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. if pos then (\<forall>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)) r1 \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length aux \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and>
          MFOTL.sat \<sigma> (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi> else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>))) r2)
    aux [ne..<ne+length aux]"

lemma wf_until_aux_UNIV_alt:
  "wf_until_aux \<sigma> n UNIV pos \<phi> I \<psi> aux ne \<longleftrightarrow> list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      wf_table n (MFOTL.fv \<phi>) (\<lambda>v. if pos
          then (\<forall>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)) r1 \<and>
      wf_table n (MFOTL.fv \<psi>) (\<lambda>v. \<exists>j. i \<le> j \<and> j < ne + length aux \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and>
          MFOTL.sat \<sigma> (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi> else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>)) r2)
    aux [ne..<ne+length aux]"
  unfolding wf_until_aux_def qtable_mem_restr_UNIV ..
   

inductive wf_mformula :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow>
  nat \<Rightarrow> 'a list set \<Rightarrow> 'a mformula \<Rightarrow> 'a MFOTL.formula \<Rightarrow> bool"
  for \<sigma> j where
  Eq: "MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
    \<forall>x\<in>MFOTL.fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>MFOTL.fv_trm t2. x < n \<Longrightarrow>
    wf_mformula \<sigma> j n R (MRel (eq_rel n t1 t2)) (MFOTL.Eq t1 t2)"
| neq_Const: "\<phi> = MRel (neq_rel n (MFOTL.Const x) (MFOTL.Const y)) \<Longrightarrow>
    wf_mformula \<sigma> j n R \<phi> (MFOTL.Neg (MFOTL.Eq (MFOTL.Const x) (MFOTL.Const y)))"
| neq_Var: "x < n \<Longrightarrow>
    wf_mformula \<sigma> j n R (MRel empty_table) (MFOTL.Neg (MFOTL.Eq (MFOTL.Var x) (MFOTL.Var x)))"
| Pred: "\<forall>x\<in>MFOTL.fv (MFOTL.Pred e ts). x < n \<Longrightarrow>
    wf_mformula \<sigma> j n R (MPred e ts) (MFOTL.Pred e ts)"
| And: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<chi> = MFOTL.And \<phi>' \<psi>' \<and> \<not> (safe_formula (MFOTL.Neg \<psi>') \<and> MFOTL.fv \<psi>' \<subseteq> MFOTL.fv \<phi>')
      else \<chi> = MFOTL.And_Not \<phi>' \<psi>' \<and> safe_formula \<psi>' \<and> MFOTL.fv \<psi>' \<subseteq> MFOTL.fv \<phi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_mformula \<sigma> j n R (MAnd \<phi> pos \<psi> buf) \<chi>"
| Or: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    MFOTL.fv \<phi>' = MFOTL.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_mformula \<sigma> j n R (MOr \<phi> \<psi> buf) (MFOTL.Or \<phi>' \<psi>')"
| Exists: "wf_mformula \<sigma> j (Suc n) (lift_envs R) \<phi> \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j n R (MExists \<phi>) (MFOTL.Exists \<phi>')"
| Prev: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow>
    first \<longleftrightarrow> j = 0 \<Longrightarrow>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>') (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>'))
      [min (progress \<sigma> \<phi>' j) (j-1)..<progress \<sigma> \<phi>' j] buf \<Longrightarrow>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi>' j) (j-1)..<j] nts \<Longrightarrow>
    wf_mformula \<sigma> j n R (MPrev I \<phi> first buf nts) (MFOTL.Prev I \<phi>')"
| Next: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow>
    first \<longleftrightarrow> progress \<sigma> \<phi>' j = 0 \<Longrightarrow>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress \<sigma> \<phi>' j - 1..<j] nts \<Longrightarrow>
    wf_mformula \<sigma> j n R (MNext I \<phi> first nts) (MFOTL.Next I \<phi>')"
| Since: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<phi>'' = \<phi>' else \<phi>'' = MFOTL.Neg \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = pos \<Longrightarrow>
    MFOTL.fv \<phi>' \<subseteq> MFOTL.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_since_aux \<sigma> n R pos \<phi>' I \<psi>' aux (progress \<sigma> (MFOTL.Since \<phi>'' I \<psi>') j) \<Longrightarrow>
    wf_mformula \<sigma> j n R (MSince pos \<phi> I \<psi> buf nts aux) (MFOTL.Since \<phi>'' I \<psi>')"
| Until: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<phi>'' = \<phi>' else \<phi>'' = MFOTL.Neg \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = pos \<Longrightarrow>
    MFOTL.fv \<phi>' \<subseteq> MFOTL.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_until_aux \<sigma> n R pos \<phi>' I \<psi>' aux (progress \<sigma> (MFOTL.Until \<phi>'' I \<psi>') j) \<Longrightarrow>
    progress \<sigma> (MFOTL.Until \<phi>'' I \<psi>') j + length aux = min (progress \<sigma> \<phi>' j) (progress \<sigma> \<psi>' j) \<Longrightarrow>
    wf_mformula \<sigma> j n R (MUntil pos \<phi> I \<psi> buf nts aux) (MFOTL.Until \<phi>'' I \<psi>')"

definition wf_mstate :: "'a MFOTL.formula \<Rightarrow> 'a MFOTL.prefix \<Rightarrow> 'a list set \<Rightarrow> 'a mstate \<Rightarrow> bool" where
  "wf_mstate \<phi> \<pi> R st \<longleftrightarrow> mstate_n st = MFOTL.nfv \<phi> \<and> (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow>
    mstate_i st = progress \<sigma> \<phi> (plen \<pi>) \<and>
    wf_mformula \<sigma> (plen \<pi>) (mstate_n st) R (mstate_m st) \<phi>)"


subsubsection \<open>Initialisation\<close>

lemma minit0_And: "\<not> (safe_formula (MFOTL.Neg \<psi>) \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi>) \<Longrightarrow>
     minit0 n (MFOTL.And \<phi> \<psi>) = MAnd (minit0 n \<phi>) True (minit0 n \<psi>) ([], [])"
  unfolding MFOTL.And_def by simp

lemma minit0_And_Not: "safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<Longrightarrow>
  minit0 n (MFOTL.And_Not \<phi> \<psi>) = (MAnd (minit0 n \<phi>) False (minit0 n \<psi>) ([], []))"
  unfolding MFOTL.And_Not_def MFOTL.is_Neg_def by (simp split: formula.split)

lemma wf_mbuf2'_0: "wf_mbuf2' \<sigma> 0 n R \<phi> \<psi> ([], [])"
  unfolding wf_mbuf2'_def wf_mbuf2_def by simp

lemma wf_ts_0: "wf_ts \<sigma> 0 \<phi> \<psi> []"
  unfolding wf_ts_def by simp

lemma wf_since_aux_Nil: "wf_since_aux \<sigma> n R pos \<phi>' I \<psi>' [] 0"
  unfolding wf_since_aux_def by simp

lemma wf_until_aux_Nil: "wf_until_aux \<sigma> n R pos \<phi>' I \<psi>' [] 0"
  unfolding wf_until_aux_def by simp

lemma wf_minit0: "safe_formula \<phi> \<Longrightarrow> \<forall>x\<in>MFOTL.fv \<phi>. x < n \<Longrightarrow>
  wf_mformula \<sigma> 0 n R (minit0 n \<phi>) \<phi>"
  by (induction arbitrary: n R rule: safe_formula_induct)
    (auto simp add: minit0_And fvi_And minit0_And_Not fvi_And_Not
      intro!: wf_mformula.intros wf_mbuf2'_0 wf_ts_0 wf_since_aux_Nil wf_until_aux_Nil
      dest: fvi_Suc_bound)

lemma wf_mstate_minit: "safe_formula \<phi> \<Longrightarrow> wf_mstate \<phi> pnil R (minit \<phi>)"
  unfolding wf_mstate_def minit_def Let_def
  by (auto intro!: wf_minit0 fvi_less_nfv)


subsubsection \<open>Evaluation\<close>

lemma match_wf_tuple: "Some f = match ts xs \<Longrightarrow> wf_tuple n (\<Union>t\<in>set ts. MFOTL.fv_trm t) (tabulate f 0 n)"
  by (induction ts xs arbitrary: f rule: match.induct)
    (fastforce simp: wf_tuple_def split: if_splits option.splits)+

lemma match_fvi_trm_None: "Some f = match ts xs \<Longrightarrow> \<forall>t\<in>set ts. x \<notin> MFOTL.fv_trm t \<Longrightarrow> f x = None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_fvi_trm_Some: "Some f = match ts xs \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> MFOTL.fv_trm t \<Longrightarrow> f x \<noteq> None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_eval_trm: "\<forall>t\<in>set ts. \<forall>i\<in>MFOTL.fv_trm t. i < n \<Longrightarrow> Some f = match ts xs \<Longrightarrow>
    map (MFOTL.eval_trm (tabulate (\<lambda>i. the (f i)) 0 n)) ts = xs"
proof (induction ts xs arbitrary: f rule: match.induct)
  case (3 x ts y ys)
  from 3(1)[symmetric] 3(2,3) show ?case
    by (auto 0 3 dest: match_fvi_trm_Some sym split: option.splits if_splits intro!: eval_trm_cong)
qed (auto split: if_splits)

lemma wf_tuple_tabulate_Some: "wf_tuple n A (tabulate f 0 n) \<Longrightarrow> x \<in> A \<Longrightarrow> x < n \<Longrightarrow> \<exists>y. f x = Some y"
  unfolding wf_tuple_def by auto

lemma ex_match: "wf_tuple n (\<Union>t\<in>set ts. MFOTL.fv_trm t) v \<Longrightarrow> \<forall>t\<in>set ts. \<forall>x\<in>MFOTL.fv_trm t. x < n \<Longrightarrow>
    \<exists>f. match ts (map (MFOTL.eval_trm (map the v)) ts) = Some f \<and> v = tabulate f 0 n"
proof (induction ts "map (MFOTL.eval_trm (map the v)) ts" arbitrary: v rule: match.induct)
  case (3 x ts y ys)
  then show ?case
  proof (cases "x \<in> (\<Union>t\<in>set ts. MFOTL.fv_trm t)")
    case True
    with 3 show ?thesis
      by (auto simp: insert_absorb dest!: wf_tuple_tabulate_Some meta_spec[of _ v])
  next
    case False
    with 3(3,4) have
      *: "map (MFOTL.eval_trm (map the v)) ts = map (MFOTL.eval_trm (map the (v[x := None]))) ts"
      by (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_cong)
    from False 3(2-4) obtain f where
      "match ts (map (MFOTL.eval_trm (map the v)) ts) = Some f" "v[x := None] = tabulate f 0 n"
      unfolding *
      by (atomize_elim, intro 3(1)[of "v[x := None]"])
        (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_cong)
    moreover from False this have "f x = None" "length v = n"
      by (auto dest: match_fvi_trm_None[OF sym] arg_cong[of _ _ length])
    ultimately show ?thesis using 3(3)
      by (auto simp: list_eq_iff_nth_eq wf_tuple_def)
  qed
qed (auto simp: wf_tuple_def intro: nth_equalityI)

lemma eq_rel_eval_trm: "v \<in> eq_rel n t1 t2 \<Longrightarrow> MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
  \<forall>x\<in>MFOTL.fv_trm t1 \<union> MFOTL.fv_trm t2. x < n \<Longrightarrow>
  MFOTL.eval_trm (map the v) t1 = MFOTL.eval_trm (map the v) t2"
  by (cases t1; cases t2) (simp_all add: singleton_table_def split: if_splits)

lemma in_eq_rel: "wf_tuple n (MFOTL.fv_trm t1 \<union> MFOTL.fv_trm t2) v \<Longrightarrow>
  MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
  MFOTL.eval_trm (map the v) t1 = MFOTL.eval_trm (map the v) t2 \<Longrightarrow>
  v \<in> eq_rel n t1 t2"
  by (cases t1; cases t2)
    (auto simp: singleton_table_def wf_tuple_def unit_table_def intro!: nth_equalityI split: if_splits)

lemma table_eq_rel: "MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
  table n (MFOTL.fv_trm t1 \<union> MFOTL.fv_trm t2) (eq_rel n t1 t2)"
  by (cases t1; cases t2; simp)

lemma wf_tuple_Suc_fviD: "wf_tuple (Suc n) (MFOTL.fvi b \<phi>) v \<Longrightarrow> wf_tuple n (MFOTL.fvi (Suc b) \<phi>) (tl v)"
  unfolding wf_tuple_def by (simp add: fvi_Suc nth_tl)

lemma table_fvi_tl: "table (Suc n) (MFOTL.fvi b \<phi>) X \<Longrightarrow> table n (MFOTL.fvi (Suc b) \<phi>) (tl ` X)"
  unfolding table_def by (auto intro: wf_tuple_Suc_fviD)

lemma wf_tuple_Suc_fvi_SomeI: "0 \<in> MFOTL.fvi b \<phi> \<Longrightarrow> wf_tuple n (MFOTL.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (MFOTL.fvi b \<phi>) (Some x # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma wf_tuple_Suc_fvi_NoneI: "0 \<notin> MFOTL.fvi b \<phi> \<Longrightarrow> wf_tuple n (MFOTL.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (MFOTL.fvi b \<phi>) (None # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma qtable_project_fv: "qtable (Suc n) (fv \<phi>) (mem_restr (lift_envs R)) P X \<Longrightarrow>
    qtable n (MFOTL.fvi (Suc 0) \<phi>) (mem_restr R)
      (\<lambda>v. \<exists>x. P ((if 0 \<in> fv \<phi> then Some x else None) # v)) (tl ` X)"
  using neq0_conv by (fastforce simp: image_iff Bex_def fvi_Suc elim!: qtable_cong dest!: qtable_project)

lemma mprev: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> i \<le> j' \<Longrightarrow> i < j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then P i X else X = empty_table)
    [i..<min j' (j-1)] ys \<and>
  list_all2 P [min j' (j-1)..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min j' (j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min j' (j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min j' (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
      elim!: list.rel_mono_strong split: prod.splits if_splits)
qed simp

lemma mnext: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [Suc i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> Suc i \<le> j' \<Longrightarrow> i < j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then P (Suc i) X else X = empty_table)
    [i..<min (j'-1) (j-1)] ys \<and>
  list_all2 P [Suc (min (j'-1) (j-1))..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (j'-1) (j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min (j' - 1) (j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min (j' - 1) (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
      elim!: list.rel_mono_strong split: prod.splits if_splits) (* slow 10 sec *)
qed simp

lemma in_foldr_UnI: "x \<in> A \<Longrightarrow> A \<in> set xs \<Longrightarrow> x \<in> foldr (\<union>) xs {}"
  by (induction xs) auto

lemma in_foldr_UnE: "x \<in> foldr (\<union>) xs {} \<Longrightarrow> (\<And>A. A \<in> set xs \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs) auto

lemma sat_the_restrict: "fv \<phi> \<subseteq> A \<Longrightarrow> MFOTL.sat \<sigma> (map the (restrict A v)) i \<phi> = MFOTL.sat \<sigma> (map the v) i \<phi>"
  by (rule sat_fvi_cong) (auto intro!: map_the_restrict)

lemma update_since:
  assumes pre: "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux ne"
    and qtable1: "qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne \<phi>) rel1"
    and qtable2: "qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne \<psi>) rel2"
    and result_eq: "(rel, aux') = update_since I pos rel1 rel2 (\<tau> \<sigma> ne) aux"
    and fvi_subset: "MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi>"
  shows "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux' (Suc ne)"
    and "qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> I \<psi>)) rel"
proof -
  let ?wf_tuple = "\<lambda>v. wf_tuple n (MFOTL.fv \<psi>) v"
  note sat.simps[simp del]

  define aux0 where "aux0 = [(t, join rel pos rel1). (t, rel) \<leftarrow> aux, \<tau> \<sigma> ne - t \<le> right I]"
  have sorted_aux0: "sorted_wrt (\<lambda>x y. fst x > fst y) aux0"
    using pre[unfolded wf_since_aux_def, THEN conjunct1]
    unfolding aux0_def
    by (induction aux) (auto simp add: sorted_wrt_append)
  have in_aux0_1: "(t, X) \<in> set aux0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> ne - t \<le> right I \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. (MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>) \<and>
        (if pos then MFOTL.sat \<sigma> (map the v) ne \<phi> else \<not> MFOTL.sat \<sigma> (map the v) ne \<phi>))) X" for t X
    unfolding aux0_def using fvi_subset
    by (auto 0 1 elim!: qtable_join[OF _ qtable1] simp: sat_the_restrict
      dest!: assms(1)[unfolded wf_since_aux_def, THEN conjunct2, THEN conjunct1, rule_format])
  then have in_aux0_le_\<tau>: "(t, X) \<in> set aux0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_aux0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> \<tau> \<sigma> ne - t \<le> right I \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set aux0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set aux"
      by (atomize_elim, intro assms(1)[unfolded wf_since_aux_def, THEN conjunct2, THEN conjunct2, rule_format])
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>\<tau> \<sigma> ne - t \<le> right I\<close> have "(t, join X pos rel1) \<in> set aux0" 
      unfolding aux0_def by (auto elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set aux0"
      by blast
  qed
  have aux0_Nil: "aux0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> ne - t \<le> right I \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_aux0_2 by (cases "ne = 0") (auto)

  have aux'_eq: "aux' = (case aux0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, rel2)]
    | x # aux' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then (fst x, snd x \<union> rel2) # aux' else (\<tau> \<sigma> ne, rel2) # x # aux'))"
    using result_eq unfolding aux0_def update_since_def Let_def by simp
  have sorted_aux': "sorted_wrt (\<lambda>x y. fst x > fst y) aux'"
    unfolding aux'_eq
    using sorted_aux0 in_aux0_le_\<tau> by (cases aux0) (fastforce)+
  have in_aux'_1: "t \<le> \<tau> \<sigma> ne \<and> \<tau> \<sigma> ne - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> (point (\<tau> \<sigma> ne - t)) \<psi>)) X"
    if aux': "(t, X) \<in> set aux'" for t X
  proof (cases aux0)
    case Nil
    with aux' show ?thesis 
      unfolding aux'_eq using qtable2 aux0_Nil
      by (auto simp: zero_enat_def[symmetric] sat_Since_rec[where i=ne]
        dest: spec[of _ "\<tau> \<sigma> (ne-1)"] elim!: qtable_cong[OF _ refl])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with aux' Cons t have "X = snd a \<union> rel2"
          unfolding aux'_eq using sorted_aux0 by auto
        moreover from in_aux0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> (ne - 1)" "\<tau> \<sigma> ne - fst a \<le> right I" "\<exists>i. \<tau> \<sigma> i = fst a"
          "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne - 1)
            (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - fst a)) \<psi>) \<and> (if pos then MFOTL.sat \<sigma> (map the v) ne \<phi>
              else \<not> MFOTL.sat \<sigma> (map the v) ne \<phi>)) (snd a)"
          by auto
        ultimately show ?thesis using qtable2 t True
          by (auto simp: sat_Since_rec[where i=ne] sat.simps(3) elim!: qtable_union)
      next
        case False
        with aux' Cons t have "X = rel2"
          unfolding aux'_eq using sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] by auto
        with aux' Cons t False show ?thesis
          unfolding aux'_eq using qtable2 in_aux0_2[of "\<tau> \<sigma> (ne-1)"] in_aux0_le_\<tau>[of "fst a" "snd a"] sorted_aux0
          by (auto simp: sat_Since_rec[where i=ne] sat.simps(3) zero_enat_def[symmetric] enat_0_iff not_le
            elim!: qtable_cong[OF _ refl] dest!: le_\<tau>_less meta_mp)
    qed
    next
      case False
      with aux' Cons have "(t, X) \<in> set aux0"
        unfolding aux'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne - 1)" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t"
        "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne - 1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - t)) \<psi>) \<and>
           (if pos then MFOTL.sat \<sigma> (map the v) ne \<phi> else \<not> MFOTL.sat \<sigma> (map the v) ne \<phi>)) X"
        using in_aux0_1 by blast+
      with False aux' Cons show ?thesis
        unfolding aux'_eq using qtable2
        by (fastforce simp: sat_Since_rec[where i=ne] sat.simps(3)
          diff_diff_right[where i="\<tau> \<sigma> ne" and j="\<tau> \<sigma> _ + \<tau> \<sigma> ne" and k="\<tau> \<sigma> (ne - 1)",
            OF trans_le_add2, simplified] elim!: qtable_cong[OF _ refl] order_trans dest: le_\<tau>_less)
    qed
  qed

  have in_aux'_2: "\<exists>X. (t, X) \<in> set aux'" if "t \<le> \<tau> \<sigma> ne" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases aux0)
      case Nil
      with True show ?thesis unfolding aux'_eq by simp
    next
      case (Cons a as)
      with True show ?thesis unfolding aux'_eq
        by (cases "fst a = \<tau> \<sigma> ne") auto
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set aux0" using \<open>\<tau> \<sigma> ne - t \<le> right I\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      by atomize_elim (auto intro!: in_aux0_2)
    then show ?thesis unfolding aux'_eq using False
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux' (Suc ne)"
    unfolding wf_since_aux_def
    by (auto dest: in_aux'_1 intro: sorted_aux' in_aux'_2)

  have rel_eq: "rel = foldr (\<union>) [rel. (t, rel) \<leftarrow> aux', left I \<le> \<tau> \<sigma> ne - t] {}"
    unfolding aux'_eq aux0_def
    using result_eq by (simp add: update_since_def Let_def)
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set aux'. if left I \<le> \<tau> \<sigma> ne - t then rel else empty_table)"
    unfolding rel_eq
    by (auto elim!: in_foldr_UnE bexI[rotated] intro!: in_foldr_UnI)
  show "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> I \<psi>)) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    left I \<le> \<tau> \<sigma> ne - t \<and> MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> (point (\<tau> \<sigma> ne - t)) \<psi>)"],
    goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_Since_point, goal_cases left right)
      case (left j)
      then show ?case using in_aux'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_Since_pointD dest: in_aux'_1)
    qed
  qed (auto dest!: in_aux'_1 intro!: qtable_empty)
qed

lemma length_update_until: "length (update_until pos I rel1 rel2 nt aux) = Suc (length aux)"
  unfolding update_until_def by simp

lemma wf_update_until:
  assumes pre: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> aux ne"
    and qtable1: "qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne + length aux) \<phi>) rel1"
    and qtable2: "qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne + length aux) \<psi>) rel2"
    and fvi_subset: "MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi>"
  shows "wf_until_aux \<sigma> n R pos \<phi> I \<psi> (update_until I pos rel1 rel2 (\<tau> \<sigma> (ne + length aux)) aux) ne"
  unfolding wf_until_aux_def length_update_until
  unfolding update_until_def list.rel_map add_Suc_right upt.simps eqTrueI[OF le_add1] if_True
proof (rule list_all2_appendI, unfold list.rel_map, goal_cases old new)
  case old
  show ?case
  proof (rule list.rel_mono_strong[OF assms(1)[unfolded wf_until_aux_def]]; safe, goal_cases mono1 mono2)
    case (mono1 i X Y v)
    then show ?case
      by (fastforce simp: sat_the_restrict less_Suc_eq
        elim!: qtable_join[OF _ qtable1] qtable_union[OF _ qtable1])
  next
    case (mono2 i X Y v)
    then show ?case using fvi_subset
      by (auto 0 3 simp: sat_the_restrict less_Suc_eq split: if_splits
        elim!: qtable_union[OF _ qtable_join_fixed[OF qtable2]]
        elim: qtable_cong[OF _ refl] intro: exI[of _ "ne + length aux"]) (* slow 8 sec*)
  qed
next
  case new
  then show ?case 
    by (auto intro!: qtable_empty qtable1 qtable2[THEN qtable_cong] exI[of _ "ne + length aux"]
      simp: less_Suc_eq zero_enat_def[symmetric])
qed

lemma wf_until_aux_Cons: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> (a # aux) ne \<Longrightarrow>
  wf_until_aux \<sigma> n R pos \<phi> I \<psi> aux (Suc ne)"
  unfolding wf_until_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong)

lemma wf_until_aux_Cons1: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_until_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_until_aux_Cons3: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow>
  qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux) \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> ne) I \<and>
    MFOTL.sat \<sigma> (map the v) j \<psi> \<and> (\<forall>k\<in>{ne..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi> else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>))) a2"
  unfolding wf_until_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma upt_append: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma wf_mbuf2_add:
  assumes "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 P [ja..<ja'] xs"
    and "list_all2 Q [jb..<jb'] ys"
    and "ja \<le> ja'" "jb \<le> jb'"
  shows "wf_mbuf2 i ja' jb' P Q (mbuf2_add xs ys buf)"
  using assms unfolding wf_mbuf2_def
  by (auto 0 3 simp: list_all2_append2 upt_append dest: list_all2_lengthD
    intro: exI[where x="[i..<ja]"] exI[where x="[ja..<ja']"]
           exI[where x="[i..<jb]"] exI[where x="[jb..<jb']"] split: prod.splits)

lemma mbuf2_take_eqD:
  assumes "mbuf2_take f buf = (xs, buf')"
    and "wf_mbuf2 i ja jb P Q buf"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 (\<lambda>i z. \<exists>x y. P i x \<and> Q i y \<and> z = f x y) [i..<min ja jb] xs"
  using assms unfolding wf_mbuf2_def
  by (induction f buf arbitrary: i xs buf' rule: mbuf2_take.induct)
    (fastforce simp add: list_all2_Cons2 upt_eq_Cons_conv min_absorb1 min_absorb2 split: prod.splits)+

lemma mbuf2t_take_eqD:
  assumes "mbuf2t_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 R [min ja jb..<j] nts'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      split: prod.split)

lemma mbuf2t_take_induct[consumes 5, case_names base step]:
  assumes "mbuf2t_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
    and "U i z"
    and "\<And>k x y t z. i \<le> k \<Longrightarrow> Suc k \<le> ja \<Longrightarrow> Suc k \<le> jb \<Longrightarrow>
      P k x \<Longrightarrow> Q k y \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f x y t z)"
  shows "U (min ja jb) z'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
       elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated] split: prod.split)

lemma mbuf2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf"
    and xs: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> j..<progress \<sigma> \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
      [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> j' n R \<phi> \<psi> buf'"
    and "list_all2 (\<lambda>i Z. \<exists>X Y.
      qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) X \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>) Y \<and>
      Z = f X Y)
      [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<min (progress \<sigma> \<phi> j') (progress \<sigma> \<psi> j')] zs"
  using pre unfolding wf_mbuf2'_def
  by (force intro!: mbuf2_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono[OF \<open>j \<le> j'\<close>])+

lemma mbuf2t_take_add':
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and pre_buf: "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> j..<progress \<sigma> \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
      [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> j' n R \<phi> \<psi> buf'"
    and "wf_ts \<sigma> j' \<phi> \<psi> nts'"
  using pre_buf pre_nts unfolding wf_mbuf2'_def wf_ts_def
  by (blast intro!: mbuf2t_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono[OF \<open>j \<le> j'\<close>]
      progress_le)+

lemma mbuf2t_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and pre_buf: "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> j..<progress \<sigma> \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
      [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> j'] ys"
    and "j \<le> j'"
    and base: "U (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)) z"
    and step: "\<And>k X Y z. min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<le> k \<Longrightarrow>
      Suc k \<le> progress \<sigma> \<phi> j' \<Longrightarrow> Suc k \<le> progress \<sigma> \<psi> j' \<Longrightarrow>
      qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) k \<phi>) X \<Longrightarrow>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) k \<psi>) Y \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f X Y (\<tau> \<sigma> k) z)"
  shows "U (min (progress \<sigma> \<phi> j') (progress \<sigma> \<psi> j')) z'"
  using pre_buf pre_nts unfolding wf_mbuf2'_def wf_ts_def
  by (blast intro!: mbuf2t_take_induct[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono[OF \<open>j \<le> j'\<close>]
      progress_le base step)

lemma progress_Until_le: "progress \<sigma> (formula.Until \<phi> I \<psi>) j \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
  by (cases "right I") (auto simp: trans_le_add1 intro!: cInf_lower)

lemma list_all2_upt_Cons: "P a x \<Longrightarrow> list_all2 P [Suc a..<b] xs \<Longrightarrow> Suc a \<le> b \<Longrightarrow>
  list_all2 P [a..<b] (x # xs)"
  by (simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all2_upt_append: "list_all2 P [a..<b] xs \<Longrightarrow> list_all2 P [b..<c] ys \<Longrightarrow>
  a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> list_all2 P [a..<c] (xs @ ys)"
  by (induction xs arbitrary: a) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma meval:
  assumes "wf_mformula \<sigma> j n R \<phi> \<phi>'"
  shows "case meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> (Suc j) n R \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>') (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>'))
    [progress \<sigma> \<phi>' j..<progress \<sigma> \<phi>' (Suc j)] xs"
using assms proof (induction \<phi> arbitrary: n R \<phi>')
  case (MRel rel)
  then show ?case
    by (cases pred: wf_mformula)
      (auto simp add: ball_Un intro: wf_mformula.intros qtableI table_eq_rel eq_rel_eval_trm
        in_eq_rel qtable_empty qtable_unit_table)
next
  case (MPred e ts)
  then show ?case
    by (cases pred: wf_mformula)
      (auto 0 4 simp: table_def in_these_eq match_wf_tuple match_eval_trm image_iff dest: ex_match
        split: if_splits intro!: wf_mformula.intros qtableI elim!: bexI[rotated])
next
  case (MAnd \<phi> pos \<psi> buf)
  from MAnd.prems show ?case
    by (cases pred: wf_mformula)
      (auto simp: fvi_And sat_And fvi_And_Not sat_And_Not sat_the_restrict
       dest!: MAnd.IH split: if_splits prod.splits intro!: wf_mformula.And qtable_join
       dest: mbuf2_take_add' elim!: list.rel_mono_strong)
next
  case (MOr \<phi> \<psi> buf)
  from MOr.prems show ?case
    by (cases pred: wf_mformula)
      (auto dest!: MOr.IH split: if_splits prod.splits intro!: wf_mformula.Or qtable_union
       dest: mbuf2_take_add' elim!: list.rel_mono_strong)
next
  case (MExists \<phi>)
  from MExists.prems show ?case
    by (cases pred: wf_mformula)
      (force simp: list.rel_map fvi_Suc sat_fvi_cong nth_Cons'
        intro!: wf_mformula.Exists dest!: MExists.IH qtable_project_fv 
        elim!: list.rel_mono_strong table_fvi_tl qtable_cong sat_fvi_cong[THEN iffD1, rotated -1]
        split: if_splits)+
next
  case (MPrev I \<phi> first buf nts)
  from MPrev.prems show ?case
  proof (cases pred: wf_mformula)
    case (Prev \<psi>)
    let ?xs = "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?\<phi> = "snd (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?ls = "fst (mprev_next I (buf @ ?xs) (nts @ [\<tau> \<sigma> j]))"
    let ?rs = "fst (snd (mprev_next I (buf @ ?xs) (nts @ [\<tau> \<sigma> j])))"
    let ?ts = "snd (snd (mprev_next I (buf @ ?xs) (nts @ [\<tau> \<sigma> j])))"
    let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>) X"
    let ?min = "min (progress \<sigma> \<psi> (Suc j)) (Suc j - 1)"
    from Prev MPrev.IH[of n R \<psi>] have IH: "wf_mformula \<sigma> (Suc j) n R ?\<phi> \<psi>" and
      "list_all2 ?P [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> (Suc j)] ?xs" by auto
    with Prev(4,5) have "list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then ?P i X else X = empty_table)
        [min (progress \<sigma> \<psi> j) (j - 1)..<?min] ?ls \<and>
       list_all2 ?P [?min..<progress \<sigma> \<psi> (Suc j)] ?rs \<and>
       list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?min..<Suc j] ?ts"
      by (intro mprev)
        (auto simp: progress_mono progress_le simp del: 
          intro!: list_all2_upt_append list_all2_appendI order.trans[OF min.cobounded1])
    moreover have "min (Suc (progress \<sigma> \<psi> j)) j = Suc (min (progress \<sigma> \<psi> j) (j-1))" if "j > 0"
      using that by auto
    ultimately show ?thesis using progress_mono[of j "Suc j" \<sigma> \<psi>] Prev(1,3) IH 
      by (auto simp: map_Suc_upt[symmetric] upt_Suc[of 0] list.rel_map qtable_empty_iff
        simp del: upt_Suc elim!: wf_mformula.Prev list.rel_mono_strong
        split: prod.split if_split_asm)
  qed simp
next
  case (MNext I \<phi> first nts)
  from MNext.prems show ?case
  proof (cases pred: wf_mformula)
    case (Next \<psi>)

    have min[simp]:
      "min (progress \<sigma> \<psi> j - Suc 0) (j - Suc 0) = progress \<sigma> \<psi> j - Suc 0"
      "min (progress \<sigma> \<psi> (Suc j) - Suc 0) j = progress \<sigma> \<psi> (Suc j) - Suc 0" for j
      using progress_le[of \<sigma> \<psi> j] progress_le[of \<sigma> \<psi> "Suc j"] by auto

    let ?xs = "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?ys = "case (?xs, first) of (_ # xs, True) \<Rightarrow> xs | _ \<Rightarrow> ?xs"
    let ?\<phi> = "snd (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?ls = "fst (mprev_next I ?ys (nts @ [\<tau> \<sigma> j]))"
    let ?rs = "fst (snd (mprev_next I ?ys (nts @ [\<tau> \<sigma> j])))"
    let ?ts = "snd (snd (mprev_next I ?ys (nts @ [\<tau> \<sigma> j])))"
    let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>) X"
    let ?min = "min (progress \<sigma> \<psi> (Suc j) - 1) (Suc j - 1)"
    from Next MNext.IH[of n R \<psi>] have IH: "wf_mformula \<sigma> (Suc j) n R ?\<phi> \<psi>"
      "list_all2 ?P [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> (Suc j)] ?xs" by auto
    with Next have "list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then ?P (Suc i) X else X = empty_table)
        [progress \<sigma> \<psi> j - 1..<?min] ?ls \<and>
       list_all2 ?P [Suc ?min..<progress \<sigma> \<psi> (Suc j)] ?rs \<and>
       list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?min..<Suc j] ?ts" if "progress \<sigma> \<psi> j < progress \<sigma> \<psi> (Suc j)"
      using progress_le[of \<sigma> \<psi> j] that
      by (intro mnext)
        (auto simp: progress_mono list_all2_Cons2 upt_eq_Cons_conv
          intro!: list_all2_upt_append list_all2_appendI split: list.splits)
    then show ?thesis using progress_mono[of j "Suc j" \<sigma> \<psi>] progress_le[of \<sigma> \<psi> "Suc j"] Next IH
      by (cases "progress \<sigma> \<psi> (Suc j) > progress \<sigma> \<psi> j")
        (auto 0 3 simp: qtable_empty_iff le_Suc_eq le_diff_conv
         elim!: wf_mformula.Next list.rel_mono_strong list_all2_appendI
         split: prod.split list.splits if_split_asm)  (* slow 5 sec*)
  qed simp
next
  case (MSince pos \<phi> I \<psi> buf nts aux)
  note sat.simps[simp del]
  from MSince.prems obtain \<phi>'' \<phi>''' \<psi>'' where Since_eq: "\<phi>' = MFOTL.Since \<phi>''' I \<psi>''"
    and pos: "if pos then \<phi>''' = \<phi>'' else \<phi>''' = MFOTL.Neg \<phi>''"
    and pos_eq: "safe_formula \<phi>''' = pos"
    and \<phi>: "wf_mformula \<sigma> j n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j n R \<psi> \<psi>''"
    and fvi_subset: "MFOTL.fv \<phi>'' \<subseteq> MFOTL.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> j \<phi>'' \<psi>'' nts"
    and aux: "wf_since_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux (progress \<sigma> (formula.Since \<phi>''' I \<psi>'') j)"
    by (cases pred: wf_mformula) (auto)
  have \<phi>''': "MFOTL.fv \<phi>''' = MFOTL.fv \<phi>''" "progress \<sigma> \<phi>''' j = progress \<sigma> \<phi>'' j" for j
    using pos by (simp_all split: if_splits)
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> \<phi>'' j) (progress \<sigma> \<psi>'' j)..<Suc j] (nts @ [\<tau> \<sigma> j])"
    using nts unfolding wf_ts_def
    by (auto simp add: progress_le[THEN min.coboundedI1] intro: list_all2_appendI)
  have update: "wf_since_aux \<sigma> n R pos \<phi>'' I \<psi>'' (snd (zs, aux')) (progress \<sigma> (formula.Since \<phi>''' I \<psi>'') (Suc j)) \<and>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>''' \<union> MFOTL.fv \<psi>'') (mem_restr R)
      (\<lambda>v. MFOTL.sat \<sigma> (map the v) i (formula.Since \<phi>''' I \<psi>'')))
      [progress \<sigma> (formula.Since \<phi>''' I \<psi>'') j..<progress \<sigma> (formula.Since \<phi>''' I \<psi>'') (Suc j)] (fst (zs, aux'))"
    if eval_\<phi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>) = xs"
      and eval_\<psi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<psi>) = ys"
      and eq: "mbuf2t_take (\<lambda>r1 r2 t (zs, aux).
        case update_since I pos r1 r2 t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbuf2_add xs ys buf) (nts @ [\<tau> \<sigma> j]) = ((zs, aux'), buf', nts')"
    for xs ys zs aux' buf' nts'
    unfolding progress.simps \<phi>'''
  proof (rule mbuf2t_take_add_induct'[where j'="Suc j" and z'="(zs, aux')", OF eq buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case 
      using MSince.IH(1)[OF \<phi>] eval_\<phi> by auto
  next
    case ys
    then show ?case 
      using MSince.IH(2)[OF \<psi>] eval_\<psi> by auto
  next
    case base
    then show ?case
     using aux by (simp add: \<phi>''')
  next
    case (step k X Y z)
    then show ?case
      using fvi_subset pos
      by (auto simp: Un_absorb1 elim!: update_since(1) list_all2_appendI dest!: update_since(2)
        split: prod.split if_splits)
  qed simp
  with MSince.IH(1)[OF \<phi>] MSince.IH(2)[OF \<psi>] show ?case
    by (auto 0 3 simp: Since_eq split: prod.split
      intro: wf_mformula.Since[OF _  _ pos pos_eq fvi_subset]
      elim: mbuf2t_take_add'(1)[OF _ buf nts_snoc] mbuf2t_take_add'(2)[OF _ buf nts_snoc])
next
  case (MUntil pos \<phi> I \<psi> buf nts aux)
  note sat.simps[simp del] progress.simps[simp del]
  from MUntil.prems obtain \<phi>'' \<phi>''' \<psi>'' where Until_eq: "\<phi>' = MFOTL.Until \<phi>''' I \<psi>''"
    and pos: "if pos then \<phi>''' = \<phi>'' else \<phi>''' = MFOTL.Neg \<phi>''"
    and pos_eq: "safe_formula \<phi>''' = pos"
    and \<phi>: "wf_mformula \<sigma> j n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j n R \<psi> \<psi>''"
    and fvi_subset: "MFOTL.fv \<phi>'' \<subseteq> MFOTL.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> j \<phi>'' \<psi>'' nts"
    and aux: "wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux (progress \<sigma> (formula.Until \<phi>''' I \<psi>'') j)"
    and length_aux: "progress \<sigma> (formula.Until \<phi>''' I \<psi>'') j + length aux =
      min (progress \<sigma> \<phi>'' j) (progress \<sigma> \<psi>'' j)"
    by (cases pred: wf_mformula) (auto)
  have \<phi>''': "progress \<sigma> \<phi>''' j = progress \<sigma> \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> \<phi>'' j) (progress \<sigma> \<psi>'' j)..<Suc j] (nts @ [\<tau> \<sigma> j])"
    using nts unfolding wf_ts_def
    by (auto simp add: progress_le[THEN min.coboundedI1] intro: list_all2_appendI)
  {
    fix xs ys zs aux' aux'' buf' nts'
    assume eval_\<phi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>) = xs"
      and eval_\<psi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<psi>) = ys"
      and eq1: "mbuf2t_take (update_until I pos) aux (mbuf2_add xs ys buf) (nts @ [\<tau> \<sigma> j]) =
        (aux', buf', nts')"
      and eq2: "eval_until I (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # _ \<Rightarrow> nt) aux' = (zs, aux'')"
    have update1: "wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux' (progress \<sigma> (formula.Until \<phi>''' I \<psi>'') j) \<and>
      progress \<sigma> (formula.Until \<phi>''' I \<psi>'') j + length aux' =
        min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j))"
      using MUntil.IH(1)[OF \<phi>] eval_\<phi> MUntil.IH(2)[OF \<psi>]
        eval_\<psi> nts_snoc nts_snoc length_aux aux fvi_subset
      unfolding \<phi>'''
      by (elim mbuf2t_take_add_induct'[where j'="Suc j", OF eq1 buf])
        (auto simp: length_update_until elim: wf_update_until)
    have nts': "wf_ts \<sigma> (Suc j) \<phi>'' \<psi>'' nts'"
      using MUntil.IH(1)[OF \<phi>] eval_\<phi> MUntil.IH(2)[OF \<psi>] eval_\<psi> nts_snoc
      unfolding wf_ts_def
      by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto simp: progress_mono progress_le
        intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def])
    have "i \<le> progress \<sigma> (formula.Until \<phi>''' I \<psi>'') (Suc j) \<Longrightarrow>
      wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux' i \<Longrightarrow>
      i + length aux' = min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)) \<Longrightarrow>
      wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux'' (progress \<sigma> (formula.Until \<phi>''' I \<psi>'') (Suc j)) \<and>
        i + length zs = progress \<sigma> (formula.Until \<phi>''' I \<psi>'') (Suc j) \<and>
        i + length zs + length aux'' = min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)) \<and>
        list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>'') (mem_restr R)
          (\<lambda>v. MFOTL.sat \<sigma> (map the v) i (formula.Until (if pos then \<phi>'' else MFOTL.Neg \<phi>'') I \<psi>'')))
          [i..<i + length zs] zs" for i
      using eq2
    proof (induction aux' arbitrary: zs aux'' i)
      case Nil
      then show ?case by (auto dest!: antisym[OF progress_Until_le])
    next
      case (Cons a aux')
      obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
      from Cons.prems(2) have aux': "wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
        by (rule wf_until_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (MFOTL.fv \<psi>'') (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> MFOTL.sat \<sigma> (map the v) j \<psi>'' \<and>
        (\<forall>k\<in>{i..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi>'' else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>''))) a2"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons3)
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j))"
        by simp
      have "i \<ge> progress \<sigma> (formula.Until \<phi>''' I \<psi>'') (Suc j)"
        if "enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt) \<le> enat t + right I"
        using that nts' unfolding wf_ts_def progress.simps
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv \<phi>'''
          intro!: cInf_lower \<tau>_mono elim!: order.trans[rotated] simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> (formula.Until \<phi>''' I \<psi>'') (Suc j)"
        if "enat t + right I < enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)"
      proof -
        from that obtain m where m: "right I = enat m" by (cases "right I") auto
        have \<tau>_min:  "\<tau> \<sigma> (min j k) = min (\<tau> \<sigma> j) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "i \<le> progress \<sigma> \<phi> i \<longleftrightarrow> progress \<sigma> \<phi> i = i" for \<phi> i
          using progress_le[of \<sigma> \<phi> i] by auto
        have min_Suc[simp]: "min j (Suc j) = j" by auto
        let ?X = "{i. \<forall>k. k < Suc j \<and> k \<le>min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)) \<longrightarrow> enat (\<tau> \<sigma> k) \<le> enat (\<tau> \<sigma> i) + right I}"
        let ?min = "min j (min (progress \<sigma> \<phi>'' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> j"
          by (rule \<tau>_mono) auto
        from m have "?X \<noteq> {}"
          by (auto dest!: \<tau>_mono[of _ "progress \<sigma> \<phi>'' (Suc j)" \<sigma>]
           simp: not_le not_less \<phi>''' intro!: exI[of _ "progress \<sigma> \<phi>'' (Suc j)"])
        thm less_le_trans[of "\<tau> \<sigma> i + m" "\<tau> \<sigma> _" "\<tau> \<sigma> _ + m"]
        from m show ?thesis
          using that nts' unfolding wf_ts_def progress.simps
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto simp: 1 \<phi>''' not_le not_less list_all2_Cons2 upt_eq_Cons_conv less_Suc_eq
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"] less_le_trans[of "\<tau> \<sigma> i + m" "\<tau> \<sigma> _" "\<tau> \<sigma> _ + m"] less_\<tau>D)
      qed
      moreover have *: "k < progress \<sigma> \<psi> (Suc j)" if
        "enat (\<tau> \<sigma> i) + right I < enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)"
        "enat (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
      proof -
        from that(1,2) obtain m where "right I = enat m"
           "\<tau> \<sigma> i + m < (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)" "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> m"
          by (cases "right I") auto
        with that(3) nts' progress_le[of \<sigma> \<psi>'' "Suc j"] progress_le[of \<sigma> \<phi>'' "Suc j"]
        show ?thesis
          unfolding wf_ts_def le_diff_conv
          by (auto simp: not_le list_all2_Cons2 upt_eq_Cons_conv less_Suc_eq add.commute
            simp del: upt_Suc split: list.splits if_splits dest!: le_less_trans[of "\<tau> \<sigma> k"] less_\<tau>D)
      qed
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, a1, a2)\<close>
        by (auto simp: \<phi>''' 1 sat.simps upt_conv_Cons dest!:  Cons.IH[OF _ aux' Suc_i_aux']
          simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])
    qed
    note this[OF progress_mono[OF le_SucI, OF order.refl] conjunct1[OF update1] conjunct2[OF update1]]
  }
  note update = this
  from MUntil.IH(1)[OF \<phi>] MUntil.IH(2)[OF \<psi>] pos pos_eq fvi_subset show ?case
    by (auto 0 4 simp: Until_eq \<phi>''' progress.simps(3) split: prod.split if_splits
      dest!: update[OF refl refl, rotated]
      intro!: wf_mformula.Until
      elim!: list.rel_mono_strong qtable_cong
      elim: mbuf2t_take_add'(1)[OF _ buf nts_snoc] mbuf2t_take_add'(2)[OF _ buf nts_snoc])
qed


subsubsection \<open>Monitor Step\<close>

lemma wf_mstate_mstep: "wf_mstate \<phi> \<pi> R st \<Longrightarrow> last_ts \<pi> \<le> snd tdb \<Longrightarrow>
  wf_mstate \<phi> (psnoc \<pi> tdb) R (snd (mstep tdb st))"
  unfolding wf_mstate_def mstep_def Let_def
  by (fastforce simp add: progress_mono le_imp_diff_is_add split: prod.splits
      elim!: prefix_of_psnocE dest: meval list_all2_lengthD)

lemma mstep_output_iff: 
  assumes "wf_mstate \<phi> \<pi> R st" "last_ts \<pi> \<le> snd tdb" "prefix_of (psnoc \<pi> tdb) \<sigma>" "mem_restr R v" 
  shows "(i, v) \<in> fst (mstep tdb st) \<longleftrightarrow>
    progress \<sigma> \<phi> (plen \<pi>) \<le> i \<and> i < progress \<sigma> \<phi> (Suc (plen \<pi>)) \<and>
    wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<and> MFOTL.sat \<sigma> (map the v) i \<phi>"
proof -
  from prefix_of_psnocE[OF assms(3,2)] have "prefix_of \<pi> \<sigma>" 
    "\<Gamma> \<sigma> (plen \<pi>) = fst tdb" "\<tau> \<sigma> (plen \<pi>) = snd tdb" by auto
  moreover from assms(1) \<open>prefix_of \<pi> \<sigma>\<close> have "mstate_n st = MFOTL.nfv \<phi>"
    "mstate_i st = progress \<sigma> \<phi> (plen \<pi>)" "wf_mformula \<sigma> (plen \<pi>) (mstate_n st) R (mstate_m st) \<phi>"
    unfolding wf_mstate_def by blast+
  moreover from meval[OF \<open>wf_mformula \<sigma> (plen \<pi>) (mstate_n st) R (mstate_m st) \<phi>\<close>] obtain Vs st' where
    "meval (mstate_n st) (\<tau> \<sigma> (plen \<pi>)) (\<Gamma> \<sigma> (plen \<pi>)) (mstate_m st) = (Vs, st')"
    "wf_mformula \<sigma> (Suc (plen \<pi>)) (mstate_n st) R st' \<phi>"
    "list_all2 (\<lambda>i. qtable (mstate_n st) (fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> (plen \<pi>)..<progress \<sigma> \<phi> (Suc (plen \<pi>))] Vs" by blast
  moreover from this assms(4) have "qtable (mstate_n st) (fv \<phi>) (mem_restr R)
    (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) (Vs ! (i - progress \<sigma> \<phi> (plen \<pi>)))"
      if "progress \<sigma> \<phi> (plen \<pi>) \<le> i" "i < progress \<sigma> \<phi> (Suc (plen \<pi>))"
    using that by (auto simp: list_all2_conv_all_nth
      dest!: spec[of _ "(i - progress \<sigma> \<phi> (plen \<pi>))"])
  ultimately show ?thesis
    using assms(4) unfolding mstep_def Let_def
    by (auto simp: in_set_enumerate_eq list_all2_conv_all_nth progress_mono le_imp_diff_is_add
      elim!: in_qtableE in_qtableI intro!: bexI[of _ "(i, Vs ! (i - progress \<sigma> \<phi> (plen \<pi>)))"])
qed


subsubsection \<open>Monitor Function\<close>

definition minit_safe where
  "minit_safe \<phi> = (if mmonitorable_exec \<phi> then minit \<phi> else undefined)"

lemma minit_safe_minit: "mmonitorable \<phi> \<Longrightarrow> minit_safe \<phi> = minit \<phi>"
  unfolding minit_safe_def monitorable_formula_code by simp

lemma mstep_mverdicts:
  assumes wf: "wf_mstate \<phi> \<pi> R st"
    and le[simp]: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R v"
  shows "(i, v) \<in> fst (mstep tdb st) \<longleftrightarrow> (i, v) \<in> mverdicts \<phi> (psnoc \<pi> tdb) - mverdicts \<phi> \<pi>"
proof -
  obtain \<sigma> where p2: "prefix_of (psnoc \<pi> tdb) \<sigma>"
    using ex_prefix_of by blast
  with le have p1: "prefix_of \<pi> \<sigma>" by (blast elim!: prefix_of_psnocE)
  show ?thesis
    unfolding verimon.verdicts_def
    by (auto 0 3 simp: p2 progress_prefix_conv[OF _ p1] sat_prefix_conv[OF _ p1] not_less
      dest:  mstep_output_iff[OF wf le p2 restrict, THEN iffD1] spec[of _ \<sigma>]
             mstep_output_iff[OF wf le _ restrict, THEN iffD1] verimon.progress_sat_cong[OF p1]
      intro: mstep_output_iff[OF wf le p2 restrict, THEN iffD2] p1)
qed

primrec msteps0 where
  "msteps0 [] st = ({}, st)"
| "msteps0 (tdb # \<pi>) st =
    (let (V', st') = mstep tdb st; (V'', st'') = msteps0 \<pi> st' in (V' \<union> V'', st''))"

primrec msteps0_stateless where
  "msteps0_stateless [] st = {}"
| "msteps0_stateless (tdb # \<pi>) st = (let (V', st') = mstep tdb st in V' \<union> msteps0_stateless \<pi> st')"

lemma msteps0_msteps0_stateless: "fst (msteps0 w st) = msteps0_stateless w st"
  by (induct w arbitrary: st) (auto simp: split_beta)

lift_definition msteps :: "'a MFOTL.prefix \<Rightarrow> 'a mstate \<Rightarrow> (nat \<times> 'a option list) set \<times> 'a mstate"
  is msteps0 .

lift_definition msteps_stateless :: "'a MFOTL.prefix \<Rightarrow> 'a mstate \<Rightarrow> (nat \<times> 'a option list) set"
  is msteps0_stateless .

lemma msteps_msteps_stateless: "fst (msteps w st) = msteps_stateless w st"
  by transfer (rule msteps0_msteps0_stateless)

lemma msteps0_snoc: "msteps0 (\<pi> @ [tdb]) st =
   (let (V', st') = msteps0 \<pi> st; (V'', st'') = mstep tdb st' in (V' \<union> V'', st''))"
  by (induct \<pi> arbitrary: st) (auto split: prod.splits)

lemma msteps_psnoc: "last_ts \<pi> \<le> snd tdb \<Longrightarrow> msteps (psnoc \<pi> tdb) st =
   (let (V', st') = msteps \<pi> st; (V'', st'') = mstep tdb st' in (V' \<union> V'', st''))"
  by transfer (auto simp: msteps0_snoc split: list.splits prod.splits if_splits)

definition monitor where
  "monitor \<phi> \<pi> = msteps_stateless \<pi> (minit_safe \<phi>)"

lemma Suc_length_conv_snoc: "(Suc n = length xs) = (\<exists>y ys. xs = ys @ [y] \<and> length ys = n)"
  by (cases xs rule: rev_cases) auto

lemma wf_mstate_msteps: "wf_mstate \<phi> \<pi> R st \<Longrightarrow> mem_restr R v \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow>
  X = msteps (pdrop (plen \<pi>) \<pi>') st \<Longrightarrow> wf_mstate \<phi> \<pi>' R (snd X) \<and>
  ((i, v) \<in> fst X) = ((i, v) \<in> mverdicts \<phi> \<pi>' - mverdicts \<phi> \<pi>)"
proof (induct "plen \<pi>' - plen \<pi>" arbitrary: X st \<pi> \<pi>')
  case 0
  from 0(1,4,5) have "\<pi> = \<pi>'"  "X = ({}, st)"
    by (transfer; auto)+
  with 0(2) show ?case by simp
next
  case (Suc x)
  from Suc(2,5) obtain \<pi>'' tdb where "x = plen \<pi>'' - plen \<pi>"  "\<pi> \<le> \<pi>''"
    "\<pi>' = psnoc \<pi>'' tdb" "pdrop (plen \<pi>) (psnoc \<pi>'' tdb) = psnoc (pdrop (plen \<pi>) \<pi>'') tdb"
    "last_ts (pdrop (plen \<pi>) \<pi>'') \<le> snd tdb" "last_ts \<pi>'' \<le> snd tdb"
    "\<pi>'' \<le> psnoc \<pi>'' tdb"
  proof (atomize_elim, transfer, elim exE, goal_cases prefix)
    case (prefix _ _ \<pi>' _ \<pi>_tdb)
    then show ?case
    proof (cases \<pi>_tdb rule: rev_cases)
      case (snoc \<pi> tdb)
      with prefix show ?thesis
        by (intro bexI[of _ "\<pi>' @ \<pi>"] exI[of _ tdb])
          (force simp: sorted_append append_eq_Cons_conv split: list.splits if_splits)+
    qed simp
  qed
  with Suc(1)[OF this(1) Suc.prems(1,2) this(2) refl] Suc.prems show ?case
    unfolding msteps_msteps_stateless[symmetric]
    by (auto simp: msteps_psnoc split_beta mstep_mverdicts
      dest: verimon.verdicts_mono[THEN set_mp, rotated] intro!: wf_mstate_mstep)
qed

lemma wf_mstate_msteps_stateless:
  assumes "wf_mstate \<phi> \<pi> R st" "mem_restr R v" "\<pi> \<le> \<pi>'"
  shows "(i, v) \<in> msteps_stateless (pdrop (plen \<pi>) \<pi>') st \<longleftrightarrow> (i, v) \<in> mverdicts \<phi> \<pi>' - mverdicts \<phi> \<pi>"
  using wf_mstate_msteps[OF assms refl] unfolding msteps_msteps_stateless by simp

lemma wf_mstate_msteps_stateless_UNIV: "wf_mstate \<phi> \<pi> UNIV st \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow>
  msteps_stateless (pdrop (plen \<pi>) \<pi>') st = mverdicts \<phi> \<pi>' - mverdicts \<phi> \<pi>"
  by (auto dest: wf_mstate_msteps_stateless[OF _ mem_restr_UNIV])

lemma mverdicts_Nil: "mverdicts \<phi> pnil = {}"
  unfolding verimon.verdicts_def
  by (auto intro: ex_prefix_of)

lemma wf_mstate_minit_safe: "mmonitorable \<phi> \<Longrightarrow> wf_mstate \<phi> pnil R (minit_safe \<phi>)"
  using wf_mstate_minit minit_safe_minit mmonitorable_def by metis

lemma monitor_mverdicts: "mmonitorable \<phi> \<Longrightarrow> monitor \<phi> \<pi> = mverdicts \<phi> \<pi>"
  unfolding monitor_def
  by (subst wf_mstate_msteps_stateless_UNIV[OF wf_mstate_minit_safe, simplified])
    (auto simp: mmonitorable_def mverdicts_Nil)

subsection \<open>Collected Correctness Results\<close>

text \<open>We summarize the main results proved above.
\begin{enumerate}
\item The term @{term mverdicts} describes semantically the monitor's expected behaviour:
\begin{itemize}
\item @{thm[source] verimon.mono_monitor}: @{thm verimon.mono_monitor[no_vars]}
\item @{thm[source] verimon.sound_monitor}: @{thm verimon.sound_monitor[no_vars]}
\item @{thm[source] verimon.complete_monitor}: @{thm verimon.complete_monitor[no_vars]}
\item @{thm[source] verimon.monitor_slice}: @{thm verimon.monitor_slice[no_vars]}
\end{itemize}
\item The executable monitor's online interface @{term minit_safe} and @{term mstep}
  preserves the invariant @{term wf_mstate} and produces the the verdicts according
  to @{term mverdicts}:
\begin{itemize}
\item @{thm[source] wf_mstate_minit_safe}: @{thm wf_mstate_minit_safe[no_vars]}
\item @{thm[source] wf_mstate_mstep}: @{thm wf_mstate_mstep[no_vars]}
\item @{thm[source] mstep_mverdicts}: @{thm mstep_mverdicts[no_vars]}
\end{itemize}
\item The executable monitor's offline interface @{term monitor} implements @{term mverdicts}:
\begin{itemize}
\item @{thm[source] monitor_mverdicts}: @{thm monitor_mverdicts[no_vars]}
\end{itemize}
\end{enumerate}
\<close>

(*<*)
end
(*>*)
