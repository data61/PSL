section \<open>Derivatives of Abstract Formulas\<close>
(* Author: Dmitriy Traytel *)

(*<*)
theory Abstract_Formula
imports
  Automaton
  Deriving.Compare_Instances
  "HOL-Library.Code_Target_Nat"
  While_Default
begin
(*>*)

subsection \<open>Preliminaries\<close>

lemma pred_Diff_0[simp]: "0 \<notin> A \<Longrightarrow> i \<in> (\<lambda>x. x - Suc 0) ` A \<longleftrightarrow> Suc i \<in> A"
  by (cases i) (fastforce simp: image_iff le_Suc_eq  elim: contrapos_np)+

lemma funpow_cycle_mult: "(f ^^ k) x = x \<Longrightarrow> (f ^^ (m * k)) x = x"
  by (induct m) (auto simp: funpow_add)

lemma funpow_cycle: "(f ^^ k) x = x \<Longrightarrow> (f ^^ l) x = (f ^^ (l mod k)) x"
  by (subst div_mult_mod_eq[symmetric, of l k])
    (simp only: add.commute funpow_add funpow_cycle_mult o_apply)

lemma funpow_cycle_offset:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "(f ^^ k) x = (f ^^ i) x" "i \<le> k" "i \<le> l"
  shows "(f ^^ l) x = (f ^^ ((l - i) mod (k - i) + i)) x"
proof -
  from assms have
    "(f ^^ (k - i)) ((f ^^ i) x) = ((f ^^ i) x)"
    "(f ^^ l) x = (f ^^ (l - i)) ((f ^^ i) x)"
    unfolding fun_cong[OF funpow_add[symmetric, unfolded o_def]] by simp_all
  from funpow_cycle[OF this(1), of "l - i"] this(2) show ?thesis
    by (simp add: funpow_add)
qed

lemma in_set_tlD: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
  by (cases xs) auto

definition "dec k m = (if m > k then m - Suc 0 else m :: nat)"


subsection \<open>Abstract formulas\<close>

datatype (discs_sels) ('a, 'k) aformula =
  FBool bool
| FBase 'a
| FNot "('a, 'k) aformula"
| FOr "('a, 'k) aformula" "('a, 'k) aformula"
| FAnd "('a, 'k) aformula" "('a, 'k) aformula"
| FEx 'k "('a, 'k) aformula"
| FAll 'k "('a, 'k) aformula"
derive linorder aformula

fun nFOR where
  "nFOR [] = FBool False"
| "nFOR [x] = x"
| "nFOR (x # xs) = FOr x (nFOR xs)"

fun nFAND where
  "nFAND [] = FBool True"
| "nFAND [x] = x"
| "nFAND (x # xs) = FAnd x (nFAND xs)"

definition "NFOR = nFOR o sorted_list_of_set"
definition "NFAND = nFAND o sorted_list_of_set"

fun disjuncts where
  "disjuncts (FOr \<phi> \<psi>) = disjuncts \<phi> \<union> disjuncts \<psi>"
| "disjuncts \<phi> = {\<phi>}"

fun conjuncts where
  "conjuncts (FAnd \<phi> \<psi>) = conjuncts \<phi> \<union> conjuncts \<psi>"
| "conjuncts \<phi> = {\<phi>}"

fun disjuncts_list where
  "disjuncts_list (FOr \<phi> \<psi>) = disjuncts_list \<phi> @ disjuncts_list \<psi>"
| "disjuncts_list \<phi> = [\<phi>]"

fun conjuncts_list where
  "conjuncts_list (FAnd \<phi> \<psi>) = conjuncts_list \<phi> @ conjuncts_list \<psi>"
| "conjuncts_list \<phi> = [\<phi>]"

lemma finite_juncts[simp]: "finite (disjuncts \<phi>)" "finite (conjuncts \<phi>)"
  and nonempty_juncts[simp]: "disjuncts \<phi> \<noteq> {}" "conjuncts \<phi> \<noteq> {}"
  by (induct \<phi>) auto

lemma juncts_eq_set_juncts_list:
  "disjuncts \<phi> = set (disjuncts_list \<phi>)"
  "conjuncts \<phi> = set (conjuncts_list \<phi>)"
  by (induct \<phi>) auto

lemma notin_juncts:
  "\<lbrakk>\<psi> \<in> disjuncts \<phi>; is_FOr \<psi>\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>\<psi> \<in> conjuncts \<phi>; is_FAnd \<psi>\<rbrakk> \<Longrightarrow> False"
  by (induct \<phi>) auto

lemma juncts_list_singleton:
  "\<not> is_FOr \<phi> \<Longrightarrow> disjuncts_list \<phi> = [\<phi>]"
  "\<not> is_FAnd \<phi> \<Longrightarrow> conjuncts_list \<phi> = [\<phi>]"
  by (induct \<phi>) auto

lemma juncts_singleton:
  "\<not> is_FOr \<phi> \<Longrightarrow> disjuncts \<phi> = {\<phi>}"
  "\<not> is_FAnd \<phi> \<Longrightarrow> conjuncts \<phi> = {\<phi>}"
  by (induct \<phi>) auto

lemma nonempty_juncts_list: "conjuncts_list \<phi> \<noteq> []" "disjuncts_list \<phi> \<noteq> []"
  using nonempty_juncts[of \<phi>] by (auto simp: Suc_le_eq juncts_eq_set_juncts_list)

primrec norm_ACI ("\<langle>_\<rangle>") where
  "\<langle>FBool b\<rangle> = FBool b"
| "\<langle>FBase a\<rangle> = FBase a"
| "\<langle>FNot \<phi>\<rangle> = FNot \<langle>\<phi>\<rangle>"
| "\<langle>FOr \<phi> \<psi>\<rangle> = NFOR (disjuncts (FOr \<langle>\<phi>\<rangle> \<langle>\<psi>\<rangle>))"
| "\<langle>FAnd \<phi> \<psi>\<rangle> = NFAND (conjuncts (FAnd \<langle>\<phi>\<rangle> \<langle>\<psi>\<rangle>))"
| "\<langle>FEx k \<phi>\<rangle> = FEx k \<langle>\<phi>\<rangle>"
| "\<langle>FAll k \<phi>\<rangle> = FAll k \<langle>\<phi>\<rangle>"

fun nf_ACI where
  "nf_ACI (FOr \<psi>1 \<psi>2) = (\<not> is_FOr \<psi>1 \<and> (let \<phi>s = \<psi>1 # disjuncts_list \<psi>2 in
    sorted \<phi>s \<and> distinct \<phi>s \<and> nf_ACI \<psi>1 \<and> nf_ACI \<psi>2))"
| "nf_ACI (FAnd \<psi>1 \<psi>2) = (\<not> is_FAnd \<psi>1 \<and> (let \<phi>s = \<psi>1 # conjuncts_list \<psi>2 in
    sorted \<phi>s \<and> distinct \<phi>s \<and> nf_ACI \<psi>1 \<and> nf_ACI \<psi>2))"
| "nf_ACI (FNot \<phi>) = nf_ACI \<phi>"
| "nf_ACI (FEx k \<phi>) = nf_ACI \<phi>"
| "nf_ACI (FAll k \<phi>) = nf_ACI \<phi>"
| "nf_ACI \<phi> = True"

lemma nf_ACI_D:
  "nf_ACI \<phi> \<Longrightarrow> sorted (disjuncts_list \<phi>)"
  "nf_ACI \<phi> \<Longrightarrow> sorted (conjuncts_list \<phi>)"
  "nf_ACI \<phi> \<Longrightarrow> distinct (disjuncts_list \<phi>)"
  "nf_ACI \<phi> \<Longrightarrow> distinct (conjuncts_list \<phi>)"
  "nf_ACI \<phi> \<Longrightarrow> list_all nf_ACI (disjuncts_list \<phi>)"
  "nf_ACI \<phi> \<Longrightarrow> list_all nf_ACI (conjuncts_list \<phi>)"
  by (induct \<phi>) (auto simp: juncts_list_singleton)

lemma disjuncts_list_nFOR:
  "\<lbrakk>list_all (\<lambda>x. \<not> is_FOr x) \<phi>s; \<phi>s \<noteq> []\<rbrakk> \<Longrightarrow> disjuncts_list (nFOR \<phi>s) = \<phi>s"
  by (induct \<phi>s rule: nFOR.induct) (auto simp: juncts_list_singleton)

lemma conjuncts_list_nFAND:
  "\<lbrakk>list_all (\<lambda>x. \<not> is_FAnd x) \<phi>s; \<phi>s \<noteq> []\<rbrakk> \<Longrightarrow> conjuncts_list (nFAND \<phi>s) = \<phi>s"
  by (induct \<phi>s rule: nFAND.induct) (auto simp: juncts_list_singleton)

lemma disjuncts_NFOR:
  "\<lbrakk>finite X; X \<noteq> {}; \<forall>x \<in> X. \<not> is_FOr x\<rbrakk> \<Longrightarrow> disjuncts (NFOR X) = X"
  unfolding NFOR_def by (auto simp: juncts_eq_set_juncts_list list_all_iff disjuncts_list_nFOR)

lemma conjuncts_NFAND:
  "\<lbrakk>finite X; X \<noteq> {}; \<forall>x \<in> X. \<not> is_FAnd x\<rbrakk> \<Longrightarrow> conjuncts (NFAND X) = X"
  unfolding NFAND_def by (auto simp: juncts_eq_set_juncts_list list_all_iff conjuncts_list_nFAND)

lemma nf_ACI_nFOR: 
  "\<lbrakk>sorted \<phi>s; distinct \<phi>s; list_all nf_ACI \<phi>s; list_all (\<lambda>x. \<not> is_FOr x) \<phi>s\<rbrakk> \<Longrightarrow> nf_ACI (nFOR \<phi>s)"
  by (induct \<phi>s rule: nFOR.induct)
    (auto simp: juncts_list_singleton disjuncts_list_nFOR nf_ACI_D)

lemma nf_ACI_nFAND: 
  "\<lbrakk>sorted \<phi>s; distinct \<phi>s; list_all nf_ACI \<phi>s; list_all (\<lambda>x. \<not> is_FAnd x) \<phi>s\<rbrakk> \<Longrightarrow> nf_ACI (nFAND \<phi>s)"
  by (induct \<phi>s rule: nFAND.induct)
    (auto simp: juncts_list_singleton conjuncts_list_nFAND nf_ACI_D)

lemma nf_ACI_juncts:
  "\<lbrakk>\<psi> \<in> disjuncts \<phi>; nf_ACI \<phi>\<rbrakk> \<Longrightarrow> nf_ACI \<psi>"
  "\<lbrakk>\<psi> \<in> conjuncts \<phi>; nf_ACI \<phi>\<rbrakk> \<Longrightarrow> nf_ACI \<psi>"
  by (induct \<phi>) auto

lemma nf_ACI_norm_ACI: "nf_ACI \<langle>\<phi>\<rangle>"
  by (induct \<phi>)
    (force simp: NFOR_def NFAND_def list_all_iff
      intro!: nf_ACI_nFOR nf_ACI_nFAND elim: nf_ACI_juncts notin_juncts)+

lemma nFOR_Cons: "nFOR (x # xs) = (if xs = [] then x else FOr x (nFOR xs))"
  by (cases xs) simp_all

lemma nFAND_Cons: "nFAND (x # xs) = (if xs = [] then x else FAnd x (nFAND xs))"
  by (cases xs) simp_all

lemma nFOR_disjuncts: "nf_ACI \<psi> \<Longrightarrow> nFOR (disjuncts_list \<psi>) = \<psi>"
  by (induct \<psi>) (auto simp: juncts_list_singleton nFOR_Cons)

lemma nFAND_conjuncts: "nf_ACI \<psi> \<Longrightarrow> nFAND (conjuncts_list \<psi>) = \<psi>"
  by (induct \<psi>) (auto simp: juncts_list_singleton nFAND_Cons)

lemma NFOR_disjuncts: "nf_ACI \<psi> \<Longrightarrow> NFOR (disjuncts \<psi>) = \<psi>"
  using nFOR_disjuncts[of \<psi>] unfolding NFOR_def o_apply juncts_eq_set_juncts_list
  by (metis finite_set finite_sorted_distinct_unique nf_ACI_D(1,3) sorted_list_of_set)

lemma NFAND_conjuncts: "nf_ACI \<psi> \<Longrightarrow> NFAND (conjuncts \<psi>) = \<psi>"
  using nFAND_conjuncts[of \<psi>] unfolding NFAND_def o_apply juncts_eq_set_juncts_list
  by (metis finite_set finite_sorted_distinct_unique nf_ACI_D(2,4) sorted_list_of_set)

lemma norm_ACI_if_nf_ACI: "nf_ACI \<phi> \<Longrightarrow> \<langle>\<phi>\<rangle> = \<phi>"
  by (induct \<phi>)
    (auto simp: juncts_list_singleton juncts_eq_set_juncts_list nonempty_juncts_list
      NFOR_def NFAND_def nFOR_Cons nFAND_Cons nFOR_disjuncts nFAND_conjuncts
      sorted_list_of_set_sort_remdups distinct_remdups_id sorted_sort_id insort_is_Cons)

lemma norm_ACI_idem: "\<langle>\<langle>\<phi>\<rangle>\<rangle> = \<langle>\<phi>\<rangle>"
  by (metis nf_ACI_norm_ACI norm_ACI_if_nf_ACI)

lemma norm_ACI_juncts:
  "nf_ACI \<phi> \<Longrightarrow> norm_ACI ` disjuncts \<phi> = disjuncts \<phi>"
  "nf_ACI \<phi> \<Longrightarrow> norm_ACI ` conjuncts \<phi> = conjuncts \<phi>"
  by (drule nf_ACI_D(5,6), force simp: list_all_iff juncts_eq_set_juncts_list norm_ACI_if_nf_ACI)+

lemma
  norm_ACI_NFOR: "nf_ACI \<phi> \<Longrightarrow> \<phi> = NFOR (norm_ACI ` disjuncts \<phi>)" and
  norm_ACI_NFAND: "nf_ACI \<phi> \<Longrightarrow> \<phi> = NFAND (norm_ACI ` conjuncts \<phi>)"
  by (simp_all add: norm_ACI_juncts NFOR_disjuncts NFAND_conjuncts)

(*
'a - atomic formula
'i - interpretation
'k - kind of quantifier
'n - De Brujin index
'x - alphabet element
'v - valuation
*)
locale Formula_Operations =
  fixes TYPEVARS :: "'a :: linorder \<times> 'i \<times> 'k :: {linorder, enum} \<times> 'n \<times> 'x \<times> 'v"

  (* De Bruijn indices abstractly *)
  and SUC :: "'k \<Rightarrow> 'n \<Rightarrow> 'n"
  and LESS :: "'k \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool"

  (* Interpratations *)
  and assigns :: "nat \<Rightarrow> 'i \<Rightarrow> 'k \<Rightarrow> 'v" ("_\<^bsup>_\<^esup>_" [900, 999, 999] 999)
  and nvars :: "'i \<Rightarrow> 'n" ("#\<^sub>V _" [1000] 900)
  and Extend :: "'k \<Rightarrow> nat \<Rightarrow> 'i \<Rightarrow> 'v \<Rightarrow> 'i"
  and CONS :: "'x \<Rightarrow> 'i \<Rightarrow> 'i"
  and SNOC :: "'x \<Rightarrow> 'i \<Rightarrow> 'i"
  and Length :: "'i \<Rightarrow> nat"

  (* Alphabet elements *)
  and extend :: "'k \<Rightarrow> bool \<Rightarrow> 'x \<Rightarrow> 'x"
  and size :: "'x \<Rightarrow> 'n"
  and zero :: "'n \<Rightarrow> 'x"
  and alphabet :: "'n \<Rightarrow> 'x list"

  (* Valuations *)
  and eval :: "'v \<Rightarrow> nat \<Rightarrow> bool"
  and downshift :: "'v \<Rightarrow> 'v"
  and upshift :: "'v \<Rightarrow> 'v"
  and add :: "nat \<Rightarrow> 'v \<Rightarrow> 'v"
  and cut :: "nat \<Rightarrow> 'v \<Rightarrow> 'v"
  and len :: "'v \<Rightarrow> nat"

  (* Restrictions *)
  and restrict :: "'k \<Rightarrow> 'v \<Rightarrow> bool"
  and Restrict :: "'k \<Rightarrow> nat \<Rightarrow> ('a, 'k) aformula"

  (* Function extensions for the base cases *)
  and lformula0 :: "'a \<Rightarrow> bool"
  and FV0 :: "'k \<Rightarrow> 'a \<Rightarrow> nat set"
  and find0 :: "'k \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
  and wf0 :: "'n \<Rightarrow> 'a \<Rightarrow> bool"
  and decr0 :: "'k \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  and satisfies0 :: "'i \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>0" 50)
  and nullable0 :: "'a \<Rightarrow> bool"
  and lderiv0 :: "'x \<Rightarrow> 'a \<Rightarrow> ('a, 'k) aformula"
  and rderiv0 :: "'x \<Rightarrow> 'a \<Rightarrow> ('a, 'k) aformula"
begin

abbreviation "LEQ k l n \<equiv> LESS k l (SUC k n)"

primrec FV where
  "FV (FBool _) k = {}"
| "FV (FBase a) k = FV0 k a"
| "FV (FNot \<phi>) k = FV \<phi> k"
| "FV (FOr \<phi> \<psi>) k = FV \<phi> k \<union> FV \<psi> k"
| "FV (FAnd \<phi> \<psi>) k = FV \<phi> k \<union> FV \<psi> k"
| "FV (FEx k' \<phi>) k = (if k' = k then (\<lambda>x. x - 1) ` (FV \<phi> k - {0}) else FV \<phi> k)"
| "FV (FAll k' \<phi>) k = (if k' = k then (\<lambda>x. x - 1) ` (FV \<phi> k - {0}) else FV \<phi> k)"

primrec find where
  "find k l (FBool _) = False"
| "find k l (FBase a) = find0 k l a"
| "find k l (FNot \<phi>) = find k l \<phi>"
| "find k l (FOr \<phi> \<psi>) = (find k l \<phi> \<or> find k l \<psi>)"
| "find k l (FAnd \<phi> \<psi>) = (find k l \<phi> \<or> find k l \<psi>)"
| "find k l (FEx k' \<phi>) = find k (if k = k' then Suc l else l) \<phi>"
| "find k l (FAll k' \<phi>) = find k (if k = k' then Suc l else l) \<phi>"

primrec wf :: "'n \<Rightarrow> ('a, 'k) aformula \<Rightarrow> bool" where
  "wf n (FBool _) = True"
| "wf n (FBase a) = wf0 n a"
| "wf n (FNot \<phi>) = wf n \<phi>"
| "wf n (FOr \<phi> \<psi>) = (wf n \<phi> \<and> wf n \<psi>)"
| "wf n (FAnd \<phi> \<psi>) = (wf n \<phi> \<and> wf n \<psi>)"
| "wf n (FEx k \<phi>) = wf (SUC k n) \<phi>"
| "wf n (FAll k \<phi>) = wf (SUC k n) \<phi>"

primrec lformula :: "('a, 'k) aformula \<Rightarrow> bool" where
  "lformula (FBool _) = True"
| "lformula (FBase a) = lformula0 a"
| "lformula (FNot \<phi>) = lformula \<phi>"
| "lformula (FOr \<phi> \<psi>) = (lformula \<phi> \<and> lformula \<psi>)"
| "lformula (FAnd \<phi> \<psi>) = (lformula \<phi> \<and> lformula \<psi>)"
| "lformula (FEx k \<phi>) = lformula \<phi>"
| "lformula (FAll k \<phi>) = lformula \<phi>"

primrec decr :: "'k \<Rightarrow> nat \<Rightarrow> ('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "decr k l (FBool b) = FBool b"
| "decr k l (FBase a) = FBase (decr0 k l a)"
| "decr k l (FNot \<phi>) = FNot (decr k l \<phi>)"
| "decr k l (FOr \<phi> \<psi>) = FOr (decr k l \<phi>) (decr k l \<psi>)"
| "decr k l (FAnd \<phi> \<psi>) = FAnd (decr k l \<phi>) (decr k l \<psi>)"
| "decr k l (FEx k' \<phi>) = FEx k' (decr k (if k = k' then Suc l else l) \<phi>)"
| "decr k l (FAll k' \<phi>) = FAll k' (decr k (if k = k' then Suc l else l) \<phi>)"

primrec satisfies_gen :: "('k \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'i \<Rightarrow> ('a, 'k) aformula \<Rightarrow> bool" where
  "satisfies_gen r \<AA> (FBool b) = b"
| "satisfies_gen r \<AA> (FBase a) = (\<AA> \<Turnstile>\<^sub>0 a)"
| "satisfies_gen r \<AA> (FNot \<phi>) = (\<not> satisfies_gen r \<AA> \<phi>)"
| "satisfies_gen r \<AA> (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = (satisfies_gen r \<AA> \<phi>\<^sub>1 \<or> satisfies_gen r \<AA> \<phi>\<^sub>2)"
| "satisfies_gen r \<AA> (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = (satisfies_gen r \<AA> \<phi>\<^sub>1 \<and> satisfies_gen r \<AA> \<phi>\<^sub>2)"
| "satisfies_gen r \<AA> (FEx k \<phi>) = (\<exists>P. r k P (Length \<AA>) \<and> satisfies_gen r (Extend k 0 \<AA> P) \<phi>)"
| "satisfies_gen r \<AA> (FAll k \<phi>) = (\<forall>P. r k P (Length \<AA>) \<longrightarrow> satisfies_gen r (Extend k 0 \<AA> P) \<phi>)"

abbreviation satisfies (infix "\<Turnstile>" 50) where
  "\<AA> \<Turnstile> \<phi> \<equiv> satisfies_gen (\<lambda>_ _ _. True) \<AA> \<phi>"

abbreviation satisfies_bounded (infix "\<Turnstile>\<^sub>b" 50) where
  "\<AA> \<Turnstile>\<^sub>b \<phi> \<equiv> satisfies_gen (\<lambda>_ P n. len P \<le> n) \<AA> \<phi>"

abbreviation sat_vars_gen where
  "sat_vars_gen r K \<AA> \<phi> \<equiv>
    satisfies_gen (\<lambda>k P n. restrict k P \<and> r k P n) \<AA> \<phi> \<and> (\<forall>k \<in> K. \<forall>x \<in> FV \<phi> k. restrict k (x\<^bsup>\<AA>\<^esup>k))"

definition sat where
  "sat \<AA> \<phi> \<equiv> sat_vars_gen (\<lambda>_ _ _. True) UNIV \<AA> \<phi>"

definition sat\<^sub>b where
  "sat\<^sub>b \<AA> \<phi> \<equiv> sat_vars_gen (\<lambda>_ P n. len P \<le> n) UNIV \<AA> \<phi>"

fun RESTR where
  "RESTR (FOr \<phi> \<psi>) = FOr (RESTR \<phi>) (RESTR \<psi>)"
| "RESTR (FAnd \<phi> \<psi>) = FAnd (RESTR \<phi>) (RESTR \<psi>)"
| "RESTR (FNot \<phi>) = FNot (RESTR \<phi>)"
| "RESTR (FEx k \<phi>) = FEx k (FAnd (Restrict k 0) (RESTR \<phi>))"
| "RESTR (FAll k \<phi>) = FAll k (FOr (FNot (Restrict k 0)) (RESTR \<phi>))"
| "RESTR \<phi> = \<phi>"

abbreviation RESTRICT_VARS where
  "RESTRICT_VARS ks V \<phi> \<equiv>
     foldr (%k \<phi>. foldr (\<lambda>x \<phi>. FAnd (Restrict k x) \<phi>) (V k) \<phi>) ks (RESTR \<phi>)"

definition RESTRICT where
  "RESTRICT \<phi> \<equiv> RESTRICT_VARS Enum.enum (sorted_list_of_set o FV \<phi>) \<phi>"

primrec nullable :: "('a, 'k) aformula \<Rightarrow> bool" where
  "nullable (FBool b) = b"
| "nullable (FBase a) = nullable0 a"
| "nullable (FNot \<phi>) = (\<not> nullable \<phi>)"
| "nullable (FOr \<phi> \<psi>) = (nullable \<phi> \<or> nullable \<psi>)"
| "nullable (FAnd \<phi> \<psi>) = (nullable \<phi> \<and> nullable \<psi>)"
| "nullable (FEx k \<phi>) = nullable \<phi>"
| "nullable (FAll k \<phi>) = nullable \<phi>"

fun nFOr :: "('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "nFOr (FBool b1) (FBool b2) = FBool (b1 \<or> b2)"
| "nFOr (FBool b) \<psi> = (if b then FBool True else \<psi>)"
| "nFOr \<phi> (FBool b) = (if b then FBool True else \<phi>)"
| "nFOr (FOr \<phi>1 \<phi>2) \<psi> = nFOr \<phi>1 (nFOr \<phi>2 \<psi>)"
| "nFOr \<phi> (FOr \<psi>1 \<psi>2) =
  (if \<phi> = \<psi>1 then FOr \<psi>1 \<psi>2
  else if \<phi> < \<psi>1 then FOr \<phi> (FOr \<psi>1 \<psi>2)
  else FOr \<psi>1 (nFOr \<phi> \<psi>2))"
| "nFOr \<phi> \<psi> =
  (if \<phi> = \<psi> then \<phi>
  else if \<phi> < \<psi> then FOr \<phi> \<psi>
  else FOr \<psi> \<phi>)"

fun nFAnd :: "('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "nFAnd (FBool b1) (FBool b2) = FBool (b1 \<and> b2)"
| "nFAnd (FBool b) \<psi> = (if b then \<psi> else FBool False)"
| "nFAnd \<phi> (FBool b) = (if b then \<phi> else FBool False)"
| "nFAnd (FAnd \<phi>1 \<phi>2) \<psi> = nFAnd \<phi>1 (nFAnd \<phi>2 \<psi>)"
| "nFAnd \<phi> (FAnd \<psi>1 \<psi>2) =
  (if \<phi> = \<psi>1 then FAnd \<psi>1 \<psi>2
  else if \<phi> < \<psi>1 then FAnd \<phi> (FAnd \<psi>1 \<psi>2)
  else FAnd \<psi>1 (nFAnd \<phi> \<psi>2))"
| "nFAnd \<phi> \<psi> =
  (if \<phi> = \<psi> then \<phi>
  else if \<phi> < \<psi> then FAnd \<phi> \<psi>
  else FAnd \<psi> \<phi>)"

fun nFEx :: "'k \<Rightarrow> ('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "nFEx k (FOr \<phi> \<psi>) = nFOr (nFEx k \<phi>) (nFEx k \<psi>)"
| "nFEx k \<phi> = (if find k 0 \<phi> then FEx k \<phi> else decr k 0 \<phi>)"

fun nFAll where
  "nFAll k (FAnd \<phi> \<psi>) = nFAnd (nFAll k \<phi>) (nFAll k \<psi>)"
| "nFAll k \<phi> = (if find k 0 \<phi> then FAll k \<phi> else decr k 0 \<phi>)"

fun nFNot :: "('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "nFNot (FNot \<phi>) = \<phi>"
| "nFNot (FOr \<phi> \<psi>) = nFAnd (nFNot \<phi>) (nFNot \<psi>)"
| "nFNot (FAnd \<phi> \<psi>) = nFOr (nFNot \<phi>) (nFNot \<psi>)"
| "nFNot (FEx b \<phi>) = nFAll b (nFNot \<phi>)"
| "nFNot (FAll b \<phi>) = nFEx b (nFNot \<phi>)"
| "nFNot (FBool b) = FBool (\<not> b)"
| "nFNot \<phi> = FNot \<phi>"

fun norm where
  "norm (FOr \<phi> \<psi>) = nFOr (norm \<phi>) (norm \<psi>)"
| "norm (FAnd \<phi> \<psi>) = nFAnd (norm \<phi>) (norm \<psi>)"
| "norm (FNot \<phi>) = nFNot (norm \<phi>)"
| "norm (FEx k \<phi>) = nFEx k (norm \<phi>)"
| "norm (FAll k \<phi>) = nFAll k (norm \<phi>)"
| "norm \<phi> = \<phi>"

context
fixes deriv0 :: "'x \<Rightarrow> 'a \<Rightarrow> ('a, 'k) aformula"
begin

primrec deriv :: "'x \<Rightarrow> ('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "deriv x (FBool b) = FBool b"
| "deriv x (FBase a) = deriv0 x a"
| "deriv x (FNot \<phi>) = FNot (deriv x \<phi>)"
| "deriv x (FOr \<phi> \<psi>) = FOr (deriv x \<phi>) (deriv x \<psi>)"
| "deriv x (FAnd \<phi> \<psi>) = FAnd (deriv x \<phi>) (deriv x \<psi>)"
| "deriv x (FEx k \<phi>) = FEx k (FOr (deriv (extend k True x) \<phi>) (deriv (extend k False x) \<phi>))"
| "deriv x (FAll k \<phi>) = FAll k (FAnd (deriv (extend k True x) \<phi>) (deriv (extend k False x) \<phi>))"

end

abbreviation "lderiv \<equiv> deriv lderiv0"
abbreviation "rderiv \<equiv> deriv rderiv0"

lemma fold_deriv_FBool: "fold (deriv d0) xs (FBool b) = FBool b"
  by (induct xs) auto

lemma fold_deriv_FNot:
  "fold (deriv d0) xs (FNot \<phi>) = FNot (fold (deriv d0) xs \<phi>)"
  by (induct xs arbitrary: \<phi>) auto

lemma fold_deriv_FOr:
  "fold (deriv d0) xs (FOr \<phi> \<psi>) = FOr (fold (deriv d0) xs \<phi>) (fold (deriv d0) xs \<psi>)"
  by (induct xs arbitrary: \<phi> \<psi>) auto

lemma fold_deriv_FAnd:
  "fold (deriv d0) xs (FAnd \<phi> \<psi>) = FAnd (fold (deriv d0) xs \<phi>) (fold (deriv d0) xs \<psi>)"
  by (induct xs arbitrary: \<phi> \<psi>) auto

lemma fold_deriv_FEx:
  "{\<langle>fold (deriv d0) xs (FEx k \<phi>)\<rangle> | xs. True} \<subseteq>
    {FEx k \<psi> | \<psi>. nf_ACI \<psi> \<and> disjuncts \<psi> \<subseteq> (\<Union>xs. disjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)}"
proof -
  { fix xs
    have "\<exists>\<psi>. \<langle>fold (deriv d0) xs (FEx k \<phi>)\<rangle> = FEx k \<psi> \<and>
      nf_ACI \<psi> \<and> disjuncts \<psi> \<subseteq> (\<Union>xs. disjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)"
    proof (induct xs arbitrary: \<phi>)
      case (Cons x xs)
      let ?\<phi> = "FOr (deriv d0 (extend k True x) \<phi>) (deriv d0 (extend k False x) \<phi>)"
      from Cons[of ?\<phi>] obtain \<psi> where "\<langle>fold (deriv d0) xs (FEx k ?\<phi>)\<rangle> = FEx k \<psi>"
        "nf_ACI \<psi>" and *: "disjuncts \<psi> \<subseteq> (\<Union>xs. disjuncts \<langle>fold (deriv d0) xs ?\<phi>\<rangle>)" by blast+
      then show ?case
      proof (intro exI conjI)
        have "(\<Union>xs. disjuncts \<langle>fold (deriv d0) xs ?\<phi>\<rangle>) \<subseteq>
          (\<Union>xs. disjuncts \<langle>fold (Formula_Operations.deriv extend d0) xs \<phi>\<rangle>)"
        by (force simp: fold_deriv_FOr nf_ACI_juncts nf_ACI_norm_ACI
          dest: notin_juncts subsetD[OF equalityD1[OF disjuncts_NFOR], rotated -1]
          intro: exI[of _ "extend k b x # xs" for b xs])
        with * show "disjuncts \<psi> \<subseteq> \<dots>" by blast
      qed simp_all
    qed (auto simp: nf_ACI_norm_ACI intro!: exI[of _ "[]"])
  }
  then show ?thesis by blast
qed

lemma fold_deriv_FAll:
  "{\<langle>fold (deriv d0) xs (FAll k \<phi>)\<rangle> | xs. True} \<subseteq>
    {FAll k \<psi> | \<psi>. nf_ACI \<psi> \<and> conjuncts \<psi> \<subseteq> (\<Union>xs. conjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)}"
proof -
  { fix xs
    have "\<exists>\<psi>. \<langle>fold (deriv d0) xs (FAll k \<phi>)\<rangle> = FAll k \<psi> \<and>
      nf_ACI \<psi> \<and> conjuncts \<psi> \<subseteq> (\<Union>xs. conjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)"
    proof (induct xs arbitrary: \<phi>)
      case (Cons x xs)
      let ?\<phi> = "FAnd (deriv d0 (extend k True x) \<phi>) (deriv d0 (extend k False x) \<phi>)"
      from Cons[of ?\<phi>] obtain \<psi> where "\<langle>fold (deriv d0) xs (FAll k ?\<phi>)\<rangle> = FAll k \<psi>"
        "nf_ACI \<psi>" and *: "conjuncts \<psi> \<subseteq> (\<Union>xs. conjuncts \<langle>fold (deriv d0) xs ?\<phi>\<rangle>)" by blast+
      then show ?case
      proof (intro exI conjI)
        have "(\<Union>xs. conjuncts \<langle>fold (deriv d0) xs ?\<phi>\<rangle>) \<subseteq>
          (\<Union>xs. conjuncts \<langle>fold (Formula_Operations.deriv extend d0) xs \<phi>\<rangle>)"
        by (force simp: fold_deriv_FAnd nf_ACI_juncts nf_ACI_norm_ACI
          dest: notin_juncts subsetD[OF equalityD1[OF conjuncts_NFAND], rotated -1]
          intro: exI[of _ "extend k b x # xs" for b xs])
        with * show "conjuncts \<psi> \<subseteq> \<dots>" by blast
      qed simp_all
    qed (auto simp: nf_ACI_norm_ACI intro!: exI[of _ "[]"])
  }
  then show ?thesis by blast
qed

lemma finite_norm_ACI_juncts:
  fixes f :: "('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula"
  shows "finite B \<Longrightarrow> finite {f \<phi> | \<phi>. nf_ACI \<phi> \<and> disjuncts \<phi> \<subseteq> B}"
        "finite B \<Longrightarrow> finite {f \<phi> | \<phi>. nf_ACI \<phi> \<and> conjuncts \<phi> \<subseteq> B}"
  by (elim finite_surj[OF iffD2[OF finite_Pow_iff], of _ _ "f o NFOR o image norm_ACI"]
    finite_surj[OF iffD2[OF finite_Pow_iff], of _ _ "f o NFAND o image norm_ACI"],
    force simp: Pow_def image_Collect intro: arg_cong[OF norm_ACI_NFOR] arg_cong[OF norm_ACI_NFAND])+

end

locale Formula = Formula_Operations
  where TYPEVARS = TYPEVARS
  for TYPEVARS :: "'a :: linorder \<times> 'i \<times> 'k :: {linorder, enum} \<times> 'n \<times> 'x \<times> 'v" +
  (* De Bruijn indices abstractly *)
  assumes SUC_SUC: "SUC k (SUC k' idx) = SUC k' (SUC k idx)"
  and LEQ_0: "LEQ k 0 idx"
  and LESS_SUC: "LEQ k (Suc l) idx = LESS k l idx"
    "k \<noteq> k' \<Longrightarrow> LESS k l (SUC k' idx) = LESS k l idx"

  (* Interpretations *)
  and nvars_Extend: "#\<^sub>V (Extend k i \<AA> P) = SUC k (#\<^sub>V \<AA>)"
  and Length_Extend: "Length (Extend k i \<AA> P) = max (Length \<AA>) (len P)"
  and Length_0_inj: "\<lbrakk>Length \<AA> = 0; Length \<BB> = 0; #\<^sub>V \<AA> = #\<^sub>V \<BB>\<rbrakk> \<Longrightarrow> \<AA> = \<BB>"
  and ex_Length_0: "\<exists>\<AA>. Length \<AA> = 0 \<and> #\<^sub>V \<AA> = idx"
  and Extend_commute_safe: "\<lbrakk>j \<le> i; LEQ k i (#\<^sub>V \<AA>)\<rbrakk> \<Longrightarrow>
      Extend k j (Extend k i \<AA> P) Q = Extend k (Suc i) (Extend k j \<AA> Q) P"
  and Extend_commute_unsafe: "k \<noteq> k' \<Longrightarrow>
      Extend k j (Extend k' i \<AA> P) Q = Extend k' i (Extend k j \<AA> Q) P"
  and assigns_Extend:  "LEQ k i (#\<^sub>V \<AA>) \<Longrightarrow>
    m\<^bsup>Extend k i \<AA> P\<^esup>k' = (if k = k' then (if m = i then P else dec i m\<^bsup>\<AA>\<^esup>k) else m\<^bsup>\<AA>\<^esup>k')"
  and assigns_SNOC_zero: "LESS k m (#\<^sub>V \<AA>) \<Longrightarrow> m\<^bsup>SNOC (zero (#\<^sub>V \<AA>)) \<AA>\<^esup>k = m\<^bsup>\<AA>\<^esup>k"
  and Length_CONS: "Length (CONS x \<AA>) = Length \<AA> + 1"
  and Length_SNOC: "Length (SNOC x \<AA>) = Suc (Length \<AA>)"
  and nvars_CONS: "#\<^sub>V (CONS x \<AA>) = #\<^sub>V \<AA>"
  and nvars_SNOC: "#\<^sub>V (SNOC x \<AA>) = #\<^sub>V \<AA>"
  and Extend_CONS: "#\<^sub>V \<AA> = size x \<Longrightarrow> Extend k 0 (CONS x \<AA>) P =
      CONS (extend k (if eval P 0 then True else False) x) (Extend k 0 \<AA> (downshift P))"
  and Extend_SNOC_cut: "#\<^sub>V \<AA> = size x \<Longrightarrow> len P \<le> Length (SNOC x \<AA>) \<Longrightarrow>
    Extend k 0 (SNOC x \<AA>) P =
    SNOC (extend k (if eval P (Length \<AA>) then True else False) x) (Extend k 0 \<AA> (cut (Length \<AA>) P))"
  and CONS_inj: "size x = #\<^sub>V \<AA> \<Longrightarrow> size y = #\<^sub>V \<AA> \<Longrightarrow> #\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow>
    CONS x \<AA> = CONS y \<BB> \<longleftrightarrow> (x = y \<and> \<AA> = \<BB>)"
  and CONS_surj: "Length \<AA> \<noteq> 0 \<Longrightarrow> #\<^sub>V \<AA> = idx \<Longrightarrow>
    \<exists>x \<BB>. \<AA> = CONS x \<BB> \<and> #\<^sub>V \<BB> = idx \<and> size x = idx"

  (* Alphabet elements *)
  and size_zero: "size (zero idx) = idx"
  and size_extend: "size (extend k b x) = SUC k (size x)"
  and distinct_alphabet: "distinct (alphabet idx)"
  and alphabet_size: "x \<in> set (alphabet idx) \<longleftrightarrow> size x = idx"

  (* Valuations *)
  and downshift_upshift: "downshift (upshift P) = P"
  and downshift_add_zero: "downshift (add 0 P) = downshift P"
  and eval_add: "eval (add n P) n"
  and eval_upshift: "\<not> eval (upshift P) 0"
  and eval_ge_len: "p \<ge> len P \<Longrightarrow> \<not> eval P p"
  and len_cut_le: "len (cut n P) \<le> n"
  and len_cut: "len P \<le> n \<Longrightarrow> cut n P = P"
  and cut_add: "cut n (add m P) = (if m \<ge> n then cut n P else add m (cut n P))"
  and len_add: "len (add m P) = max (Suc m) (len P)"
  and len_upshift: "len (upshift P) = (case len P of 0 \<Rightarrow> 0 | n \<Rightarrow> Suc n)"
  and len_downshift: "len (downshift P) = (case len P of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> n)"

  (* Function extensions for the base cases *)
  and wf0_decr0: "\<lbrakk>wf0 (SUC k idx) a; LESS k l (SUC k idx); \<not> find0 k l a\<rbrakk> \<Longrightarrow> wf0 idx (decr0 k l a)"
  and lformula0_decr0: "lformula0 \<phi> \<Longrightarrow> lformula0 (decr0 k l \<phi>)"
  and Extend_satisfies0: "\<lbrakk>\<not> find0 k i a; LESS k i (SUC k (#\<^sub>V \<AA>)); lformula0 a \<or> len P \<le> Length \<AA>\<rbrakk> \<Longrightarrow>
      Extend k i \<AA> P \<Turnstile>\<^sub>0 a \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>0 decr0 k i a"
  and nullable0_satisfies0: "Length \<AA> = 0 \<Longrightarrow> nullable0 a \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>0 a"
  and satisfies0_eqI: "wf0 (#\<^sub>V \<BB>) a \<Longrightarrow> #\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow> lformula0 a \<Longrightarrow>
    (\<And>m k. LESS k m (#\<^sub>V \<BB>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k) \<Longrightarrow> \<AA> \<Turnstile>\<^sub>0 a \<longleftrightarrow> \<BB> \<Turnstile>\<^sub>0 a"
  and wf_lderiv0: "\<lbrakk>wf0 idx a; lformula0 a\<rbrakk> \<Longrightarrow> wf idx (lderiv0 x a)"
  and lformula_lderiv0: "lformula0 a \<Longrightarrow> lformula (lderiv0 x a)"
  and wf_rderiv0: "wf0 idx a \<Longrightarrow> wf idx (rderiv0 x a)"
  and satisfies_lderiv0:
    "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = size x; lformula0 a\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile> lderiv0 x a \<longleftrightarrow> CONS x \<AA> \<Turnstile>\<^sub>0 a"
  and satisfies_bounded_lderiv0:
    "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = size x; lformula0 a\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b lderiv0 x a \<longleftrightarrow> CONS x \<AA> \<Turnstile>\<^sub>0 a"
  and satisfies_bounded_rderiv0:
    "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = size x\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b rderiv0 x a \<longleftrightarrow> SNOC x \<AA> \<Turnstile>\<^sub>0 a"
  and find0_FV0: "\<lbrakk>wf0 idx a; LESS k l idx\<rbrakk> \<Longrightarrow> find0 k l a \<longleftrightarrow> l \<in> FV0 k a"
  and finite_FV0: "finite (FV0 k a)"
  and wf0_FV0_LESS: "\<lbrakk>wf0 idx a; v \<in> FV0 k a\<rbrakk> \<Longrightarrow> LESS k v idx"
  and restrict_Restrict: "i\<^bsup>\<AA>\<^esup>k = P \<Longrightarrow> restrict k P \<longleftrightarrow> satisfies_gen r \<AA> (Restrict k i)"
  and wf_Restrict: "LESS k i idx \<Longrightarrow> wf idx (Restrict k i)"
  and lformula_Restrict: "lformula (Restrict k i)"
  and finite_lderiv0: "lformula0 a \<Longrightarrow> finite {fold lderiv xs (FBase a) | xs. True}"
  and finite_rderiv0: "finite {fold rderiv xs (FBase a) | xs. True}"

context Formula
begin

lemma satisfies_eqI:
  "\<lbrakk>wf (#\<^sub>V \<AA>) \<phi>; #\<^sub>V \<AA> = #\<^sub>V \<BB>; \<And>m k. LESS k m (#\<^sub>V \<AA>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k; lformula \<phi>\<rbrakk> \<Longrightarrow>
   \<AA> \<Turnstile> \<phi> \<longleftrightarrow> \<BB> \<Turnstile> \<phi>"
proof (induct \<phi> arbitrary: \<AA> \<BB>)
  case (FEx k \<phi>)
  from FEx.prems have "\<And>P. (Extend k 0 \<AA> P \<Turnstile> \<phi>) \<longleftrightarrow> (Extend k 0 \<BB> P \<Turnstile> \<phi>)"
    by (intro FEx.hyps) (auto simp: nvars_Extend assigns_Extend dec_def gr0_conv_Suc LEQ_0 LESS_SUC)
  then show ?case by simp
next
  case (FAll k \<phi>)
  from FAll.prems have "\<And>P. (Extend k 0 \<AA> P \<Turnstile> \<phi>) \<longleftrightarrow> (Extend k 0 \<BB> P \<Turnstile> \<phi>)"
    by (intro FAll.hyps) (auto simp: nvars_Extend assigns_Extend dec_def gr0_conv_Suc LEQ_0 LESS_SUC)
  then show ?case by simp
next
  case (FNot \<phi>)
  from FNot.prems have "(\<AA> \<Turnstile> \<phi>) \<longleftrightarrow> (\<BB> \<Turnstile> \<phi>)" by (intro FNot.hyps) simp_all
  then show ?case by simp
qed (auto dest: satisfies0_eqI)

lemma wf_decr:
  "\<lbrakk>wf (SUC k idx) \<phi>; LEQ k l idx; \<not> find k l \<phi>\<rbrakk> \<Longrightarrow> wf idx (decr k l \<phi>)"
  by (induct \<phi> arbitrary: idx l) (auto simp: wf0_decr0 LESS_SUC SUC_SUC)

lemma lformula_decr:
  "lformula \<phi> \<Longrightarrow> lformula (decr k l \<phi>)"
  by (induct \<phi> arbitrary: l) (auto simp: lformula0_decr0)

lemma Extend_satisfies_decr:
  "\<lbrakk>\<not> find k i \<phi>; LEQ k i (#\<^sub>V \<AA>); lformula \<phi>\<rbrakk> \<Longrightarrow> Extend k i \<AA> P \<Turnstile> \<phi> \<longleftrightarrow> \<AA> \<Turnstile> decr k i \<phi>"
  by (induct \<phi> arbitrary: i \<AA>)
    (auto simp: Extend_commute_unsafe[of _ k 0 _ _ P] Extend_commute_safe
      Extend_satisfies0 nvars_Extend LESS_SUC SUC_SUC split: bool.splits)

lemma LEQ_SUC: "k \<noteq> k' \<Longrightarrow> LEQ k i (SUC k' idx) = LEQ k i idx"
  by (metis LESS_SUC(2) SUC_SUC)

lemma Extend_satisfies_bounded_decr:
  "\<lbrakk>\<not> find k i \<phi>; LEQ k i (#\<^sub>V \<AA>); len P \<le> Length \<AA>\<rbrakk> \<Longrightarrow>
   Extend k i \<AA> P \<Turnstile>\<^sub>b \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b decr k i \<phi>"
proof (induct \<phi> arbitrary: i \<AA> P)
  case (FEx k' \<phi>)
  show ?case
  proof (cases "k = k'")
    case True
    with FEx(2,3,4) show ?thesis
      using FEx(1)[of "Suc i" "Extend k' 0 \<AA> Q" P for Q j]
      by (auto simp: Extend_commute_safe LESS_SUC Length_Extend nvars_Extend max_def)
  next
    case False
    with FEx(2,3,4) show ?thesis
      using FEx(1)[of "i" "Extend k' j \<AA> Q" P for Q j]
      by (auto simp: Extend_commute_unsafe LEQ_SUC Length_Extend nvars_Extend max_def)
  qed
next
  case (FAll k' \<phi>)  show ?case
  proof (cases "k = k'")
    case True
    with FAll(2,3,4) show ?thesis
      using FAll(1)[of "Suc i" "Extend k' 0 \<AA> Q" P for Q j]
      by (auto simp: Extend_commute_safe LESS_SUC Length_Extend nvars_Extend max_def)
  next
    case False
    with FAll(2,3,4) show ?thesis
      using FAll(1)[of "i" "Extend k' j \<AA> Q" P for Q j]
      by (auto simp: Extend_commute_unsafe LEQ_SUC Length_Extend nvars_Extend max_def)
  qed
qed (auto simp: Extend_satisfies0 split: bool.splits)


subsection \<open>Normalization\<close>

lemma wf_nFOr:
  "wf idx (FOr \<phi> \<psi>) \<Longrightarrow> wf idx (nFOr \<phi> \<psi>)"
  by (induct \<phi> \<psi> rule: nFOr.induct) (simp_all add: Let_def)

lemma wf_nFAnd:
  "wf idx (FAnd \<phi> \<psi>) \<Longrightarrow> wf idx (nFAnd \<phi> \<psi>)"
  by (induct \<phi> \<psi> rule: nFAnd.induct) (simp_all add: Let_def)

lemma wf_nFEx:
  "wf idx (FEx b \<phi>) \<Longrightarrow> wf idx (nFEx b \<phi>)"
  by (induct \<phi> arbitrary: idx rule: nFEx.induct)
    (auto simp: SUC_SUC LEQ_0 LESS_SUC(1) gr0_conv_Suc wf_nFOr intro: wf0_decr0 wf_decr)

lemma wf_nFAll:
  "wf idx (FAll b \<phi>) \<Longrightarrow> wf idx (nFAll b \<phi>)"
  by (induct \<phi> arbitrary: idx rule: nFAll.induct)
    (auto simp: SUC_SUC LEQ_0 LESS_SUC(1) gr0_conv_Suc wf_nFAnd intro: wf0_decr0 wf_decr)

lemma wf_nFNot:
  "wf idx (FNot \<phi>) \<Longrightarrow> wf idx (nFNot \<phi>)"
  by (induct \<phi> arbitrary: idx rule: nFNot.induct) (auto simp: wf_nFOr wf_nFAnd wf_nFEx wf_nFAll)

lemma wf_norm: "wf idx \<phi> \<Longrightarrow> wf idx (norm \<phi>)"
  by (induct \<phi> arbitrary: idx) (simp_all add: wf_nFOr wf_nFAnd wf_nFNot wf_nFEx wf_nFAll)

lemma lformula_nFOr:
  "lformula (FOr \<phi> \<psi>) \<Longrightarrow> lformula (nFOr \<phi> \<psi>)"
  by (induct \<phi> \<psi> rule: nFOr.induct) (simp_all add: Let_def)

lemma lformula_nFAnd:
  "lformula (FAnd \<phi> \<psi>) \<Longrightarrow> lformula (nFAnd \<phi> \<psi>)"
  by (induct \<phi> \<psi> rule: nFAnd.induct) (simp_all add: Let_def)

lemma lformula_nFEx:
  "lformula (FEx b \<phi>) \<Longrightarrow> lformula (nFEx b \<phi>)"
  by (induct \<phi> rule: nFEx.induct)
    (auto simp: lformula_nFOr lformula0_decr0 lformula_decr)

lemma lformula_nFAll:
  "lformula (FAll b \<phi>) \<Longrightarrow> lformula (nFAll b \<phi>)"
  by (induct \<phi> rule: nFAll.induct)
    (auto simp: lformula_nFAnd lformula0_decr0 lformula_decr)

lemma lformula_nFNot:
  "lformula (FNot \<phi>) \<Longrightarrow> lformula (nFNot \<phi>)"
  by (induct \<phi> rule: nFNot.induct) (auto simp: lformula_nFOr lformula_nFAnd lformula_nFEx lformula_nFAll)

lemma lformula_norm: "lformula \<phi> \<Longrightarrow> lformula (norm \<phi>)"
  by (induct \<phi>) (simp_all add: lformula_nFOr lformula_nFAnd lformula_nFNot
    lformula_nFEx lformula_nFAll)

lemma satisfies_nFOr:
  "\<AA> \<Turnstile> nFOr \<phi> \<psi> \<longleftrightarrow> \<AA> \<Turnstile> FOr \<phi> \<psi>"
  by (induct \<phi> \<psi> arbitrary: \<AA> rule: nFOr.induct) auto

lemma satisfies_nFAnd:
  "\<AA> \<Turnstile> nFAnd \<phi> \<psi> \<longleftrightarrow> \<AA> \<Turnstile> FAnd \<phi> \<psi>"
  by (induct \<phi> \<psi> arbitrary: \<AA> rule: nFAnd.induct) auto

lemma satisfies_nFEx: "lformula \<phi> \<Longrightarrow> \<AA> \<Turnstile> nFEx b \<phi> \<longleftrightarrow> \<AA> \<Turnstile> FEx b \<phi>"
  by (induct \<phi> rule: nFEx.induct)
    (auto simp add: satisfies_nFOr Extend_satisfies_decr
      LEQ_0 LESS_SUC(1) nvars_Extend Extend_satisfies0 Extend_commute_safe Extend_commute_unsafe)

lemma satisfies_nFAll: "lformula \<phi> \<Longrightarrow> \<AA> \<Turnstile> nFAll b \<phi> \<longleftrightarrow> \<AA> \<Turnstile> FAll b \<phi>"
  by (induct \<phi> rule: nFAll.induct)
    (auto simp add: satisfies_nFAnd Extend_satisfies_decr
      Extend_satisfies0 LEQ_0 LESS_SUC(1) nvars_Extend Extend_commute_safe Extend_commute_unsafe)

lemma satisfies_nFNot:
  "lformula \<phi> \<Longrightarrow> \<AA> \<Turnstile> nFNot \<phi> \<longleftrightarrow> \<AA> \<Turnstile> FNot \<phi>"
  by (induct \<phi> arbitrary: \<AA>)
    (simp_all add: satisfies_nFOr satisfies_nFAnd satisfies_nFEx satisfies_nFAll
    lformula_nFNot)

lemma satisfies_norm: "lformula \<phi> \<Longrightarrow> \<AA> \<Turnstile> norm \<phi> \<longleftrightarrow> \<AA> \<Turnstile> \<phi>"
  using satisfies_nFOr satisfies_nFAnd satisfies_nFNot satisfies_nFEx satisfies_nFAll
  by (induct \<phi> arbitrary: \<AA>) (simp_all add: lformula_norm)

lemma satisfies_bounded_nFOr:
  "\<AA> \<Turnstile>\<^sub>b nFOr \<phi> \<psi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b FOr \<phi> \<psi>"
  by (induct \<phi> \<psi> arbitrary: \<AA> rule: nFOr.induct) auto

lemma satisfies_bounded_nFAnd:
  "\<AA> \<Turnstile>\<^sub>b nFAnd \<phi> \<psi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b FAnd \<phi> \<psi>"
  by (induct \<phi> \<psi> arbitrary: \<AA> rule: nFAnd.induct) auto

lemma len_cut_0: "len (cut 0 P) = 0"
  by (metis le_0_eq len_cut_le)

lemma satisfies_bounded_nFEx: "\<AA> \<Turnstile>\<^sub>b nFEx b \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b FEx b \<phi>"
  by (induct \<phi> rule: nFEx.induct)
    (auto 4 4 simp add: satisfies_bounded_nFOr Extend_satisfies_bounded_decr
      LEQ_0 LESS_SUC(1) nvars_Extend Length_Extend len_cut_0
      Extend_satisfies0 Extend_commute_safe Extend_commute_unsafe cong: ex_cong split: bool.splits
      intro: exI[where P = "\<lambda>x. P x \<and> Q x" for P Q, OF conjI[rotated]] exI[of _ "cut 0 P" for P])

lemma satisfies_bounded_nFAll: "\<AA> \<Turnstile>\<^sub>b nFAll b \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b FAll b \<phi>"
  by (induct \<phi> rule: nFAll.induct)
    (auto 4 4 simp add: satisfies_bounded_nFAnd Extend_satisfies_bounded_decr
      LEQ_0 LESS_SUC(1) nvars_Extend Length_Extend len_cut_0
      Extend_satisfies0 Extend_commute_safe Extend_commute_unsafe cong: split: bool.splits
      intro: exI[where P = "\<lambda>x. P x \<and> Q x" for P Q, OF conjI[rotated]] dest: spec[of _ "cut 0 P" for P])

lemma satisfies_bounded_nFNot:
  "\<AA> \<Turnstile>\<^sub>b nFNot \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b FNot \<phi>"
  by (induct \<phi> arbitrary: \<AA>)
    (auto simp: satisfies_bounded_nFOr satisfies_bounded_nFAnd satisfies_bounded_nFEx satisfies_bounded_nFAll)

lemma satisfies_bounded_norm: "\<AA> \<Turnstile>\<^sub>b norm \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b \<phi>"
  by (induct \<phi> arbitrary: \<AA>)
    (simp_all add: satisfies_bounded_nFOr satisfies_bounded_nFAnd
      satisfies_bounded_nFNot satisfies_bounded_nFEx satisfies_bounded_nFAll)


subsection \<open>Derivatives of Formulas\<close>

lemma wf_lderiv:
  "\<lbrakk>wf idx \<phi>; lformula \<phi>\<rbrakk> \<Longrightarrow> wf idx (lderiv x \<phi>)"
  by (induct \<phi> arbitrary: x idx) (auto simp: wf_lderiv0)

lemma lformula_lderiv:
  "lformula \<phi> \<Longrightarrow> lformula (lderiv x \<phi>)"
  by (induct \<phi> arbitrary: x) (auto simp: lformula_lderiv0)

lemma wf_rderiv:
  "wf idx \<phi> \<Longrightarrow> wf idx (rderiv x \<phi>)"
  by (induct \<phi> arbitrary: x idx) (auto simp: wf_rderiv0)

theorem satisfies_lderiv:
  "\<lbrakk>wf (#\<^sub>V \<AA>) \<phi>; #\<^sub>V \<AA> = size x; lformula \<phi>\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile> lderiv x \<phi> \<longleftrightarrow> CONS x \<AA> \<Turnstile> \<phi>"
proof (induct \<phi> arbitrary: x \<AA>)
  case (FEx k \<phi>)
  from FEx.prems FEx.hyps[of "Extend k 0 \<AA> P" "extend k b x" for P b] show ?case
    by (auto simp: nvars_Extend size_extend Extend_CONS
      downshift_upshift eval_add eval_upshift downshift_add_zero
      intro: exI[of _ "add 0 (upshift P)" for P] exI[of _ "upshift P" for P])
next
  case (FAll k \<phi>)
  from FAll.prems FAll.hyps[of "Extend k 0 \<AA> P" "extend k b x" for P b] show ?case
    by (auto simp: nvars_Extend size_extend Extend_CONS
      downshift_upshift eval_add eval_upshift downshift_add_zero
      dest: spec[of _ "add 0 (upshift P)" for P] spec[of _ "upshift P" for P])
qed (simp_all add: satisfies_lderiv0 split: bool.splits)

theorem satisfies_bounded_lderiv:
  "\<lbrakk>wf (#\<^sub>V \<AA>) \<phi>; #\<^sub>V \<AA> = size x; lformula \<phi>\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b lderiv x \<phi> \<longleftrightarrow> CONS x \<AA> \<Turnstile>\<^sub>b \<phi>"
proof (induct \<phi> arbitrary: x \<AA>)
  case (FEx k \<phi>)
  note [simp] = nvars_Extend size_extend Extend_CONS Length_CONS
    downshift_upshift eval_add eval_upshift downshift_add_zero len_add len_upshift len_downshift
  from FEx.prems FEx.hyps[of "Extend k 0 \<AA> P" "extend k b x" for P b] show ?case
    by auto (force intro: exI[of _ "add 0 (upshift P)" for P] exI[of _ "upshift P" for P] split: nat.splits)+
next
  case (FAll k \<phi>)
  note [simp] = nvars_Extend size_extend Extend_CONS Length_CONS
    downshift_upshift eval_add eval_upshift downshift_add_zero len_add len_upshift len_downshift
  from FAll.prems FAll.hyps[of "Extend k 0 \<AA> P" "extend k b x" for P b] show ?case
    by auto (force dest: spec[of _ "add 0 (upshift P)" for P] spec[of _ "upshift P" for P] split: nat.splits)+
qed (simp_all add: satisfies_bounded_lderiv0 split: bool.splits)

theorem satisfies_bounded_rderiv:
  "\<lbrakk>wf (#\<^sub>V \<AA>) \<phi>; #\<^sub>V \<AA> = size x\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b rderiv x \<phi> \<longleftrightarrow> SNOC x \<AA> \<Turnstile>\<^sub>b \<phi>"
proof (induct \<phi> arbitrary: x \<AA>)
  case (FEx k \<phi>)
  from FEx.prems FEx.hyps[of "Extend k 0 \<AA> P" "extend k b x" for P b] show ?case
    by (auto simp: nvars_Extend size_extend Extend_SNOC_cut len_cut_le eval_ge_len 
      eval_add cut_add Length_SNOC len_add len_cut le_Suc_eq max_def
      intro: exI[of _ "cut (Length \<AA>) P" for P] exI[of _ "add (Length \<AA>) P" for P] split: if_splits)
next
  case (FAll k \<phi>)
  from FAll.prems FAll.hyps[of "Extend k 0 \<AA> P" "extend k b x" for P b] show ?case
    by (auto simp: nvars_Extend size_extend Extend_SNOC_cut len_cut_le eval_ge_len 
      eval_add cut_add Length_SNOC len_add len_cut le_Suc_eq max_def
      dest: spec[of _ "cut (Length \<AA>) P" for P] spec[of _ "add (Length \<AA>) P" for P] split: if_splits)
qed (simp_all add: satisfies_bounded_rderiv0 split: bool.splits)

lemma wf_norm_rderivs: "wf idx \<phi> \<Longrightarrow> wf idx (((norm \<circ> rderiv (zero idx)) ^^ k) \<phi>)"
  by (induct k) (auto simp: wf_norm wf_rderiv)

subsection \<open>Finiteness of Derivatives Modulo ACI\<close>

lemma finite_fold_deriv:
  assumes "(d0 = lderiv0 \<and> lformula \<phi>) \<or> d0 = rderiv0"
  shows "finite {\<langle>fold (deriv d0) xs \<phi>\<rangle> | xs. True}"
using assms proof (induct \<phi>)
  case (FBase a) then show ?case
    by (auto intro:
      finite_subset[OF _ finite_imageI[OF finite_lderiv0]]
      finite_subset[OF _ finite_imageI[OF finite_rderiv0]])
next
  case (FNot \<phi>)
  then show ?case
    by (auto simp: fold_deriv_FNot intro!: finite_surj[OF FNot(1)])
next
  case (FOr \<phi> \<psi>)
  then show ?case
    by (auto simp: fold_deriv_FOr intro!: finite_surj[OF finite_cartesian_product[OF FOr(1,2)]])
next
  case (FAnd \<phi> \<psi>)
  then show ?case
    by (auto simp: fold_deriv_FAnd intro!: finite_surj[OF finite_cartesian_product[OF FAnd(1,2)]])
next
  case (FEx k \<phi>)
  then have "finite (\<Union> (disjuncts ` {\<langle>fold (deriv d0) xs \<phi>\<rangle> | xs . True}))" by auto
  then have "finite (\<Union>xs. disjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)" by (rule finite_subset[rotated]) auto
  then have "finite {FEx k \<psi> | \<psi>. nf_ACI \<psi> \<and> disjuncts \<psi> \<subseteq> (\<Union>xs. disjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)}"
    by (rule finite_norm_ACI_juncts)
  then show ?case by (rule finite_subset[OF fold_deriv_FEx])
next
  case (FAll k \<phi>)
  then have "finite (\<Union> (conjuncts ` {\<langle>fold (deriv d0) xs \<phi>\<rangle> | xs . True}))" by auto
  then have "finite (\<Union>xs. conjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)" by (rule finite_subset[rotated]) auto
  then have "finite {FAll k \<psi> | \<psi>. nf_ACI \<psi> \<and> conjuncts \<psi> \<subseteq> (\<Union>xs. conjuncts \<langle>fold (deriv d0) xs \<phi>\<rangle>)}"
    by (rule finite_norm_ACI_juncts)
  then show ?case  by (rule finite_subset[OF fold_deriv_FAll])
qed (simp add: fold_deriv_FBool)

lemma lformula_nFOR: "lformula (nFOR \<phi>s) = (\<forall>\<phi> \<in> set \<phi>s. lformula \<phi>)"
  by (induct \<phi>s rule: nFOR.induct) auto

lemma lformula_nFAND: "lformula (nFAND \<phi>s) = (\<forall>\<phi> \<in> set \<phi>s. lformula \<phi>)"
  by (induct \<phi>s rule: nFAND.induct) auto

lemma lformula_NFOR: "finite \<Phi> \<Longrightarrow> lformula (NFOR \<Phi>) = (\<forall>\<phi> \<in> \<Phi>. lformula \<phi>)"
  unfolding NFOR_def o_apply lformula_nFOR by simp

lemma lformula_NFAND: "finite \<Phi> \<Longrightarrow> lformula (NFAND \<Phi>) = (\<forall>\<phi> \<in> \<Phi>. lformula \<phi>)"
  unfolding NFAND_def o_apply lformula_nFAND by simp

lemma lformula_disjuncts: "(\<forall>\<psi> \<in> disjuncts \<phi>. lformula \<psi>) = lformula \<phi>"
  by (induct \<phi> rule: disjuncts.induct) fastforce+

lemma lformula_conjuncts: "(\<forall>\<psi> \<in> conjuncts \<phi>. lformula \<psi>) = lformula \<phi>"
  by (induct \<phi> rule: conjuncts.induct) fastforce+

lemma lformula_norm_ACI: "lformula \<langle>\<phi>\<rangle> = lformula \<phi>"
  by (induct \<phi>) (simp_all add: ball_Un
    lformula_NFOR lformula_disjuncts lformula_NFAND lformula_conjuncts)

theorem
  finite_fold_lderiv: "lformula \<phi> \<Longrightarrow> finite {\<langle>fold lderiv xs \<langle>\<phi>\<rangle>\<rangle> | xs. True}" and
  finite_fold_rderiv: "finite {\<langle>fold rderiv xs \<langle>\<phi>\<rangle>\<rangle> | xs. True}"
  by (subst (asm) lformula_norm_ACI[symmetric]) (blast intro: nf_ACI_norm_ACI finite_fold_deriv)+

lemma wf_nFOR: "wf idx (nFOR \<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. wf idx \<phi>)"
  by (induct rule: nFOR.induct) auto

lemma wf_nFAND: "wf idx (nFAND \<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. wf idx \<phi>)"
  by (induct rule: nFAND.induct) auto

lemma wf_NFOR: "finite \<Phi> \<Longrightarrow> wf idx (NFOR \<Phi>) \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. wf idx \<phi>)"
  unfolding NFOR_def o_apply by (auto simp: wf_nFOR)

lemma wf_NFAND: "finite \<Phi> \<Longrightarrow> wf idx (NFAND \<Phi>) \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. wf idx \<phi>)"
  unfolding NFAND_def o_apply by (auto simp: wf_nFAND)

lemma satisfies_bounded_nFOR: "\<AA> \<Turnstile>\<^sub>b nFOR \<phi>s \<longleftrightarrow> (\<exists>\<phi> \<in> set \<phi>s. \<AA> \<Turnstile>\<^sub>b \<phi>)"
  by (induct rule: nFOR.induct) (auto simp: satisfies_bounded_nFOr)

lemma satisfies_bounded_nFAND: "\<AA> \<Turnstile>\<^sub>b nFAND \<phi>s \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. \<AA> \<Turnstile>\<^sub>b \<phi>)"
  by (induct rule: nFAND.induct) (auto simp: satisfies_bounded_nFAnd)

lemma satisfies_bounded_NFOR: "finite \<Phi> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b NFOR \<Phi> \<longleftrightarrow> (\<exists>\<phi> \<in> \<Phi>. \<AA> \<Turnstile>\<^sub>b \<phi>)"
  unfolding NFOR_def o_apply by (auto simp: satisfies_bounded_nFOR)

lemma satisfies_bounded_NFAND: "finite \<Phi> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b NFAND \<Phi> \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. \<AA> \<Turnstile>\<^sub>b \<phi>)"
  unfolding NFAND_def o_apply by (auto simp: satisfies_bounded_nFAND)

lemma wf_juncts:
  "wf idx \<phi> \<longleftrightarrow> (\<forall>\<psi> \<in> disjuncts \<phi>. wf idx \<psi>)"
  "wf idx \<phi> \<longleftrightarrow> (\<forall>\<psi> \<in> conjuncts \<phi>. wf idx \<psi>)"
  by (induct \<phi>) auto

lemma wf_norm_ACI: "wf idx \<langle>\<phi>\<rangle> = wf idx \<phi>"
  by (induct \<phi> arbitrary: idx) (auto simp: wf_NFOR wf_NFAND ball_Un wf_juncts[symmetric])

lemma satisfies_bounded_disjuncts:
  "\<AA> \<Turnstile>\<^sub>b \<phi> \<longleftrightarrow> (\<exists>\<psi> \<in> disjuncts \<phi>. \<AA> \<Turnstile>\<^sub>b \<psi>)"
  by (induct \<phi> arbitrary: \<AA>) auto

lemma satisfies_bounded_conjuncts:
  "\<AA> \<Turnstile>\<^sub>b \<phi> \<longleftrightarrow> (\<forall>\<psi> \<in> conjuncts \<phi>. \<AA> \<Turnstile>\<^sub>b \<psi>)"
  by (induct \<phi> arbitrary: \<AA>) auto

lemma satisfies_bounded_norm_ACI: "\<AA> \<Turnstile>\<^sub>b \<langle>\<phi>\<rangle> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b \<phi>"
  by (rule sym, induct \<phi> arbitrary: \<AA>)
    (auto simp: satisfies_bounded_NFOR satisfies_bounded_NFAND
      intro: iffD2[OF satisfies_bounded_disjuncts] iffD2[OF satisfies_bounded_conjuncts]
      dest: iffD1[OF satisfies_bounded_disjuncts] iffD1[OF satisfies_bounded_conjuncts])

lemma nvars_SNOCs: "#\<^sub>V ((SNOC x^^k) \<AA>) = #\<^sub>V \<AA>"
  by (induct k) (auto simp: nvars_SNOC)

lemma wf_fold_rderiv: "wf idx \<phi> \<Longrightarrow> wf idx (fold rderiv (replicate k x) \<phi>)"
  by (induct k arbitrary: \<phi>) (auto simp: wf_rderiv)

lemma satisfies_bounded_fold_rderiv:
  "\<lbrakk>wf idx \<phi>; #\<^sub>V \<AA> = idx; size x = idx\<rbrakk> \<Longrightarrow>
     \<AA> \<Turnstile>\<^sub>b fold rderiv (replicate k x) \<phi> \<longleftrightarrow> (SNOC x^^k) \<AA> \<Turnstile>\<^sub>b \<phi>"
  by (induct k arbitrary: \<AA> \<phi>) (auto simp: satisfies_bounded_rderiv wf_rderiv nvars_SNOCs)


subsection \<open>Emptiness Check\<close>

context
  fixes b :: bool
  and idx :: 'n
  and \<psi> :: "('a, 'k) aformula"
begin

abbreviation "fut_test \<equiv> \<lambda>(\<phi>, \<Phi>). \<phi> \<notin> set \<Phi>"
abbreviation "fut_step \<equiv> \<lambda>(\<phi>, \<Phi>). (norm (rderiv (zero idx) \<phi>), \<phi> # \<Phi>)"
definition "fut_derivs k \<phi> \<equiv> ((norm o rderiv (zero idx))^^k) \<phi>"

lemma fut_derivs_Suc[simp]: "norm (rderiv (zero idx) (fut_derivs k \<phi>)) = fut_derivs (Suc k) \<phi>"
  unfolding fut_derivs_def by auto

definition "fut_invariant =
  (\<lambda>(\<phi>, \<Phi>). wf idx \<phi> \<and> (\<forall>\<phi> \<in> set \<Phi>. wf idx \<phi>) \<and>
    (\<exists>k. \<phi> = fut_derivs k \<psi> \<and> \<Phi> = map (\<lambda>i. fut_derivs i \<psi>) (rev [0 ..< k])))"
definition "fut_spec \<phi>\<Phi> \<equiv> (\<forall>\<phi> \<in> set (snd \<phi>\<Phi>). wf idx \<phi>) \<and>
  (\<forall>\<AA>. #\<^sub>V \<AA> = idx \<longrightarrow>
    (if b then (\<exists>k. (SNOC (zero idx) ^^ k) \<AA> \<Turnstile>\<^sub>b \<psi>) \<longleftrightarrow> (\<exists>\<phi> \<in> set (snd \<phi>\<Phi>). \<AA> \<Turnstile>\<^sub>b \<phi>)
    else (\<forall>k. (SNOC (zero idx) ^^ k) \<AA> \<Turnstile>\<^sub>b \<psi>) \<longleftrightarrow> (\<forall>\<phi> \<in> set (snd \<phi>\<Phi>). \<AA> \<Turnstile>\<^sub>b \<phi>)))"

definition "fut_default =
  (\<psi>, sorted_list_of_set {\<langle>fold rderiv (replicate k (zero idx)) \<langle>\<psi>\<rangle>\<rangle> | k. True})"

lemma finite_fold_rderiv_zeros: "finite {\<langle>fold rderiv (replicate k (zero idx)) \<langle>\<psi>\<rangle>\<rangle> | k. True}"
  by (rule finite_subset[OF _ finite_fold_rderiv[of \<psi>]]) blast

definition fut :: "('a, 'k) aformula" where
  "fut = (if b then nFOR else nFAND) (snd (while_default fut_default fut_test fut_step (\<psi>, [])))"

context
  assumes wf: "wf idx \<psi>"
begin 

lemma wf_fut_derivs:
  "wf idx (fut_derivs k \<psi>)"
  by (induct k) (auto simp: wf_norm wf_rderiv wf fut_derivs_def)

lemma satisfies_bounded_fut_derivs:
  "#\<^sub>V \<AA> = idx \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b fut_derivs k \<psi> \<longleftrightarrow> (SNOC (zero idx)^^k) \<AA> \<Turnstile>\<^sub>b \<psi>"
  by (induct k arbitrary: \<AA>) (auto simp: fut_derivs_def satisfies_bounded_rderiv satisfies_bounded_norm
    wf_norm_rderivs size_zero nvars_SNOC funpow_swap1[of "SNOC x" for x] wf)

lemma fut_init: "fut_invariant (\<psi>, [])"
  unfolding fut_invariant_def by (auto simp: fut_derivs_def wf)

lemma fut_spec_default: "fut_spec fut_default"
  using satisfies_bounded_fold_rderiv[OF iffD2[OF wf_norm_ACI wf] sym size_zero] 
  unfolding fut_spec_def fut_default_def snd_conv
    set_sorted_list_of_set[OF finite_fold_rderiv_zeros]
  by (auto simp: satisfies_bounded_norm_ACI wf_fold_rderiv wf wf_norm_ACI simp del: fold_replicate)

lemma fut_invariant: "fut_invariant \<phi>\<Phi> \<Longrightarrow> fut_test \<phi>\<Phi> \<Longrightarrow> fut_invariant (fut_step \<phi>\<Phi>)"
  by (cases \<phi>\<Phi>) (auto simp: fut_invariant_def wf_norm wf_rderiv split: if_splits)

lemma fut_terminate: "fut_invariant \<phi>\<Phi> \<Longrightarrow> \<not> fut_test \<phi>\<Phi> \<Longrightarrow> fut_spec \<phi>\<Phi>"
proof (induct \<phi>\<Phi>, unfold prod.case not_not)
  fix \<phi> \<Phi> assume "fut_invariant (\<phi>, \<Phi>)" "\<phi> \<in> set \<Phi>"
  then obtain i k where "i < k" and \<phi>_def: "\<phi> = fut_derivs i \<psi>"
    and \<Phi>_def: "\<Phi> = map (\<lambda>i. fut_derivs i \<psi>) (rev [0..<k])"
    and *: "fut_derivs k \<psi> = fut_derivs i \<psi>" unfolding fut_invariant_def by auto
  have "set \<Phi> = {fut_derivs k \<psi> | k . True}"
  unfolding \<Phi>_def set_map set_rev set_upt proof safe
    fix j
    show "fut_derivs j \<psi> \<in> (\<lambda>i. fut_derivs i \<psi>) ` {0..<k}"
    proof (cases "j < k")
      case False
      with * \<open>i < k\<close> have "fut_derivs j \<psi> = fut_derivs ((j - i) mod (k - i) + i) \<psi>"
        unfolding fut_derivs_def by (auto intro: funpow_cycle_offset)
      then show ?thesis using \<open>i < k\<close> \<open>\<not> j < k\<close>
        by (metis image_eqI atLeastLessThan_iff le0 less_diff_conv mod_less_divisor zero_less_diff)
    qed simp
  qed (blast intro: *)
  then show "fut_spec (\<phi>, \<Phi>)"
    unfolding fut_spec_def using satisfies_bounded_fut_derivs by (auto simp: wf_fut_derivs)
qed

lemma fut_spec_while_default:
  "fut_spec (while_default fut_default fut_test fut_step (\<psi>, []))"
  using fut_invariant fut_terminate fut_init fut_spec_default by (rule while_default_rule)

lemma wf_fut: "wf idx fut"
  using fut_spec_while_default unfolding fut_def fut_spec_def by (auto simp: wf_nFOR wf_nFAND)

lemma satisfies_bounded_fut:
  assumes "#\<^sub>V \<AA> = idx"
  shows "\<AA> \<Turnstile>\<^sub>b fut \<longleftrightarrow>
    (if b then (\<exists>k. (SNOC (zero idx) ^^ k) \<AA> \<Turnstile>\<^sub>b \<psi>) else (\<forall>k. (SNOC (zero idx) ^^ k) \<AA> \<Turnstile>\<^sub>b \<psi>))"
  using fut_spec_while_default assms unfolding fut_def fut_spec_def
  by (auto simp: satisfies_bounded_nFOR satisfies_bounded_nFAND)

end

end

fun finalize :: "'n \<Rightarrow> ('a, 'k) aformula \<Rightarrow> ('a, 'k) aformula" where
  "finalize idx (FEx k \<phi>) = fut True idx (nFEx k (finalize (SUC k idx) \<phi>))"
| "finalize idx (FAll k \<phi>) = fut False idx (nFAll k (finalize (SUC k idx) \<phi>))"
| "finalize idx (FOr \<phi> \<psi>) = FOr (finalize idx \<phi>) (finalize idx \<psi>)"
| "finalize idx (FAnd \<phi> \<psi>) = FAnd (finalize idx \<phi>) (finalize idx \<psi>)"
| "finalize idx (FNot \<phi>) = FNot (finalize idx \<phi>)"
| "finalize idx \<phi> = \<phi>"

definition final :: "'n \<Rightarrow> ('a, 'k) aformula \<Rightarrow> bool" where
  "final idx = nullable o finalize idx"

lemma wf_finalize: "wf idx \<phi> \<Longrightarrow> wf idx (finalize idx \<phi>)"
  by (induct \<phi> arbitrary: idx) (auto simp: wf_fut wf_nFEx wf_nFAll)

lemma Length_SNOCs: "Length ((SNOC x ^^ i) \<AA>) = Length \<AA> + i"
  by (induct i arbitrary: \<AA>) (auto simp: Length_SNOC)

lemma assigns_SNOCs_zero:
  "\<lbrakk>LESS k m (#\<^sub>V \<AA>); #\<^sub>V \<AA> = idx\<rbrakk>  \<Longrightarrow> m\<^bsup>(SNOC (zero idx) ^^ i) \<AA>\<^esup>k = m\<^bsup>\<AA>\<^esup>k"
  by (induct i arbitrary: \<AA>) (auto simp: assigns_SNOC_zero nvars_SNOC funpow_swap1)

lemma Extend_SNOCs_zero_satisfies: "\<lbrakk>wf (SUC k idx) \<phi>; #\<^sub>V \<AA> = idx; lformula \<phi>\<rbrakk> \<Longrightarrow>
  Extend k 0 ((SNOC (zero (#\<^sub>V \<AA>)) ^^ i) \<AA>) P \<Turnstile> \<phi> \<longleftrightarrow> Extend k 0 \<AA> P \<Turnstile> \<phi>"
  by (rule satisfies_eqI)
   (auto simp: nvars_Extend nvars_SNOCs assigns_Extend assigns_SNOCs_zero LEQ_0 LESS_SUC
     dec_def gr0_conv_Suc)

lemma finalize_satisfies: "\<lbrakk>wf idx \<phi>; #\<^sub>V \<AA> = idx; lformula \<phi>\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b finalize idx \<phi> \<longleftrightarrow> \<AA> \<Turnstile> \<phi>"
  by (induct \<phi> arbitrary: idx \<AA>)
    (force simp add: wf_nFEx wf_nFAll wf_finalize Length_SNOCs nvars_Extend nvars_SNOCs
      satisfies_bounded_fut satisfies_bounded_nFEx satisfies_bounded_nFAll Extend_SNOCs_zero_satisfies
      intro: le_add2)+

lemma Extend_empty_satisfies0:
  "\<lbrakk>Length \<AA> = 0; len P = 0\<rbrakk> \<Longrightarrow> Extend k i \<AA> P \<Turnstile>\<^sub>0 a \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>0 a"
  by (intro box_equals[OF _ nullable0_satisfies0 nullable0_satisfies0])
    (auto simp: nvars_Extend Length_Extend)

lemma Extend_empty_satisfies_bounded:
  "\<lbrakk>Length \<AA> = 0; len P = 0\<rbrakk> \<Longrightarrow> Extend k 0 \<AA> P \<Turnstile>\<^sub>b \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b \<phi>"
  by (induct \<phi> arbitrary: k \<AA> P)
    (auto simp: Extend_empty_satisfies0 Length_Extend split: bool.splits)

lemma nullable_satisfies_bounded: "Length \<AA> = 0 \<Longrightarrow> nullable \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b \<phi>"
  by (induct \<phi>) (auto simp: nullable0_satisfies0 Extend_empty_satisfies_bounded len_cut_0
    intro: exI[of _ "cut 0 P" for P])

lemma final_satisfies:
  "\<lbrakk>wf idx \<phi> \<and> lformula \<phi>; Length \<AA> = 0; #\<^sub>V \<AA> = idx\<rbrakk> \<Longrightarrow> final idx \<phi> = (\<AA> \<Turnstile> \<phi>)"
  by (simp only: final_def o_apply nullable_satisfies_bounded finalize_satisfies)

subsection \<open>Restrictions\<close>

lemma satisfies_gen_restrict_RESTR:
  "satisfies_gen (\<lambda>k P n. restrict k P \<and> r k P n) \<AA> \<phi> \<longleftrightarrow> satisfies_gen r \<AA> (RESTR \<phi>)"
  by (induct \<phi> arbitrary: \<AA>) (auto simp: restrict_Restrict[symmetric] assigns_Extend LEQ_0)

lemma finite_FV: "finite (FV \<phi> k)"
  by (induct \<phi>) (auto simp: finite_FV0)

lemma satisfies_gen_restrict:
  "satisfies_gen r \<AA> \<phi> \<and> (\<forall>x\<in>set V. restrict k (x\<^bsup>\<AA>\<^esup>k)) \<longleftrightarrow>
   satisfies_gen r \<AA> (foldr (\<lambda>x. FAnd (Restrict k x)) V \<phi>)"
  by (induct V arbitrary: \<phi>) (auto simp: restrict_Restrict[symmetric])

lemma sat_vars_RESTRICT_VARS:
  fixes \<phi>
  defines "vs \<equiv> sorted_list_of_set o FV \<phi>"
  assumes "\<forall>k \<in> set ks. finite (FV \<phi> k)"
  shows "sat_vars_gen r (set ks) \<AA> \<phi> \<longleftrightarrow> satisfies_gen r \<AA> (RESTRICT_VARS ks vs \<phi>)"
using assms proof (induct ks)
  case (Cons k ks)
  with satisfies_gen_restrict[of r \<AA> "(RESTRICT_VARS ks vs \<phi>)" "vs k"] show ?case by auto
qed (simp add: satisfies_gen_restrict_RESTR)

lemma sat_RESTRICT: "sat \<AA> \<phi> \<longleftrightarrow> \<AA> \<Turnstile> RESTRICT \<phi>"
  unfolding sat_def RESTRICT_def using sat_vars_RESTRICT_VARS[of Enum.enum, symmetric]
  by (auto simp: finite_FV enum_UNIV)

lemma sat\<^sub>b_RESTRICT: "sat\<^sub>b \<AA> \<phi> \<longleftrightarrow> \<AA> \<Turnstile>\<^sub>b RESTRICT \<phi>"
  unfolding sat\<^sub>b_def RESTRICT_def using sat_vars_RESTRICT_VARS[of Enum.enum, symmetric]
  by (auto simp: finite_FV enum_UNIV)

lemma wf_RESTR: "wf idx \<phi> \<Longrightarrow> wf idx (RESTR \<phi>)"
  by (induct \<phi> arbitrary: idx) (auto simp: wf_Restrict LESS_SUC LEQ_0)

lemma wf_RESTRICT_VARS: "\<lbrakk>wf idx \<phi>; \<forall>k \<in> set ks. \<forall>v \<in> set (vs k). LESS k v idx\<rbrakk> \<Longrightarrow>
  wf idx (RESTRICT_VARS ks vs \<phi>)"
proof (induct ks)
  case (Cons k ks)
  moreover
  { fix vs \<phi> assume "\<forall>v \<in> set vs. LESS k v idx" "wf idx \<phi>"
    then have "wf idx (foldr (\<lambda>x. FAnd (Restrict k x)) vs \<phi>)"
      by (induct vs arbitrary: \<phi>) (auto simp: wf_Restrict)
  }
  ultimately show ?case by auto
qed (simp add: wf_RESTR)

lemma wf_FV_LESS: "\<lbrakk>wf idx \<phi>; v \<in> FV \<phi> k\<rbrakk> \<Longrightarrow> LESS k v idx"
  by (induct \<phi> arbitrary: idx v)
    (force simp: wf0_FV0_LESS LESS_SUC split: if_splits)+

lemma wf_RESTRICT: "wf idx \<phi> \<Longrightarrow> wf idx (RESTRICT \<phi>)"
  unfolding RESTRICT_def by (rule wf_RESTRICT_VARS) (auto simp: list_all_iff wf_FV_LESS finite_FV)

lemma lformula_RESTR: "lformula \<phi> \<Longrightarrow> lformula (RESTR \<phi>)"
  by (induct \<phi>) (auto simp: lformula_Restrict)

lemma lformula_RESTRICT_VARS: "lformula \<phi> \<Longrightarrow> lformula (RESTRICT_VARS ks vs \<phi>)"
proof (induct ks)
  case (Cons k ks)
  moreover
  { fix vs \<phi> assume "lformula \<phi>"
    then have "lformula (foldr (\<lambda>x. FAnd (Restrict k x)) vs \<phi>)"
      by (induct vs arbitrary: \<phi>) (auto simp: lformula_Restrict)
  }
  ultimately show ?case by auto
qed (simp add: lformula_RESTR)

lemma lformula_RESTRICT: "lformula \<phi> \<Longrightarrow> lformula (RESTRICT \<phi>)"
  unfolding RESTRICT_def by (rule lformula_RESTRICT_VARS)

lemma ex_fold_CONS: "\<exists>xs \<BB>. \<AA> = fold CONS xs \<BB> \<and> Length \<BB> = 0 \<and> Length \<AA> = length xs \<and>
   #\<^sub>V \<BB> = #\<^sub>V \<AA> \<and> (\<forall>x \<in> set xs. size x = #\<^sub>V \<AA>)"
proof (induct "Length \<AA>" arbitrary: \<AA>)
  case (Suc m)
  from Suc(2) CONS_surj obtain a \<BB> where "\<AA> = CONS a \<BB>" "#\<^sub>V \<BB> = #\<^sub>V \<AA>" "size a = #\<^sub>V \<AA>" by force
  moreover with Suc(2) have "Length \<BB> = m" by (simp add: Length_CONS)
  with Suc(1)[of \<BB>] obtain xs \<CC> where "\<BB> = fold CONS xs \<CC>" "Length \<CC> = 0" "Length \<BB> = length xs"
    "#\<^sub>V \<CC> = #\<^sub>V \<BB>" "\<forall>x \<in> set xs. size x = #\<^sub>V \<BB>" by blast
  ultimately show ?case by (intro exI[of _ "xs @ [a]"] exI[of _ \<CC>]) (auto simp: Length_CONS)
qed simp

primcorec L where
  "L idx I = Lang (\<exists>\<AA>. Length \<AA> = 0 \<and> #\<^sub>V \<AA> = idx \<and> \<AA> \<in> I)
    (\<lambda>a. if size a = idx then L idx {\<BB>. CONS a \<BB> \<in> I} else Zero)"

lemma L_empty: "L idx {} = Zero"
  by coinduction auto

lemma L_alt: "L idx I =
    to_language {xs. \<exists>\<AA> \<in> I. \<exists>\<BB>. \<AA> = fold CONS (rev xs) \<BB> \<and> Length \<BB> = 0 \<and>
      #\<^sub>V \<BB> = idx \<and> (\<forall>x \<in> set xs. size x = idx)}"
  by (coinduction arbitrary: I)
    (auto 0 4 simp: L_empty intro: exI[of _ "{}"] arg_cong[of _ _ to_language])

definition "lang idx \<phi> = L idx {\<AA>. \<AA> \<Turnstile> \<phi> \<and> #\<^sub>V \<AA> = idx}"
definition "lang\<^sub>b idx \<phi> = L idx {\<AA>. \<AA> \<Turnstile>\<^sub>b \<phi> \<and> #\<^sub>V \<AA> = idx}"
definition "language idx \<phi> = L idx {\<AA>. sat \<AA> \<phi> \<and> #\<^sub>V \<AA> = idx}"
definition "language\<^sub>b idx \<phi> = L idx {\<AA>. sat\<^sub>b \<AA> \<phi> \<and> #\<^sub>V \<AA> = idx}"

lemma "lformula \<phi> \<Longrightarrow> lang n (norm \<phi>) = lang n \<phi>"
  unfolding lang_def using satisfies_norm by auto

lemma in_language_Zero[simp]: "\<not> in_language Zero w"
  by (induct w) auto

lemma in_language_L_size: "in_language (L idx I) w \<Longrightarrow> x \<in> set w \<Longrightarrow> size x = idx"
  by (induct w arbitrary: x I) (auto split: if_splits)

end

sublocale Formula <
  bounded: DA "alphabet idx" "\<lambda>\<phi>. norm (RESTRICT \<phi>)" "\<lambda>a \<phi>. norm (lderiv a \<phi>)" "nullable"
     "\<lambda>\<phi>. wf idx \<phi> \<and> lformula \<phi>" "lang\<^sub>b idx"
     "\<lambda>\<phi>. wf idx \<phi> \<and> lformula \<phi>" "language\<^sub>b idx" for idx
  using ex_Length_0[of idx]
  by unfold_locales
    (auto simp: lformula_norm lformula_lderiv distinct_alphabet alphabet_size wf_norm wf_lderiv
    lang\<^sub>b_def language\<^sub>b_def nullable_satisfies_bounded wf_RESTRICT lformula_RESTRICT sat\<^sub>b_RESTRICT
    satisfies_bounded_norm in_language_L_size satisfies_bounded_lderiv nvars_CONS
    dest: Length_0_inj intro: arg_cong[of _ _ "L (size _)"])

sublocale Formula <
  unbounded?: DA "alphabet idx" "\<lambda>\<phi>. norm (RESTRICT \<phi>)" "\<lambda>a \<phi>. norm (lderiv a \<phi>)" "final idx"
     "\<lambda>\<phi>. wf idx \<phi> \<and> lformula \<phi>" "lang idx"
     "\<lambda>\<phi>. wf idx \<phi> \<and> lformula \<phi>" "language idx" for idx
  using ex_Length_0[of idx]
  by unfold_locales
    (auto simp: lformula_norm lformula_lderiv distinct_alphabet alphabet_size wf_norm wf_lderiv
    lang_def language_def final_satisfies wf_RESTRICT lformula_RESTRICT sat_RESTRICT
    satisfies_norm in_language_L_size satisfies_lderiv nvars_CONS
    dest: Length_0_inj intro: arg_cong[of _ _ "L (size _)"])

lemma (in Formula) check_eqv_soundness:
  "\<lbrakk>#\<^sub>V \<AA> = idx; check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> sat \<AA> \<phi> \<longleftrightarrow> sat \<AA> \<psi>"
  using ex_fold_CONS[of \<AA>]
  by (auto simp: language_def L_alt set_eq_iff
    dest!: soundness[unfolded rel_language_eq] injD[OF bij_is_inj[OF to_language_bij]])
    (metis Length_0_inj rev_rev_ident set_rev)+

lemma (in Formula) bounded_check_eqv_soundness:
  "\<lbrakk>#\<^sub>V \<AA> = idx; bounded.check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> sat\<^sub>b \<AA> \<phi> \<longleftrightarrow> sat\<^sub>b \<AA> \<psi>"
  using ex_fold_CONS[of \<AA>]
  by (auto simp: language\<^sub>b_def L_alt set_eq_iff
    dest!: bounded.soundness[unfolded rel_language_eq] injD[OF bij_is_inj[OF to_language_bij]])
    (metis Length_0_inj rev_rev_ident set_rev)+

end
