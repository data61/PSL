(*  Title:       Terminated coinductive list
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

section \<open>Terminated coinductive lists and their operations\<close>

theory TLList imports
  Coinductive_List
begin

text \<open>
  Terminated coinductive lists \<open>('a, 'b) tllist\<close> are the codatatype defined by the construtors
  \<open>TNil\<close> of type \<open>'b \<Rightarrow> ('a, 'b) tllist\<close> and
  \<open>TCons\<close> of type \<open>'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist\<close>.
\<close>

subsection \<open>Auxiliary lemmas\<close>

lemma split_fst: "R (fst p) = (\<forall>x y. p = (x, y) \<longrightarrow> R x)"
by(cases p) simp

lemma split_fst_asm: "R (fst p) \<longleftrightarrow> (\<not> (\<exists>x y. p = (x, y) \<and> \<not> R x))"
by(cases p) simp

subsection \<open>Type definition\<close>

consts terminal0 :: "'a"

codatatype (tset: 'a, 'b) tllist =
    TNil (terminal : 'b)
  | TCons (thd : 'a) (ttl : "('a, 'b) tllist")
for
  map: tmap
  rel: tllist_all2
where
  "thd (TNil _) = undefined"
| "ttl (TNil b) = TNil b"
| "terminal (TCons _ xs) = terminal0 xs"

overloading
  terminal0 == "terminal0::('a, 'b) tllist \<Rightarrow> 'b"
begin

partial_function (tailrec) terminal0 
where "terminal0 xs = (if is_TNil xs then case_tllist id undefined xs else terminal0 (ttl xs))"

end

lemma terminal0_terminal [simp]: "terminal0 = terminal"
apply(rule ext)
apply(subst terminal0.simps)
apply(case_tac x)
apply(simp_all add: terminal_def)
done

lemmas terminal_TNil [code, nitpick_simp] = tllist.sel(1)

lemma terminal_TCons [simp, code, nitpick_simp]: "terminal (TCons x xs) = terminal xs"
by simp

declare tllist.sel(2) [simp del]

primcorec unfold_tllist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('c, 'b) tllist" where
  "p a \<Longrightarrow> unfold_tllist p g1 g21 g22 a = TNil (g1 a)" |
  "_ \<Longrightarrow> unfold_tllist p g1 g21 g22 a =
     TCons (g21 a) (unfold_tllist p g1 g21 g22 (g22 a))"

declare
  unfold_tllist.ctr(1) [simp]
  tllist.corec(1) [simp]

subsection \<open>Code generator setup\<close>

text \<open>Test quickcheck setup\<close>

lemma "xs = TNil x"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "TCons x xs = TCons x xs"
quickcheck[narrowing, expect=no_counterexample]
oops

text \<open>More lemmas about generated constants\<close>

lemma ttl_unfold_tllist:
  "ttl (unfold_tllist IS_TNIL TNIL THD TTL a) = 
  (if IS_TNIL a then TNil (TNIL a) else unfold_tllist IS_TNIL TNIL THD TTL (TTL a))"
by(simp)

lemma is_TNil_ttl [simp]: "is_TNil xs \<Longrightarrow> is_TNil (ttl xs)"
by(cases xs) simp_all

lemma terminal_ttl [simp]: "terminal (ttl xs) = terminal xs"
by(cases xs) simp_all

lemma unfold_tllist_eq_TNil [simp]:
  "unfold_tllist IS_TNIL TNIL THD TTL a = TNil b \<longleftrightarrow> IS_TNIL a \<and> b = TNIL a"
by(auto simp add: unfold_tllist.code)

lemma TNil_eq_unfold_tllist [simp]:
  "TNil b = unfold_tllist IS_TNIL TNIL THD TTL a \<longleftrightarrow> IS_TNIL a \<and> b = TNIL a"
by(auto simp add: unfold_tllist.code)

lemma tmap_is_TNil: "is_TNil xs \<Longrightarrow> tmap f g xs = TNil (g (terminal xs))"
by(clarsimp simp add: is_TNil_def)

declare tllist.map_sel(2)[simp]

lemma ttl_tmap [simp]: "ttl (tmap f g xs) = tmap f g (ttl xs)"
by(cases xs) simp_all

lemma tmap_eq_TNil_conv:
  "tmap f g xs = TNil y \<longleftrightarrow> (\<exists>y'. xs = TNil y' \<and> g y' = y)"
by(cases xs) simp_all

lemma TNil_eq_tmap_conv:
  "TNil y = tmap f g xs \<longleftrightarrow> (\<exists>y'. xs = TNil y' \<and> g y' = y)"
by(cases xs) auto

declare tllist.set_sel(1)[simp]

lemma tset_ttl: "tset (ttl xs) \<subseteq> tset xs"
by(cases xs) auto

lemma in_tset_ttlD: "x \<in> tset (ttl xs) \<Longrightarrow> x \<in> tset xs"
using tset_ttl[of xs] by auto

theorem tllist_set_induct[consumes 1, case_names find step]:
  assumes "x \<in> tset xs" and "\<And>xs. \<not> is_TNil xs \<Longrightarrow> P (thd xs) xs"
  and "\<And>xs y. \<lbrakk>\<not> is_TNil xs; y \<in> tset (ttl xs); P y (ttl xs)\<rbrakk> \<Longrightarrow> P y xs"
  shows "P x xs"
using assms by(induct)(fastforce simp del: tllist.disc(2) iff: tllist.disc(2), auto)

theorem set2_tllist_induct[consumes 1, case_names find step]:
  assumes "x \<in> set2_tllist xs" and "\<And>xs. is_TNil xs \<Longrightarrow> P (terminal xs) xs"
  and "\<And>xs y. \<lbrakk>\<not> is_TNil xs; y \<in> set2_tllist (ttl xs); P y (ttl xs)\<rbrakk> \<Longrightarrow> P y xs"
  shows "P x xs"
using assms by(induct)(fastforce simp del: tllist.disc(1) iff: tllist.disc(1), auto)


subsection \<open>Connection with @{typ "'a llist"}\<close>

context fixes b :: 'b begin
primcorec tllist_of_llist :: "'a llist \<Rightarrow> ('a, 'b) tllist" where
  "tllist_of_llist xs = (case xs of LNil \<Rightarrow> TNil b | LCons x xs' \<Rightarrow> TCons x (tllist_of_llist xs'))"
end

primcorec llist_of_tllist :: "('a, 'b) tllist \<Rightarrow> 'a llist"
where "llist_of_tllist xs = (case xs of TNil _ \<Rightarrow> LNil | TCons x xs' \<Rightarrow> LCons x (llist_of_tllist xs'))"

simps_of_case tllist_of_llist_simps [simp, code, nitpick_simp]: tllist_of_llist.code

lemmas tllist_of_llist_LNil = tllist_of_llist_simps(1)
  and tllist_of_llist_LCons = tllist_of_llist_simps(2)

lemma terminal_tllist_of_llist_lnull [simp]:
  "lnull xs \<Longrightarrow> terminal (tllist_of_llist b xs) = b"
unfolding lnull_def by simp

declare tllist_of_llist.sel(1)[simp del]

lemma lhd_LNil: "lhd LNil = undefined"
by(simp add: lhd_def)

lemma thd_TNil: "thd (TNil b) = undefined"
by(simp add: thd_def)

lemma thd_tllist_of_llist [simp]: "thd (tllist_of_llist b xs) = lhd xs"
by(cases xs)(simp_all add: thd_TNil lhd_LNil)

lemma ttl_tllist_of_llist [simp]: "ttl (tllist_of_llist b xs) = tllist_of_llist b (ltl xs)"
by(cases xs) simp_all

lemma llist_of_tllist_eq_LNil:
  "llist_of_tllist xs = LNil \<longleftrightarrow> is_TNil xs"
using llist_of_tllist.disc_iff(1) unfolding lnull_def .

simps_of_case llist_of_tllist_simps [simp, code, nitpick_simp]: llist_of_tllist.code

lemmas llist_of_tllist_TNil = llist_of_tllist_simps(1)
  and llist_of_tllist_TCons = llist_of_tllist_simps(2)

declare llist_of_tllist.sel [simp del]

lemma lhd_llist_of_tllist [simp]: "\<not> is_TNil xs \<Longrightarrow> lhd (llist_of_tllist xs) = thd xs"
by(cases xs) simp_all

lemma ltl_llist_of_tllist [simp]:
  "ltl (llist_of_tllist xs) = llist_of_tllist (ttl xs)"
by(cases xs) simp_all

lemma tllist_of_llist_cong [cong]:
  assumes "xs = xs'" "lfinite xs' \<Longrightarrow> b = b'"
  shows "tllist_of_llist b xs = tllist_of_llist b' xs'"
proof(unfold \<open>xs = xs'\<close>)
  from assms have "lfinite xs' \<longrightarrow> b = b'" by simp
  thus "tllist_of_llist b xs' = tllist_of_llist b' xs'"
    by(coinduction arbitrary: xs') auto
qed

lemma llist_of_tllist_inverse [simp]: 
  "tllist_of_llist (terminal b) (llist_of_tllist b) = b"
by(coinduction arbitrary: b) simp_all

lemma tllist_of_llist_eq [simp]: "tllist_of_llist b' xs = TNil b \<longleftrightarrow> b = b' \<and> xs = LNil"
by(cases xs) auto

lemma TNil_eq_tllist_of_llist [simp]: "TNil b = tllist_of_llist b' xs \<longleftrightarrow> b = b' \<and> xs = LNil"
by(cases xs) auto

lemma tllist_of_llist_inject [simp]:
  "tllist_of_llist b xs = tllist_of_llist c ys \<longleftrightarrow> xs = ys \<and> (lfinite ys \<longrightarrow> b = c)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI impI)
  assume ?rhs
  thus ?lhs by(auto intro: tllist_of_llist_cong)
next
  assume ?lhs
  thus "xs = ys"
    by(coinduction arbitrary: xs ys)(auto simp add: lnull_def neq_LNil_conv)
  assume "lfinite ys"
  thus "b = c" using \<open>?lhs\<close>
    unfolding \<open>xs = ys\<close> by(induct) simp_all
qed

lemma tllist_of_llist_inverse [simp]:
  "llist_of_tllist (tllist_of_llist b xs) = xs"
by(coinduction arbitrary: xs) auto

definition cr_tllist :: "('a llist \<times> 'b) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> bool"
  where "cr_tllist \<equiv> (\<lambda>(xs, b) ys. tllist_of_llist b xs = ys)"

lemma Quotient_tllist:
  "Quotient (\<lambda>(xs, a) (ys, b). xs = ys \<and> (lfinite ys \<longrightarrow> a = b))
     (\<lambda>(xs, a). tllist_of_llist a xs) (\<lambda>ys. (llist_of_tllist ys, terminal ys)) cr_tllist"
unfolding Quotient_alt_def cr_tllist_def by(auto intro: tllist_of_llist_cong)

lemma reflp_tllist: "reflp (\<lambda>(xs, a) (ys, b). xs = ys \<and> (lfinite ys \<longrightarrow> a = b))"
by(simp add: reflp_def)

setup_lifting Quotient_tllist reflp_tllist

context includes lifting_syntax
begin

lemma TNil_transfer [transfer_rule]:
  "(B ===> pcr_tllist A B) (Pair LNil) TNil"
by(force simp add: pcr_tllist_def cr_tllist_def)

lemma TCons_transfer [transfer_rule]:
  "(A ===> pcr_tllist A B ===> pcr_tllist A B) (apfst \<circ> LCons) TCons"
by(force simp add: pcr_tllist_def llist_all2_LCons1 cr_tllist_def)

lemma tmap_tllist_of_llist:
  "tmap f g (tllist_of_llist b xs) = tllist_of_llist (g b) (lmap f xs)"
by(coinduction arbitrary: xs)(auto simp add: tmap_is_TNil)

lemma tmap_transfer [transfer_rule]:
  "((=) ===> (=) ===> pcr_tllist (=) (=) ===> pcr_tllist (=) (=)) (map_prod \<circ> lmap) tmap"
by(force simp add: cr_tllist_def tllist.pcr_cr_eq tmap_tllist_of_llist)

lemma lset_llist_of_tllist [simp]:
  "lset (llist_of_tllist xs) = tset xs" (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs"
  thus "x \<in> ?rhs"
    by(induct "llist_of_tllist xs" arbitrary: xs rule: llist_set_induct)(auto simp: tllist.set_sel(2))
next
  fix x
  assume "x \<in> ?rhs"
  thus "x \<in> ?lhs"
  proof(induct rule: tllist_set_induct)
    case (find xs)
    thus ?case by(cases xs) auto
  next
    case step
    thus ?case
      by(auto simp add: ltl_llist_of_tllist[symmetric] simp del: ltl_llist_of_tllist dest: in_lset_ltlD)
  qed
qed

lemma tset_tllist_of_llist [simp]:
  "tset (tllist_of_llist b xs) = lset xs"
by(simp add: lset_llist_of_tllist[symmetric] del: lset_llist_of_tllist)

lemma tset_transfer [transfer_rule]:
  "(pcr_tllist (=) (=) ===> (=)) (lset \<circ> fst) tset"
by(auto simp add: cr_tllist_def tllist.pcr_cr_eq)

lemma is_TNil_transfer [transfer_rule]:
  "(pcr_tllist (=) (=) ===> (=)) (\<lambda>(xs, b). lnull xs) is_TNil"
by(auto simp add: tllist.pcr_cr_eq cr_tllist_def)

lemma thd_transfer [transfer_rule]:
  "(pcr_tllist (=) (=) ===> (=)) (lhd \<circ> fst) thd"
by(auto simp add: cr_tllist_def tllist.pcr_cr_eq)

lemma ttl_transfer [transfer_rule]:
  "(pcr_tllist A B ===> pcr_tllist A B) (apfst ltl) ttl"
by(force simp add: pcr_tllist_def cr_tllist_def intro: llist_all2_ltlI)

lemma llist_of_tllist_transfer [transfer_rule]:
  "(pcr_tllist (=) B ===> (=)) fst llist_of_tllist"
by(auto simp add: pcr_tllist_def cr_tllist_def llist.rel_eq)

lemma tllist_of_llist_transfer [transfer_rule]:
  "((=) ===> (=) ===> pcr_tllist (=) (=)) (\<lambda>b xs. (xs, b)) tllist_of_llist"
by(auto simp add: tllist.pcr_cr_eq cr_tllist_def)

lemma terminal_tllist_of_llist_lfinite [simp]:
  "lfinite xs \<Longrightarrow> terminal (tllist_of_llist b xs) = b"
by(induct rule: lfinite.induct) simp_all

lemma set2_tllist_tllist_of_llist [simp]:
  "set2_tllist (tllist_of_llist b xs) = (if lfinite xs then {b} else {})"
proof(cases "lfinite xs")
  case True
  thus ?thesis by(induct) auto
next
  case False
  { fix x
    assume "x \<in> set2_tllist (tllist_of_llist b xs)"
    hence False using False
      by(induct "tllist_of_llist b xs" arbitrary: xs rule: set2_tllist_induct) fastforce+ }
  thus ?thesis using False by auto
qed

lemma set2_tllist_transfer [transfer_rule]:
  "(pcr_tllist A B ===> rel_set B) (\<lambda>(xs, b). if lfinite xs then {b} else {}) set2_tllist"
by(auto 4 4 simp add: pcr_tllist_def cr_tllist_def dest: llist_all2_lfiniteD intro: rel_setI)

lemma tllist_all2_transfer [transfer_rule]:
  "((=) ===> (=) ===> pcr_tllist (=) (=) ===> pcr_tllist (=) (=) ===> (=))
     (\<lambda>P Q (xs, b) (ys, b'). llist_all2 P xs ys \<and> (lfinite xs \<longrightarrow> Q b b')) tllist_all2"
unfolding tllist.pcr_cr_eq
apply(rule rel_funI)+
apply(clarsimp simp add: cr_tllist_def llist_all2_def tllist_all2_def)
apply(safe elim!: GrpE)
   apply simp_all
   apply(rule_tac b="tllist_of_llist (b, ba) bb" in relcomppI)
    apply(auto intro!: GrpI simp add: tmap_tllist_of_llist)[2]
  apply(rule_tac b="tllist_of_llist (b, ba) bb" in relcomppI)
   apply(auto simp add: tmap_tllist_of_llist intro!: GrpI split: if_split_asm)[2]
 apply(rule_tac b="llist_of_tllist bb" in relcomppI)
apply(auto intro!: GrpI)
apply(transfer, auto intro: GrpI split: if_split_asm)+
done

subsection \<open>Library function definitions\<close>

text \<open>
  We lift the constants from @{typ "'a llist"} to @{typ "('a, 'b) tllist"} using the lifting package.
  This way, many results are transferred easily.
\<close>

lift_definition tappend :: "('a, 'b) tllist \<Rightarrow> ('b \<Rightarrow> ('a, 'c) tllist) \<Rightarrow> ('a, 'c) tllist"
is "\<lambda>(xs, b) f. apfst (lappend xs) (f b)"
by(auto simp add: split_def lappend_inf)

lift_definition lappendt :: "'a llist \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "apfst \<circ> lappend"
by(simp add: split_def)

lift_definition tfilter :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "\<lambda>b P (xs, b'). (lfilter P xs, if lfinite xs then b' else b)"
by(simp add: split_beta)

lift_definition tconcat :: "'b \<Rightarrow> ('a llist, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "\<lambda>b (xss, b'). (lconcat xss, if lfinite xss then b' else b)"
by(simp add: split_beta)

lift_definition tnth :: "('a, 'b) tllist \<Rightarrow> nat \<Rightarrow> 'a"
is "lnth \<circ> fst" by(auto)

lift_definition tlength :: "('a, 'b) tllist \<Rightarrow> enat"
is "llength \<circ> fst" by auto

lift_definition tdropn :: "nat \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "apfst \<circ> ldropn" by auto

abbreviation tfinite :: "('a, 'b) tllist \<Rightarrow> bool"
where "tfinite xs \<equiv> lfinite (llist_of_tllist xs)"

subsection \<open>@{term "tfinite"}\<close>

lemma tfinite_induct [consumes 1, case_names TNil TCons]:
  assumes "tfinite xs"
  and "\<And>y. P (TNil y)"
  and "\<And>x xs. \<lbrakk>tfinite xs; P xs\<rbrakk> \<Longrightarrow> P (TCons x xs)"
  shows "P xs"
using assms
by transfer (clarsimp, erule lfinite.induct)

lemma is_TNil_tfinite [simp]: "is_TNil xs \<Longrightarrow> tfinite xs"
by transfer clarsimp

subsection \<open>The terminal element @{term "terminal"}\<close>

lemma terminal_tinfinite:
  assumes "\<not> tfinite xs"
  shows "terminal xs = undefined"
unfolding terminal0_terminal[symmetric]
using assms
apply(rule contrapos_np)
by(induct xs rule: terminal0.raw_induct[rotated 1, OF refl, consumes 1])(auto split: tllist.split_asm) 

lemma terminal_tllist_of_llist:
  "terminal (tllist_of_llist y xs) = (if lfinite xs then y else undefined)"
by(simp add: terminal_tinfinite)

lemma terminal_transfer [transfer_rule]:
  "(pcr_tllist A (=) ===> (=)) (\<lambda>(xs, b). if lfinite xs then b else undefined) terminal"
by(force simp add: cr_tllist_def pcr_tllist_def terminal_tllist_of_llist dest: llist_all2_lfiniteD)

lemma terminal_tmap [simp]: "tfinite xs \<Longrightarrow> terminal (tmap f g xs) = g (terminal xs)"
by(induct rule: tfinite_induct) simp_all

subsection \<open>@{term "tmap"}\<close>

lemma tmap_eq_TCons_conv:
  "tmap f g xs = TCons y ys \<longleftrightarrow>
  (\<exists>z zs. xs = TCons z zs \<and> f z = y \<and> tmap f g zs = ys)"
by(cases xs) simp_all

lemma TCons_eq_tmap_conv:
  "TCons y ys = tmap f g xs \<longleftrightarrow>
  (\<exists>z zs. xs = TCons z zs \<and> f z = y \<and> tmap f g zs = ys)"
by(cases xs) auto

subsection \<open>Appending two terminated lazy lists @{term "tappend" }\<close>

lemma tappend_TNil [simp, code, nitpick_simp]:
  "tappend (TNil b) f = f b"
by transfer auto

lemma tappend_TCons [simp, code, nitpick_simp]:
  "tappend (TCons a tr) f = TCons a (tappend tr f)"
by transfer(auto simp add: apfst_def map_prod_def split: prod.splits)

lemma tappend_TNil2 [simp]:
  "tappend xs TNil = xs"
by transfer auto

lemma tappend_assoc: "tappend (tappend xs f) g = tappend xs (\<lambda>b. tappend (f b) g)"
by transfer(auto simp add: split_beta lappend_assoc)

lemma terminal_tappend:
  "terminal (tappend xs f) = (if tfinite xs then terminal (f (terminal xs)) else terminal xs)"
by transfer(auto simp add: split_beta)

lemma tfinite_tappend: "tfinite (tappend xs f) \<longleftrightarrow> tfinite xs \<and> tfinite (f (terminal xs))"
by transfer auto

lift_definition tcast :: "('a, 'b) tllist \<Rightarrow> ('a, 'c) tllist"
is "\<lambda>(xs, a). (xs, undefined)" by clarsimp

lemma tappend_inf: "\<not> tfinite xs \<Longrightarrow> tappend xs f = tcast xs"
by(transfer)(auto simp add: apfst_def map_prod_def split_beta lappend_inf)

text \<open>@{term tappend} is the monadic bind on @{typ "('a, 'b) tllist"}\<close>

lemmas tllist_monad = tappend_TNil tappend_TNil2 tappend_assoc

subsection \<open>Appending a terminated lazy list to a lazy list @{term "lappendt"}\<close>

lemma lappendt_LNil [simp, code, nitpick_simp]: "lappendt LNil tr = tr"
by transfer auto

lemma lappendt_LCons [simp, code, nitpick_simp]:
  "lappendt (LCons x xs) tr = TCons x (lappendt xs tr)"
by transfer auto

lemma terminal_lappendt_lfinite [simp]:
  "lfinite xs \<Longrightarrow> terminal (lappendt xs ys) = terminal ys"
by transfer auto

lemma tllist_of_llist_eq_lappendt_conv:
  "tllist_of_llist a xs = lappendt ys zs \<longleftrightarrow> 
  (\<exists>xs' a'. xs = lappend ys xs' \<and> zs = tllist_of_llist a' xs' \<and> (lfinite ys \<longrightarrow> a = a'))"
by transfer auto

lemma tset_lappendt_lfinite [simp]:
  "lfinite xs \<Longrightarrow> tset (lappendt xs ys) = lset xs \<union> tset ys"
by transfer auto

subsection \<open>Filtering terminated lazy lists @{term tfilter}\<close>

lemma tfilter_TNil [simp]:
  "tfilter b' P (TNil b) = TNil b"
by transfer auto

lemma tfilter_TCons [simp]:
  "tfilter b P (TCons a tr) = (if P a then TCons a (tfilter b P tr) else tfilter b P tr)"
by transfer auto

lemma is_TNil_tfilter[simp]:
  "is_TNil (tfilter y P xs) \<longleftrightarrow> (\<forall>x \<in> tset xs. \<not> P x)"
by transfer auto

lemma tfilter_empty_conv:
  "tfilter y P xs = TNil y' \<longleftrightarrow> (\<forall>x \<in> tset xs. \<not> P x) \<and> (if tfinite xs then terminal xs = y' else y = y')"
by transfer(clarsimp simp add: lfilter_eq_LNil)

lemma tfilter_eq_TConsD:
  "tfilter a P ys = TCons x xs \<Longrightarrow>
   \<exists>us vs. ys = lappendt us (TCons x vs) \<and> lfinite us \<and> (\<forall>u\<in>lset us. \<not> P u) \<and> P x \<and> xs = tfilter a P vs"
by transfer(fastforce dest: lfilter_eq_LConsD[OF sym])

text \<open>Use a version of @{term "tfilter"} for code generation that does not evaluate the first argument\<close>

definition tfilter' :: "(unit \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
where [simp, code del]: "tfilter' b = tfilter (b ())"

lemma tfilter_code [code, code_unfold]:
  "tfilter = (\<lambda>b. tfilter' (\<lambda>_. b))" 
by simp

lemma tfilter'_code [code]:
  "tfilter' b' P (TNil b) = TNil b"
  "tfilter' b' P (TCons a tr) = (if P a then TCons a (tfilter' b' P tr) else tfilter' b' P tr)"
by simp_all

end

hide_const (open) tfilter'

subsection \<open>Concatenating a terminated lazy list of lazy lists @{term tconcat}\<close>

lemma tconcat_TNil [simp]: "tconcat b (TNil b') = TNil b'"
by transfer auto

lemma tconcat_TCons [simp]: "tconcat b (TCons a tr) = lappendt a (tconcat b tr)"
by transfer auto

text \<open>Use a version of @{term "tconcat"} for code generation that does not evaluate the first argument\<close>

definition tconcat' :: "(unit \<Rightarrow> 'b) \<Rightarrow> ('a llist, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
where [simp, code del]: "tconcat' b = tconcat (b ())"

lemma tconcat_code [code, code_unfold]: "tconcat = (\<lambda>b. tconcat' (\<lambda>_. b))"
by simp

lemma tconcat'_code [code]:
  "tconcat' b (TNil b') = TNil b'"
  "tconcat' b (TCons a tr) = lappendt a (tconcat' b tr)"
by simp_all

hide_const (open) tconcat'

subsection \<open>@{term tllist_all2}\<close>

lemmas tllist_all2_TNil = tllist.rel_inject(1)
lemmas tllist_all2_TCons = tllist.rel_inject(2)

lemma tllist_all2_TNil1: "tllist_all2 P Q (TNil b) ts \<longleftrightarrow> (\<exists>b'. ts = TNil b' \<and> Q b b')"
by transfer auto

lemma tllist_all2_TNil2: "tllist_all2 P Q ts (TNil b') \<longleftrightarrow> (\<exists>b. ts = TNil b \<and> Q b b')"
by transfer auto

lemma tllist_all2_TCons1: 
  "tllist_all2 P Q (TCons x ts) ts' \<longleftrightarrow> (\<exists>x' ts''. ts' = TCons x' ts'' \<and> P x x' \<and> tllist_all2 P Q ts ts'')"
by transfer(fastforce simp add: llist_all2_LCons1 dest: llist_all2_lfiniteD)

lemma tllist_all2_TCons2: 
  "tllist_all2 P Q ts' (TCons x ts) \<longleftrightarrow> (\<exists>x' ts''. ts' = TCons x' ts'' \<and> P x' x \<and> tllist_all2 P Q ts'' ts)"
by transfer(fastforce simp add: llist_all2_LCons2 dest: llist_all2_lfiniteD)

lemma tllist_all2_coinduct [consumes 1, case_names tllist_all2, case_conclusion tllist_all2 is_TNil TNil TCons, coinduct pred: tllist_all2]:
  assumes "X xs ys"
  and "\<And>xs ys. X xs ys \<Longrightarrow>
  (is_TNil xs \<longleftrightarrow> is_TNil ys) \<and>
  (is_TNil xs \<longrightarrow> is_TNil ys \<longrightarrow> R (terminal xs) (terminal ys)) \<and>
  (\<not> is_TNil xs \<longrightarrow> \<not> is_TNil ys \<longrightarrow> P (thd xs) (thd ys) \<and> (X (ttl xs) (ttl ys) \<or> tllist_all2 P R (ttl xs) (ttl ys)))"
  shows "tllist_all2 P R xs ys"
using assms
apply(transfer fixing: P R)
apply clarsimp
apply(rule conjI)
 apply(erule llist_all2_coinduct, blast, blast)
apply (rule impI)
subgoal premises prems for X xs b ys c
proof -
  from \<open>lfinite xs\<close> \<open>X (xs, b) (ys, c)\<close>
  show "R b c"
    by(induct arbitrary: ys rule: lfinite_induct)(auto dest: prems(2))
qed
done

lemma tllist_all2_cases[consumes 1, case_names TNil TCons, cases pred]:
  assumes "tllist_all2 P Q xs ys"
  obtains (TNil) b b' where "xs = TNil b" "ys = TNil b'" "Q b b'"
  | (TCons) x xs' y ys'
    where "xs = TCons x xs'" and "ys = TCons y ys'" 
    and "P x y" and "tllist_all2 P Q xs' ys'"
using assms
by(cases xs)(fastforce simp add: tllist_all2_TCons1 tllist_all2_TNil1)+

lemma tllist_all2_tmap1:
  "tllist_all2 P Q (tmap f g xs) ys \<longleftrightarrow> tllist_all2 (\<lambda>x. P (f x)) (\<lambda>x. Q (g x)) xs ys"
by(transfer)(auto simp add: llist_all2_lmap1)

lemma tllist_all2_tmap2:
  "tllist_all2 P Q xs (tmap f g ys) \<longleftrightarrow> tllist_all2 (\<lambda>x y. P x (f y)) (\<lambda>x y. Q x (g y)) xs ys"
by(transfer)(auto simp add: llist_all2_lmap2)

lemma tllist_all2_mono:
  "\<lbrakk> tllist_all2 P Q xs ys; \<And>x y. P x y \<Longrightarrow> P' x y; \<And>x y. Q x y \<Longrightarrow> Q' x y \<rbrakk>
  \<Longrightarrow> tllist_all2 P' Q' xs ys"
by transfer(auto elim!: llist_all2_mono)

lemma tllist_all2_tlengthD: "tllist_all2 P Q xs ys \<Longrightarrow> tlength xs = tlength ys"
by(transfer)(auto dest: llist_all2_llengthD)

lemma tllist_all2_tfiniteD: "tllist_all2 P Q xs ys \<Longrightarrow> tfinite xs = tfinite ys"
by(transfer)(auto dest: llist_all2_lfiniteD)

lemma tllist_all2_tfinite1_terminalD:
  "\<lbrakk> tllist_all2 P Q xs ys; tfinite xs \<rbrakk> \<Longrightarrow> Q (terminal xs) (terminal ys)"
by(frule tllist_all2_tfiniteD)(transfer, auto)

lemma tllist_all2_tfinite2_terminalD:
  "\<lbrakk> tllist_all2 P Q xs ys; tfinite ys \<rbrakk> \<Longrightarrow> Q (terminal xs) (terminal ys)"
by(metis tllist_all2_tfinite1_terminalD tllist_all2_tfiniteD)

lemma tllist_all2D_llist_all2_llist_of_tllist:
  "tllist_all2 P Q xs ys \<Longrightarrow> llist_all2 P (llist_of_tllist xs) (llist_of_tllist ys)"
by(transfer) auto

lemma tllist_all2_is_TNilD:
  "tllist_all2 P Q xs ys \<Longrightarrow> is_TNil xs \<longleftrightarrow> is_TNil ys"
by(cases xs)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)

lemma tllist_all2_thdD:
  "\<lbrakk> tllist_all2 P Q xs ys; \<not> is_TNil xs \<or> \<not> is_TNil ys \<rbrakk> \<Longrightarrow> P (thd xs) (thd ys)"
by(cases xs)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)

lemma tllist_all2_ttlI:
  "\<lbrakk> tllist_all2 P Q xs ys; \<not> is_TNil xs \<or> \<not> is_TNil ys \<rbrakk> \<Longrightarrow> tllist_all2 P Q (ttl xs) (ttl ys)"
by(cases xs)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)

lemma tllist_all2_refl:
  "tllist_all2 P Q xs xs \<longleftrightarrow> (\<forall>x \<in> tset xs. P x x) \<and> (tfinite xs \<longrightarrow> Q (terminal xs) (terminal xs))"
by transfer(auto)

lemma tllist_all2_reflI:
  "\<lbrakk> \<And>x. x \<in> tset xs \<Longrightarrow> P x x; tfinite xs \<Longrightarrow> Q (terminal xs) (terminal xs) \<rbrakk>
  \<Longrightarrow> tllist_all2 P Q xs xs"
by(simp add: tllist_all2_refl)

lemma tllist_all2_conv_all_tnth:
  "tllist_all2 P Q xs ys \<longleftrightarrow> 
  tlength xs = tlength ys \<and> 
  (\<forall>n. enat n < tlength xs \<longrightarrow> P (tnth xs n) (tnth ys n)) \<and>
  (tfinite xs \<longrightarrow> Q (terminal xs) (terminal ys))"
by transfer(auto 4 4 simp add: llist_all2_conv_all_lnth split: if_split_asm dest: lfinite_llength_enat not_lfinite_llength)

lemma tllist_all2_tnthD:
  "\<lbrakk> tllist_all2 P Q xs ys; enat n < tlength xs \<rbrakk> 
  \<Longrightarrow> P (tnth xs n) (tnth ys n)"
by(simp add: tllist_all2_conv_all_tnth)

lemma tllist_all2_tnthD2:
  "\<lbrakk> tllist_all2 P Q xs ys; enat n < tlength ys \<rbrakk> 
  \<Longrightarrow> P (tnth xs n) (tnth ys n)"
by(simp add: tllist_all2_conv_all_tnth)

lemmas tllist_all2_eq = tllist.rel_eq

lemma tmap_eq_tmap_conv_tllist_all2:
  "tmap f g xs = tmap f' g' ys \<longleftrightarrow>
  tllist_all2 (\<lambda>x y. f x = f' y) (\<lambda>x y. g x = g' y) xs ys"
apply transfer
apply(clarsimp simp add: lmap_eq_lmap_conv_llist_all2)
apply(auto dest: llist_all2_lfiniteD)
done

lemma tllist_all2_trans:
  "\<lbrakk> tllist_all2 P Q xs ys; tllist_all2 P Q ys zs; transp P; transp Q \<rbrakk>
  \<Longrightarrow> tllist_all2 P Q xs zs"
by transfer(auto elim: llist_all2_trans dest: llist_all2_lfiniteD transpD)

lemma tllist_all2_tappendI:
  "\<lbrakk> tllist_all2 P Q xs ys;
     \<lbrakk> tfinite xs; tfinite ys; Q (terminal xs) (terminal ys) \<rbrakk>
     \<Longrightarrow> tllist_all2 P R (xs' (terminal xs)) (ys' (terminal ys)) \<rbrakk>
  \<Longrightarrow> tllist_all2 P R (tappend xs xs') (tappend ys ys')"
apply transfer
apply(auto 4 3 simp add: apfst_def map_prod_def lappend_inf split: prod.split_asm dest: llist_all2_lfiniteD intro: llist_all2_lappendI)
apply(frule llist_all2_lfiniteD, simp add: lappend_inf)
done

lemma llist_all2_tllist_of_llistI:
  "tllist_all2 A B xs ys \<Longrightarrow> llist_all2 A (llist_of_tllist xs) (llist_of_tllist ys)"
by(coinduction arbitrary: xs ys)(auto dest: tllist_all2_is_TNilD tllist_all2_thdD intro: tllist_all2_ttlI)

lemma tllist_all2_tllist_of_llist [simp]:
  "tllist_all2 A B (tllist_of_llist b xs) (tllist_of_llist c ys) \<longleftrightarrow>
  llist_all2 A xs ys \<and> (lfinite xs \<longrightarrow> B b c)"
by transfer auto

subsection \<open>From a terminated lazy list to a lazy list @{term llist_of_tllist}\<close>

lemma llist_of_tllist_tmap [simp]:
  "llist_of_tllist (tmap f g xs) = lmap f (llist_of_tllist xs)"
by transfer auto

lemma llist_of_tllist_tappend:
  "llist_of_tllist (tappend xs f) = lappend (llist_of_tllist xs) (llist_of_tllist (f (terminal xs)))"
by(transfer)(auto simp add: lappend_inf)

lemma llist_of_tllist_lappendt [simp]:
  "llist_of_tllist (lappendt xs tr) = lappend xs (llist_of_tllist tr)"
by transfer auto

lemma llist_of_tllist_tfilter [simp]:
  "llist_of_tllist (tfilter b P tr) = lfilter P (llist_of_tllist tr)"
by transfer auto

lemma llist_of_tllist_tconcat:
  "llist_of_tllist (tconcat b trs) = lconcat (llist_of_tllist trs)"
by transfer auto

lemma llist_of_tllist_eq_lappend_conv:
  "llist_of_tllist xs = lappend us vs \<longleftrightarrow> 
  (\<exists>ys. xs = lappendt us ys \<and> vs = llist_of_tllist ys \<and> terminal xs = terminal ys)"
by transfer auto

subsection \<open>The nth element of a terminated lazy list @{term "tnth"}\<close>

lemma tnth_TNil [nitpick_simp]:
  "tnth (TNil b) n = undefined n"
by(transfer)(simp add: lnth_LNil)

lemma tnth_TCons:
  "tnth (TCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> tnth xs n')"
by(transfer)(auto simp add: lnth_LCons split: nat.split)

lemma tnth_code [simp, nitpick_simp, code]:
  shows tnth_0: "tnth (TCons x xs) 0 = x"
  and tnth_Suc_TCons: "tnth (TCons x xs) (Suc n) = tnth xs n"
by(simp_all add: tnth_TCons)

lemma lnth_llist_of_tllist [simp]:
  "lnth (llist_of_tllist xs) = tnth xs"
by(transfer)(auto)

lemma tnth_tmap [simp]: "enat n < tlength xs \<Longrightarrow> tnth (tmap f g xs) n = f (tnth xs n)"
by transfer simp

subsection \<open>The length of a terminated lazy list @{term "tlength"}\<close>

lemma [simp, nitpick_simp]:
  shows tlength_TNil: "tlength (TNil b) = 0"
  and tlength_TCons: "tlength (TCons x xs) = eSuc (tlength xs)"
 apply(transfer, simp)
apply(transfer, auto)
done

lemma llength_llist_of_tllist [simp]: "llength (llist_of_tllist xs) = tlength xs"
by transfer auto

lemma tlength_tmap [simp]: "tlength (tmap f g xs) = tlength xs"
by transfer simp

definition gen_tlength :: "nat \<Rightarrow> ('a, 'b) tllist \<Rightarrow> enat"
where "gen_tlength n xs = enat n + tlength xs"

lemma gen_tlength_code [code]:
  "gen_tlength n (TNil b) = enat n"
  "gen_tlength n (TCons x xs) = gen_tlength (n + 1) xs"
by(simp_all add: gen_tlength_def iadd_Suc eSuc_enat[symmetric] iadd_Suc_right)

lemma tlength_code [code]: "tlength = gen_tlength 0"
by(simp add: gen_tlength_def fun_eq_iff zero_enat_def)

subsection \<open>@{term "tdropn"}\<close>

lemma tdropn_0 [simp, code, nitpick_simp]: "tdropn 0 xs = xs"
by transfer auto

lemma tdropn_TNil [simp, code]: "tdropn n (TNil b) = (TNil b)"
by transfer(auto)

lemma tdropn_Suc_TCons [simp, code]: "tdropn (Suc n) (TCons x xs) = tdropn n xs"
by transfer(auto)

lemma tdropn_Suc [nitpick_simp]: "tdropn (Suc n) xs = (case xs of TNil b \<Rightarrow> TNil b | TCons x xs' \<Rightarrow> tdropn n xs')"
by(cases xs) simp_all

lemma lappendt_ltake_tdropn:
  "lappendt (ltake (enat n) (llist_of_tllist xs)) (tdropn n xs) = xs"
by transfer (auto)

lemma llist_of_tllist_tdropn [simp]:
  "llist_of_tllist (tdropn n xs) = ldropn n (llist_of_tllist xs)"
by transfer auto

lemma tdropn_Suc_conv_tdropn:
  "enat n < tlength xs \<Longrightarrow> TCons (tnth xs n) (tdropn (Suc n) xs) = tdropn n xs" 
by transfer(auto simp add: ldropn_Suc_conv_ldropn)

lemma tlength_tdropn [simp]: "tlength (tdropn n xs) = tlength xs - enat n"
by transfer auto

lemma tnth_tdropn [simp]: "enat (n + m) < tlength xs \<Longrightarrow> tnth (tdropn n xs) m = tnth xs (m + n)"
by transfer auto

subsection \<open>@{term "tset"}\<close>

lemma tset_induct [consumes 1, case_names find step]:
  assumes "x \<in> tset xs"
  and "\<And>xs. P (TCons x xs)"
  and "\<And>x' xs. \<lbrakk> x \<in> tset xs; x \<noteq> x'; P xs \<rbrakk> \<Longrightarrow> P (TCons x' xs)"
  shows "P xs"
using assms
by transfer(clarsimp, erule lset_induct)

lemma tset_conv_tnth: "tset xs = {tnth xs n|n . enat n < tlength xs}"
by transfer(simp add: lset_conv_lnth)

lemma in_tset_conv_tnth: "x \<in> tset xs \<longleftrightarrow> (\<exists>n. enat n < tlength xs \<and> tnth xs n = x)"
using tset_conv_tnth[of xs] by auto

subsection \<open>Setup for Lifting/Transfer\<close>

subsubsection \<open>Relator and predicator properties\<close>

abbreviation "tllist_all == pred_tllist"

subsubsection \<open>Transfer rules for the Transfer package\<close>

context includes lifting_syntax
begin

lemma set1_pre_tllist_transfer [transfer_rule]:
  "(rel_pre_tllist A B C ===> rel_set A) set1_pre_tllist set1_pre_tllist"
by(auto simp add: rel_pre_tllist_def vimage2p_def rel_fun_def set1_pre_tllist_def rel_set_def collect_def sum_set_defs prod_set_defs elim: rel_sum.cases split: sum.split_asm)

lemma set2_pre_tllist_transfer [transfer_rule]:
  "(rel_pre_tllist A B C ===> rel_set B) set2_pre_tllist set2_pre_tllist"
by(auto simp add: rel_pre_tllist_def vimage2p_def rel_fun_def set2_pre_tllist_def rel_set_def collect_def sum_set_defs prod_set_defs elim: rel_sum.cases split: sum.split_asm)

lemma set3_pre_tllist_transfer [transfer_rule]:
  "(rel_pre_tllist A B C ===> rel_set C) set3_pre_tllist set3_pre_tllist"
by(auto simp add: rel_pre_tllist_def vimage2p_def rel_fun_def set3_pre_tllist_def rel_set_def collect_def sum_set_defs prod_set_defs elim: rel_sum.cases split: sum.split_asm)

lemma TNil_transfer2 [transfer_rule]: "(B ===> tllist_all2 A B) TNil TNil"
by auto
declare TNil_transfer [transfer_rule]

lemma TCons_transfer2 [transfer_rule]:
  "(A ===> tllist_all2 A B ===> tllist_all2 A B) TCons TCons"
unfolding rel_fun_def by simp
declare TCons_transfer [transfer_rule]

lemma case_tllist_transfer [transfer_rule]:
  "((B ===> C) ===> (A ===> tllist_all2 A B ===> C) ===> tllist_all2 A B ===> C)
    case_tllist case_tllist"
unfolding rel_fun_def
by (simp add: tllist_all2_TNil1 tllist_all2_TNil2 split: tllist.split)

lemma unfold_tllist_transfer [transfer_rule]:
  "((A ===> (=)) ===> (A ===> B) ===> (A ===> C) ===> (A ===> A) ===> A ===> tllist_all2 C B) unfold_tllist unfold_tllist"
proof(rule rel_funI)+
  fix IS_TNIL1 :: "'a \<Rightarrow> bool" and IS_TNIL2
    TERMINAL1 TERMINAL2 THD1 THD2 TTL1 TTL2 x y
  assume rel: "(A ===> (=)) IS_TNIL1 IS_TNIL2" "(A ===> B) TERMINAL1 TERMINAL2"
    "(A ===> C) THD1 THD2" "(A ===> A) TTL1 TTL2"
    and "A x y"
  show "tllist_all2 C B (unfold_tllist IS_TNIL1 TERMINAL1 THD1 TTL1 x) (unfold_tllist IS_TNIL2 TERMINAL2 THD2 TTL2 y)"
    using \<open>A x y\<close>
    apply(coinduction arbitrary: x y)
    using rel by(auto 4 4 elim: rel_funE)
qed

lemma corec_tllist_transfer [transfer_rule]:
  "((A ===> (=)) ===> (A ===> B) ===> (A ===> C) ===> (A ===> (=)) ===> (A ===> tllist_all2 C B) ===> (A ===> A) ===> A ===> tllist_all2 C B) corec_tllist corec_tllist"
proof(rule rel_funI)+
  fix IS_TNIL1 MORE1 :: "'a \<Rightarrow> bool" and IS_TNIL2
    TERMINAL1 TERMINAL2 THD1 THD2 MORE2 STOP1 STOP2 TTL1 TTL2 x y
  assume rel: "(A ===> (=)) IS_TNIL1 IS_TNIL2" "(A ===> B) TERMINAL1 TERMINAL2"
    "(A ===> C) THD1 THD2" "(A ===> (=)) MORE1 MORE2"
    "(A ===> tllist_all2 C B) STOP1 STOP2" "(A ===> A) TTL1 TTL2"
    and "A x y"
  show "tllist_all2 C B (corec_tllist IS_TNIL1 TERMINAL1 THD1 MORE1 STOP1 TTL1 x) (corec_tllist IS_TNIL2 TERMINAL2 THD2 MORE2 STOP2 TTL2 y)"
    using \<open>A x y\<close>
    apply(coinduction arbitrary: x y)
    using rel by(auto 4 4 elim: rel_funE)
qed

lemma ttl_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> tllist_all2 A B) ttl ttl"
  unfolding ttl_def[abs_def] by transfer_prover
declare ttl_transfer [transfer_rule]

lemma tset_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> rel_set A) tset tset"
by (intro rel_funI rel_setI) (auto simp only: in_tset_conv_tnth tllist_all2_conv_all_tnth Bex_def)

lemma tmap_transfer2 [transfer_rule]:
  "((A ===> B) ===> (C ===> D) ===> tllist_all2 A C ===> tllist_all2 B D) tmap tmap"
by(auto simp add: rel_fun_def tllist_all2_tmap1 tllist_all2_tmap2 elim: tllist_all2_mono)
declare tmap_transfer [transfer_rule]

lemma is_TNil_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> (=)) is_TNil is_TNil"
by(auto dest: tllist_all2_is_TNilD)
declare is_TNil_transfer [transfer_rule]

lemma tappend_transfer [transfer_rule]:
  "(tllist_all2 A B ===> (B ===> tllist_all2 A C) ===> tllist_all2 A C) tappend tappend"
by(auto intro: tllist_all2_tappendI elim: rel_funE)
declare tappend.transfer [transfer_rule]

lemma lappendt_transfer [transfer_rule]:
  "(llist_all2 A ===> tllist_all2 A B ===> tllist_all2 A B) lappendt lappendt"
unfolding rel_fun_def
by transfer(auto intro: llist_all2_lappendI)
declare lappendt.transfer [transfer_rule]

lemma llist_of_tllist_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> llist_all2 A) llist_of_tllist llist_of_tllist"
by(auto intro: llist_all2_tllist_of_llistI)
declare llist_of_tllist_transfer [transfer_rule]

lemma tllist_of_llist_transfer2 [transfer_rule]:
  "(B ===> llist_all2 A ===> tllist_all2 A B) tllist_of_llist tllist_of_llist"
by(auto intro!: rel_funI)
declare tllist_of_llist_transfer [transfer_rule]

lemma tlength_transfer [transfer_rule]:
  "(tllist_all2 A B ===> (=)) tlength tlength"
by(auto dest: tllist_all2_tlengthD)
declare tlength.transfer [transfer_rule]

lemma tdropn_transfer [transfer_rule]:
  "((=) ===> tllist_all2 A B ===> tllist_all2 A B) tdropn tdropn"
unfolding rel_fun_def
by transfer(auto intro: llist_all2_ldropnI)
declare tdropn.transfer [transfer_rule]

lemma tfilter_transfer [transfer_rule]:
  "(B ===> (A ===> (=)) ===> tllist_all2 A B ===> tllist_all2 A B) tfilter tfilter"
unfolding rel_fun_def
by transfer(auto intro: llist_all2_lfilterI dest: llist_all2_lfiniteD)
declare tfilter.transfer [transfer_rule]

lemma tconcat_transfer [transfer_rule]:
  "(B ===> tllist_all2 (llist_all2 A) B ===> tllist_all2 A B) tconcat tconcat"
unfolding rel_fun_def
by transfer(auto intro: llist_all2_lconcatI dest: llist_all2_lfiniteD)
declare tconcat.transfer [transfer_rule]

lemma tllist_all2_rsp:
  assumes R1: "\<forall>x y. R1 x y \<longrightarrow> (\<forall>a b. R1 a b \<longrightarrow> S x a = T y b)"
  and R2: "\<forall>x y. R2 x y \<longrightarrow> (\<forall>a b. R2 a b \<longrightarrow> S' x a = T' y b)"
  and xsys: "tllist_all2 R1 R2 xs ys"
  and xs'ys': "tllist_all2 R1 R2 xs' ys'"
  shows "tllist_all2 S S' xs xs' = tllist_all2 T T' ys ys'"
proof
  assume "tllist_all2 S S' xs xs'"
  with xsys xs'ys' show "tllist_all2 T T' ys ys'"
  proof(coinduction arbitrary: ys ys' xs xs')
    case (tllist_all2 ys ys' xs xs')
    thus ?case
      by cases (auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
next
  assume "tllist_all2 T T' ys ys'"
  with xsys xs'ys' show "tllist_all2 S S' xs xs'"
  proof(coinduction arbitrary: xs xs' ys ys')
    case (tllist_all2 xs xs' ys ys')
    thus ?case
      by cases(auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
qed

lemma tllist_all2_transfer2 [transfer_rule]:
  "((R1 ===> R1 ===> (=)) ===> (R2 ===> R2 ===> (=)) ===>
    tllist_all2 R1 R2 ===> tllist_all2 R1 R2 ===> (=)) tllist_all2 tllist_all2"
by (simp add: tllist_all2_rsp rel_fun_def)
declare tllist_all2_transfer [transfer_rule]

end

text \<open>
  Delete lifting rules for @{typ "('a, 'b) tllist"} 
  because the parametricity rules take precedence over
  most of the transfer rules. They can be restored by 
  including the bundle \<open>tllist.lifting\<close>.
\<close>

lifting_update tllist.lifting
lifting_forget tllist.lifting

end
