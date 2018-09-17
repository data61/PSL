(*  Title:      Coinductive/Coinductive_Stream.thy
    Author:     Peter Gammie and Andreas Lochbihler
*)
section {* Infinite lists as a codatatype *}

theory Coinductive_Stream
imports
  "HOL-Library.Stream"
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
  Coinductive_List
begin

lemma eq_onpI: "P x \<Longrightarrow> eq_onp P x x"
by(simp add: eq_onp_def)

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b stream" where
  "unfold_stream g1 g2 a = g1 a ## unfold_stream g1 g2 (g2 a)"

text {*
  The following setup should be done by the BNF package.
*}

text {* congruence rule *}

declare stream.map_cong [cong]

text {* lemmas about generated constants *}

lemma eq_SConsD: "xs = SCons y ys \<Longrightarrow> shd xs = y \<and> stl xs = ys"
by auto

declare stream.map_ident[simp]

lemma smap_eq_SCons_conv:
  "smap f xs = y ## ys \<longleftrightarrow>
  (\<exists>x xs'. xs = x ## xs' \<and> y = f x \<and> ys = smap f xs')"
by(cases xs)(auto)

lemma smap_unfold_stream:
  "smap f (unfold_stream SHD STL b) = unfold_stream (f \<circ> SHD) STL b"
by(coinduction arbitrary: b) auto

lemma smap_corec_stream:
  "smap f (corec_stream SHD endORmore STL_end STL_more b) =
   corec_stream (f \<circ> SHD) endORmore (smap f \<circ> STL_end) STL_more b"
by(coinduction arbitrary: b rule: stream.coinduct_strong) auto

lemma unfold_stream_ltl_unroll:
  "unfold_stream SHD STL (STL b) = unfold_stream (SHD \<circ> STL) STL b"
by(coinduction arbitrary: b) auto

lemma unfold_stream_eq_SCons [simp]:
  "unfold_stream SHD STL b = x ## xs \<longleftrightarrow>
  x = SHD b \<and> xs = unfold_stream SHD STL (STL b)"
by(subst unfold_stream.ctr) auto

lemma unfold_stream_id [simp]: "unfold_stream shd stl xs = xs"
by(coinduction arbitrary: xs) simp_all

lemma sset_neq_empty [simp]: "sset xs \<noteq> {}"
by(cases xs) simp_all

declare stream.set_sel(1)[simp]

lemma sset_stl: "sset (stl xs) \<subseteq> sset xs"
by(cases xs) auto

text {* induction rules *}

lemmas stream_set_induct = sset_induct

subsection {* Lemmas about operations from @{theory "HOL-Library.Stream"} *}

lemma szip_iterates:
  "szip (siterate f a) (siterate g b) = siterate (map_prod f g) (a, b)"
by(coinduction arbitrary: a b) auto

lemma szip_smap1: "szip (smap f xs) ys = smap (apfst f) (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma szip_smap2: "szip xs (smap g ys) = smap (apsnd g) (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma szip_smap [simp]: "szip (smap f xs) (smap g ys) = smap (map_prod f g) (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma smap_fst_szip [simp]: "smap fst (szip xs ys) = xs"
by(coinduction arbitrary: xs ys) auto

lemma smap_snd_szip [simp]: "smap snd (szip xs ys) = ys"
by(coinduction arbitrary: xs ys) auto

lemma snth_shift: "snth (shift xs ys) n = (if n < length xs then xs ! n else snth ys (n - length xs))"
by simp

declare szip_unfold [simp, nitpick_simp]

lemma szip_shift:
  "length xs = length us
  \<Longrightarrow> szip (xs @- ys) (us @- zs) = zip xs us @- szip ys zs"
by(induct xs arbitrary: us)(auto simp add: Suc_length_conv)


subsection {* Link @{typ "'a stream"} to @{typ "'a llist"} *}

definition llist_of_stream :: "'a stream \<Rightarrow> 'a llist"
where "llist_of_stream = unfold_llist (\<lambda>_. False) shd stl"

definition stream_of_llist :: "'a llist \<Rightarrow> 'a stream"
where "stream_of_llist = unfold_stream lhd ltl"

lemma lnull_llist_of_stream [simp]: "\<not> lnull (llist_of_stream xs)"
by(simp add: llist_of_stream_def)

lemma ltl_llist_of_stream [simp]: "ltl (llist_of_stream xs) = llist_of_stream (stl xs)"
by(simp add: llist_of_stream_def)

lemma stl_stream_of_llist [simp]: "stl (stream_of_llist xs) = stream_of_llist (ltl xs)"
by(simp add: stream_of_llist_def)

lemma shd_stream_of_llist [simp]: "shd (stream_of_llist xs) = lhd xs"
by(simp add: stream_of_llist_def)

lemma lhd_llist_of_stream [simp]: "lhd (llist_of_stream xs) = shd xs"
by(simp add: llist_of_stream_def)

lemma stream_of_llist_llist_of_stream [simp]:
  "stream_of_llist (llist_of_stream xs) = xs"
by(coinduction arbitrary: xs) simp_all

lemma llist_of_stream_stream_of_llist [simp]:
  "\<not> lfinite xs \<Longrightarrow> llist_of_stream (stream_of_llist xs) = xs"
by(coinduction arbitrary: xs) auto

lemma lfinite_llist_of_stream [simp]: "\<not> lfinite (llist_of_stream xs)"
proof
  assume "lfinite (llist_of_stream xs)"
  thus False
    by(induct "llist_of_stream xs" arbitrary: xs rule: lfinite_induct) auto
qed

lemma stream_from_llist: "type_definition llist_of_stream stream_of_llist {xs. \<not> lfinite xs}"
by(unfold_locales) simp_all

interpretation stream: type_definition llist_of_stream stream_of_llist "{xs. \<not> lfinite xs}"
by(fact stream_from_llist)

declare stream.exhaust[cases type: stream]

locale stream_from_llist_setup
begin
setup_lifting stream_from_llist
end

context
begin

interpretation stream_from_llist_setup .

lemma cr_streamI: "\<not> lfinite xs \<Longrightarrow> cr_stream xs (stream_of_llist xs)"
by(simp add: cr_stream_def Abs_stream_inverse)

lemma llist_of_stream_unfold_stream [simp]:
  "llist_of_stream (unfold_stream SHD STL x) = unfold_llist (\<lambda>_. False) SHD STL x"
by(coinduction arbitrary: x) auto

lemma llist_of_stream_corec_stream [simp]:
  "llist_of_stream (corec_stream SHD endORmore STL_more STL_end x) =
   corec_llist (\<lambda>_. False) SHD endORmore (llist_of_stream \<circ> STL_more) STL_end x"
by(coinduction arbitrary: x rule: llist.coinduct_strong) auto

lemma LCons_llist_of_stream [simp]: "LCons x (llist_of_stream xs) = llist_of_stream (x ## xs)"
by(rule sym)(simp add: llist_of_stream_def)

lemma lmap_llist_of_stream [simp]:
  "lmap f (llist_of_stream xs) = llist_of_stream (smap f xs)"
by(coinduction arbitrary: xs) auto

lemma lset_llist_of_stream [simp]: "lset (llist_of_stream xs) = sset xs" (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs"
  thus "x \<in> ?rhs"
    by(induct "llist_of_stream xs" arbitrary: xs rule: llist_set_induct)
      (auto dest: stream.set_sel(2))
next
  fix x
  assume "x \<in> ?rhs"
  thus "x \<in> ?lhs"
  proof(induct)
    case (shd xs)
    thus ?case using llist.set_sel(1)[of "llist_of_stream xs"] by simp
  next
    case stl
    thus ?case
      by(auto simp add: ltl_llist_of_stream[symmetric] simp del: ltl_llist_of_stream dest: in_lset_ltlD)
  qed
qed

lemma lnth_list_of_stream [simp]:
  "lnth (llist_of_stream xs) = snth xs"
proof
  fix n
  show "lnth (llist_of_stream xs) n = snth xs n"
    by(induction n arbitrary: xs)(simp_all add: lnth_0_conv_lhd lnth_ltl[symmetric])
qed

lemma llist_of_stream_siterates [simp]: "llist_of_stream (siterate f x) = iterates f x"
by(coinduction arbitrary: x) auto

lemma lappend_llist_of_stream_conv_shift [simp]:
  "lappend (llist_of xs) (llist_of_stream ys) = llist_of_stream (xs @- ys)"
by(induct xs) simp_all

lemma lzip_llist_of_stream [simp]:
  "lzip (llist_of_stream xs) (llist_of_stream ys) = llist_of_stream (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

context includes lifting_syntax
begin

lemma lmap_infinite_transfer [transfer_rule]:
  "((=) ===> eq_onp (\<lambda>xs. \<not> lfinite xs) ===> eq_onp (\<lambda>xs. \<not> lfinite xs)) lmap lmap"
by(simp add: rel_fun_def eq_onp_def)

lemma lset_infinite_transfer [transfer_rule]:
  "(eq_onp (\<lambda>xs. \<not> lfinite xs) ===> (=)) lset lset"
by(simp add: rel_fun_def eq_onp_def)

lemma unfold_stream_transfer [transfer_rule]:
  "((=) ===> (=) ===> (=) ===> pcr_stream (=)) (unfold_llist (\<lambda>_. False)) unfold_stream"
by(auto simp add: stream.pcr_cr_eq cr_stream_def intro!: rel_funI)

lemma corec_stream_transfer [transfer_rule]:
  "((=) ===> (=) ===> ((=) ===> pcr_stream (=)) ===> (=) ===> (=) ===> pcr_stream (=))
   (corec_llist (\<lambda>_. False)) corec_stream"
apply(auto intro!: rel_funI simp add: cr_stream_def stream.pcr_cr_eq)
apply(rule fun_cong) back
apply(rule_tac x=yc in fun_cong)
apply(rule_tac x=xb in arg_cong)
apply(auto elim: rel_funE)
done

lemma shd_transfer [transfer_rule]: "(pcr_stream A ===> A) lhd shd"
by(auto simp add: pcr_stream_def cr_stream_def intro!: rel_funI relcomppI)(frule llist_all2_lhdD, auto dest: llist_all2_lnullD)

lemma stl_transfer [transfer_rule]: "(pcr_stream A ===> pcr_stream A) ltl stl"
by(auto simp add: pcr_stream_def cr_stream_def intro!: rel_funI relcomppI dest: llist_all2_ltlI)

lemma llist_of_stream_transfer [transfer_rule]: "(pcr_stream (=) ===> (=)) id llist_of_stream"
by(simp add: rel_fun_def stream.pcr_cr_eq cr_stream_def)

lemma stream_of_llist_transfer [transfer_rule]:
  "(eq_onp (\<lambda>xs. \<not> lfinite xs) ===> pcr_stream (=)) (\<lambda>xs. xs) stream_of_llist"
by(simp add: eq_onp_def rel_fun_def stream.pcr_cr_eq cr_stream_def)

lemma SCons_transfer [transfer_rule]:
  "(A ===> pcr_stream A ===> pcr_stream A) LCons (##)"
by(auto simp add: cr_stream_def pcr_stream_def intro!: rel_funI relcomppI intro: llist_all2_expand)

lemma sset_transfer [transfer_rule]: "(pcr_stream A ===> rel_set A) lset sset"
by(auto 4 3 simp add: pcr_stream_def cr_stream_def intro!: rel_funI relcomppI rel_setI dest: llist_all2_lsetD1 llist_all2_lsetD2)

lemma smap_transfer [transfer_rule]:
  "((A ===> B) ===> pcr_stream A ===> pcr_stream B) lmap smap"
by(auto simp add: cr_stream_def pcr_stream_def intro!: rel_funI relcomppI dest: lmap_transfer[THEN rel_funD] elim: rel_funD)

lemma snth_transfer [transfer_rule]: "(pcr_stream (=) ===> (=)) lnth snth"
by(rule rel_funI)(clarsimp simp add: stream.pcr_cr_eq cr_stream_def fun_eq_iff)

lemma siterate_transfer [transfer_rule]:
  "((=) ===> (=) ===> pcr_stream (=)) iterates siterate"
by(rule rel_funI)+(clarsimp simp add: stream.pcr_cr_eq cr_stream_def)

context
  fixes xs
  assumes inf: "\<not> lfinite xs"
  notes [transfer_rule] = eq_onpI[where P="\<lambda>xs. \<not> lfinite xs", OF inf]
begin

lemma smap_stream_of_llist [simp]:
  shows "smap f (stream_of_llist xs) = stream_of_llist (lmap f xs)"
by transfer simp

lemma sset_stream_of_llist [simp]:
  assumes "\<not> lfinite xs"
  shows "sset (stream_of_llist xs) = lset xs"
by transfer simp

end

lemma llist_all2_llist_of_stream [simp]:
  "llist_all2 P (llist_of_stream xs) (llist_of_stream ys) = stream_all2 P xs ys"
apply(cases xs ys rule: stream.Abs_cases[case_product stream.Abs_cases])
apply(simp add: llist_all2_def stream_all2_def)
apply(safe elim!: GrpE)
 apply(rule_tac b="stream_of_llist b" in relcomppI; auto intro!: GrpI)
apply(rule_tac b="llist_of_stream b" in relcomppI; auto intro!: GrpI)
done

lemma stream_all2_transfer [transfer_rule]:
  "((=) ===> pcr_stream (=) ===> pcr_stream (=) ===> (=)) llist_all2 stream_all2"
by(simp add: rel_fun_def stream.pcr_cr_eq cr_stream_def)

lemma stream_all2_coinduct:
  assumes "X xs ys"
  and "\<And>xs ys. X xs ys \<Longrightarrow> P (shd xs) (shd ys) \<and> (X (stl xs) (stl ys) \<or> stream_all2 P (stl xs) (stl ys))"
  shows "stream_all2 P xs ys"
using assms
apply transfer
apply(rule_tac X="\<lambda>xs ys. \<not> lfinite xs \<and> \<not> lfinite ys \<and> X xs ys" in llist_all2_coinduct)
apply auto
done

lemma shift_transfer [transfer_rule]:
  "((=) ===> pcr_stream (=) ===> pcr_stream (=)) (lappend \<circ> llist_of) shift"
by(clarsimp simp add: rel_fun_def stream.pcr_cr_eq cr_stream_def)

lemma szip_transfer [transfer_rule]:
  "(pcr_stream (=) ===> pcr_stream (=) ===> pcr_stream (=)) lzip szip"
by(simp add: stream.pcr_cr_eq cr_stream_def rel_fun_def)

subsection {* Link @{typ "'a stream"} with @{typ "nat \<Rightarrow> 'a"} *}

lift_definition of_seq :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" is "inf_llist" by simp

lemma of_seq_rec [code]: "of_seq f = f 0 ## of_seq (f \<circ> Suc)"
by transfer (subst inf_llist_rec, simp add: o_def)

lemma snth_of_seq [simp]: "snth (of_seq f) = f"
by transfer (simp add: fun_eq_iff)

lemma snth_SCons: "snth (x ## xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> snth xs n')"
by(simp split: nat.split)

lemma snth_SCons_simps [simp]:
  shows snth_SCons_0: "(x ## xs) !! 0 = x"
  and snth_SCons_Suc: "(x ## xs) !! Suc n = xs !! n"
by(simp_all add: snth_SCons)

lemma of_seq_snth [simp]: "of_seq (snth xs) = xs"
by transfer simp

lemma shd_of_seq [simp]: "shd (of_seq f) = f 0"
by transfer simp

lemma stl_of_seq [simp]: "stl (of_seq f) = of_seq (\<lambda>n. f (Suc n))"
by transfer simp

lemma sset_of_seq [simp]: "sset (of_seq f) = range f"
by transfer simp

lemma smap_of_seq [simp]: "smap f (of_seq g) = of_seq (f \<circ> g)"
by transfer simp
end

subsection{* Function iteration @{const siterate}  and @{term sconst} *}

lemmas siterate [nitpick_simp] = siterate.code

lemma smap_iterates: "smap f (siterate f x) = siterate f (f x)"
by transfer (rule lmap_iterates)

lemma siterate_smap: "siterate f x = x ## (smap f (siterate f x))"
by transfer (rule iterates_lmap)

lemma siterate_conv_of_seq: "siterate f a = of_seq (\<lambda>n. (f ^^ n) a)"
by transfer (rule iterates_conv_inf_llist)

lemma sconst_conv_of_seq: "sconst a = of_seq (\<lambda>_. a)"
by(simp add: siterate_conv_of_seq)

lemma szip_sconst1 [simp]: "szip (sconst a) xs = smap (Pair a) xs"
by(coinduction arbitrary: xs) auto

lemma szip_sconst2 [simp]: "szip xs (sconst b) = smap (\<lambda>x. (x, b)) xs"
by(coinduction arbitrary: xs) auto

end

subsection \<open> Counting elements \<close>

partial_function (lfp) scount :: "('s stream \<Rightarrow> bool) \<Rightarrow> 's stream \<Rightarrow> enat" where
  "scount P \<omega> = (if P \<omega> then eSuc (scount P (stl \<omega>)) else scount P (stl \<omega>))"

lemma scount_simps:
  "P \<omega> \<Longrightarrow> scount P \<omega> = eSuc (scount P (stl \<omega>))"
  "\<not> P \<omega> \<Longrightarrow> scount P \<omega> = scount P (stl \<omega>)"
  using scount.simps[of P \<omega>] by auto

lemma scount_eq_0I: "alw (not P) \<omega> \<Longrightarrow> scount P \<omega> = 0"
  by (induct arbitrary: \<omega> rule: scount.fixp_induct)
     (auto simp: bot_enat_def intro!: admissible_all admissible_imp admissible_eq_mcontI mcont_const)

lemma scount_eq_0D: "scount P \<omega> = 0 \<Longrightarrow> alw (not P) \<omega>"
proof (induction rule: alw.coinduct)
  case (alw \<omega>) with scount.simps[of P \<omega>] show ?case
    by (simp split: if_split_asm)
qed

lemma scount_eq_0_iff: "scount P \<omega> = 0 \<longleftrightarrow> alw (not P) \<omega>"
  by (metis scount_eq_0D scount_eq_0I)

lemma
  assumes "ev (alw (not P)) \<omega>"
  shows scount_eq_card: "scount P \<omega> = enat (card {i. P (sdrop i \<omega>)})"
    and ev_alw_not_HLD_finite: "finite {i. P (sdrop i \<omega>)}"
  using assms
proof (induction \<omega>)
  case (step \<omega>)
  have eq: "{i. P (sdrop i \<omega>)} = (if P \<omega> then {0} else {}) \<union> (Suc ` {i. P (sdrop i (stl \<omega>))})"
    apply (intro set_eqI)
    apply (case_tac x)
    apply (auto simp: image_iff)
    done
  { case 1 show ?case
      using step unfolding eq by (auto simp: scount_simps card_image zero_notin_Suc_image eSuc_enat) }
  { case 2 show ?case
      using step unfolding eq by auto }
next
   case (base \<omega>)
   then have [simp]: "{i. P (sdrop i \<omega>)} = {}"
     by (simp add: not_HLD alw_iff_sdrop)
   { case 1 show ?case using base by (simp add: scount_eq_0I enat_0) }
   { case 2 show ?case by simp }
qed

lemma scount_finite: "ev (alw (not P)) \<omega> \<Longrightarrow> scount P \<omega> < \<infinity>"
  using scount_eq_card[of P \<omega>] by auto

lemma scount_infinite:
  "alw (ev P) \<omega> \<Longrightarrow> scount P \<omega> = \<infinity>"
proof (coinduction arbitrary: \<omega> rule: enat_coinduct)
  case (Eq_enat \<omega>)
  then have "ev P \<omega>" "alw (ev P) \<omega>"
    by auto
  then show ?case
    by (induction rule: ev_induct_strong) (auto simp add: scount_simps)
qed

lemma scount_infinite_iff: "scount P \<omega> = \<infinity> \<longleftrightarrow> alw (ev P) \<omega>"
  by (metis enat_ord_simps(4) not_alw_not scount_finite scount_infinite)

lemma scount_eq:
  "scount P \<omega> = (if alw (ev P) \<omega> then \<infinity> else enat (card {i. P (sdrop i \<omega>)}))"
  by (auto simp: scount_infinite_iff scount_eq_card not_alw_iff not_ev_iff)

subsection \<open> First index of an element \<close>

partial_function (gfp) sfirst :: "('s stream \<Rightarrow> bool) \<Rightarrow> 's stream \<Rightarrow> enat" where
  "sfirst P \<omega> = (if P \<omega> then 0 else eSuc (sfirst P (stl \<omega>)))"

lemma sfirst_eq_0: "sfirst P \<omega> = 0 \<longleftrightarrow> P \<omega>"
  by (subst sfirst.simps) auto

lemma sfirst_0[simp]: "P \<omega> \<Longrightarrow> sfirst P \<omega> = 0"
  by (subst sfirst.simps) auto

lemma sfirst_eSuc[simp]: "\<not> P \<omega> \<Longrightarrow> sfirst P \<omega> = eSuc (sfirst P (stl \<omega>))"
  by (subst sfirst.simps) auto

lemma less_sfirstD:
  fixes n :: nat
  assumes "enat n < sfirst P \<omega>" shows "\<not> P (sdrop n \<omega>)"
  using assms
proof (induction n arbitrary: \<omega>)
  case (Suc n) then show ?case
    by (auto simp: sfirst.simps[of _ \<omega>] eSuc_enat[symmetric] split: if_split_asm)
qed (simp add: enat_0 sfirst_eq_0)

lemma sfirst_finite: "sfirst P \<omega> < \<infinity> \<longleftrightarrow> ev P \<omega>"
proof
  assume "sfirst P \<omega> < \<infinity>"
  then obtain n where "sfirst P \<omega> = enat n" by auto
  then show "ev P \<omega>"
  proof (induction n arbitrary: \<omega>)
    case (Suc n) then show ?case
      by (auto simp add: eSuc_enat[symmetric] sfirst.simps[of P \<omega>] split: if_split_asm)
  qed (auto simp add: enat_0 sfirst_eq_0)
next
  assume "ev P \<omega>" then show "sfirst P \<omega> < \<infinity>"
    by (induction rule: ev_induct_strong) (auto simp: eSuc_enat)
qed

lemma sfirst_Stream: "sfirst P (s ## x) = (if P (s ## x) then 0 else eSuc (sfirst P x))"
  by (subst sfirst.simps) (simp add: HLD_iff)

lemma less_sfirst_iff: "(not P until (alw P)) \<omega> \<Longrightarrow> enat n < sfirst P \<omega> \<longleftrightarrow> \<not> P (sdrop n \<omega>)"
proof (induction n arbitrary: \<omega>)
  case 0 then show ?case
    by (simp add: enat_0 sfirst_eq_0 HLD_iff)
next
  case (Suc n)
  from Suc.prems have **: "P \<omega> \<Longrightarrow> P (stl \<omega>)"
    by (auto elim: UNTIL.cases)
  have *: "\<not> P (sdrop n (stl \<omega>)) \<longleftrightarrow> enat n < sfirst P (stl \<omega>)"
    using Suc.prems by (intro Suc.IH[symmetric]) (auto intro: UNTIL.intros elim: UNTIL.cases)
  show ?case
    unfolding sdrop.simps * by (cases "P \<omega>") (simp_all add: ** eSuc_enat[symmetric])
qed

lemma sfirst_eq_Inf: "sfirst P \<omega> = Inf {enat i | i. P (sdrop i \<omega>)}"
proof (rule antisym)
  show "sfirst P \<omega> \<le> \<Sqinter>{enat i |i. P (sdrop i \<omega>)}"
  proof (safe intro!: Inf_greatest)
    fix \<omega> i assume "P (sdrop i \<omega>)" then show "sfirst P \<omega> \<le> enat i"
    proof (induction i arbitrary: \<omega>)
      case (Suc i) then show ?case
       by (auto simp add: sfirst.simps[of P \<omega>] eSuc_enat[symmetric])
    qed auto
  qed
  show "\<Sqinter>{enat i |i. P (sdrop i \<omega>)} \<le> sfirst P \<omega>"
  proof (induction arbitrary: \<omega> rule: sfirst.fixp_induct)
    case (3 f)
    have "{enat i |i. P (sdrop i \<omega>)} = (if P \<omega> then {0} else {}) \<union> eSuc ` {enat i |i. P (sdrop i (stl \<omega>))}"
      apply (intro set_eqI)
      apply (case_tac x rule: enat_coexhaust)
      apply (auto simp add: enat_0_iff image_iff eSuc_enat_iff)
      done
    with 3[of "stl \<omega>"] show ?case
      by (auto simp: inf.absorb1 eSuc_Inf[symmetric])
  qed simp_all
qed

lemma sfirst_eq_enat_iff: "sfirst P \<omega> = enat n \<longleftrightarrow> ev_at P n \<omega>"
  by (induction n arbitrary: \<omega>)
     (simp_all add: eSuc_enat[symmetric] sfirst.simps enat_0)

subsection {* @{text stakeWhile} *}

definition stakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'a llist"
where "stakeWhile P xs = ltakeWhile P (llist_of_stream xs)"

lemma stakeWhile_SCons [simp]:
  "stakeWhile P (x ## xs) = (if P x then LCons x (stakeWhile P xs) else LNil)"
by(simp add: stakeWhile_def LCons_llist_of_stream[symmetric] del: LCons_llist_of_stream)

lemma lnull_stakeWhile [simp]: "lnull (stakeWhile P xs) \<longleftrightarrow> \<not> P (shd xs)"
by(simp add: stakeWhile_def)

lemma lhd_stakeWhile [simp]: "P (shd xs) \<Longrightarrow> lhd (stakeWhile P xs) = shd xs"
by(simp add: stakeWhile_def)

lemma ltl_stakeWhile [simp]:
  "ltl (stakeWhile P xs) = (if P (shd xs) then stakeWhile P (stl xs) else LNil)"
by(simp add: stakeWhile_def)

lemma stakeWhile_K_False [simp]: "stakeWhile (\<lambda>_. False) xs = LNil"
by(simp add: stakeWhile_def)

lemma stakeWhile_K_True [simp]: "stakeWhile (\<lambda>_. True) xs = llist_of_stream xs"
by(simp add: stakeWhile_def)

lemma stakeWhile_smap: "stakeWhile P (smap f xs) = lmap f (stakeWhile (P \<circ> f) xs)"
by(simp add: stakeWhile_def ltakeWhile_lmap[symmetric] del: o_apply)

lemma lfinite_stakeWhile [simp]: "lfinite (stakeWhile P xs) \<longleftrightarrow> (\<exists>x\<in>sset xs. \<not> P x)"
by(simp add: stakeWhile_def lfinite_ltakeWhile)

end
