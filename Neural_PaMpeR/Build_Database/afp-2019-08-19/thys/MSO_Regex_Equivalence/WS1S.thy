(* Author: Dmitriy Traytel *)

section \<open>WS1S\<close>

(*<*)
theory WS1S
imports Formula Pi_Regular_Operators "HOL-Library.Stream"
begin
(*>*)

subsection \<open>Encodings\<close>

definition "cut_same x s = stake (LEAST n. sdrop n s = sconst x) s"

abbreviation "poss I \<equiv> (\<Union>x\<in>set I. case x of Inl p \<Rightarrow> {p} | Inr P \<Rightarrow> P)"

declare smap_sconst[simp]

lemma (in wellorder) min_Least:
  "\<lbrakk>\<exists>n. P n; \<exists>n. Q n\<rbrakk> \<Longrightarrow> min (Least P) (Least Q) = (LEAST n. P n \<or> Q n)"
proof (intro sym[OF Least_equality])
  fix y assume "P y \<or> Q y"
  thus "min (Least P) (Least Q) \<le> y"
  proof (elim disjE)
    assume "P y"
    hence "Least P \<le> y" by (auto intro: LeastI2_wellorder)
    thus "min (Least P) (Least Q) \<le> y" unfolding min_def by auto
  next
    assume "Q y"
    hence "Least Q \<le> y" by (auto intro: LeastI2_wellorder)
    thus "min (Least P) (Least Q) \<le> y" unfolding min_def by auto
  qed
qed (metis LeastI_ex min_def)

lemma sconst_collapse: "y ## sconst y = sconst y"
  by (subst (2) siterate.ctr) auto

lemma shift_sconst_inj: "\<lbrakk>length x = length y; x @- sconst z = y @- sconst z\<rbrakk> \<Longrightarrow> x = y"
  by (induct rule: list_induct2) auto

context formula
begin

definition "any \<equiv> hd \<Sigma>"

lemma any_\<Sigma>[simp]: "any \<in> set \<Sigma>"
  unfolding any_def by (auto simp: nonempty intro: someI[of _ "hd \<Sigma>"])

lemma any_\<sigma>[simp]: "length bs = n \<Longrightarrow> (any, bs) \<in> set (\<sigma> \<Sigma> n)"
  by (auto simp: \<sigma>_def set_n_lists)

fun stream_enc :: "'a interp \<Rightarrow> ('a \<times> bool list) stream" where
  "stream_enc (w, I) = smap2 (enc_atom I) nats (w @- sconst any)"

lemma tl_stream_enc[simp]: "smap \<pi> (stream_enc (w, x # I)) = stream_enc (w, I)"
  by (auto simp: comp_def \<pi>_def)

lemma enc_atom_max: "\<lbrakk>\<forall>x\<in>set I. case x of Inl p \<Rightarrow> p \<le> n | Inr P \<Rightarrow> \<forall>p\<in>P. p \<le> n; n \<le> n'\<rbrakk> \<Longrightarrow>
  enc_atom I (Suc n') a = (a, replicate (length I) False)"
  by (induct I) (auto split: sum.splits)

lemma ex_Loop_stream_enc:
assumes "\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True"
shows "\<exists>n. sdrop n (stream_enc (w, I)) = sconst (any, replicate (length I) False)"
proof -
  from assms have "\<exists>n > length w. \<forall>x\<in>set I. case x of Inl p \<Rightarrow> p \<le> n | Inr P \<Rightarrow> \<forall>p\<in>P. p \<le> n"
  proof (induct I)
    case (Cons x I)
    then obtain n where IH: "length w < n"
      "\<forall>x\<in>set I. case x of Inl p \<Rightarrow> p \<le> n | Inr P \<Rightarrow> \<forall>p\<in>P. p \<le> n" by auto
    thus ?case
    proof (cases x)
      case (Inl p)
      with IH show ?thesis
        by (intro exI[of _ "max p n"]) (fastforce split: sum.splits)
    next
      case (Inr P)
      with IH Cons(2) show ?thesis
        by (intro exI[of _ "max (Max P) n"]) (fastforce dest: Max_ge split: sum.splits)
    qed
  qed auto
  then obtain n where "length w < n" "\<forall>x\<in>set I. case x of Inl p \<Rightarrow> p \<le> n | Inr P \<Rightarrow> \<forall>p\<in>P. p \<le> n"
    by (elim exE conjE)
  hence "sdrop (Suc n) (stream_enc (w, I)) = sconst (any, replicate (length I) False)"
    (is "?s1 n = ?s2")
    by (intro stream.coinduct[of "\<lambda>s1 s2. \<exists>n'\<ge> n. s1 = ?s1 n' \<and> s2 = ?s2"])
      (auto simp: enc_atom_max dest: le_SucI)
  thus ?thesis by blast
qed

lemma length_snth_enc[simp]: "length (snd (stream_enc (w, I) !! n)) = length I"
  by auto

lemma sset_singleton[simp]: "sset s \<subseteq> {x} \<longleftrightarrow> sset s = {x}"
  by (cases s) auto

lemma drop_sconstE: "\<lbrakk>drop n w @- sconst y = sconst y; p < length w; \<not> p < n\<rbrakk> \<Longrightarrow> w ! p = y"
unfolding not_less sconst_alt proof (induct p arbitrary: w n)
  case (Suc p)
  with Suc(1)[of 0 "tl w"] show ?case
    by (cases w n rule: list.exhaust[case_product nat.exhaust]) auto
qed (auto simp add: neq_Nil_conv)

lemma less_length_cut_same:
  "\<lbrakk>(w @- sconst y) !! p = a\<rbrakk> \<Longrightarrow> a = y \<or> (p < length (cut_same y (w @- sconst y)) \<and> w ! p = a)"
  unfolding cut_same_def length_stake
  by (rule LeastI2_ex[OF exI[of _ "length w"]])
    (auto simp: sdrop_shift shift_snth split: if_split_asm elim!: drop_sconstE)

lemma less_length_cut_same_Inl:
  "\<lbrakk>(\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True); r < length I; I ! r = Inl p\<rbrakk> \<Longrightarrow>
  p < length (cut_same (any, replicate (length I) False) (stream_enc (w, I)))"
  unfolding cut_same_def length_stake
  by (erule LeastI2_ex[OF ex_Loop_stream_enc ccontr],
    auto simp: smap2_alt list_eq_iff_nth_eq add.commute dest!: add_diff_inverse split: sum.splits,
    metis)

lemma less_length_cut_same_Inr:
  "\<lbrakk>(\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True); r < length I; I ! r = Inr P\<rbrakk> \<Longrightarrow>
  \<forall>p \<in> P. p < length (cut_same (any, replicate (length I) False) (stream_enc (w, I)))"
  unfolding cut_same_def length_stake
  by (rule ballI, erule LeastI2_ex[OF ex_Loop_stream_enc ccontr],
    auto simp: smap2_alt list_eq_iff_nth_eq add.commute dest!: add_diff_inverse split: sum.splits,
    metis)

fun enc :: "'a interp \<Rightarrow> ('a \<times> bool list) list set" where
  "enc (w, I) = {x. \<exists>n. x = (cut_same (any, replicate (length I) False) (stream_enc (w, I)) @
     replicate n (any, replicate (length I) False))}"

lemma cut_same_all[simp]: "cut_same x (sconst x) = []"
  unfolding cut_same_def by (auto intro: Least_equality)

lemma cut_same_stop[simp]:
  assumes "x \<noteq> y"
  shows "cut_same x (xs @- y ## sconst x) = xs @ [y]" (is "cut_same x ?s = _")
proof -
  have "(LEAST n. sdrop n ?s = sconst x) = Suc (length xs)"
  proof (rule Least_equality)
    show "sdrop (Suc (length xs)) ?s = sconst x" by (auto simp: sdrop_shift)
  next
    fix m assume *: "sdrop m ?s = sconst x"
    { assume "m < Suc (length xs)"
      hence "m \<le> length xs" by simp
      then obtain ys where "sdrop m ?s = ys @- y ## sconst x"
        by atomize_elim (induct m arbitrary: xs, auto)
      with * obtain "ys @- y ## sconst x = sconst x" by simp
      from arg_cong[OF this, of "sdrop (length ys)"] have "y ## sconst x = sconst x"
        by (auto simp: sdrop_shift)
      with assms have False by (metis siterate.code stream.inject)
    }
    thus "Suc (length xs) \<le> m" by (blast intro: leI)
  qed
  thus ?thesis unfolding cut_same_def stake_shift by simp
qed

lemma cut_same_shift_sconst: "\<exists>n. w = cut_same x (w @- sconst x) @ replicate n x"
proof (induct w rule: rev_induct)
  case (snoc a w)
  then obtain n where "w = cut_same x (w @- sconst x) @ replicate n x" by blast
  thus ?case
    by (cases "a = x")
     (auto simp: id_def[symmetric] siterate.code[of id, simplified id_apply, symmetric]
      replicate_append_same[symmetric] intro!: exI[of _ "Suc n"])
qed (simp add: id_def[symmetric])

lemma set_cut_same: "set (cut_same x (w @- sconst x)) \<subseteq> set w"
proof (induct w rule: rev_induct)
  case (snoc a w)
  thus ?case by (cases "a = x")
    (auto simp: id_def[symmetric] siterate.code[of id, simplified id_apply, symmetric])
qed  (simp add: id_def[symmetric])

lemma stream_enc_cut_same:
  assumes "(\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True)"
  shows "stream_enc (w, I) = cut_same (any, replicate (length I) False) (stream_enc (w, I)) @-
    sconst (any, replicate (length I) False)"
  unfolding cut_same_def
  by (rule trans[OF sym[OF stake_sdrop] arg_cong2[of _ _ _ _ "(@-)", OF refl]])
     (rule LeastI_ex[OF ex_Loop_stream_enc[OF assms]])

lemma stream_enc_enc:
  assumes "(\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True)" and  v: "v \<in> enc (w, I)"
  shows "stream_enc (w, I) = v @- sconst (any, replicate (length I) False)"
  (is "?s = ?v @- sconst ?F")
proof -
  from assms(1) obtain n where "sdrop n (stream_enc (w, I)) = sconst ?F" by (metis ex_Loop_stream_enc)
  moreover from v obtain m where "?v = cut_same ?F ?s @ replicate m ?F" by auto
  ultimately show "?s = v @- sconst ?F"
    by (auto simp del: stream_enc.simps intro: stream_enc_cut_same[OF assms(1)])
qed

lemma stream_enc_enc_some:
  assumes "(\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True)"
  shows "stream_enc (w, I) = (SOME v. v \<in> enc (w, I)) @- sconst (any, replicate (length I) False)"
  by (rule stream_enc_enc[OF assms], rule someI_ex) auto

lemma enc_unique_length: "v \<in> enc (w, I) \<Longrightarrow> \<forall>v'. length v' = length v \<and> v' \<in> enc (w, I) \<longrightarrow> v = v'"
  by auto

lemma sdrop_sconst: "sdrop n s = sconst x \<Longrightarrow> n \<le> m \<Longrightarrow> s !! m = x"
  by (metis le_iff_add sdrop_snth snth_siterate[of id, simplified id_funpow id_apply])

lemma fin_cut_same_tl:
  assumes "\<exists>n. sdrop n s = sconst x" 
  shows "fin_cut_same (\<pi> x) (map \<pi> (cut_same x s)) = cut_same (\<pi> x) (smap \<pi> s)"
proof -
  define min where "min = (LEAST n. sdrop n s = sconst x)"
  from assms have min: "sdrop min s = sconst x" "\<And>m. sdrop m s = sconst x \<Longrightarrow> min \<le> m"
    unfolding min_def by (auto intro: LeastI Least_le)
  have Ex: "\<exists>n. drop n (map \<pi> (stake min s)) = replicate (length (map \<pi> (stake min s)) - n) (\<pi> x)"
    by (auto intro: exI[of _ "length (map \<pi> (stake min s))"])
  have "fin_cut_same (\<pi> x) (map \<pi> (cut_same x s)) =
     map \<pi> (stake  (LEAST n.
       map \<pi> (stake (min - n) (sdrop n s)) = replicate (min - n) (\<pi> x) \<or> sdrop n s = sconst x) s)"
    unfolding fin_cut_same_def cut_same_def take_map take_stake min_Least[OF Ex assms, folded min_def]
      min_def[symmetric] by (auto simp: drop_map drop_stake)
  also have "(\<lambda>n. map \<pi> (stake (min - n) (sdrop n s)) = replicate (min - n) (\<pi> x) \<or> sdrop n s = sconst x) =
     (\<lambda>n. smap \<pi> (sdrop n s) = sconst (\<pi> x))"
  proof (rule ext, unfold smap_alt snth_siterate[of id, simplified id_funpow id_apply], safe)
    fix n m
    assume "map \<pi> (stake (min - n) (sdrop n s)) = replicate (min - n) (\<pi> x)"
    hence "\<forall>y\<in>set (stake (min - n) (sdrop n s)). \<pi> y = \<pi> x"
      by (intro iffD1[OF map_eq_conv]) (metis length_stake map_replicate_const)
    hence "\<forall>i<min - n. \<pi> (sdrop n s !! i) = \<pi> x"
      unfolding all_set_conv_all_nth by (auto simp: sdrop_snth)
    thus "\<pi> (sdrop n s !! m) = \<pi> x"
    proof (cases "m < min - n")
      case False
      hence "min \<le> n + m" by linarith
      hence "sdrop n s !! m = x" unfolding sdrop_snth by (rule sdrop_sconst[OF min(1)])
      thus ?thesis by simp
    qed auto
  next
    fix n
    assume "\<forall>m. \<pi> (sdrop n s !! m) = \<pi> x"
    thus "map \<pi> (stake (min - n) (sdrop n s)) = replicate (min - n) (\<pi> x)"
      unfolding stake_smap[symmetric] smap_alt[symmetric, of \<pi> "sdrop n s" "sconst (\<pi> x)", simplified]
        by (auto simp: map_replicate_const)
  qed auto
  finally show ?thesis unfolding cut_same_def sdrop_smap stake_smap .
qed

lemma tl_enc[simp]:
  assumes "\<forall>x \<in> set (x # I). case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True"
  shows "SAMEQUOT (any, replicate (length I) False) (map \<pi> ` enc (w, x # I)) = enc (w, I)"
  unfolding SAMEQUOT_def
  by (fastforce simp: assms \<pi>_def
    fin_cut_same_tl[OF ex_Loop_stream_enc[OF assms], unfolded \<pi>_def, simplified, symmetric])

lemma encD:
  "\<lbrakk>v \<in> enc (w, I); (\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True)\<rbrakk> \<Longrightarrow>
  v = map (case_prod (enc_atom I)) (zip [0 ..< length v] (stake (length v) (w @- sconst any)))"
  by (erule box_equals[OF sym[OF arg_cong[of _ _ "stake (length v)" ,OF stream_enc_enc]]])
   (auto simp: stake_shift sdrop_shift stake_add[symmetric] map_replicate_const)

lemma enc_Inl: "\<lbrakk>x \<in> enc (w, I); (\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True);
  m < length I; I ! m = Inl p\<rbrakk> \<Longrightarrow> p < length x \<and> snd (x ! p) ! m"
  by (auto dest!: less_length_cut_same_Inl[of _ _ _ w] simp: nth_append cut_same_def)

lemma enc_Inr: assumes "x \<in> enc (w, I)" "\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True"
  "M < length I" "I ! M = Inr P"
  shows "p \<in> P \<longleftrightarrow> p < length x \<and> snd (x ! p) ! M"
proof
  assume "p \<in> P" with assms show "p < length x \<and> snd (x ! p) ! M"
    by (auto dest!: less_length_cut_same_Inr[of _ _ _ w] simp: nth_append cut_same_def)
next
  assume "p < length x \<and> snd (x ! p) ! M"
  thus "p \<in> P" using assms by (subst (asm) (2) encD[OF assms(1,2)]) auto
qed

lemma enc_length:
  assumes "enc (w, I) = enc (w', I')"
  shows "length I = length I'"
proof -
  let ?cL = "\<lambda>w I. cut_same (any, replicate (length I) False) (stream_enc (w, I))"
  let ?w = "\<lambda>w I m. ?cL w I @ replicate (m - length (?cL w I)) (any, replicate (length I) False)"
  let ?max = "max (length (?cL w I)) (length (?cL w' I')) + 1"
  from assms have "?w w I ?max \<in> enc (w, I)" "?w w' I' ?max \<in> enc (w', I')" by auto
  hence "?w w I ?max = ?w w' I' ?max" using enc_unique_length assms by (simp del: enc.simps)
  moreover have "last (?w w I ?max) = (any, replicate (length I) False)"
                "last (?w w' I' ?max) = (any, replicate (length I') False)" by auto
  ultimately show "length I = length I'" by auto
qed

lemma enc_stream_enc: 
  "\<lbrakk>(\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True);
    (\<forall>x \<in> set I'. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True); 
    enc (w, I) = enc (w', I')\<rbrakk> \<Longrightarrow> stream_enc (w, I) = stream_enc (w', I')"
  by (rule box_equals[OF _ sym[OF stream_enc_enc_some] sym[OF stream_enc_enc_some]])
    (auto dest: enc_length simp del: enc.simps)

abbreviation "wf_interp w I \<equiv>
  ((\<forall>a \<in> set w. a \<in> set \<Sigma>) \<and> (\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True))"

fun wf_interp_for_formula :: "'a interp \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "wf_interp_for_formula (w, I) \<phi> =
    (wf_interp w I \<and>
     (\<forall>n \<in> FOV \<phi>. case I ! n of Inl _ \<Rightarrow> True | _ \<Rightarrow> False) \<and>
     (\<forall>n \<in> SOV \<phi>. case I ! n of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True))"

fun satisfies :: "'a interp \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "(w, I) \<Turnstile> FQ a m = ((case I ! m of Inl p \<Rightarrow> if p < length w then w ! p else any) = a)"
| "(w, I) \<Turnstile> FLess m1 m2 = ((case I ! m1 of Inl p \<Rightarrow> p) < (case I ! m2 of Inl p \<Rightarrow> p))"
| "(w, I) \<Turnstile> FIn m M = ((case I ! m of Inl p \<Rightarrow> p) \<in> (case I ! M of Inr P \<Rightarrow> P))"
| "(w, I) \<Turnstile> FNot \<phi> = (\<not> (w, I) \<Turnstile> \<phi>)"
| "(w, I) \<Turnstile> (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = ((w, I) \<Turnstile> \<phi>\<^sub>1 \<or> (w, I) \<Turnstile> \<phi>\<^sub>2)"
| "(w, I) \<Turnstile> (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = ((w, I) \<Turnstile> \<phi>\<^sub>1 \<and> (w, I) \<Turnstile> \<phi>\<^sub>2)"
| "(w, I) \<Turnstile> (FExists \<phi>) = (\<exists>p. (w, Inl p # I) \<Turnstile> \<phi>)"
| "(w, I) \<Turnstile> (FEXISTS \<phi>) = (\<exists>P. finite P \<and> (w, Inr P # I) \<Turnstile> \<phi>)"

definition lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a \<times> bool list) list set" where
  "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi> = \<Union>{enc (w, I) | w I . length I = n \<and> wf_interp_for_formula (w, I) \<phi> \<and> (w, I) \<Turnstile> \<phi>}"

lemma encD_ex: "\<lbrakk>x \<in> enc (w, I); (\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True)\<rbrakk> \<Longrightarrow>
  \<exists>n. x = map (case_prod (enc_atom I)) (zip [0 ..< n] (stake n (w @- sconst any)))"
  by (auto dest!: encD simp del: enc.simps)

lemma enc_set_\<sigma>: "\<lbrakk>x \<in> enc (w, I); (\<forall>x \<in> set I. case x of Inr P \<Rightarrow> finite P | _ \<Rightarrow> True);
  length I = n; a \<in> set x; set w \<subseteq> set \<Sigma>\<rbrakk> \<Longrightarrow> a \<in> set (\<sigma> \<Sigma> n)"
  by (force dest: encD_ex intro: enc_atom_\<sigma> simp: in_set_zip shift_snth simp del: enc.simps)

definition "positions_in_row s i =
  Option.these (sset (smap2 (\<lambda>p (_, bs). if nth bs i then Some p else None) nats s))"

lemma positions_in_row: "positions_in_row s i = {p. snd (s !! p) ! i}"
  unfolding positions_in_row_def Option.these_def smap2_szip stream.set_map sset_range
  by (auto split: if_split_asm intro!: image_eqI[of _ the] split: prod.splits)

lemma positions_in_row_unique: "\<exists>!p. snd (s !! p) ! i \<Longrightarrow>
  the_elem (positions_in_row s i) = (THE p. snd (s !! p) ! i)"
  by (rule the1I2) (auto simp: the_elem_def positions_in_row)

lemma positions_in_row_nth: "\<exists>!p. snd (s !! p) ! i \<Longrightarrow>
  snd (s !! the_elem (positions_in_row s i)) ! i"
  unfolding positions_in_row_unique by (rule the1I2) auto

definition "dec_word s = cut_same any (smap fst s)"

lemma dec_word_stream_enc: "dec_word (stream_enc (w, I)) = cut_same any (w @- sconst any)"
  unfolding dec_word_def by (auto intro!: arg_cong[of _ _ "cut_same any"] simp: smap2_alt)

definition "stream_dec n FO (s :: ('a \<times> bool list) stream) = map (\<lambda>i.
  if i \<in> FO
  then Inl (the_elem (positions_in_row s i))
  else Inr (positions_in_row s i)) [0..<n]"

lemma stream_dec_Inl: "\<lbrakk>i \<in> FO; i < n\<rbrakk> \<Longrightarrow> \<exists>p. stream_dec n FO s ! i = Inl p"
  unfolding stream_dec_def using nth_map[of n "[0..<n]"] by auto

lemma stream_dec_not_Inr: "\<lbrakk>stream_dec n FO s ! i = Inr P; i \<in> FO; i < n\<rbrakk> \<Longrightarrow> False"
  unfolding stream_dec_def using nth_map[of n "[0..<n]"] by auto

lemma stream_dec_Inr: "\<lbrakk>i \<notin> FO; i < n\<rbrakk> \<Longrightarrow> \<exists>P. stream_dec n FO s ! i = Inr P"
  unfolding stream_dec_def using nth_map[of n "[0..<n]"] by auto

lemma stream_dec_not_Inl: "\<lbrakk>stream_dec n FO s ! i = Inl p; i \<notin> FO; i < n\<rbrakk> \<Longrightarrow> False"
  unfolding stream_dec_def using nth_map[of n "[0..<n]"] by auto

lemma Inr_dec_finite: "\<lbrakk>\<forall>i<n. finite {p. snd (s !! p) ! i}; Inr P \<in> set (stream_dec n FO s)\<rbrakk> \<Longrightarrow>
  finite P"
  unfolding stream_dec_def by (auto simp: positions_in_row)

lemma enc_atom_dec: 
  "\<lbrakk>\<forall>p. length (snd (s !! p)) = n; \<forall>i \<in> FO. i < n \<longrightarrow> (\<exists>!p. snd (s !! p) ! i); a = fst (s !! p)\<rbrakk> \<Longrightarrow>
   enc_atom (stream_dec n FO s) p a = s !! p"
  unfolding stream_dec_def
  by (rule sym, subst surjective_pairing[of "s !! p"])
    (auto intro!: nth_equalityI simp: positions_in_row simp del: prod.collapse split: if_split_asm,
    (metis positions_in_row positions_in_row_nth)+)

lemma length_stream_dec[simp]: "length (stream_dec n FO x) = n"
  unfolding stream_dec_def by auto

lemma stream_enc_dec:
  "\<lbrakk>\<exists>n. sdrop n (smap fst s) = sconst any;
   stream_all (\<lambda>x. length (snd x) = n) s; \<forall>i \<in> FO. (\<exists>!p. snd (s !! p) ! i)\<rbrakk> \<Longrightarrow>
   stream_enc (dec_word s, stream_dec n FO s) = s"
  unfolding dec_word_def
  by (drule LeastI_ex)
    (auto intro!: enc_atom_dec simp: smap2_alt cut_same_def
    simp del: stake_smap sdrop_smap
    intro!: trans[OF arg_cong2[of _ _ _ _ "(!!)"] snth_smap]
            trans[OF arg_cong2[of _ _ _ _ "(@-)"] stake_sdrop])

lemma stream_enc_unique: 
  "i < length I \<Longrightarrow> \<exists>p. I ! i = Inl p \<Longrightarrow> \<exists>!p. snd (stream_enc (w, I) !! p) ! i"
  by auto

lemma stream_dec_enc_Inl:
  "\<lbrakk>stream_dec n FO (stream_enc (w, I)) ! i = Inl p'; I ! i = Inl p; i \<in> FO; i < n; length I = n\<rbrakk> \<Longrightarrow>
  p = p'"
  unfolding stream_dec_def
  by (auto intro!: trans[OF _ sym[OF  positions_in_row_unique[OF stream_enc_unique]]]
    simp del: stream_enc.simps) simp

lemma stream_dec_enc_Inr:
  "\<lbrakk>stream_dec n FO (stream_enc (w, I)) ! i = Inr P'; I ! i = Inr P; i \<notin> FO; i < n; length I = n\<rbrakk> \<Longrightarrow>
  P = P'"
  unfolding stream_dec_def positions_in_row by auto

lemma Collect_snth: "{p. P ((x ## s) !! p)} \<subseteq> {0} \<union> Suc ` {p. P (s !! p)}"
  unfolding image_def by (auto simp: gr0_conv_Suc)

lemma finite_True_in_row: "\<forall>i < n. finite {p. snd ((w @- sconst (any, replicate n False)) !! p) ! i}"
  by (induct w) (auto simp: id_def[symmetric] intro: finite_subset[OF Collect_snth])

lemma lang_ENC:
 assumes "FO \<subseteq> {0 ..< n}" "SO \<subseteq> {0 ..< n} - FO"
 shows "lang n (ENC n FO) = \<Union>{enc (w, I) | w I . length I = n \<and> wf_interp w I \<and>
   (\<forall>i \<in> FO. case I ! i of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False) \<and>
   (\<forall>i \<in> SO. case I ! i of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)}"
   (is "?L = ?R")
proof (intro equalityI subsetI)
  fix x assume L: "x \<in> ?L"
  from assms(1) have fin: "finite FO" by (auto simp: finite_subset)
  have *: "set x \<subseteq> set (\<sigma> \<Sigma> n)" using subsetD[OF assms(1)]
    bspec[OF wf_lang_wf_word[OF wf_rexp_ENC[OF fin]] L]
    by (cases n) (auto simp: wf_word)
  let ?s = "x @- sconst (any, replicate n False)"
  from assms have "list_all (\<lambda>bs. length (snd bs) = n) x"
    using * by (auto simp: list_all_iff \<sigma>_def set_n_lists)
  hence "stream_all (\<lambda>x. length (snd x) = n) (x @- sconst (any, replicate n False))"
    by (auto simp only: stream_all_shift sset_sconst length_replicate snd_conv)
  moreover
  { fix m assume "m \<in> FO"
    with assms have "m < n" by (auto simp: max_idx_vars)
    with L \<open>m \<in> FO\<close> assms obtain u z v where uzv: "x = u @ z @ v"
      "u \<in> star (lang n (Atom (Arbitrary_Except m False)))"
      "z \<in> lang n (Atom (Arbitrary_Except m True))"
      "v \<in> star (lang n (Atom (Arbitrary_Except m False)))" unfolding ENC_def
      by (cases n)
       (auto simp: not_less max_idx_vars valid_ENC_def fin intro!: wf_rexp_valid_ENC finite_FOV
        dest!: iffD1[OF lang_flatten_INTERSECT, rotated -1], fast)
    with \<open>m < n\<close> have "\<exists>!p.  snd (x ! p) ! m \<and> p < length x"
    proof (intro ex1I[of _ "length u"])
      fix p assume "m < n" "snd (x ! p) ! m \<and> p < length x"
      with star_Arbitrary_ExceptD[OF uzv(2)] Arbitrary_ExceptD[OF uzv(3)] star_Arbitrary_ExceptD[OF uzv(4)]
      show "p = length u" by (cases rule: linorder_cases) (auto simp: nth_append uzv(1))
    qed (auto dest!: Arbitrary_ExceptD)
    then obtain p where p: "p < length x" "snd (x ! p) ! m"
      "\<And>q. snd (x ! q) ! m \<and> q < length x \<longrightarrow> q = p" by auto
    from this(1,2) have "\<exists>!p. snd (?s !! p) ! m"
    proof (intro ex1I[of _ p])
      fix q from p(1,2) p(3)[of q] \<open>m < n\<close> show "snd (?s !! q) ! m \<Longrightarrow> q = p"
        by (cases "q < length x")  auto
    qed auto
  }
  moreover have "sdrop (length x) (smap fst (x @- sconst (any, replicate n False))) = sconst any"
    unfolding sdrop_smap by (simp add: sdrop_shift)
  ultimately have enc_dec: "stream_enc (dec_word ?s, stream_dec n FO ?s) =
    x @- sconst (any, replicate n False)" by (intro stream_enc_dec) auto
  define I where "I = stream_dec n FO ?s"
  with assms have "wf_interp (dec_word ?s) I \<and>
   (\<forall>i \<in> FO. case I ! i of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False) \<and>
   (\<forall>i \<in> SO. case I ! i of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)" unfolding I_def dec_word_def
    by (auto dest: stream_dec_not_Inr stream_dec_not_Inl simp: \<sigma>_def  max_idx_vars
      dest!: subsetD[OF set_cut_same[of any "map fst x"]] subsetD[OF *]  split: sum.splits)
      (auto simp: stream_dec_def positions_in_row finite_True_in_row)
  moreover have "length I = n" unfolding I_def by simp
  moreover have "x \<in> enc (dec_word ?s, I)" unfolding I_def
    by (simp add: enc_dec cut_same_shift_sconst del: stream_enc.simps)
  ultimately show "x \<in> ?R" by blast
next
  fix x assume "x \<in> ?R"
  then obtain w I where I: "x \<in> enc (w, I)" "wf_interp w I \<and>
   (\<forall>i \<in> FO. case I ! i of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False) \<and>
   (\<forall>i \<in> SO. case I ! i of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)" "length I = n" by blast
  { fix i from I(2) have "(w @- sconst any) !! i \<in> set \<Sigma>" by (cases "i < length w") auto } note * = this
  from I have "x @- sconst (any, replicate (length I) False) = stream_enc (w, I)" (is "x @- ?F = ?s")
    by (intro stream_enc_enc[symmetric]) auto
  with * \<open>length I = n\<close> have "\<forall>x \<in> set x. length (snd x) = n \<and> fst x \<in> set \<Sigma>"
    by (auto dest!: shift_snth_less[of _ _ ?F, symmetric] simp: in_set_conv_nth)
  thus "x \<in> ?L"
  proof (cases "FO = {}")
    case False
    hence nonempty: "valid_ENC n ` FO \<noteq> {}" by simp
    have finite: "finite (valid_ENC n ` FO)" by (rule finite_imageI[OF finite_subset[OF assms(1)]]) simp
    from False assms(1) have "0 < n" by (cases n) (auto split: dest!: max_idx_vars)
    with wf_rexp_valid_ENC assms have wf_rexp: "\<forall>x \<in> valid_ENC n ` FO. wf n x"
      by (auto simp: max_idx_vars)
    { fix r assume "r \<in> FO"
      with I(2) obtain p where p: "I ! r = Inl p" by (cases "I ! r") auto
      from \<open>r \<in> FO\<close> assms I(2,3) have r: "r < length I" by (auto dest!: max_idx_vars)
      from p I(1,2) r have "p < length x"
        using less_length_cut_same_Inl[of I r p w] by auto
      with p I r *
        have "[x ! p] \<in> lang n (Atom (Arbitrary_Except r True))"
          by (subst encD[of x w I]) (auto simp del: lang.simps intro!: enc_atom_lang_Arbitrary_Except_True)
      moreover
      from p I r * have "take p x \<in> star (lang n (Atom (Arbitrary_Except r False)))"
        by (subst encD[of x]) (auto  simp del: lang.simps simp: in_set_conv_nth intro!: Ball_starI enc_atom_lang_Arbitrary_Except_False)
      moreover
      from p I r * have "drop (Suc p) x \<in> star (lang n (Atom (Arbitrary_Except r False)))"
        by (subst encD[of x]) (auto simp: in_set_conv_nth simp del: lang.simps snth.simps intro!: Ball_starI enc_atom_lang_Arbitrary_Except_False)
      ultimately have "take p x @ [x ! p] @ drop (p + 1) x \<in> lang n (valid_ENC n r)"
        using \<open>0 < n\<close> unfolding valid_ENC_def by (auto simp del: append.simps)
      hence "x \<in> lang n (valid_ENC n r)" using id_take_nth_drop[OF \<open>p < length x\<close>] by auto
    }
    with False lang_flatten_INTERSECT[OF finite nonempty wf_rexp] show ?thesis by (auto simp: ENC_def)
  qed (simp add: ENC_def, auto simp: \<sigma>_def set_n_lists image_iff)
qed

lemma lang_ENC_formula:
  assumes "wf_formula n \<phi>"
  shows "lang n (ENC n (FOV \<phi>)) = \<Union>{enc (w, I) | w I . length I = n \<and> wf_interp_for_formula (w, I) \<phi>}"
proof -
  from assms max_idx_vars have *: "FOV \<phi> \<subseteq> {0 ..< n}" "SOV \<phi> \<subseteq> {0 ..< n} - FOV \<phi>" by auto
  show ?thesis unfolding lang_ENC[OF *] by simp
qed

subsection \<open>Welldefinedness of enc wrt. Models\<close>

lemma wf_interp_for_formula_FExists: 
 "\<lbrakk>wf_formula (length I) (FExists \<phi>)\<rbrakk>\<Longrightarrow>
  wf_interp_for_formula (w, I) (FExists \<phi>) \<longleftrightarrow> (\<forall>p. wf_interp_for_formula (w, Inl p # I) \<phi>)"
  by (auto simp: nth_Cons' split: if_split_asm)

lemma wf_interp_for_formula_any_Inl: "wf_interp_for_formula (w, Inl p # I) \<phi> \<Longrightarrow>
  \<forall>p. wf_interp_for_formula (w, Inl p # I) \<phi>"
  by (auto simp: nth_Cons' split: if_split_asm)

lemma wf_interp_for_formula_FEXISTS: 
 "\<lbrakk>wf_formula (length I) (FEXISTS \<phi>)\<rbrakk>\<Longrightarrow>
  wf_interp_for_formula (w, I) (FEXISTS \<phi>) \<longleftrightarrow> (\<forall>P. finite P \<longrightarrow> wf_interp_for_formula (w, Inr P # I) \<phi>)"
  by (auto simp: nth_Cons' split: if_split_asm)

lemma wf_interp_for_formula_any_Inr: "wf_interp_for_formula (w, Inr P # I) \<phi> \<Longrightarrow>
  \<forall>P. finite P \<longrightarrow> wf_interp_for_formula (w, Inr P # I) \<phi>"
  by (auto simp: nth_Cons' split: if_split_asm)

lemma wf_interp_for_formula_FOr:
  "wf_interp_for_formula (w, I) (FOr \<phi>1 \<phi>2) =
     (wf_interp_for_formula (w, I) \<phi>1 \<and> wf_interp_for_formula (w, I) \<phi>2)"
  by auto

lemma wf_interp_for_formula_FAnd:
  "wf_interp_for_formula (w, I) (FAnd \<phi>1 \<phi>2) =
     (wf_interp_for_formula (w, I) \<phi>1 \<and> wf_interp_for_formula (w, I) \<phi>2)"
  by auto

lemma enc_wf_interp: 
 "\<lbrakk>wf_formula (length I) \<phi>; wf_interp_for_formula (w, I) \<phi>; x \<in> enc (w, I)\<rbrakk> \<Longrightarrow>
  wf_interp_for_formula (dec_word (x @- sconst (any, replicate (length I) False)),
    stream_dec (length I) (FOV \<phi>) (x @- sconst (any, replicate (length I) False))) \<phi>"
  using
    stream_dec_Inl[of _ "FOV \<phi>" "length I" "stream_enc (w, I)", OF _ bspec[OF max_idx_vars]]
    stream_dec_Inr[of _ "FOV \<phi>" "length I" "stream_enc (w, I)", OF _ bspec[OF max_idx_vars]]
  by (auto split: sum.splits intro: Inr_dec_finite[OF finite_True_in_row] simp: max_idx_vars dec_word_def
    dest!: stream_dec_not_Inl stream_dec_not_Inr subsetD[OF set_cut_same] simp del: stream_enc.simps)
    (auto simp: cut_same_def in_set_zip smap2_alt shift_snth)

lemma enc_atom_welldef: "\<forall>x a. enc_atom I x a = enc_atom I' x a \<Longrightarrow> m < length I \<Longrightarrow>
  (case (I ! m, I' ! m) of (Inl p, Inl q) \<Rightarrow> p = q | (Inr P, Inr Q) \<Rightarrow> P = Q | _ \<Rightarrow> True)"
proof (induct "length I" arbitrary: I I' m)
  case (Suc n I I')
  then obtain x xs x' xs' where *: "I = x # xs" "I' = x' # xs'"
    by (fastforce simp: Suc_length_conv map_eq_Cons_conv)
  with Suc show ?case
  proof (cases m)
    case 0 thus ?thesis using Suc(3) unfolding *
      by (cases x x' rule: sum.exhaust[case_product sum.exhaust]) auto
  qed auto
qed simp

lemma stream_enc_welldef: "\<lbrakk>stream_enc (w, I) = stream_enc (w', I'); wf_formula (length I) \<phi>;
  wf_interp_for_formula (w, I) \<phi>; wf_interp_for_formula (w', I') \<phi>\<rbrakk> \<Longrightarrow>
  (w, I) \<Turnstile> \<phi> \<longleftrightarrow> (w', I') \<Turnstile> \<phi>"
proof (induction \<phi> arbitrary: w w' I I')
  case (FQ a m) thus ?case using enc_atom_welldef[of I I' m]
    by (simp split: sum.splits add: smap2_alt shift_snth)
      (metis snth_siterate[of id, simplified id_funpow id_apply])
next
  case (FLess m1 m2) thus ?case using enc_atom_welldef[of I I' m1] enc_atom_welldef[of I I' m2]
    by (auto split: sum.splits simp add: smap2_alt)
next
  case (FIn m M) thus ?case using enc_atom_welldef[of I I' m] enc_atom_welldef[of I I' M]
    by (auto split: sum.splits simp add: smap2_alt)
next
  case (FOr \<phi>1 \<phi>2) show ?case unfolding satisfies.simps(5)
  proof (intro disj_cong)
    from FOr(3-6) show "(w, I) \<Turnstile> \<phi>1 \<longleftrightarrow> (w', I') \<Turnstile> \<phi>1"
      by (intro FOr(1)) auto
  next
    from FOr(3-6) show "(w, I) \<Turnstile> \<phi>2 \<longleftrightarrow> (w', I') \<Turnstile> \<phi>2"
      by (intro FOr(2)) auto
  qed
next
  case (FAnd \<phi>1 \<phi>2) show ?case unfolding satisfies.simps(6)
  proof (intro conj_cong)
    from FAnd(3-6) show "(w, I) \<Turnstile> \<phi>1 \<longleftrightarrow> (w', I') \<Turnstile> \<phi>1"
      by (intro FAnd(1)) auto
  next
    from FAnd(3-6) show "(w, I) \<Turnstile> \<phi>2 \<longleftrightarrow> (w', I') \<Turnstile> \<phi>2"
      by (intro FAnd(2)) auto
  qed
next
  case (FExists \<phi>)
  hence length: "length I' = length I" by (metis length_snth_enc)
  show ?case
  proof
    assume "(w, I) \<Turnstile> FExists \<phi>"
    with FExists.prems(3) obtain p where "(w, Inl p # I) \<Turnstile> \<phi>" by auto
    moreover
    with FExists.prems(1,2) have "(w', Inl p # I') \<Turnstile> \<phi>"
    proof (intro iffD1[OF FExists.IH[of w "Inl p # I" w' "Inl p # I'"]])
      from FExists.prems(2,3) show "wf_interp_for_formula (w, Inl p # I) \<phi>"
        by (blast dest: wf_interp_for_formula_FExists[of I])
    next
      from FExists.prems(2,4) show "wf_interp_for_formula (w', Inl p # I') \<phi>"
        by (blast dest: wf_interp_for_formula_FExists[of I', unfolded length])
    qed (auto simp: smap2_alt split: sum.splits if_split_asm)
    ultimately show "(w', I') \<Turnstile> FExists \<phi>" by auto
  next
    assume "(w', I') \<Turnstile> FExists \<phi>"
    with FExists.prems(1,2,4) obtain p where "(w', Inl p # I') \<Turnstile> \<phi>" by auto
    moreover
    with FExists.prems(1,2) have "(w, Inl p # I) \<Turnstile> \<phi>"
    proof (intro iffD2[OF FExists.IH[of w "Inl p # I" w' "Inl p # I'"]])
      from FExists.prems(2,3) show "wf_interp_for_formula (w, Inl p # I) \<phi>"
        by (blast dest: wf_interp_for_formula_FExists[of I])
    next
      from FExists.prems(2,4) show "wf_interp_for_formula (w', Inl p # I') \<phi>"
        by (blast dest: wf_interp_for_formula_FExists[of I', unfolded length])
    qed (auto simp: smap2_alt split: sum.splits if_split_asm)
    ultimately show "(w, I) \<Turnstile> FExists \<phi>" by auto
  qed
next
  case (FEXISTS \<phi>)
  hence length: "length I' = length I" by (metis length_snth_enc)
  show ?case
  proof
    assume "(w, I) \<Turnstile> FEXISTS \<phi>"
    with FEXISTS.prems(3) obtain P where "finite P" "(w, Inr P # I) \<Turnstile> \<phi>" by auto
    moreover
    with FEXISTS.prems(1,2) have "(w', Inr P # I') \<Turnstile> \<phi>"
    proof (intro iffD1[OF FEXISTS.IH[of w "Inr P # I" w' "Inr P # I'"]])
      from FEXISTS.prems(2,3) \<open>finite P\<close> show "wf_interp_for_formula (w, Inr P # I) \<phi>"
        by (blast dest: wf_interp_for_formula_FEXISTS[of I])
    next
      from FEXISTS.prems(2,4) \<open>finite P\<close> show "wf_interp_for_formula (w', Inr P # I') \<phi>"
        by (blast dest: wf_interp_for_formula_FEXISTS[of I', unfolded length])
    qed (auto simp: smap2_alt split: sum.splits if_split_asm)
    ultimately show "(w', I') \<Turnstile> FEXISTS \<phi>" by auto
  next
    assume "(w', I') \<Turnstile> FEXISTS \<phi>"
    with FEXISTS.prems(1,2,4) obtain P where "finite P" "(w', Inr P # I') \<Turnstile> \<phi>" by auto
    moreover
    with FEXISTS.prems have "(w, Inr P # I) \<Turnstile> \<phi>"
    proof (intro iffD2[OF FEXISTS.IH[of w "Inr P # I" w' "Inr P # I'"]])
      from FEXISTS.prems(2,3) \<open>finite P\<close> show "wf_interp_for_formula (w, Inr P # I) \<phi>"
        by (blast dest: wf_interp_for_formula_FEXISTS[of I])
    next
      from FEXISTS.prems(2,4) \<open>finite P\<close> show "wf_interp_for_formula (w', Inr P # I') \<phi>"
        by (blast dest: wf_interp_for_formula_FEXISTS[of I', unfolded length])
    qed (auto simp: smap2_alt split: sum.splits if_split_asm)
    ultimately show "(w, I) \<Turnstile> FEXISTS \<phi>" by auto
  qed
qed auto

lemma lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_FOr:
  assumes "wf_formula n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)"
  shows "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq>
    (lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1 \<union> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2) \<inter> \<Union>{enc (w, I) | w I. length I = n \<and> wf_interp_for_formula (w, I) (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)}"
    (is "_ \<subseteq> (?L1 \<union> ?L2) \<inter> ?ENC")
proof (intro equalityI subsetI)
  fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)"
  then obtain w I where
    *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)" "length I = n" and
     "satisfies (w, I) \<phi>\<^sub>1 \<or> satisfies (w, I) \<phi>\<^sub>2" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
  thus "x \<in> (?L1 \<union> ?L2) \<inter> ?ENC"
  proof (elim disjE)
    assume "satisfies (w, I) \<phi>\<^sub>1"
    with * have "x \<in> ?L1" using assms unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by (fastforce simp del: enc.simps)
    with * show ?thesis by auto
  next
    assume "satisfies (w, I) \<phi>\<^sub>2"
    with * have "x \<in>?L2" using assms unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by (fastforce simp del: enc.simps)
    with * show ?thesis by auto
  qed
qed

lemma lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_FAnd:
  assumes "wf_formula n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)"
  shows "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq>
    lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1 \<inter> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2 \<inter> \<Union>{enc (w, I) | w I. length I = n \<and> wf_interp_for_formula (w, I) (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)}"
  using assms unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by (fastforce simp del: enc.simps)

subsection \<open>From WS1S to Regular expressions\<close>

fun rexp_of :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a atom) rexp" where
  "rexp_of n (FQ a m) =
    Inter (TIMES [rexp.Not Zero, Atom (AQ m a), rexp.Not Zero])
    (ENC n (FOV (FQ a m)))"
| "rexp_of n (FLess m1 m2) = (if m1 = m2 then Zero else
    Inter (TIMES [rexp.Not Zero, Atom (Arbitrary_Except m1 True),
      rexp.Not Zero, Atom (Arbitrary_Except m2 True),
      rexp.Not Zero]) (ENC n (FOV (FLess m1 m2 :: 'a formula))))"
| "rexp_of n (FIn m M) = 
    Inter (TIMES [rexp.Not Zero, Atom (Arbitrary_Except2 m M), rexp.Not Zero])
    (ENC n (FOV (FIn m M :: 'a formula)))"
| "rexp_of n (FNot \<phi>) = Inter (rexp.Not (rexp_of n \<phi>)) (ENC n (FOV (FNot \<phi>)))"
| "rexp_of n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = Inter (Plus (rexp_of n \<phi>\<^sub>1) (rexp_of n \<phi>\<^sub>2)) (ENC n (FOV (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)))"
| "rexp_of n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = INTERSECT [rexp_of n \<phi>\<^sub>1, rexp_of n \<phi>\<^sub>2, ENC n (FOV (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2))]"
| "rexp_of n (FExists \<phi>) = samequot_exec (any, replicate n False) (Pr (rexp_of (n + 1) \<phi>))"
| "rexp_of n (FEXISTS \<phi>) = samequot_exec (any, replicate n False) (Pr (rexp_of (n + 1) \<phi>))"

fun rexp_of_alt :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a atom) rexp" where
  "rexp_of_alt n (FQ a m) =
    TIMES [rexp.Not Zero, Atom (AQ m a), rexp.Not Zero]"
| "rexp_of_alt n (FLess m1 m2) = (if m1 = m2 then Zero else
    TIMES [rexp.Not Zero, Atom (Arbitrary_Except m1 True),
      rexp.Not Zero, Atom (Arbitrary_Except m2 True),
      rexp.Not Zero])"
| "rexp_of_alt n (FIn m M) = 
    TIMES [rexp.Not Zero, Atom (Arbitrary_Except2 m M), rexp.Not Zero]"
| "rexp_of_alt n (FNot \<phi>) = rexp.Not (rexp_of_alt n \<phi>)"
| "rexp_of_alt n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = Plus (rexp_of_alt n \<phi>\<^sub>1) (rexp_of_alt n \<phi>\<^sub>2)"
| "rexp_of_alt n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = Inter (rexp_of_alt n \<phi>\<^sub>1) (rexp_of_alt n \<phi>\<^sub>2)"
| "rexp_of_alt n (FExists \<phi>) = samequot_exec (any, replicate n False) (Pr (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (Suc n) (FOV \<phi>))))"
| "rexp_of_alt n (FEXISTS \<phi>) = samequot_exec (any, replicate n False) (Pr (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (Suc n) (FOV \<phi>))))"

definition "rexp_of' n \<phi> = Inter (rexp_of_alt n \<phi>) (ENC n (FOV \<phi>))"

fun rexp_of_alt' :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a atom) rexp" where
  "rexp_of_alt' n (FQ a m) = TIMES [Full, Atom (AQ m a), Full]"
| "rexp_of_alt' n (FLess m1 m2) = (if m1 = m2 then Zero else
    TIMES [Full, Atom (Arbitrary_Except m1 True), Full, Atom (Arbitrary_Except m2 True), Full])"
| "rexp_of_alt' n (FIn m M) = TIMES [Full, Atom (Arbitrary_Except2 m M), Full]"
| "rexp_of_alt' n (FNot \<phi>) = rexp.Not (rexp_of_alt' n \<phi>)"
| "rexp_of_alt' n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = Plus (rexp_of_alt' n \<phi>\<^sub>1) (rexp_of_alt' n \<phi>\<^sub>2)"
| "rexp_of_alt' n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = Inter (rexp_of_alt' n \<phi>\<^sub>1) (rexp_of_alt' n \<phi>\<^sub>2)"
| "rexp_of_alt' n (FExists \<phi>) = samequot_exec (any, replicate n False) (Pr (Inter (rexp_of_alt' (n + 1) \<phi>) (ENC (n + 1) {0})))"
| "rexp_of_alt' n (FEXISTS \<phi>) = samequot_exec (any, replicate n False) (Pr (rexp_of_alt' (n + 1) \<phi>))"

definition "rexp_of'' n \<phi> = Inter (rexp_of_alt' n \<phi>) (ENC n (FOV \<phi>))"

lemma enc_eqI:
  assumes "x \<in> enc (w, I)" "x \<in> enc (w', I')" "wf_interp_for_formula (w, I) \<phi>" "wf_interp_for_formula (w', I') \<phi>"
    "length I = length I'"
  shows "enc (w, I) = enc (w', I')"
proof -
  from assms have "stream_enc (w, I) = stream_enc (w', I')"
    by (intro box_equals[OF _ stream_enc_enc[symmetric] stream_enc_enc[symmetric]]) auto
  thus ?thesis using assms(5) by auto
qed

lemma enc_eq_welldef:
  "\<lbrakk>enc (w, I) = enc (w', I'); wf_formula (length I) \<phi>; wf_interp_for_formula (w, I) \<phi> ;wf_interp_for_formula (w', I') \<phi>\<rbrakk> \<Longrightarrow>
  (w, I) \<Turnstile> \<phi> \<longleftrightarrow> (w', I') \<Turnstile> \<phi>"
  by (intro stream_enc_welldef) (auto simp del: stream_enc.simps intro!: enc_stream_enc)

lemma enc_welldef:
  "\<lbrakk>x \<in> enc (w, I); x \<in> enc (w', I'); length I = length I'; wf_formula (length I) \<phi>;
  wf_interp_for_formula (w, I) \<phi> ;wf_interp_for_formula (w', I') \<phi>\<rbrakk> \<Longrightarrow>
  (w, I) \<Turnstile> \<phi> \<longleftrightarrow> (w', I') \<Turnstile> \<phi>"
  by (intro enc_eq_welldef[OF enc_eqI])

lemma wf_rexp_of: "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of n \<phi>)"
  by (induct \<phi> arbitrary: n)
    (auto intro!: wf_samequot_exec wf_rexp_ENC,
    auto simp: max_idx_vars finite_FOV)

theorem lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of: "wf_formula n \<phi> \<Longrightarrow> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi> = lang n (rexp_of n \<phi>)"
   (is "_ \<Longrightarrow> _ = ?L n \<phi>")
proof (induct \<phi> arbitrary: n)
  case (FQ a m)
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FQ a m)"
    then obtain w I where
      *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FQ a m)" "length I = n" "(w, I) \<Turnstile> FQ a m"
      unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by blast
    hence x_alt: "x = map (case_prod (enc_atom I)) (zip [0 ..< length x] (stake (length x) (w @- sconst any)))"
      by (intro encD) auto
    from FQ(1) *(2,4) obtain p where p: "I ! m = Inl p"
      by (auto simp: all_set_conv_all_nth split: sum.splits)
    with FQ(1) * have p_less: "p < length x"
      by (auto simp del: stream_enc.simps intro: trans_less_add1[OF less_length_cut_same_Inl])
    hence enc_atom: "x ! p = enc_atom I p ((w @- sconst any) !! p)" (is "_ = enc_atom _ _ ?p")
      by (subst x_alt, simp)
    with *(1) p_less(1) have "x = take p x @ [enc_atom I p ?p] @ drop (p + 1) x"
      using id_take_nth_drop[of p x] by auto
    moreover
    from *(2,3,4) FQ(1) p have "[enc_atom I p ?p] \<in> lang n (Atom (AQ m a))"
      by (auto simp del: lang.simps intro!: enc_atom_lang_AQ) 
    moreover from *(2,3) have "take p x \<in> lang n (rexp.Not Zero)"
      by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_takeD)
    moreover from *(2,3) have "drop (Suc p) x \<in> lang n (rexp.Not Zero)"
      by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_dropD)
    ultimately show "x \<in> ?L n (FQ a m)" using *(1,2,3)
      unfolding rexp_of.simps lang.simps(6,9) rexp_of_list.simps lang_ENC_formula[OF FQ]
      by (auto elim: ssubst simp del: o_apply append.simps lang.simps enc.simps)
  next
    fix x let ?x = "x @- sconst (any, replicate n False)"
    assume x: "x \<in> ?L n (FQ a m)"
    with FQ obtain w I where
      I: "x \<in> enc (w, I)" "length I = n" "wf_interp_for_formula (w, I) (FQ a m)"
      unfolding rexp_of.simps lang.simps lang_ENC_formula[OF FQ] by fastforce
    hence stream_enc: "stream_enc (w, I) = ?x" using stream_enc_enc by auto
    from I FQ obtain p where m: "I ! m = Inl p" "m < length I" by (auto split: sum.splits)
    with I have "wf_interp_for_formula (dec_word ?x, stream_dec n {m} ?x) (FQ a m)" unfolding I(1)
      using enc_wf_interp[OF FQ(1)[folded I(2)]] by auto
    moreover
    from x obtain u1 u u2 where "x = u1 @ u @ u2" "u \<in> lang n (Atom (AQ m a))"
      unfolding rexp_of.simps lang.simps rexp_of_list.simps using concE by fast
    with FQ(1) obtain v where v: "x = u1 @ [v] @ u2" "snd v ! m" "fst v = a"
      using AQ_D[of u n m a] by fastforce
    from v have u: "length u1 < length x" by auto
    { from v have "snd (x ! length u1) ! m" by auto
      moreover
      from m I have "p < length x" "snd (x ! p) ! m" by (auto dest: enc_Inl simp del: enc.simps)
      moreover
      from m I have ex1: "\<exists>!p. snd (stream_enc (w, I) !! p) ! m" by (intro stream_enc_unique) auto
      ultimately have "p = length u1" unfolding stream_enc using u I(3) by auto
    } note * = this
    from v have "v = x ! length u1" by simp
    with u have "?x !! length u1 = v" by (auto simp: shift_snth)
    with * m I v(3) have "(dec_word ?x, stream_dec n {m} ?x) \<Turnstile> FQ a m"
      using stream_enc_enc[OF _ I(1), symmetric] less_length_cut_same[of w "any" "length u1" a]
      by (auto simp del: enc.simps stream_enc.simps simp: dec_word_stream_enc dest!:
        stream_dec_enc_Inl stream_dec_not_Inr split: sum.splits)
        (auto simp: smap2_alt cut_same_def)
    moreover from m I(2)
      have stream_enc_dec: "stream_enc (dec_word (stream_enc (w, I)), stream_dec n {m} (stream_enc (w, I))) = stream_enc (w, I)"
        by (intro stream_enc_dec)
          (auto simp: smap2_alt sdrop_snth shift_snth intro: stream_enc_unique,
           auto simp: smap2_szip stream.set_map)
    moreover from I have "wf_word n x" unfolding wf_word by (auto elim: enc_set_\<sigma> simp del: enc.simps)
    ultimately show "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FQ a m)" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def using m I(1,3)
        by (auto simp del: enc.simps stream_enc.simps intro!: exI[of _ "enc (dec_word ?x, stream_dec n {m} ?x)"],
          fastforce simp del: enc.simps stream_enc.simps,
          auto simp del: stream_enc.simps simp: stream_enc[symmetric] I(2))
  qed
next
  case (FLess m m')
  show ?case
  proof (cases "m = m'")
    case False
    thus ?thesis
    proof (intro equalityI subsetI)
      fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FLess m m')"
      then obtain w I where
        *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FLess m m')" "length I = n" "(w, I) \<Turnstile> FLess m m'"
        unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by blast
      hence x_alt: "x = map (case_prod (enc_atom I)) (zip [0 ..< length x] (stake (length x) (w @- sconst any)))"
        by (intro encD) auto
      from FLess(1) *(2,4) obtain p q where pq: "I ! m = Inl p" "I ! m' = Inl q" "p < q"
        by (auto simp: all_set_conv_all_nth split: sum.splits)
      with FLess(1) *(1,2,3) have pq_less: "p < length x" "q < length x"
        by (auto simp del: stream_enc.simps intro!: trans_less_add1[OF less_length_cut_same_Inl])
      hence enc_atom: "x ! p = enc_atom I p ((w @- sconst any) !! p)" (is "_ = enc_atom _ _ ?p")
                      "x ! q = enc_atom I q ((w @- sconst any) !! q)" (is "_ = enc_atom _ _ ?q") by (subst x_alt, simp)+
      with *(1) pq_less(1) have "x = take p x @ [enc_atom I p ?p] @ drop (p + 1) x"
        using id_take_nth_drop[of p x] by auto
      also have "drop (p + 1) x = take (q - p - 1) (drop (p + 1) x) @
        [enc_atom I q ?q] @ drop (q - p) (drop (p + 1) x)" (is "_ = ?LHS")
        using id_take_nth_drop[of "q - p - 1" "drop (p + 1) x"] pq pq_less(2) enc_atom(2) by auto
      finally have "x = take p x @ [enc_atom I p ?p] @ ?LHS" .
      moreover from *(2,3) FLess(1) pq(1)
       have "[enc_atom I p ?p] \<in> lang n (Atom (Arbitrary_Except m True))"
         by (intro enc_atom_lang_Arbitrary_Except_True) (auto simp: shift_snth)
      moreover from *(2,3) FLess(1) pq(2)
       have "[enc_atom I q ?q] \<in> lang n (Atom (Arbitrary_Except m' True))"
         by (intro enc_atom_lang_Arbitrary_Except_True) (auto simp: shift_snth)
      moreover from *(2,3) have "take p x \<in> lang n (rexp.Not Zero)"
        by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_takeD)
      moreover from *(2,3) have "take (q - p - 1) (drop (Suc p) x) \<in> lang n (rexp.Not Zero)"
        by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_dropD in_set_takeD)
      moreover from *(2,3) have "drop (q - p) (drop (Suc p) x) \<in> lang n (rexp.Not Zero)"
        by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_dropD)
      ultimately show "x \<in> ?L n (FLess m m')" using *(1,2,3)
        unfolding rexp_of.simps lang.simps(6,9) rexp_of_list.simps Int_Diff lang_ENC_formula[OF FLess] if_not_P[OF False]
        by (auto elim: ssubst simp del: o_apply append.simps lang.simps enc.simps)
    next
      fix x let ?x = "x @- sconst (any, replicate n False)"
      assume x: "x \<in> ?L n (FLess m m')"
      with FLess obtain w I where
        I: "x \<in> enc (w, I)" "length I = n" "wf_interp_for_formula (w, I) (FLess m m')"
        unfolding rexp_of.simps lang.simps lang_ENC_formula[OF FLess] if_not_P[OF False] by fastforce
      hence stream_enc: "stream_enc (w, I) = x @- sconst (any, replicate n False)" using stream_enc_enc by auto
      from I FLess obtain p p' where m: "I ! m = Inl p" "m < length I" "I ! m' = Inl p'" "m' < length I"
        by (auto split: sum.splits)
      with I have "wf_interp_for_formula (dec_word ?x, stream_dec n {m, m'} ?x) (FLess m m')" unfolding I(1)
        using enc_wf_interp[OF FLess(1)[folded I(2)]] by auto
      moreover
      from x obtain u1 u u2 u' u3 where "x = u1 @ u @ u2 @ u' @ u3"
        "u \<in> lang n (Atom (Arbitrary_Except m True))" "u' \<in> lang n (Atom (Arbitrary_Except m' True))"
        unfolding rexp_of.simps lang.simps rexp_of_list.simps if_not_P[OF False] using concE by fast
      with FLess(1) obtain v v' where v: "x = u1 @ [v] @ u2 @ [v'] @ u3"
         "snd v ! m" "snd v' ! m'" "fst v \<in> set \<Sigma>" "fst v' \<in> set \<Sigma>"
        using Arbitrary_ExceptD[of u n m True] Arbitrary_ExceptD[of u' n m' True]
          by simp (auto simp: \<sigma>_def)
      hence u: "length u1 < length x" and u': "Suc (length u1 + length u2) < length x" (is "?u' < _") by auto
      { from v have "snd (x ! length u1) ! m" by auto
        moreover
        from m I have "p < length x" "snd (x ! p) ! m" by (auto dest: enc_Inl simp del: enc.simps)
        moreover
        from m I have ex1: "\<exists>!p. snd (stream_enc (w, I) !! p) ! m" by (intro stream_enc_unique) auto
        ultimately have "p = length u1" unfolding stream_enc using u I(3) by auto
      }
      { from v have "snd (x ! ?u') ! m'" by (auto simp: nth_append)
        moreover
        from m I have "p' < length x" "snd (x ! p') ! m'" by (auto dest: enc_Inl simp del: enc.simps)
        moreover
        from m I have ex1: "\<exists>!p. snd (stream_enc (w, I) !! p) ! m'" unfolding I(1) by (intro stream_enc_unique) auto
        ultimately have "p' = ?u'" unfolding stream_enc using u' I(3) by auto (metis shift_snth_less)
      } note * = this \<open>p = length u1\<close>
      with m I have "(dec_word ?x, stream_dec n {m, m'} ?x) \<Turnstile> FLess m m'"
        using stream_enc_enc[OF _ I(1), symmetric]
        by (auto dest: stream_dec_not_Inr stream_dec_enc_Inl split: sum.splits simp del: stream_enc.simps)
      moreover from m I(2)
        have stream_enc_dec: "stream_enc (dec_word (stream_enc (w, I)), stream_dec n {m, m'} (stream_enc (w, I))) = stream_enc (w, I)"
        by (intro stream_enc_dec)
          (auto simp: smap2_alt sdrop_snth shift_snth intro: stream_enc_unique,
           auto simp: smap2_szip stream.set_map)
      moreover from I have "wf_word n x" unfolding wf_word by (auto elim: enc_set_\<sigma> simp del: enc.simps)
      ultimately show "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FLess m m')" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def using m I(1,3)
        by (auto simp del: enc.simps stream_enc.simps intro!: exI[of _ "enc (dec_word ?x, stream_dec n {m, m'} ?x)"],
          fastforce simp del: enc.simps stream_enc.simps,
          auto simp del: stream_enc.simps simp: stream_enc[symmetric] I(2))
    qed
  qed (simp add: lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def del: o_apply)
next
  case (FIn m M)
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FIn m M)"
    then obtain w I where
      *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FIn m M)" "length I = n" "(w, I) \<Turnstile> FIn m M"
      unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by blast
    hence x_alt: "x = map (case_prod (enc_atom I)) (zip [0 ..< length x] (stake (length x) (w @- sconst any)))"
      by (intro encD) auto
    from FIn(1) *(2,4) obtain p P where p: "I ! m = Inl p" "I ! M = Inr P" "p \<in> P"
      by (auto simp: all_set_conv_all_nth split: sum.splits)
    with FIn(1) *(1,2,3) have p_less: "p < length x" "\<forall>p \<in> P. p < length x"
      by (auto simp del: stream_enc.simps intro: trans_less_add1[OF less_length_cut_same_Inl]
        trans_less_add1[OF bspec[OF less_length_cut_same_Inr]])
    hence enc_atom: "x ! p = enc_atom I p ((w @- sconst any) !! p)" (is "_ = enc_atom _ _ ?p")
            "\<forall>p \<in> P. x ! p = enc_atom I p ((w @- sconst any) !! p)" (is "Ball _ (\<lambda>p. _ = enc_atom _ _ (?P p))")
      by (subst x_alt, simp)+
    with *(1) p_less(1) have "x = take p x @ [enc_atom I p ?p] @ drop (p + 1) x"
      using id_take_nth_drop[of p x] by auto
    moreover
    from *(2,3) FIn(1) p have "[enc_atom I p ?p] \<in> lang n (Atom (Arbitrary_Except2 m M))"
      by (intro enc_atom_lang_Arbitrary_Except2) (auto simp: shift_snth)
    moreover from *(2,3) have "take p x \<in> lang n (rexp.Not Zero)"
      by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_takeD)
    moreover from *(2,3) have "drop (Suc p) x \<in> lang n (rexp.Not Zero)"
      by (subst x_alt) (auto simp: in_set_zip shift_snth intro!: enc_atom_\<sigma> dest!: in_set_dropD)
    ultimately show "x \<in> ?L n (FIn m M)" using *(1,2,3)
      unfolding rexp_of.simps lang.simps(6,9) rexp_of_list.simps Int_Diff lang_ENC_formula[OF FIn]
      by (auto elim: ssubst simp del: o_apply append.simps lang.simps enc.simps)
  next
    fix x let ?x = "x @- sconst (any, replicate n False)"
    assume x: "x \<in> ?L n (FIn m M)"
    with FIn obtain w I where
      I: "x \<in> enc (w, I)" "length I = n" "wf_interp_for_formula (w, I) (FIn m M)"
      unfolding rexp_of.simps lang.simps lang_ENC_formula[OF FIn] by fastforce
    hence stream_enc: "stream_enc (w, I) = ?x" using stream_enc_enc by auto
    from I FIn obtain p P where m: "I ! m = Inl p" "m < length I" "I ! M = Inr P" "M < length I"
      by (auto split: sum.splits)
    with I have "wf_interp_for_formula (dec_word ?x, stream_dec n {m} ?x) (FIn m M)" unfolding I(1)
      using enc_wf_interp[OF FIn(1)[folded I(2)]] by auto
    moreover
    from x obtain u1 u u2 where "x = u1 @ u @ u2"
      "u \<in> lang n (Atom (Arbitrary_Except2 m M))"
      unfolding rexp_of.simps lang.simps rexp_of_list.simps using concE by fast
    with FIn(1) obtain v where v: "x = u1 @ [v] @ u2" "snd v ! m" "snd v ! M" and "fst v \<in> set \<Sigma>"
      using Arbitrary_Except2D[of u n m M] by simp (auto simp: \<sigma>_def)
    from v have u: "length u1 < length x" by auto
    { from v have "snd (x ! length u1) ! m" by auto
      moreover
      from m I have "p < length x" "snd (x ! p) ! m" by (auto dest: enc_Inl simp del: enc.simps)
      moreover
      from m I have ex1: "\<exists>!p. snd (stream_enc (w, I) !! p) ! m" by (intro stream_enc_unique) auto
      ultimately have "p = length u1" unfolding stream_enc using u I(3) by auto
    } note * = this
    from v have "v = x ! length u1" by simp
    with v(3) m(3,4) u I(1,3) have "length u1 \<in> P" by (auto dest!: enc_Inr simp del: enc.simps)
    with * m I have "(dec_word ?x, stream_dec n {m} ?x) \<Turnstile> FIn m M"
      using stream_enc_enc[OF _ I(1), symmetric]
      by (auto simp del: stream_enc.simps dest: stream_dec_not_Inr stream_dec_not_Inl
        stream_dec_enc_Inl stream_dec_enc_Inr split: sum.splits)
    moreover from m I(2)
      have stream_enc_dec: "stream_enc (dec_word (stream_enc (w, I)), stream_dec n {m} (stream_enc (w, I))) = stream_enc (w, I)"
        by (intro stream_enc_dec)
          (auto simp: smap2_alt sdrop_snth shift_snth intro: stream_enc_unique,
           auto simp: smap2_szip stream.set_map)
    moreover from I have "wf_word n x" unfolding wf_word by (auto elim: enc_set_\<sigma> simp del: enc.simps)
    ultimately show "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FIn m M)" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def using m I(1,3)
        by (auto simp del: enc.simps stream_enc.simps intro!: exI[of _ "enc (dec_word ?x, stream_dec n {m} ?x)"],
          fastforce simp del: enc.simps stream_enc.simps,
          auto simp del: stream_enc.simps simp: stream_enc[symmetric] I(2))
  qed
next
  case (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)
  from FOr(3) have IH1: "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1 = lang n (rexp_of n \<phi>\<^sub>1)"
    by (intro FOr(1)) auto
  from FOr(3) have IH2: "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2 = lang n (rexp_of n \<phi>\<^sub>2)"
    by (intro FOr(2)) auto
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)" thus "x \<in> lang n (rexp_of n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2))"
      using lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_FOr[OF FOr(3)] unfolding lang_ENC_formula[OF FOr(3)] rexp_of.simps lang.simps IH1 IH2 by blast
  next
    fix x assume "x \<in> lang n (rexp_of n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2))"
    then obtain w I where or: "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1 \<or> x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2" and I: "x \<in> enc (w, I)" "length I = n"
      "wf_interp_for_formula (w, I) (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)"
      unfolding lang_ENC_formula[OF FOr(3)] rexp_of.simps lang.simps IH1 IH2 Int_Diff by auto
    have "(w, I) \<Turnstile> \<phi>\<^sub>1 \<or> (w, I) \<Turnstile> \<phi>\<^sub>2"
    proof (intro mp[OF disj_mono[OF impI impI] or])
      assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1"
      with I FOr(3) show "(w, I) \<Turnstile> \<phi>\<^sub>1"
        unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def I(1) wf_interp_for_formula_FOr
        by (auto dest!: enc_welldef[of x w I _ _ \<phi>\<^sub>1] simp del: enc.simps)
    next
      assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2"
      with I FOr(3) show "(w, I) \<Turnstile> \<phi>\<^sub>2"
        unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def I(1) wf_interp_for_formula_FOr
        by (auto dest!: enc_welldef[of x w I _ _ \<phi>\<^sub>2] simp del: enc.simps)
    qed
    with I show "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
  qed
next
  case (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
  from FAnd(3) have IH1: "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1 = lang n (rexp_of n \<phi>\<^sub>1)"
    by (intro FAnd(1)) auto
  from FAnd(3) have IH2: "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2 = lang n (rexp_of n \<phi>\<^sub>2)"
    by (intro FAnd(2)) auto
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)" thus "x \<in> lang n (rexp_of n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2))"
      using lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_FAnd[OF FAnd(3)]
      unfolding lang_ENC_formula[OF FAnd(3)] rexp_of.simps rexp_of_list.simps lang.simps IH1 IH2 Int_assoc
      by blast
  next
    fix x assume "x \<in> lang n (rexp_of n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2))"
    then obtain w I where "and": "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1 \<and> x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2" and I: "x \<in> enc (w, I)" "length I = n"
      "wf_interp_for_formula (w, I) (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)"
      unfolding lang_ENC_formula[OF FAnd(3)] rexp_of.simps rexp_of_list.simps lang.simps IH1 IH2 Int_Diff by auto
    have "(w, I) \<Turnstile> \<phi>\<^sub>1 \<and> (w, I) \<Turnstile> \<phi>\<^sub>2"
    proof (intro mp[OF conj_mono[OF impI impI] "and"])
      assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>1"
      with I FAnd(3) show "(w, I) \<Turnstile> \<phi>\<^sub>1"
        unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def I(1) wf_interp_for_formula_FAnd
        by (auto dest!: enc_welldef[of x w I _ _ \<phi>\<^sub>1] simp del: enc.simps)
    next
      assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>\<^sub>2"
      with I FAnd(3) show "(w, I) \<Turnstile> \<phi>\<^sub>2"
        unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def I(1) wf_interp_for_formula_FAnd
        by (auto dest!: enc_welldef[of x w I _ _ \<phi>\<^sub>2] simp del: enc.simps)
    qed
    with I show "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
  qed
next
  case (FNot \<phi>)
  hence IH: "?L n \<phi> =  lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>" by simp
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FNot \<phi>)"
    then obtain w I where
      *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) \<phi>" "length I = n" and unsat: "\<not> (w, I) \<Turnstile> \<phi>"
       unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
    { assume "x \<in> ?L n \<phi>"
      hence "(w, I) \<Turnstile> \<phi>" using enc_welldef[of x w I _ _ \<phi>, OF *(1) _ _ _ *(2)] FNot(2)
        unfolding *(3) lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def IH by auto
    }
    with unsat have "x \<notin> ?L n \<phi>" by blast
    with * show "x \<in> ?L n (FNot \<phi>)" unfolding rexp_of.simps lang.simps using lang_ENC_formula[OF FNot(2)]
      by (auto simp del: enc.simps simp: comp_def intro: enc_set_\<sigma>)
  next
    fix x assume "x \<in> ?L n (FNot \<phi>)"
    with IH have "x \<in> lang n (ENC n (FOV (FNot \<phi>)))" and x: "x \<notin> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>" by (auto simp del: o_apply)
    then obtain w I where *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FNot \<phi>)" "length I = n"
      unfolding lang_ENC_formula[OF FNot(2)] by blast
    { assume "\<not> (w, I) \<Turnstile> FNot \<phi>"
      with * have "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
    }
    with x * show "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FNot \<phi>)"  unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by blast
  qed
next
  case (FExists \<phi>)
  have \<sigma>: "(any, replicate n False) \<in> (set o \<sigma> \<Sigma>) n" by (auto simp: \<sigma>_def set_n_lists image_iff)
  from FExists(2) have wf: "wf n (Pr (rexp_of (Suc n) \<phi>))" by (fastforce intro: wf_rexp_of)
  note lang_quot = lang_samequot_exec[OF wf \<sigma>]
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FExists \<phi>)"
    then obtain w I p where
      *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FExists \<phi>)" "length I = n" "(w, Inl p # I) \<Turnstile> \<phi>"
       unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
    with FExists(2) have "enc (w, Inl p # I) \<subseteq> ?L (Suc n) \<phi>"
      by (subst FExists(1)[of "Suc n", symmetric])
        (fastforce simp del: enc.simps simp: lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def nth_Cons' intro!: exI[of _ "enc (w, Inl p # I)"])+
    thus "x \<in> ?L n (FExists \<phi>)" using *(1,2,3)
      by (auto simp: lang_quot simp del: o_apply enc.simps elim: subsetD[OF SAMEQUOT_mono[OF image_mono]])
  next
    fix x assume "x \<in> ?L n (FExists \<phi>)"
    then obtain x' m where "x' \<in> ?L (Suc n) \<phi>" and
      x: "x = fin_cut_same (any, replicate n False) (map \<pi> x') @ replicate m (any, replicate n False)" 
      by (auto simp: lang_quot SAMEQUOT_def simp del: o_apply enc.simps)
    with FExists(2) have "x' \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S (Suc n) \<phi>"
      by (intro subsetD[OF equalityD2[OF FExists(1)], of "Suc n" x'])
        (auto split: if_split_asm sum.splits)
    then obtain w I' where
      *: "x' \<in> enc (w, I')" "wf_interp_for_formula (w, I') \<phi>" "length I' = Suc n" "(w, I') \<Turnstile> \<phi>"
       unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by blast
    moreover then obtain I\<^sub>0 I where "I' = I\<^sub>0 # I" by (cases I') auto
    moreover with FExists(2) *(2) obtain p where "I\<^sub>0 = Inl p"
      by (auto simp: nth_Cons' split: sum.splits if_split_asm)
    ultimately have "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FExists \<phi>)" "length I = n"
      "(w, I) \<Turnstile> FExists \<phi>" using FExists(2) fin_cut_same_tl[OF ex_Loop_stream_enc, of "Inl p # I" w]
      unfolding x by (auto simp add: \<pi>_def nth_Cons' split: if_split_asm)
    thus "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FExists \<phi>)" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by (auto intro!: exI[of _ I])
  qed
next
  case (FEXISTS \<phi>)
  have \<sigma>: "(any, replicate n False) \<in> (set o \<sigma> \<Sigma>) n" by (auto simp: \<sigma>_def set_n_lists image_iff)
  from FEXISTS(2) have wf: "wf n (Pr (rexp_of (Suc n) \<phi>))" by (fastforce intro: wf_rexp_of)
  note lang_quot = lang_samequot_exec[OF wf \<sigma>]
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FEXISTS \<phi>)"
    then obtain w I P where
      *: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FEXISTS \<phi>)" "length I = n" "finite P" "(w, Inr P # I) \<Turnstile> \<phi>"
       unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto
    with FEXISTS(2) have "enc (w, Inr P # I) \<subseteq> ?L (Suc n) \<phi>"
      by (subst FEXISTS(1)[of "Suc n", symmetric])
        (fastforce simp del: enc.simps simp: lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def nth_Cons' intro!: exI[of _ "enc (w, Inr P # I)"])+
    thus "x \<in> ?L n (FEXISTS \<phi>)" using *(1,2,3,4)
      by (auto simp: lang_quot simp del: o_apply enc.simps elim: subsetD[OF SAMEQUOT_mono[OF image_mono]])
  next
    fix x assume "x \<in> ?L n (FEXISTS \<phi>)"
    then obtain x' m where "x' \<in> ?L (Suc n) \<phi>" and
      x: "x = fin_cut_same (any, replicate n False) (map \<pi> x') @ replicate m (any, replicate n False)" 
      by (auto simp: lang_quot SAMEQUOT_def simp del: o_apply enc.simps)
    with FEXISTS(2) have "x' \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S (Suc n) \<phi>"
      by (intro subsetD[OF equalityD2[OF FEXISTS(1)], of "Suc n" x'])
        (auto split: if_split_asm sum.splits)
    then obtain w I' where
      *: "x' \<in> enc (w, I')" "wf_interp_for_formula (w, I') \<phi>" "length I' = Suc n" "(w, I') \<Turnstile> \<phi>"
       unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by blast
    moreover then obtain I\<^sub>0 I where "I' = I\<^sub>0 # I" by (cases I') auto
    moreover with FEXISTS(2) *(2) obtain P where "I\<^sub>0 = Inr P" "finite P"
      by (auto simp: nth_Cons' split: sum.splits if_split_asm)
    ultimately have "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FEXISTS \<phi>)" "length I = n"
      "(w, I) \<Turnstile> FEXISTS \<phi>"  using FEXISTS(2) fin_cut_same_tl[OF ex_Loop_stream_enc, of "Inr P # I"]
      unfolding x by (auto simp: nth_Cons' \<pi>_def split: if_split_asm)
    thus "x \<in> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (FEXISTS \<phi>)" unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by (auto intro!: exI[of _ I])
  qed
qed

lemma wf_rexp_of_alt: "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of_alt n \<phi>)"
  by (induct \<phi> arbitrary: n)
    (auto intro!: wf_samequot_exec wf_rexp_ENC,
     auto simp: max_idx_vars finite_FOV)

lemma wf_rexp_of': "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of' n \<phi>)"
  unfolding rexp_of'_def by (auto simp: max_idx_vars intro: wf_rexp_of_alt wf_rexp_ENC[OF finite_FOV])

lemma wf_rexp_of_alt': "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of_alt' n \<phi>)"
  by (induct \<phi> arbitrary: n)
    (auto intro!: wf_samequot_exec wf_rexp_ENC,
     auto simp: max_idx_vars finite_FOV)

lemma wf_rexp_of'': "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of'' n \<phi>)"
  unfolding rexp_of''_def by (auto simp: wf_rexp_ENC wf_rexp_of_alt' finite_FOV max_idx_vars)


lemma ENC_FNot: "ENC n (FOV (FNot \<phi>)) = ENC n (FOV \<phi>)"
  unfolding ENC_def by auto

lemma ENC_FAnd:
  "wf_formula n (FAnd \<phi> \<psi>) \<Longrightarrow> lang n (ENC n (FOV (FAnd \<phi> \<psi>))) \<subseteq> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>))"
proof
  fix x assume wf: "wf_formula n (FAnd \<phi> \<psi>)" and x: "x \<in> lang n (ENC n (FOV (FAnd \<phi> \<psi>)))"
  hence wf1: "wf_formula n \<phi>" and wf2: "wf_formula n \<psi>" by auto
  from x obtain w I where I: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FAnd \<phi> \<psi>)" "length I = n"
    using lang_ENC_formula[OF wf] by auto
  hence "wf_interp_for_formula (w, I) \<phi>" "wf_interp_for_formula (w, I) \<psi>"
    using wf_interp_for_formula_FAnd by auto
  thus "x \<in> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>))"
    unfolding lang_ENC_formula[OF wf1] lang_ENC_formula[OF wf2] using I by blast
qed
  
lemma ENC_FOr:
  "wf_formula n (FOr \<phi> \<psi>) \<Longrightarrow> lang n (ENC n (FOV (FOr \<phi> \<psi>))) \<subseteq> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>))"
proof
  fix x assume wf: "wf_formula n (FOr \<phi> \<psi>)" and x: "x \<in> lang n (ENC n (FOV (FOr \<phi> \<psi>)))"
  hence wf1: "wf_formula n \<phi>" and wf2: "wf_formula n \<psi>" by auto
  from x obtain w I where I: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FOr \<phi> \<psi>)" "length I = n"
    using lang_ENC_formula[OF wf] by auto
  hence "wf_interp_for_formula (w, I) \<phi>" "wf_interp_for_formula (w, I) \<psi>"
    using wf_interp_for_formula_FOr by auto
  thus "x \<in> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>))"
    unfolding lang_ENC_formula[OF wf1] lang_ENC_formula[OF wf2] using I by blast
qed

lemma ENC_FExists:
  "wf_formula n (FExists \<phi>) \<Longrightarrow> lang n (ENC n (FOV (FExists \<phi>))) =
  SAMEQUOT (any, replicate n False) (map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)))" (is "_ \<Longrightarrow> ?L = ?R")
proof (intro equalityI subsetI)
  fix x assume wf: "wf_formula n (FExists \<phi>)" and x: "x \<in> ?L"
  hence wf1: "wf_formula (Suc n) \<phi>" by auto
  from x obtain w I where I: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FExists \<phi>)" "length I = n"
    using lang_ENC_formula[OF wf] by auto
  from I(2) obtain p where "wf_interp_for_formula (w, Inl p # I) \<phi>"
    using wf_interp_for_formula_FExists[OF wf[folded I(3)]] by blast
  with I(3) show "x \<in> ?R"
    unfolding lang_ENC_formula[OF wf1] using I(1) tl_enc[of "Inl p" I, symmetric]
    by (simp del: enc.simps) 
      (fastforce simp del: enc.simps elim!: rev_subsetD[OF _ SAMEQUOT_mono[OF image_mono]]
        intro: exI[of _ "enc (w, Inl p # I)"])
next
  fix x assume wf: "wf_formula n (FExists \<phi>)" and x: "x \<in> ?R"
  hence wf1: "wf_formula (Suc n) \<phi>" and "0 \<in> FOV \<phi>" by auto
  from x obtain w I where I: "x \<in> SAMEQUOT (any, replicate n False) (map \<pi> ` enc (w, I))"
    "wf_interp_for_formula (w, I) \<phi>" "length I = Suc n"
    using lang_ENC_formula[OF wf1] unfolding SAMEQUOT_def by fast
  with \<open>0 \<in> FOV \<phi>\<close> obtain p I' where I': "I = Inl p # I'" by (cases I) (fastforce split: sum.splits)+
  with I have wtlI: "x \<in> enc (w, I')" "length I' = n" using tl_enc[of "Inl p" I' w] by auto
  have "wf_interp_for_formula (w, I') (FExists \<phi>)"
    using wf_interp_for_formula_FExists[OF wf[folded wtlI(2)]]
          wf_interp_for_formula_any_Inl[OF I(2)[unfolded I']] ..
  with wtlI show "x \<in> ?L" unfolding lang_ENC_formula[OF wf] by blast
qed

lemma ENC_FEXISTS:
  "wf_formula n (FEXISTS \<phi>) \<Longrightarrow> lang n (ENC n (FOV (FEXISTS \<phi>))) =
  SAMEQUOT (any, replicate n False) (map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)))" (is "_ \<Longrightarrow> ?L = ?R")
proof (intro equalityI subsetI)
  fix x assume wf: "wf_formula n (FEXISTS \<phi>)" and x: "x \<in> ?L"
  hence wf1: "wf_formula (Suc n) \<phi>" by auto
  from x obtain w I where I: "x \<in> enc (w, I)" "wf_interp_for_formula (w, I) (FEXISTS \<phi>)" "length I = n"
    using lang_ENC_formula[OF wf] by auto
  from I(2) obtain P where "wf_interp_for_formula (w, Inr P # I) \<phi>"
    using wf_interp_for_formula_FEXISTS[OF wf[folded I(3)]] by blast
  with I(3) show "x \<in> ?R"
    unfolding lang_ENC_formula[OF wf1] using I(1) tl_enc[of "Inr P" I, symmetric]
    by (simp del: enc.simps) 
      (fastforce simp del: enc.simps elim!: rev_subsetD[OF _ SAMEQUOT_mono[OF image_mono]]
        intro: exI[of _ "enc (w, Inr P # I)"])
next
  fix x assume wf: "wf_formula n (FEXISTS \<phi>)" and x: "x \<in> ?R"
  hence wf1: "wf_formula (Suc n) \<phi>" and "0 \<in> SOV \<phi>" by auto
  from x obtain w I where I: "x \<in> SAMEQUOT (any, replicate n False) (map \<pi> ` enc (w, I))"
    "wf_interp_for_formula (w, I) \<phi>" "length I = Suc n"
    using lang_ENC_formula[OF wf1] unfolding SAMEQUOT_def by fast
  with \<open>0 \<in> SOV \<phi>\<close> obtain P I' where I': "I = Inr P # I'" by (cases I) (fastforce split: sum.splits)+
  with I have wtlI: "x \<in> enc (w, I')" "length I' = n" using tl_enc[of "Inr P" I' w] by auto
  have "wf_interp_for_formula (w, I') (FEXISTS \<phi>)"
    using wf_interp_for_formula_FEXISTS[OF wf[folded wtlI(2)]]
          wf_interp_for_formula_any_Inr[OF I(2)[unfolded I']] ..
  with wtlI show "x \<in> ?L" unfolding lang_ENC_formula[OF wf] by blast
qed

lemma lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of_rexp_of':
  "wf_formula n \<phi> \<Longrightarrow> lang n (rexp_of n \<phi>) = lang n (rexp_of' n \<phi>)"
unfolding rexp_of'_def proof (induction \<phi> arbitrary: n)
  case (FNot \<phi>)
  hence "wf_formula n \<phi>" by simp
  with FNot.IH show ?case unfolding rexp_of.simps rexp_of_alt.simps lang.simps ENC_FNot by blast
next
  case (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FAnd.IH(1)[OF wf1] FAnd.IH(2)[OF wf2] show ?case using ENC_FAnd[OF FAnd.prems]
    unfolding rexp_of.simps rexp_of_alt.simps lang.simps rexp_of_list.simps by blast
next
  case (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FOr.IH(1)[OF wf1] FOr.IH(2)[OF wf2] show ?case using ENC_FOr[OF FOr.prems]
    unfolding rexp_of.simps rexp_of_alt.simps lang.simps by blast
next
  case (FExists \<phi>)
  from FExists(2) have IH: "lang (n + 1) (rexp_of (n + 1) \<phi>) =
    lang (n + 1) (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>)))" by (intro FExists.IH) auto
  have \<sigma>: "(any, replicate n False) \<in> (set o \<sigma> \<Sigma>) n" by (auto simp: \<sigma>_def set_n_lists image_iff)
  from FExists(2) have wf: "wf n (Pr (rexp.Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>))))"
    "wf n (Pr (rexp_of (n + 1) \<phi>))" by (fastforce simp: max_idx_vars intro!: wf_rexp_of wf_rexp_of_alt wf_rexp_ENC[OF finite_FOV])+
  note lang_quot = lang_samequot_exec[OF wf(1) \<sigma>] lang_samequot_exec[OF wf(2) \<sigma>]
  show ?case unfolding rexp_of.simps rexp_of_alt.simps lang.simps IH lang_quot Suc_eq_plus1
    ENC_FExists[OF FExists.prems, unfolded Suc_eq_plus1] by (auto simp add: SAMEQUOT_def)
next
  case (FEXISTS \<phi>)
  from FEXISTS(2) have IH: "lang (n + 1) (rexp_of (n + 1) \<phi>) =
    lang (n + 1) (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>)))" by (intro FEXISTS.IH) auto
  have \<sigma>: "(any, replicate n False) \<in> (set o \<sigma> \<Sigma>) n" by (auto simp: \<sigma>_def set_n_lists image_iff)
  from FEXISTS(2) have wf: "wf n (Pr (rexp.Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>))))"
    "wf n (Pr (rexp_of (n + 1) \<phi>))" by (fastforce simp: max_idx_vars intro: wf_rexp_of wf_rexp_of_alt wf_rexp_ENC[OF finite_FOV])+
  note lang_quot = lang_samequot_exec[OF wf(1) \<sigma>] lang_samequot_exec[OF wf(2) \<sigma>]
  show ?case unfolding rexp_of.simps rexp_of_alt.simps lang.simps IH lang_quot Suc_eq_plus1
    ENC_FEXISTS[OF FEXISTS.prems, unfolded Suc_eq_plus1] by (auto simp add: SAMEQUOT_def)
qed auto

lemma SAMEQUTO_UN[simp]: "SAMEQUOT x (\<Union>y \<in> A. B y) = (\<Union>y \<in> A. SAMEQUOT x (B y))"
  unfolding SAMEQUOT_def by auto

lemma finite_positions_in_row[simp]:
  "n > 0 \<Longrightarrow> finite (positions_in_row (x @- sconst (any, replicate n False)) 0)"
  unfolding positions_in_row shift_snth by auto

lemma fin_cut_same_snoc: "fin_cut_same x (xs @ [y]) = (if x = y then fin_cut_same x xs else xs @ [y])"
  by (induct xs) auto

lemma fin_cut_same_idem: "fin_cut_same x (fin_cut_same x xs) = fin_cut_same x xs"
  by (induct xs) auto

lemma cut_same_sconst: "cut_same x (xs @- sconst x) = fin_cut_same x xs"
proof (induct xs rule: rev_induct)
  case (snoc y ys)
  then show ?case  by (auto simp del: id_apply simp add: fin_cut_same_snoc sconst_collapse)
qed (simp del: id_apply)

lemma length_cut_same: "length (cut_same x s) = (LEAST n. sdrop n s = sconst x)"
  unfolding cut_same_def by simp

lemma enc_alt: "wf_interp w I \<Longrightarrow>
  x \<in> enc (w, I) \<longleftrightarrow> x @- sconst ((any, replicate (length I) False)) = stream_enc (w, I)"
  unfolding enc.simps
  by (force simp only: shift_append shift_replicate_sconst stream_enc_cut_same[symmetric]
    length_append length_replicate length_cut_same sdrop_shift drop_all diff_self_eq_0
    shift.simps sdrop.simps
    dest: sym[of _ "stream_enc (w, I)"]
    intro: shift_sconst_inj[rotated, of _ "(any, replicate (length I) False)"] Least_le
      exI[of _ "length x - length (cut_same (any, replicate (length I) False) (stream_enc (w, I)))"]
      le_add_diff_inverse[symmetric] )

lemma stream_stream_eqI: "\<lbrakk>\<forall>(_, x) \<in> sset xs. x \<noteq> []; \<forall>(_, x) \<in> sset ys. x \<noteq> [];
  smap (\<lambda>(_, x). hd x) xs = smap (\<lambda>(_, x). hd x) ys; smap \<pi> xs = smap \<pi> ys\<rbrakk> \<Longrightarrow> xs = ys"
proof (coinduction arbitrary: xs ys)
  case Eq_stream
  then show ?case
  proof (cases xs ys rule: stream.exhaust[case_product stream.exhaust])
    case (SCons_SCons h1 t1 h2 t2)
    with Eq_stream show ?thesis
      by (cases "snd h1" "snd h2" rule: list.exhaust[case_product list.exhaust])
        (auto simp: \<pi>_def split: prod.splits)
  qed
qed

lemma project_enc_extend:
  fixes x I
  defines "n \<equiv> length I"
  defines "z \<equiv> \<lambda>n. (any, replicate n False)"
  defines "I' \<equiv> Inr (positions_in_row (x @- sconst (z (Suc n))) 0) # I"
  assumes wf: "wf_interp w I"
  assumes enc: "fin_cut_same (z n) (map \<pi> x) @ replicate m (z n) \<in> enc (w, I)"
  assumes nonempty: "\<forall>(_, x) \<in> set x. x \<noteq> []"
  shows "x \<in> enc (w, I')"
proof -
  have [simp]: "\<pi> (z (Suc n)) = z n"
    and z_def: "\<And>n. z n = (any, replicate n False)" unfolding \<pi>_def z_def by auto
  have wf': "wf_interp w I'" by (simp add: wf I'_def z_def del: replicate_Suc)
  note simps[simp del] = stream_enc.simps
  show ?thesis unfolding enc_alt[OF wf']
  proof (rule stream_stream_eqI)
    from nonempty stream_smap_nats[of "map (\<lambda>(_, y). hd y) x @- sconst False"]
      smap_szip_fst
    show "smap (\<lambda>(_, x). hd x) (x @- sconst (any, replicate (length I') False)) =
      smap (\<lambda>(_, x). hd x) (stream_enc (w, I'))"
      by (auto simp add: stream_enc.simps I'_def z_def smap2_szip stream.map_comp o_def split_def
        positions_in_row shift_snth hd_conv_nth intro: smap_szip_fst[symmetric]
        cong: stream.map_cong)
  next
    from wf have "fin_cut_same (z n) (map \<pi> x) = cut_same (z n) (stream_enc (w, I))"
      using stream_enc_enc[OF _ enc] by (auto simp add: cut_same_sconst z_def n_def fin_cut_same_idem)
    then obtain m' where \<pi>x: "map \<pi> x = cut_same (z n) (stream_enc (w, I)) @ replicate m' (z n)"
      by (auto dest!: fin_cut_sameE)
    with wf show "smap \<pi> (x @- sconst (any, replicate (length I') False)) =
      smap \<pi> (stream_enc (w, I'))"
      by (simp del: replicate_Suc add: n_def[symmetric] z_def[symmetric] I'_def
        stream_enc_cut_same[of I, symmetric, folded n_def z_def])
  qed (insert nonempty, simp_all add: stream_enc.simps I'_def split_beta smap2_szip stream.set_map)
qed

lemma pred_case_conv: "x - Suc 0 = (case x of 0 \<Rightarrow> 0 | Suc m \<Rightarrow> m)"
  by (cases x) auto

lemma in_pred_image_iff: "0 \<notin> X \<Longrightarrow> (x \<in> (\<lambda>x. x - Suc 0) ` X) = (Suc x \<in> X)"
  by (auto simp: pred_case_conv split: nat.splits)

lemma map_project_Int_ENC:
  fixes X Z n
  defines "z \<equiv> (any, replicate n False)"
  assumes "0 \<notin> X" "X \<subseteq> {0 ..< n + 1}" "Z \<subseteq> lists ((set o \<sigma> \<Sigma>) (n + 1))"
  shows "SAMEQUOT z (map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X))) =
    SAMEQUOT z (map \<pi> ` Z) \<inter> lang n (ENC n ((\<lambda>x. x - 1) ` X))"
proof -
  let ?Y = "{0 ..< n + 1} - X"
  let ?fX = "(\<lambda>x. x - 1) ` X"
  let ?fY = "{0 ..< n} - (\<lambda>x. x - 1) ` X"
  from assms have *: "(\<lambda>x. x - 1) ` X \<subseteq> {0 ..< n}" by (cases n) auto
  show ?thesis
  proof (safe elim!: subsetD[OF SAMEQUOT_mono[OF subset_trans[OF image_Int_subset Int_lower1]]])
    fix w assume "w \<in> SAMEQUOT z (map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X)))"
    then have "w \<in> SAMEQUOT z (map \<pi> ` lang (n + 1) (ENC (n + 1) X))"
      by (rule rev_subsetD[OF _ SAMEQUOT_mono]) auto
    with assms(2) show "w \<in> lang n (ENC n ((\<lambda>x. x - 1) ` X))"
      unfolding lang_ENC[OF assms(3) subset_refl] lang_ENC[OF * subset_refl]
      by (auto simp: image_Union z_def length_Suc_conv simp del: enc.simps
        intro!: exI[of _ "enc (w, I)" for w I, OF conjI[of _ "x \<in> A" for x A]])
        (fastforce simp: nth_Cons image_iff split: nat.splits sum.splits)
  next
    fix w assume "w \<in> SAMEQUOT z (map \<pi> ` Z)" "w \<in> lang n (ENC n ((\<lambda>x. x - 1) ` X))"
    then show "w \<in> SAMEQUOT z (map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X)))"
    unfolding  z_def SAMEQUOT_def proof (safe, intro exI conjI)
      fix m x
      assume \<pi>x: "fin_cut_same (any, replicate n False) (map \<pi> x) @
       replicate m (any, replicate n False) \<in> lang n (ENC n ((\<lambda>x. x - 1) ` X))" and "x \<in> Z"
      show "map \<pi> x \<in> map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X))"
      proof (intro imageI IntI)
        from \<open>x \<in> Z\<close> assms(4) have "\<forall>(_, x)\<in>set x. x \<noteq> []" by (auto simp: \<sigma>_def)
        with \<pi>x assms(2) show "x \<in> lang (n + 1) (ENC (n + 1) X)"
        unfolding lang_ENC[OF assms(3) subset_refl] lang_ENC[OF * subset_refl]
        proof (safe, intro UnionI[OF _ project_enc_extend[rotated]] CollectI exI conjI)
          fix w and I :: "(nat + nat set) list"
          assume "Ball (set I) (case_sum (\<lambda>a. True) finite)"
          then show "Ball (set
             (Inr (positions_in_row (x @- sconst (any, replicate (Suc (length I)) False)) 0) #I))
           (case_sum (\<lambda>a. True) finite)" by (auto simp del: replicate_Suc)
        qed (auto simp add: nth_Cons' Ball_def in_pred_image_iff)
      qed (rule \<open>x \<in> Z\<close>)
    qed (rule refl)
  qed
qed

lemma lang_ENC_split:
  assumes "finite X" "X = Y1 \<union> Y2" "n = 0 \<or> (\<forall>p \<in> X. p < n)"
  shows "lang n (ENC n X) = lang n (ENC n Y1) \<inter> lang n (ENC n Y2)"
  unfolding ENC_def lang_INTERSECT using assms lang_subset_lists[OF wf_rexp_valid_ENC, of n] by auto

lemma map_project_ENC:
  fixes n
  assumes "X \<subseteq> {0 ..< n + 1}" "Z \<subseteq> lists ((set o \<sigma> \<Sigma>) (n + 1))"
  defines "z \<equiv> (any, replicate n False)"
  shows "SAMEQUOT z (map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X))) =
    (if 0 \<in> X
    then SAMEQUOT z (map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) {0}))) \<inter> lang n (ENC n ((\<lambda>x. x - 1) ` (X - {0})))
    else SAMEQUOT z (map \<pi> ` Z) \<inter> lang n (ENC n ((\<lambda>x. x - 1) ` (X - {0}))))"
    (is "?L = (if _ then ?R1 else ?R2)")
proof (split if_splits, intro conjI impI)
  assume 0: "0 \<notin> X"
  from assms have fin: "finite X" "finite ((\<lambda>x. x - 1) ` X)"
    by (auto elim: finite_subset intro!: finite_imageI[of "X"])
  from 0 show "?L = ?R2" using map_project_Int_ENC[OF 0 assms(1,2)]
    unfolding lists_image[symmetric] \<pi>_\<sigma>
      Int_absorb1[OF lang_subset_lists[OF wf_rexp_ENC[OF fin(1)]], of "n + 1"]
      Int_absorb1[OF lang_subset_lists[OF wf_rexp_ENC[OF fin(2)]], of n] unfolding z_def
    by auto
next
  assume "0 \<in> X"
  hence 0: "0 \<notin> X - {0}" and X: "X = {0} \<union> (X - {0})" by auto
  from assms have fin: "finite X"
    by (auto elim: finite_subset intro!: finite_imageI[of "X"])
  have "?L = SAMEQUOT z (map \<pi> ` ((Z \<inter> lang (n + 1) (ENC (n + 1) {0})) \<inter> lang (n + 1) (ENC (n + 1) (X - {0}))))"
    unfolding Int_assoc z_def using assms by (subst lang_ENC_split[OF fin X, of "n + 1"]) auto
  also have "\<dots> = ?R1" unfolding z_def
    using assms(1,2) by (intro map_project_Int_ENC) auto
  finally show "?L = ?R1" .
qed

lemma lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'_rexp_of'':
  "wf_formula n \<phi> \<Longrightarrow> lang n (rexp_of' n \<phi>) = lang n (rexp_of'' n \<phi>)"
unfolding rexp_of'_def rexp_of''_def
proof (induction \<phi> arbitrary: n)
  case (FNot \<phi>)
  hence "wf_formula n \<phi>" by simp
  with FNot.IH show ?case unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps ENC_FNot by blast
next
  case (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FAnd.IH(1)[OF wf1] FAnd.IH(2)[OF wf2] show ?case using ENC_FAnd[OF FAnd.prems]
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps rexp_of_list.simps by blast
next
  case (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FOr.IH(1)[OF wf1] FOr.IH(2)[OF wf2] show ?case using ENC_FOr[OF FOr.prems]
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps rexp_of_list.simps by blast
next
  case (FExists \<phi>)
  hence wf: "wf_formula (n + 1) \<phi>" and 0: "0 \<in> FOV \<phi>" by auto
  then show ?case
    using max_idx_vars[of "n + 1" \<phi>] wf_rexp_of_alt'[OF wf]
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps Suc_eq_plus1
    proof (subst (1 2) lang_samequot_exec)
      show "SAMEQUOT (any, replicate n False)
          (lang n (Pr (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>))))) \<inter>
          lang n (ENC n (FOV (FExists \<phi>))) =
        SAMEQUOT (any, replicate n False)
          (lang n (Pr (Inter (rexp_of_alt' (n + 1) \<phi>) (ENC (n + 1) {0})))) \<inter>
          lang n (ENC n (FOV (FExists \<phi>)))"
        using wf 0 max_idx_vars[of "n + 1" \<phi>] wf_rexp_of_alt'[OF wf]
        unfolding lang.simps FExists.IH[OF wf, unfolded lang.simps]
        by (subst (1) map_project_ENC) (auto dest: subsetD[OF lang_subset_lists])
    qed (auto simp add: wf_rexp_of_alt finite_FOV wf_rexp_ENC)
next
  case (FEXISTS \<phi>)
  hence wf: "wf_formula (n + 1) \<phi>" and 0: "0 \<notin> FOV \<phi>" by auto
  then show ?case
    using max_idx_vars[of "n + 1" \<phi>] wf_rexp_of_alt'[OF wf]
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps Suc_eq_plus1
    proof (subst (1 2) lang_samequot_exec)
      show "SAMEQUOT (any, replicate n False)
          (lang n (Pr (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>))))) \<inter>
          lang n (ENC n (FOV (FEXISTS \<phi>))) =
        SAMEQUOT (any, replicate n False)
          (lang n (Pr (rexp_of_alt' (n + 1) \<phi>))) \<inter>
          lang n (ENC n (FOV (FEXISTS \<phi>)))"
        using wf 0 max_idx_vars[of "n + 1" \<phi>] wf_rexp_of_alt'[OF wf]
        unfolding lang.simps FEXISTS.IH[OF wf, unfolded lang.simps]
        by (subst (1) map_project_ENC) (auto dest: subsetD[OF lang_subset_lists])
    qed (auto simp add: wf_rexp_of_alt finite_FOV wf_rexp_ENC)
qed simp_all

theorem lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of': "wf_formula n \<phi> \<Longrightarrow> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi> = lang n (rexp_of' n \<phi>)"
  unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of_rexp_of'[symmetric] by (rule lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of)

theorem lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of'': "wf_formula n \<phi> \<Longrightarrow> lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi> = lang n (rexp_of'' n \<phi>)"
  unfolding lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'_rexp_of''[symmetric] by (rule lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_rexp_of')

end

(*<*)
end
(*>*)
