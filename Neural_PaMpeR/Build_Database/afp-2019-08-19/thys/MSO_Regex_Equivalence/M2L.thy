(* Author: Dmitriy Traytel *)

section \<open>M2L\<close>

(*<*)
theory M2L
imports Formula
begin
(*>*)

subsection \<open>Encodings\<close>

context formula
begin

fun enc :: "'a interp \<Rightarrow> ('a \<times> bool list) list" where
  "enc (w, I) = map_index (enc_atom I) w"

abbreviation "wf_interp w I \<equiv> (length w > 0 \<and>
    (\<forall>a \<in> set w. a \<in> set \<Sigma>) \<and>
    (\<forall>x \<in> set I. case x of Inl p \<Rightarrow> p < length w | Inr P \<Rightarrow> \<forall>p \<in> P. p < length w))"

fun wf_interp_for_formula :: "'a interp \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "wf_interp_for_formula (w, I) \<phi> =
    (wf_interp w I \<and>
    (\<forall>n \<in> FOV \<phi>. case I ! n of Inl _ \<Rightarrow> True | _ \<Rightarrow> False) \<and>
    (\<forall>n \<in> SOV \<phi>. case I ! n of Inl _ \<Rightarrow> False | _ \<Rightarrow> True))"

fun satisfies :: "'a interp \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "(w, I) \<Turnstile> FQ a m = (w ! (case I ! m of Inl p \<Rightarrow> p) = a)"
| "(w, I) \<Turnstile> FLess m1 m2 = ((case I ! m1 of Inl p \<Rightarrow> p) < (case I ! m2 of Inl p \<Rightarrow> p))"
| "(w, I) \<Turnstile> FIn m M = ((case I ! m of Inl p \<Rightarrow> p) \<in> (case I ! M of Inr P \<Rightarrow> P))"
| "(w, I) \<Turnstile> FNot \<phi> = (\<not> (w, I) \<Turnstile> \<phi>)"
| "(w, I) \<Turnstile> (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = ((w, I) \<Turnstile> \<phi>\<^sub>1 \<or> (w, I) \<Turnstile> \<phi>\<^sub>2)"
| "(w, I) \<Turnstile> (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = ((w, I) \<Turnstile> \<phi>\<^sub>1 \<and> (w, I) \<Turnstile> \<phi>\<^sub>2)"
| "(w, I) \<Turnstile> (FExists \<phi>) = (\<exists>p. p \<in> {0 .. length w - 1} \<and> (w, Inl p # I) \<Turnstile> \<phi>)"
| "(w, I) \<Turnstile> (FEXISTS \<phi>) = (\<exists>P. P \<subseteq> {0 .. length w - 1} \<and> (w, Inr P # I) \<Turnstile> \<phi>)"

definition lang\<^sub>M\<^sub>2\<^sub>L :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a \<times> bool list) list set" where
  "lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = {enc (w, I) | w I.
     length I = n \<and> wf_interp_for_formula (w, I) \<phi> \<and> satisfies (w, I) \<phi>}"

definition "dec_word \<equiv> map fst"

definition "positions_in_row w i =
  Option.these (set (map_index (\<lambda>p a_bs. if nth (snd a_bs) i then Some p else None) w))"

definition "dec_interp n FO (w :: ('a \<times> bool list) list) \<equiv> map (\<lambda>i.
  if i \<in> FO
  then Inl (the_elem (positions_in_row w i))
  else Inr (positions_in_row w i)) [0..<n]"

lemma positions_in_row: "positions_in_row w i = {p. p < length w \<and> snd (w ! p) ! i}"
  unfolding positions_in_row_def Option.these_def by (auto intro!: image_eqI[of _ the])

lemma positions_in_row_unique: "\<exists>!p. p < length w \<and> snd (w ! p) ! i \<Longrightarrow>
  the_elem (positions_in_row w i) = (THE p. p < length w \<and> snd (w ! p) ! i)"
  by (rule the1I2) (auto simp: the_elem_def positions_in_row)

lemma positions_in_row_length: "\<exists>!p. p < length w \<and> snd (w ! p) ! i \<Longrightarrow>
  the_elem (positions_in_row w i) < length w"
  unfolding positions_in_row_unique by (rule the1I2) auto

lemma dec_interp_Inl: "\<lbrakk>i \<in> FO; i < n\<rbrakk> \<Longrightarrow> \<exists>p. dec_interp n FO x ! i = Inl p"
  unfolding dec_interp_def using nth_map[of n "[0..<n]"] by auto

lemma dec_interp_not_Inr: "\<lbrakk>dec_interp n FO x ! i = Inr P; i \<in> FO; i < n\<rbrakk> \<Longrightarrow> False"
  unfolding dec_interp_def using nth_map[of n "[0..<n]"] by auto

lemma dec_interp_Inr: "\<lbrakk>i \<notin> FO; i < n\<rbrakk> \<Longrightarrow> \<exists>P. dec_interp n FO x ! i = Inr P"
  unfolding dec_interp_def using nth_map[of n "[0..<n]"] by auto

lemma dec_interp_not_Inl: "\<lbrakk>dec_interp n FO x ! i = Inl p; i \<notin> FO; i < n\<rbrakk> \<Longrightarrow> False"
  unfolding dec_interp_def using nth_map[of n "[0..<n]"] by auto

lemma Inl_dec_interp_length:
assumes "\<forall>i \<in> FO. \<exists>!p. p < length w \<and> snd (w ! p) ! i"
shows "Inl p \<in> set (dec_interp n FO w) \<Longrightarrow> p < length w"
  unfolding dec_interp_def by (auto intro: positions_in_row_length[OF bspec[OF assms]])

lemma Inr_dec_interp_length: "\<lbrakk>Inr P \<in> set (dec_interp n FO w); p \<in> P\<rbrakk> \<Longrightarrow> p < length w"
  unfolding dec_interp_def by (auto simp: positions_in_row)

lemma the_elem_Collect[simp]:
  assumes "\<exists>!x. P x"
  shows "the_elem (Collect P) = (The P)"
proof (unfold the_elem_def, rule the_equality)
  from assms have "P (The P)" by (rule theI')
  with assms show "Collect P = {The P}" by auto

  fix x assume "Collect P = {x}"
  then show "x = The P" by (auto intro: the_equality[symmetric])
qed
  

lemma enc_atom_dec: 
  "\<lbrakk>wf_word n w; \<forall>i \<in> FO. i < n \<longrightarrow> (\<exists>!p. p < length w \<and> snd (w ! p) ! i); p < length w\<rbrakk> \<Longrightarrow>
   enc_atom (dec_interp n FO w) p (fst (w ! p)) = w ! p"
  unfolding wf_word dec_interp_def map_filter_def Let_def
  by (auto 0 4 simp: comp_def \<sigma>_def set_n_lists positions_in_row dest: nth_mem[of p w]
    intro!: trans[OF iffD2[OF prod.inject] prod.collapse] nth_equalityI the_equality[symmetric]
    intro: the1I2[of "\<lambda>p. p < length w \<and> snd (w ! p) ! i" "\<lambda>p. snd (w ! p) ! i" for i]
    elim!: contrapos_np[of _ False])

lemma enc_dec:
  "\<lbrakk>wf_word n w; \<forall>i \<in> FO. i < n \<longrightarrow> (\<exists>!p. p < length w \<and> snd (w ! p) ! i)\<rbrakk> \<Longrightarrow>
   enc (dec_word w, dec_interp n FO w) = w"
  unfolding enc.simps dec_word_def
  by (intro trans[OF map_index_map map_index_congL] allI impI enc_atom_dec) assumption+

lemma dec_word_enc: "dec_word (enc (w, I)) = w"
  unfolding dec_word_def by auto

lemma enc_unique: 
  assumes "wf_interp w I" "i < length I"
  shows "\<exists>p. I ! i = Inl p \<Longrightarrow> \<exists>!p. p < length (enc (w, I)) \<and> snd (enc (w, I) ! p) ! i"
proof (erule exE)
  fix p assume "I ! i = Inl p"
  with assms show ?thesis by (auto simp: map_index all_set_conv_all_nth intro!: exI[of _ p])
qed

lemma dec_interp_enc_Inl:
  "\<lbrakk>dec_interp n FO (enc (w, I)) ! i = Inl p'; I ! i = Inl p; i \<in> FO; i < n; length I = n; p < length w; wf_interp w I\<rbrakk> \<Longrightarrow>
  p = p'"
  unfolding dec_interp_def using nth_map[of _ "[0..<n]"] positions_in_row_unique[OF enc_unique]
  by (auto intro: sym[OF the_equality])

lemma dec_interp_enc_Inr:
  "\<lbrakk>dec_interp n FO (enc (w, I)) ! i = Inr P'; I ! i = Inr P; i \<notin> FO; i < n; length I = n; \<forall>p \<in> P. p < length w\<rbrakk> \<Longrightarrow>
  P = P'"
  unfolding dec_interp_def positions_in_row by auto

lemma length_dec_interp[simp]: "length (dec_interp n FO x) = n"
   by (auto simp: dec_interp_def)

lemma nth_dec_interp[simp]: "i < n \<Longrightarrow> dec_interp n {} x ! i = Inr (positions_in_row x i)"
   by (auto simp: dec_interp_def)

lemma set_\<sigma>D[simp]: "(a, bs) \<in> set (\<sigma> \<Sigma> n) \<Longrightarrow> a \<in> set \<Sigma>"
  unfolding \<sigma>_def by auto

lemma lang_ENC:
 assumes "FO \<subseteq> {0 ..< n}" "SO \<subseteq> {0 ..< n} - FO"
 shows "lang n (ENC n FO) - {[]} = {enc (w, I) | w I . length I = n \<and> wf_interp w I \<and>
   (\<forall>i \<in> FO. case I ! i of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False) \<and>
   (\<forall>i \<in> SO. case I ! i of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)}"
   (is "?L = ?R")
proof (cases "FO = {}")
  case True with assms show ?thesis
    by (force simp: ENC_def dec_word_def wf_word
      in_set_conv_nth[of _ "dec_interp n {} x" for x] positions_in_row Ball_def
      intro!: enc_atom_\<sigma> exI[of _ "dec_word x :: 'a list" for x] exI[of _ "dec_interp n {} x" for x]
        enc_dec[of n _ "{}", symmetric, unfolded dec_word_def enc.simps map_index_map])
next
  case False
  hence nonempty: "valid_ENC n ` FO \<noteq> {}" by simp
  have finite: "finite (valid_ENC n ` FO)"
    by (intro finite_imageI[OF finite_subset[OF assms(1)]]) auto
  from False assms(1) have "0 < n" by auto
  with wf_rexp_valid_ENC assms(1) have wf_rexp: "\<forall>x \<in> valid_ENC n ` FO. wf n x" by auto
  { fix r w I assume "r \<in> FO" and *: "length I = n" "wf_interp w I"
      "(\<forall>i \<in> FO. case I ! i of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False)"
      "(\<forall>i \<in> SO. case I ! i of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)"
    then obtain p where p: "I ! r = Inl p" by (cases "I ! r") auto
    moreover from \<open>r \<in> FO\<close> assms(1) *(1) have "r < length I" by auto
    ultimately have "Inl p \<in> set I" by (auto simp add: in_set_conv_nth)
    with *(2) have "p < length w" by auto
    with *(2) obtain a where a: "w ! p = a" "a \<in> set \<Sigma>" by auto
    from \<open>r < length I\<close> p *(1) \<open>a \<in> set \<Sigma>\<close>
      have "[enc_atom I p a] \<in> lang n (Atom (Arbitrary_Except r True))"
      by (intro enc_atom_lang_Arbitrary_Except_True) auto
    moreover
    from \<open>r < length I\<close> p *(1) \<open>a \<in> set \<Sigma>\<close> *(2)  \<open>p < length w\<close>
      have "take p (enc (w, I)) \<in> star (lang n (Atom (Arbitrary_Except r False)))"
      by (auto simp: in_set_conv_nth simp del: lang.simps
        intro!: Ball_starI enc_atom_lang_Arbitrary_Except_False) auto
    moreover
    from \<open>r < length I\<close> p *(1) \<open>a \<in> set \<Sigma>\<close> *(2)  \<open>p < length w\<close>
      have "drop (Suc p) (enc (w, I)) \<in> star (lang n (Atom (Arbitrary_Except r False)))"
      by (auto simp: in_set_conv_nth simp del: lang.simps
        intro!: Ball_starI enc_atom_lang_Arbitrary_Except_False) auto
    ultimately have "take p (enc (w, I)) @ [enc_atom I p a] @ drop (p + 1) (enc (w, I)) \<in>
      lang n (valid_ENC n r)" using \<open>0 < n\<close> unfolding valid_ENC_def by (auto simp del: append.simps)
    with \<open>p < length w\<close> a have "enc (w, I) \<in> lang n (valid_ENC n r)"
      using id_take_nth_drop[of p "enc (w, I)"] by auto
  }
  hence "?R \<subseteq> ?L" using lang_flatten_INTERSECT[OF finite nonempty wf_rexp] by (auto simp add: ENC_def)
  moreover
  { fix x assume "x \<in> (\<Inter>r \<in> valid_ENC n ` FO. lang n r)"
    hence r: "\<forall>r \<in> FO. x \<in> lang n (valid_ENC n r)" by blast
    have "length (dec_interp n FO x) = n" unfolding dec_interp_def by simp
    moreover
    { fix r assume "r \<in> FO"
      with assms have "r < n" by auto
      from \<open>r \<in> FO\<close> r obtain u v w where uvw: "x = u @ v @ w"
        "u \<in> star (lang n (Atom (Arbitrary_Except r False)))"
        "v \<in> lang n (Atom (Arbitrary_Except r True))"
        "w \<in> star (lang n (Atom (Arbitrary_Except r False)))" using \<open>0 < n\<close> unfolding valid_ENC_def
        by (fastforce simp del: lang.simps(4))
      hence "length u < length x" "\<And>i. i < length x \<longrightarrow> snd (x ! i) ! r \<longleftrightarrow> i = length u"
         by (auto simp: nth_append nth_Cons' split: if_split_asm simp del: lang.simps
            dest!: Arbitrary_ExceptD[OF _ \<open>r < n\<close>]
            dest: star_Arbitrary_ExceptD[OF _ \<open>r < n\<close>, of u]
            elim!: iffD1[OF star_Arbitrary_ExceptD[OF _ \<open>r < n\<close>, of w False]]) auto
      hence "\<exists>!p. p < length x \<and> snd (x ! p) ! r" by auto
    } note * = this
    have x_wf_word: "wf_word n x" using wf_lang_wf_word[OF wf_rexp_valid_ENC] False r assms(1)
     by auto
    with * have "x = enc (dec_word x, dec_interp n FO x)" by (intro sym[OF enc_dec]) auto
    moreover
    from * have "wf_interp (dec_word x) (dec_interp n FO x)"
      "(\<forall>i \<in> FO. case dec_interp n FO x ! i of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False)"
      "(\<forall>i \<in> SO. case dec_interp n FO x ! i of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)"
      using False x_wf_word[unfolded wf_word, unfolded \<sigma>_def o_apply set_concat set_map set_n_lists, simplified] assms
        Inl_dec_interp_length[OF ballI, of FO x _ n] Inr_dec_interp_length[of _ n FO x]
        dec_interp_Inl[of _ FO n x] dec_interp_Inr[of _ FO n x]
      by (fastforce simp add: dec_word_def split: sum.split)+
    ultimately have "x \<in> ?R" by blast
  }
  with False lang_flatten_INTERSECT[OF finite nonempty wf_rexp] have "?L \<subseteq> ?R" by (auto simp add: ENC_def)
  ultimately show ?thesis by blast
qed

lemma lang_ENC_formula:
  assumes "wf_formula n \<phi>"
  shows "lang n (ENC n (FOV \<phi>)) - {[]} = {enc (w, I) | w I . length I = n \<and> wf_interp_for_formula (w, I) \<phi>}"
proof -
  from assms max_idx_vars have *: "FOV \<phi> \<subseteq> {0 ..< n}" "SOV \<phi> \<subseteq> {0 ..< n} - FOV \<phi>" by auto
  show ?thesis unfolding lang_ENC[OF *] by simp
qed

subsection \<open>Welldefinedness of enc wrt. Models\<close>

lemma enc_alt_def:
 "enc (w, x # I) = map_index (\<lambda>n (a, bs). (a, (case x of Inl p \<Rightarrow> n = p | Inr P \<Rightarrow> n \<in> P) # bs)) (enc (w, I))"
  by (auto simp: comp_def)

lemma enc_extend_interp: "enc (w, I) = enc (w', I') \<Longrightarrow> enc (w, x # I) = enc (w', x # I')"
  unfolding enc_alt_def by auto

lemma wf_interp_for_formula_FExists: 
  "\<lbrakk>wf_formula (length I) (FExists \<phi>); w \<noteq> []\<rbrakk>\<Longrightarrow>
    wf_interp_for_formula (w, I) (FExists \<phi>) \<longleftrightarrow>
    (\<forall>p < length w. wf_interp_for_formula (w, Inl p # I) \<phi>)"
  by (auto simp: nth_Cons' split: if_split_asm)

lemma wf_interp_for_formula_any_Inl: "wf_interp_for_formula (w, Inl p # I) \<phi> \<Longrightarrow>
  \<forall>p < length w. wf_interp_for_formula (w, Inl p # I) \<phi>"
  by (auto simp: nth_Cons' split: if_split_asm)

lemma wf_interp_for_formula_FEXISTS: 
 "\<lbrakk>wf_formula (length I) (FEXISTS \<phi>); w \<noteq> []\<rbrakk>\<Longrightarrow>
  wf_interp_for_formula (w, I) (FEXISTS \<phi>) \<longleftrightarrow> (\<forall>P \<subseteq> {0 .. length w - 1}. wf_interp_for_formula (w, Inr P # I) \<phi>)"
  by (auto simp: neq_Nil_conv nth_Cons')

lemma wf_interp_for_formula_any_Inr: "wf_interp_for_formula (w, Inr P # I) \<phi> \<Longrightarrow>
  \<forall>P \<subseteq> {0 .. length w - 1}. wf_interp_for_formula (w, Inr P # I) \<phi>"
  by (cases w) (auto simp: nth_Cons' split: if_split_asm)

lemma enc_word_length: "enc (w, I) = enc (w', I') \<Longrightarrow> length w = length w'"
  by (auto elim: map_index_eq_imp_length_eq)

lemma enc_length: 
  assumes "w \<noteq> []" "enc (w, I) = enc (w', I')"
  shows "length I = length I'"
  using assms
  length_map[of "(\<lambda>x. case x of Inl p \<Rightarrow> 0 = p | Inr P \<Rightarrow> 0 \<in> P)" I]
  length_map[of "(\<lambda>x. case x of Inl p \<Rightarrow> 0 = p | Inr P \<Rightarrow> 0 \<in> P)" I']
  by (induct rule: list_induct2[OF enc_word_length[OF assms(2)]]) auto

lemma wf_interp_for_formula_FOr:
  "wf_interp_for_formula (w, I) (FOr \<phi>1 \<phi>2) =
     (wf_interp_for_formula (w, I) \<phi>1 \<and> wf_interp_for_formula (w, I) \<phi>2)"
  by auto

lemma wf_interp_for_formula_FAnd:
  "wf_interp_for_formula (w, I) (FAnd \<phi>1 \<phi>2) =
     (wf_interp_for_formula (w, I) \<phi>1 \<and> wf_interp_for_formula (w, I) \<phi>2)"
  by auto

lemma enc_wf_interp: 
 assumes "wf_formula (length I) \<phi>" "wf_interp_for_formula (w, I) \<phi>"
 shows "wf_interp_for_formula (dec_word (enc (w, I)), dec_interp (length I) (FOV \<phi>) (enc (w, I))) \<phi>"
 (is "wf_interp_for_formula (_, ?dec) \<phi>")
  unfolding dec_word_enc
proof -
  { fix i assume i: "i \<in> FOV \<phi>"
    with assms(2) have "\<exists>p. I ! i = Inl p" by (cases "I ! i") auto
    with i assms have "\<exists>!p. p < length (enc (w, I)) \<and> snd (enc (w, I) ! p) ! i"
      by (intro enc_unique[of w I i]) (auto intro!: bspec[OF max_idx_vars] split: sum.splits)
  } note * = this
  have "\<forall>x \<in> set ?dec. case_sum (\<lambda>p. p < length w) (\<lambda>P. \<forall>p\<in>P. p < length w) x"
  proof (intro ballI, split sum.split, safe)
    fix p assume "Inl p \<in> set ?dec"
    thus "p < length w" using Inl_dec_interp_length[OF ballI[OF *]] by auto
  next
    fix p P assume "Inr P \<in> set ?dec" "p \<in> P"
    thus "p < length w" using Inr_dec_interp_length by fastforce
  qed
  thus "wf_interp_for_formula (w, ?dec) \<phi>"
  using assms
    dec_interp_Inl[of _ "FOV \<phi>" "length I" "enc (w, I)", OF _ bspec[OF max_idx_vars]]
    dec_interp_Inr[of _ "FOV \<phi>" "length I" "enc (w, I)", OF _ bspec[OF max_idx_vars]]
  by (fastforce split: sum.splits)
qed

lemma enc_welldef: "\<lbrakk>enc (w, I) = enc (w', I'); wf_formula (length I) \<phi>;
  wf_interp_for_formula (w, I) \<phi>; wf_interp_for_formula (w', I') \<phi>\<rbrakk> \<Longrightarrow>
  satisfies (w, I) \<phi> \<longleftrightarrow> satisfies (w', I') \<phi>"
proof (induction \<phi> arbitrary: I I')
  case (FQ a m)
  let ?dec = "\<lambda>w I. (dec_word (enc (w, I)), dec_interp (length I) (FOV (FQ a m)) (enc (w, I)))"
  from FQ(2,3) have "satisfies (w, I) (FQ a m) = satisfies (?dec w I) (FQ a m)"
    unfolding dec_word_enc 
    using dec_interp_enc_Inl[of "length I" "{m}" w I m]
    by (auto intro: nth_mem dest: dec_interp_not_Inr split: sum.splits) (metis nth_mem)+
  moreover
  from FQ(3) have *: "w \<noteq> []" by simp
  from FQ(2,4) have "satisfies (w', I') (FQ a m) = satisfies (?dec w' I') (FQ a m)"
    unfolding dec_word_enc enc_length[OF * FQ(1)]
    using dec_interp_enc_Inl[of "length I'" "{m}" w' I' m]
    by (auto dest: dec_interp_not_Inr split: sum.splits) (metis nth_mem)+
  ultimately show ?case unfolding FQ(1) enc_length[OF * FQ(1)] ..
next
  case (FLess m n)
  let ?dec = "\<lambda>w I. (dec_word (enc (w, I)), dec_interp (length I) (FOV (FLess m n)) (enc (w, I)))"
  from FLess(2,3) have "satisfies (w, I) (FLess m n) = satisfies (?dec (TYPE ('a)) w I) (FLess m n)"
    unfolding dec_word_enc
    using dec_interp_enc_Inl[of "length I" "{m, n}" w I m] dec_interp_enc_Inl[of "length I" "{m, n}" w I n]
    by (fastforce intro: nth_mem dest: dec_interp_not_Inr split: sum.splits)
  moreover
  from FLess(3) have *: "w \<noteq> []" by simp
  from FLess(2,4) have "satisfies (w', I') (FLess m n) = satisfies (?dec (TYPE ('a)) w' I') (FLess m n)"
    unfolding dec_word_enc enc_length[OF * FLess(1)]
    using dec_interp_enc_Inl[of "length I'" "{m, n}" w' I' m] dec_interp_enc_Inl[of "length I'" "{m, n}" w' I' n]
    by (fastforce intro: nth_mem dest: dec_interp_not_Inr split: sum.splits)
  ultimately show ?case unfolding FLess(1) enc_length[OF * FLess(1)] ..
next
  case (FIn m M)
  let ?dec = "\<lambda>w I. (dec_word (enc (w, I)), dec_interp (length I) (FOV (FIn m M)) (enc (w, I)))"
  from FIn(2,3) have "satisfies (w, I) (FIn m M) = satisfies (?dec (TYPE ('a)) w I) (FIn m M)"
    unfolding dec_word_enc
    using dec_interp_enc_Inl[of "length I" "{m}" w I m] dec_interp_enc_Inr[of "length I" "{m}" w I M]
    by (auto dest: dec_interp_not_Inr dec_interp_not_Inl split: sum.splits) (metis nth_mem)+
  moreover
  from FIn(3) have *: "w \<noteq> []" by simp
  from FIn(2,4) have "satisfies (w', I') (FIn m M) = satisfies (?dec (TYPE ('a)) w' I') (FIn m M)"
    unfolding dec_word_enc enc_length[OF * FIn(1)]
    using dec_interp_enc_Inl[of "length I'" "{m}" w' I' m] dec_interp_enc_Inr[of "length I'" "{m}" w' I' M]
    by (auto dest: dec_interp_not_Inr dec_interp_not_Inl split: sum.splits) (metis nth_mem)+
  ultimately show ?case unfolding FIn(1) enc_length[OF * FIn(1)] ..
next
  case (FOr \<phi>1 \<phi>2) show ?case unfolding satisfies.simps(5)
  proof (intro disj_cong)
    from FOr(3-6) show "satisfies (w, I) \<phi>1 = satisfies (w', I') \<phi>1"
      by (intro FOr(1)) auto
  next
    from FOr(3-6) show "satisfies (w, I) \<phi>2 = satisfies (w', I') \<phi>2"
      by (intro FOr(2)) auto
  qed
next
  case (FAnd \<phi>1 \<phi>2) show ?case unfolding satisfies.simps(6)
  proof (intro conj_cong)
    from FAnd(3-6) show "satisfies (w, I) \<phi>1 = satisfies (w', I') \<phi>1"
      by (intro FAnd(1)) auto
  next
    from FAnd(3-6) show "satisfies (w, I) \<phi>2 = satisfies (w', I') \<phi>2"
      by (intro FAnd(2)) auto
  qed
next
  case (FExists \<phi>)
  hence "w \<noteq> []" "w' \<noteq> []" by auto
  hence length: "length w = length w'" "length I = length I'"
    using enc_word_length[OF FExists.prems(1)] enc_length[OF _ FExists.prems(1)] by auto
  show ?case
  proof
    assume "satisfies (w, I) (FExists \<phi>)"
    with FExists.prems(3) obtain p where "p < length w" "satisfies (w, Inl p # I) \<phi>"
      by (auto intro: ord_less_eq_trans[OF le_imp_less_Suc Suc_pred])
    moreover
    with FExists.prems have "satisfies (w', Inl p # I') \<phi>"
    proof (intro iffD1[OF FExists.IH[of "Inl p # I" "Inl p # I'"]])
      from FExists.prems(2,3) \<open>p < length w\<close> show "wf_interp_for_formula (w, Inl p # I) \<phi>"
        by (blast dest: wf_interp_for_formula_FExists[of I, OF _ \<open>w \<noteq> []\<close>])
    next
      from FExists.prems(2,4) \<open>p < length w\<close> show "wf_interp_for_formula (w', Inl p # I') \<phi>"
        unfolding length by (blast dest: wf_interp_for_formula_FExists[of I', OF _ \<open>w' \<noteq> []\<close>])
    qed (auto elim: enc_extend_interp simp del: enc.simps)
    ultimately show "satisfies (w', I') (FExists \<phi>)" using length by (auto intro!: exI[of _ p])
  next
    assume "satisfies (w', I') (FExists \<phi>)"
    with FExists.prems(1,2,4) obtain p where "p < length w'" "satisfies (w', Inl p # I') \<phi>"
      by (auto intro: ord_less_eq_trans[OF le_imp_less_Suc Suc_pred])
    moreover
    with FExists.prems have "satisfies (w, Inl p # I) \<phi>"
    proof (intro iffD2[OF FExists.IH[of "Inl p # I" "Inl p # I'"]])
      from FExists.prems(2,3) \<open>p < length w'\<close> show "wf_interp_for_formula (w, Inl p # I) \<phi>"
        unfolding length[symmetric] by (blast dest: wf_interp_for_formula_FExists[of I, OF _ \<open>w \<noteq> []\<close>])
    next
      from FExists.prems(2,4) \<open>p < length w'\<close> show "wf_interp_for_formula (w', Inl p # I') \<phi>"
        unfolding length by (blast dest: wf_interp_for_formula_FExists[of I', OF _ \<open>w' \<noteq> []\<close>])
    qed (auto elim: enc_extend_interp simp del: enc.simps)
    ultimately show "satisfies (w, I) (FExists \<phi>)" using length by (auto intro!: exI[of _ p])
  qed
next
  case (FEXISTS \<phi>)
  hence "w \<noteq> []" "w' \<noteq> []" by auto
  hence length: "length w = length w'" "length I = length I'"
    using enc_word_length[OF FEXISTS.prems(1)] enc_length[OF _ FEXISTS.prems(1)] by auto
  show ?case
  proof
    assume "satisfies (w, I) (FEXISTS \<phi>)"
    then obtain P where P: "P \<subseteq> {0 .. length w - 1}" "satisfies (w, Inr P # I) \<phi>" by auto
    moreover
    with FEXISTS.prems have "satisfies (w', Inr P # I') \<phi>"
    proof (intro iffD1[OF FEXISTS.IH[of "Inr P # I" "Inr P # I'"]])
      from FEXISTS.prems(2,3) P(1) show "wf_interp_for_formula (w, Inr P # I) \<phi>"
        by (blast dest: wf_interp_for_formula_FEXISTS[of I, OF _ \<open>w \<noteq> []\<close>])
    next
      from FEXISTS.prems(2,4) P(1) show "wf_interp_for_formula (w', Inr P # I') \<phi>"
        unfolding length by (blast dest: wf_interp_for_formula_FEXISTS[of I', OF _ \<open>w' \<noteq> []\<close>])
    qed (auto elim: enc_extend_interp simp del: enc.simps)
    ultimately show "satisfies (w', I') (FEXISTS \<phi>)" using length by (auto intro!: exI[of _ P])
  next
    assume "satisfies (w', I') (FEXISTS \<phi>)"
    then obtain P where P: "P \<subseteq> {0 .. length w' - 1}" "satisfies (w', Inr P # I') \<phi>" by auto
    moreover
    with FEXISTS.prems have "satisfies (w, Inr P # I) \<phi>"
    proof (intro iffD2[OF FEXISTS.IH[of "Inr P # I" "Inr P # I'"]])
      from FEXISTS.prems(2,3) P(1) show "wf_interp_for_formula (w, Inr P # I) \<phi>"
        unfolding length[symmetric] by (blast dest: wf_interp_for_formula_FEXISTS[of I, OF _ \<open>w \<noteq> []\<close>])
    next
      from FEXISTS.prems(2,4) P(1) show "wf_interp_for_formula (w', Inr P # I') \<phi>"
        unfolding length by (blast dest: wf_interp_for_formula_FEXISTS[of I', OF _ \<open>w' \<noteq> []\<close>])
    qed (auto elim: enc_extend_interp simp del: enc.simps)
    ultimately show "satisfies (w, I) (FEXISTS \<phi>)" using length by (auto intro!: exI[of _ P])
  qed
qed auto

lemma lang\<^sub>M\<^sub>2\<^sub>L_FOr:
  assumes "wf_formula n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)"
  shows "lang\<^sub>M\<^sub>2\<^sub>L n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq>
    (lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1 \<union> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2) \<inter> {enc (w, I) | w I. length I = n \<and> wf_interp_for_formula (w, I) (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)}"
    (is "_ \<subseteq> (?L1 \<union> ?L2) \<inter> ?ENC")
proof (intro equalityI subsetI)
  fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)"
  then obtain w I where
    *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)" "length I = n" "length w > 0" and
     "satisfies (w, I) \<phi>\<^sub>1 \<or> satisfies (w, I) \<phi>\<^sub>2" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
  thus "x \<in> (?L1 \<union> ?L2) \<inter> ?ENC"
  proof (elim disjE)
    assume "satisfies (w, I) \<phi>\<^sub>1"
    with * have "x \<in> ?L1" using assms unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by (fastforce)
    with * show ?thesis by auto
  next
    assume "satisfies (w, I) \<phi>\<^sub>2"
    with * have "x \<in>?L2" using assms unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by (fastforce)
    with * show ?thesis by auto
  qed
qed

lemma lang\<^sub>M\<^sub>2\<^sub>L_FAnd:
  assumes "wf_formula n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)"
  shows "lang\<^sub>M\<^sub>2\<^sub>L n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq>
    lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1 \<inter> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2 \<inter> {enc (w, I) | w I. length I = n \<and> wf_interp_for_formula (w, I) (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)}"
    (is "_ \<subseteq> ?L1 \<inter> ?L2 \<inter> ?ENC")
  using assms unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by (fastforce)

subsection \<open>From M2L to Regular expressions\<close>

fun rexp_of :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a atom) rexp" where
  "rexp_of n (FQ a m) = Inter (TIMES [Full, Atom (AQ m a), Full]) (ENC n {m})"
| "rexp_of n (FLess m1 m2) = (if m1 = m2 then Zero else Inter
    (TIMES [Full, Atom (Arbitrary_Except m1 True), Full, Atom (Arbitrary_Except m2 True), Full])
    (ENC n {m1, m2}))"
| "rexp_of n (FIn m M) = 
    Inter (TIMES [Full, Atom (Arbitrary_Except2 m M), Full]) (ENC n {m})"
| "rexp_of n (FNot \<phi>) = Inter (rexp.Not (rexp_of n \<phi>)) (ENC n (FOV (FNot \<phi>)))"
| "rexp_of n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = Inter (Plus (rexp_of n \<phi>\<^sub>1) (rexp_of n \<phi>\<^sub>2)) (ENC n (FOV (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)))"
| "rexp_of n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = INTERSECT [rexp_of n \<phi>\<^sub>1, rexp_of n \<phi>\<^sub>2, ENC n (FOV (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2))]"
| "rexp_of n (FExists \<phi>) = Pr (rexp_of (n + 1) \<phi>)"
| "rexp_of n (FEXISTS \<phi>) = Pr (rexp_of (n + 1) \<phi>)"

fun rexp_of_alt :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a atom) rexp" where
  "rexp_of_alt n (FQ a m) = TIMES [Full, Atom (AQ m a), Full]"
| "rexp_of_alt n (FLess m1 m2) = (if m1 = m2 then Zero else
    TIMES [Full, Atom (Arbitrary_Except m1 True), Full, Atom (Arbitrary_Except m2 True), Full])"
| "rexp_of_alt n (FIn m M) = TIMES [Full, Atom (Arbitrary_Except2 m M), Full]"
| "rexp_of_alt n (FNot \<phi>) = rexp.Not (rexp_of_alt n \<phi>)"
| "rexp_of_alt n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = Plus (rexp_of_alt n \<phi>\<^sub>1) (rexp_of_alt n \<phi>\<^sub>2)"
| "rexp_of_alt n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = Inter (rexp_of_alt n \<phi>\<^sub>1) (rexp_of_alt n \<phi>\<^sub>2)"
| "rexp_of_alt n (FExists \<phi>) = Pr (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>)))"
| "rexp_of_alt n (FEXISTS \<phi>) = Pr (Inter (rexp_of_alt (n + 1) \<phi>) (ENC (n + 1) (FOV \<phi>)))"

definition "rexp_of' n \<phi> = Inter (rexp_of_alt n \<phi>) (ENC n (FOV \<phi>))"

fun rexp_of_alt' :: "nat \<Rightarrow> 'a formula \<Rightarrow> ('a atom) rexp" where
  "rexp_of_alt' n (FQ a m) = TIMES [Full, Atom (AQ m a), Full]"
| "rexp_of_alt' n (FLess m1 m2) = (if m1 = m2 then Zero else
    TIMES [Full, Atom (Arbitrary_Except m1 True), Full, Atom (Arbitrary_Except m2 True), Full])"
| "rexp_of_alt' n (FIn m M) = TIMES [Full, Atom (Arbitrary_Except2 m M), Full]"
| "rexp_of_alt' n (FNot \<phi>) = rexp.Not (rexp_of_alt' n \<phi>)"
| "rexp_of_alt' n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = Plus (rexp_of_alt' n \<phi>\<^sub>1) (rexp_of_alt' n \<phi>\<^sub>2)"
| "rexp_of_alt' n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = Inter (rexp_of_alt' n \<phi>\<^sub>1) (rexp_of_alt' n \<phi>\<^sub>2)"
| "rexp_of_alt' n (FExists \<phi>) = Pr (Inter (rexp_of_alt' (n + 1) \<phi>) (ENC (n + 1) {0}))"
| "rexp_of_alt' n (FEXISTS \<phi>) = Pr (rexp_of_alt' (n + 1) \<phi>)"

definition "rexp_of'' n \<phi> = Inter (rexp_of_alt' n \<phi>) (ENC n (FOV \<phi>))"

theorem lang\<^sub>M\<^sub>2\<^sub>L_rexp_of: "wf_formula n \<phi> \<Longrightarrow> lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = lang n (rexp_of n \<phi>) - {[]}"
   (is "_ \<Longrightarrow> _ = ?L n \<phi>")
proof (induct \<phi> arbitrary: n)
  case (FQ a m)
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FQ a m)"
    then obtain w I where
      *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FQ a m)" "satisfies (w, I) (FQ a m)"
       "length I = n"
      unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by blast
    with FQ(1) obtain p where p: "p < length w" "I ! m = Inl p" "w ! p = a"
      by (auto simp: all_set_conv_all_nth split: sum.splits)
    with *(1) have "x = take p (enc (w, I)) @ [enc_atom I p a] @ drop (p + 1) (enc (w, I))"
      using id_take_nth_drop[of p "enc (w, I)"] by auto
    moreover from *(4) FQ(1) p(2)
     have "[enc_atom I p a] \<in> lang n (Atom (AQ m a))"
       by (intro enc_atom_lang_AQ) auto
    moreover from *(2,4) have "take p (enc (w, I)) \<in> lang n (Full)"
      by (auto intro!: enc_atom_\<sigma> dest!: in_set_takeD)
    moreover from *(2,4) have "drop (Suc p) (enc (w, I)) \<in> lang n (Full)"
      by (auto intro!: enc_atom_\<sigma> dest!: in_set_dropD)
    ultimately show "x \<in> ?L n (FQ a m)" using *(1,2,4)
      unfolding rexp_of.simps lang.simps(6,9) rexp_of_list.simps Int_Diff
        lang_ENC_formula[OF FQ, unfolded FOV.simps]
      by (auto elim: ssubst simp del: o_apply append.simps lang.simps)
  next
    fix x assume x: "x \<in> ?L n (FQ a m)"
    with FQ obtain w I p where m: "I ! m = Inl p" "m < length I" and
      wI: "x = enc (w, I)" "length I = n" "wf_interp_for_formula (w, I) (FQ a m)"
      unfolding rexp_of.simps lang.simps lang_ENC_formula[OF FQ, unfolded FOV.simps] Int_Diff
      by atomize_elim (auto split: sum.splits)
    hence "wf_interp_for_formula (dec_word x, dec_interp n {m} x) (FQ a m)" unfolding wI(1)
      using enc_wf_interp[OF FQ(1)[folded wI(2)]] by auto
    moreover
    from x obtain u1 u u2 where "x = u1 @ u @ u2" "u \<in> lang n (Atom (AQ m a))"
      unfolding rexp_of.simps lang.simps rexp_of_list.simps using concE by fast
    with FQ(1) obtain v where v: "x = u1 @ [v] @ u2" "snd v ! m" "fst v = a"
      using AQ_D[of u n m a] by fastforce
    hence u: "length u1 < length x" by auto
    { from v have "snd (x ! length u1) ! m" by auto
      moreover
      from m wI have "p < length x" "snd (x ! p) ! m"
        by (fastforce intro: nth_mem split: sum.splits)+
      moreover
      from m wI have ex1: "\<exists>!p. p < length x \<and> snd (x ! p) ! m" unfolding wI(1) by (intro enc_unique) auto
      ultimately have "p = length u1" using u by auto
    } note * = this
    from v have "v = enc (w, I) ! length u1" unfolding wI(1) by simp
    hence "a = w ! length u1" using nth_map[OF u, of fst] unfolding wI(1) v(3)[symmetric] by auto
    with * m wI have "satisfies (dec_word x, dec_interp n {m} x) (FQ a m)"
      unfolding dec_word_enc[of w I, folded wI(1)]
      by (auto simp del: enc.simps dest: dec_interp_not_Inr split: sum.splits)
         (fastforce dest!: dec_interp_enc_Inl intro: nth_mem split: sum.splits)
    moreover from wI have "wf_word n x" unfolding wf_word by (auto intro!: enc_atom_\<sigma>)
    ultimately show "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FQ a m)" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def using m wI(3)
      by (auto simp del: enc.simps intro!: exI[of _ "dec_word x"] exI[of _ "dec_interp n {m} x"]
        intro: sym[OF enc_dec[OF _ ballI[OF impI[OF enc_unique[of w I, folded wI(1)]]]]])
  qed
next
  case (FLess m m')
  show ?case
  proof (cases "m = m'")
    case False
    thus ?thesis
    proof (intro equalityI subsetI)
      fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FLess m m')"
      then obtain w I where
        *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FLess m m')" "satisfies (w, I) (FLess m m')"
         "length I = n"
        unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by blast
      with FLess(1) obtain p q where pq: "p < length w" "I ! m = Inl p" "q < length w" "I ! m' = Inl q" "p < q"
        by (auto simp: all_set_conv_all_nth split: sum.splits)
      with *(1) have "x = take p (enc (w, I)) @ [enc_atom I p (w ! p)] @ drop (p + 1) (enc (w, I))"
        using id_take_nth_drop[of p "enc (w, I)"] by auto
      also have "drop (p + 1) (enc (w, I)) = take (q - p - 1) (drop (p + 1) (enc (w, I))) @
        [enc_atom I q (w ! q)] @ drop (q - p) (drop (p + 1) (enc (w, I)))" (is "_ = ?LHS")
        using id_take_nth_drop[of "q - p - 1" "drop (p + 1) (enc (w, I))"] pq by auto
      finally have "x = take p (enc (w, I)) @ [enc_atom I p (w ! p)] @ ?LHS" .
      moreover from *(2,4) FLess(1) pq(1,2)
       have "[enc_atom I p (w ! p)] \<in> lang n (Atom (Arbitrary_Except m True))"
         by (intro enc_atom_lang_Arbitrary_Except_True) auto
      moreover from *(2,4) FLess(1) pq(3,4)
       have "[enc_atom I q (w ! q)] \<in> lang n (Atom (Arbitrary_Except m' True))"
         by (intro enc_atom_lang_Arbitrary_Except_True) auto
      moreover from *(2,4) have "take p (enc (w, I)) \<in> lang n (Full)"
        by (auto intro!: enc_atom_\<sigma> dest!: in_set_takeD)
      moreover from *(2,4) have "take (q - p - 1) (drop (Suc p) (enc (w, I))) \<in> lang n (Full)"
        by (auto intro!: enc_atom_\<sigma> dest!: in_set_dropD in_set_takeD)
      moreover from *(2,4) have "drop (q - p) (drop (Suc p) (enc (w, I))) \<in> lang n (Full)"
        by (auto intro!: enc_atom_\<sigma> dest!: in_set_dropD)
      ultimately show "x \<in> ?L n (FLess m m')" using *(1,2,4)
        unfolding rexp_of.simps lang.simps(6,9) rexp_of_list.simps Int_Diff
          lang_ENC_formula[OF FLess, unfolded FOV.simps] if_not_P[OF False]
        by (auto elim: ssubst simp del: o_apply append.simps lang.simps)
    next
      fix x assume x: "x \<in> ?L n (FLess m m')"
      with FLess obtain w I where
        wI: "x = enc (w, I)" "length I = n" "wf_interp_for_formula (w, I) (FLess m m')"
        unfolding rexp_of.simps lang.simps lang_ENC_formula[OF FLess, unfolded FOV.simps] Int_Diff
          if_not_P[OF False]
        by (fastforce split: sum.splits)
      with FLess obtain p p' where m: "I ! m = Inl p" "m < length I" "I ! m' = Inl p'" "m' < length I"
        by (auto split: sum.splits)
      with wI have "wf_interp_for_formula (dec_word x, dec_interp n {m, m'} x) (FLess m m')" unfolding wI(1)
        using enc_wf_interp[OF FLess(1)[folded wI(2)]] by auto
      moreover
      from x obtain u1 u u2 u' u3 where "x = u1 @ u @ u2 @ u' @ u3"
        "u \<in> lang n (Atom (Arbitrary_Except m True))" 
        "u' \<in> lang n (Atom (Arbitrary_Except m' True))"
        unfolding rexp_of.simps lang.simps rexp_of_list.simps if_not_P[OF False] using concE by fast
      with FLess(1) obtain v v' where v: "x = u1 @ [v] @ u2 @ [v'] @ u3" "snd v ! m" "snd v' ! m'"
        using Arbitrary_ExceptD[of u n m True] Arbitrary_ExceptD[of u' n m' True] by fastforce
      hence u: "length u1 < length x" and u': "Suc (length u1 + length u2) < length x" (is "?u' < _") by auto
      { from v have "snd (x ! length u1) ! m" by auto
        moreover
        from m wI have "p < length x" "snd (x ! p) ! m"
          by (fastforce intro: nth_mem split: sum.splits)+
        moreover
        from m wI have ex1: "\<exists>!p. p < length x \<and> snd (x ! p) ! m" unfolding wI(1) by (intro enc_unique) auto
        ultimately have "p = length u1" using u by auto
      }
      { from v have "snd (x ! ?u') ! m'" by (auto simp: nth_append)
        moreover
        from m wI have "p' < length x" "snd (x ! p') ! m'"
          by (fastforce intro: nth_mem split: sum.splits)+
        moreover
        from m wI have ex1: "\<exists>!p. p < length x \<and> snd (x ! p) ! m'" unfolding wI(1) by (intro enc_unique) auto
        ultimately have "p' = ?u'" using u' by auto
      } note * = this \<open>p = length u1\<close>
      with * m wI have "satisfies (dec_word x, dec_interp n {m, m'} x) (FLess m m')"
        unfolding dec_word_enc[of w I, folded wI(1)]
        by (auto simp del: enc.simps dest: dec_interp_not_Inr split: sum.splits)
           (fastforce dest!: dec_interp_enc_Inl intro: nth_mem split: sum.splits)
      moreover from wI have "wf_word n x" unfolding wf_word by (auto intro!: enc_atom_\<sigma>)
      ultimately show "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FLess m m')" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def using m wI(3)
        by (auto simp del: enc.simps intro!: exI[of _ "dec_word x"] exI[of _ "dec_interp n {m, m'} x"]
          intro: sym[OF enc_dec[OF _ ballI[OF impI[OF enc_unique[of w I, folded wI(1)]]]]])
    qed
  qed (simp add: lang\<^sub>M\<^sub>2\<^sub>L_def del: o_apply)
next
  case (FIn m M)
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FIn m M)"
    then obtain w I where
      *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FIn m M)" "satisfies (w, I) (FIn m M)"
       "length I = n"
      unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by blast
    with FIn(1) obtain p P where p: "p < length w" "I ! m = Inl p" "I ! M = Inr P" "p \<in> P"
      by (auto simp: all_set_conv_all_nth split: sum.splits)
    with *(1) have "x = take p (enc (w, I)) @ [enc_atom I p (w ! p)] @ drop (p + 1) (enc (w, I))"
      using id_take_nth_drop[of p "enc (w, I)"] by auto
    moreover
     from *(2,4) FIn(1) p have "[enc_atom I p (w ! p)] \<in> lang n (Atom (Arbitrary_Except2 m M))"
       by (intro enc_atom_lang_Arbitrary_Except2) auto
    moreover from *(2,4) have "take p (enc (w, I)) \<in> lang n (Full)"
      by (auto intro!: enc_atom_\<sigma> dest!: in_set_takeD)
    moreover from *(2,4) have "drop (Suc p) (enc (w, I)) \<in> lang n (Full)"
      by (auto intro!: enc_atom_\<sigma> dest!: in_set_dropD)
    ultimately show "x \<in> ?L n (FIn m M)" using *(1,2,4)
      unfolding rexp_of.simps lang.simps(6,9) rexp_of_list.simps Int_Diff
        lang_ENC_formula[OF FIn, unfolded FOV.simps]
      by (auto elim: ssubst simp del: o_apply append.simps lang.simps)
  next
    fix x assume x: "x \<in> ?L n (FIn m M)"
    with FIn obtain w I where  wI: "x = enc (w, I)" "length I = n" "wf_interp_for_formula (w, I) (FIn m M)"
      unfolding rexp_of.simps lang.simps lang_ENC_formula[OF FIn, unfolded FOV.simps] Int_Diff
      by (fastforce split: sum.splits)
    with FIn obtain p P where m: "I ! m = Inl p" "m < length I" "I ! M = Inr P" "M < length I" by (auto split: sum.splits)
    with wI have "wf_interp_for_formula (dec_word x, dec_interp n {m} x) (FIn m M)" unfolding wI(1)
      using enc_wf_interp[OF FIn(1)[folded wI(2)]] by auto
    moreover
    from x obtain u1 u u2 where "x = u1 @ u @ u2"
      "u \<in> lang n (Atom (Arbitrary_Except2 m M))"
      unfolding rexp_of.simps lang.simps rexp_of_list.simps using concE by fast
    with FIn(1) obtain v where v: "x = u1 @ [v] @ u2" "snd v ! m" "snd v ! M"
      using Arbitrary_Except2D[of u n m M] by fastforce
    from v have u: "length u1 < length x" by auto
    { from v have "snd (x ! length u1) ! m" by auto
      moreover
      from m wI have "p < length x" "snd (x ! p) ! m"
        by (fastforce intro: nth_mem split: sum.splits)+
      moreover
      from m wI have ex1: "\<exists>!p. p < length x \<and> snd (x ! p) ! m" unfolding wI(1) by (intro enc_unique) auto
      ultimately have "p = length u1" using u by auto
    } note * = this
    from v have "v = enc (w, I) ! length u1" unfolding wI(1) by simp
    with v(3) m(3,4) u wI(1) have "length u1 \<in> P" by auto
    with * m wI have "satisfies (dec_word x, dec_interp n {m} x) (FIn m M)"
      unfolding dec_word_enc[of w I, folded wI(1)]
      by (auto simp del: enc.simps dest: dec_interp_not_Inr dec_interp_not_Inl split: sum.splits)
         (auto simp del: enc.simps dest!: dec_interp_enc_Inl dec_interp_enc_Inr dest: nth_mem split: sum.splits)
    moreover from wI have "wf_word n x" unfolding wf_word by (auto intro!: enc_atom_\<sigma>)
    ultimately show "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FIn m M)" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def using m wI(3)
      by (auto simp del: enc.simps intro!: exI[of _ "dec_word x"] exI[of _ "dec_interp n {m} x"]
        intro: sym[OF enc_dec[OF _ ballI[OF impI[OF enc_unique[of w I, folded wI(1)]]]]])
  qed
next
  case (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)
  from FOr(3) have IH1: "lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1 = lang n (rexp_of n \<phi>\<^sub>1) - {[]}"
    by (intro FOr(1)) auto
  from FOr(3) have IH2: "lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2 = lang n (rexp_of n \<phi>\<^sub>2) - {[]}"
    by (intro FOr(2)) auto
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)" thus "x \<in> lang n (rexp_of n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)) - {[]}"
      using lang\<^sub>M\<^sub>2\<^sub>L_FOr[OF FOr(3)] unfolding lang_ENC_formula[OF FOr(3)] rexp_of.simps lang.simps
        IH1 IH2 Int_Diff by auto
  next
    fix x assume "x \<in> lang n (rexp_of n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)) - {[]}"
    then obtain w I where or: "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1 \<or> x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2" and wI: "x = enc (w, I)" "length I = n"
      "wf_interp_for_formula (w, I) (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)"
      unfolding lang_ENC_formula[OF FOr(3)] rexp_of.simps lang.simps IH1 IH2 Int_Diff by auto
    have "satisfies (w, I) \<phi>\<^sub>1 \<or> satisfies (w, I) \<phi>\<^sub>2"
    proof (intro mp[OF disj_mono[OF impI impI] or])
      assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1"
      with wI(2,3) FOr(3) show "satisfies (w, I) \<phi>\<^sub>1"
        unfolding lang\<^sub>M\<^sub>2\<^sub>L_def wI(1) wf_interp_for_formula_FOr
        by (auto simp del: enc.simps dest!: iffD2[OF enc_welldef[of _ _ _ _ \<phi>\<^sub>1]])
    next
      assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2"
      with wI(2,3) FOr(3) show "satisfies (w, I) \<phi>\<^sub>2"
        unfolding lang\<^sub>M\<^sub>2\<^sub>L_def wI(1) wf_interp_for_formula_FOr
        by (auto simp del: enc.simps dest!: iffD2[OF enc_welldef[of _ _ _ _ \<phi>\<^sub>2]])
    qed
    with wI show "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
  qed
next
  case (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
  from FAnd(3) have IH1: "lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1 = lang n (rexp_of n \<phi>\<^sub>1) - {[]}"
    by (intro FAnd(1)) auto
  from FAnd(3) have IH2: "lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2 = lang n (rexp_of n \<phi>\<^sub>2) - {[]}"
    by (intro FAnd(2)) auto
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)" thus "x \<in> lang n (rexp_of n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)) - {[]}"
      using lang\<^sub>M\<^sub>2\<^sub>L_FAnd[OF FAnd(3)] unfolding lang_ENC_formula[OF FAnd(3)] rexp_of.simps
        rexp_of_list.simps lang.simps IH1 IH2 Int_Diff by auto
  next
    fix x assume "x \<in> lang n (rexp_of n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)) - {[]}"
    then obtain w I where "and": "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1 \<and> x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2" and wI: "x = enc (w, I)" "length I = n"
      "wf_interp_for_formula (w, I) (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)"
      unfolding lang_ENC_formula[OF FAnd(3)] rexp_of.simps rexp_of_list.simps lang.simps IH1 IH2
        Int_Diff by auto
    have "satisfies (w, I) \<phi>\<^sub>1 \<and> satisfies (w, I) \<phi>\<^sub>2"
    proof (intro mp[OF conj_mono[OF impI impI] "and"])
      assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>1"
      with wI(2,3) FAnd(3) show "satisfies (w, I) \<phi>\<^sub>1"
        unfolding lang\<^sub>M\<^sub>2\<^sub>L_def wI(1) wf_interp_for_formula_FAnd
        by (auto simp del: enc.simps dest!: iffD2[OF enc_welldef[of _ _ _ _ \<phi>\<^sub>1]])
    next
      assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>\<^sub>2"
      with wI(2,3) FAnd(3) show "satisfies (w, I) \<phi>\<^sub>2"
        unfolding lang\<^sub>M\<^sub>2\<^sub>L_def wI(1) wf_interp_for_formula_FAnd
        by (auto simp del: enc.simps dest!: iffD2[OF enc_welldef[of _ _ _ _ \<phi>\<^sub>2]])
    qed
    with wI show "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
  qed
next
  case (FNot \<phi>)
  hence IH: "?L n \<phi> =  lang\<^sub>M\<^sub>2\<^sub>L n \<phi>" by simp
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FNot \<phi>)"
    then obtain w I where
      *: "x = enc (w, I)" "wf_interp_for_formula (w, I) \<phi>" "length I = n" "length w > 0"
       and unsat: "\<not> (satisfies (w, I) \<phi>)"
       unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    { assume "x \<in> ?L n \<phi>"
      with IH have "satisfies (w, I) \<phi>" using enc_welldef[of _ _ w I \<phi>, OF _ _ _ *(2)] FNot(2)
        unfolding *(1,3) lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    }
    with unsat have "x \<notin> ?L n \<phi>" by blast
    with * show "x \<in> ?L n (FNot \<phi>)" unfolding rexp_of.simps lang.simps
      using lang_ENC_formula[OF FNot(2)] by (auto simp: comp_def intro!: enc_atom_\<sigma>)
  next
    fix x assume "x \<in> ?L n (FNot \<phi>)"
    with IH have "x \<in> lang n (ENC n (FOV (FNot \<phi>))) - {[]}" and x: "x \<notin> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>" by (auto simp del: o_apply)
    then obtain w I where *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FNot \<phi>)" "length I = n"
      unfolding lang_ENC_formula[OF FNot(2)] by blast
    { assume "\<not> satisfies (w, I) (FNot \<phi>)"
      with * have "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n \<phi>" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    }
    with x * show "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FNot \<phi>)"  unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by blast
  qed
next
  case (FExists \<phi>)
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FExists \<phi>)"
    then obtain w I p where
      *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FExists \<phi>)"
       "length I = n" "length w > 0" "p \<in> {0 .. length w - 1}" "satisfies (w, Inl p # I) \<phi>"
       unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    with FExists(2) have "enc (w, Inl p # I) \<in> ?L (Suc n) \<phi>"
      by (intro subsetD[OF equalityD1[OF FExists(1)], of "Suc n" "enc (w, Inl p # I)"])
       (auto simp: lang\<^sub>M\<^sub>2\<^sub>L_def nth_Cons' ord_less_eq_trans[OF le_imp_less_Suc Suc_pred[OF *(4)]]
        split: if_split_asm sum.splits intro!: exI[of _ w] exI[of _ "Inl p # I"])
    with *(1) show "x \<in> ?L n (FExists \<phi>)"
      by (auto simp: map_index intro!: image_eqI[of _ "map \<pi>"] simp del: o_apply) (auto simp: \<pi>_def)
  next
    fix x assume "x \<in> ?L n (FExists \<phi>)"
    then obtain x' where x: "x = map \<pi> x'" and "x' \<in> ?L (Suc n) \<phi>" by (auto simp del: o_apply)
    with FExists(2) have "x' \<in> lang\<^sub>M\<^sub>2\<^sub>L (Suc n) \<phi>"
      by (intro subsetD[OF equalityD2[OF FExists(1)], of "Suc n" x'])
         (auto split: if_split_asm sum.splits)
    then obtain w I' where
      *: "x' = enc (w, I')" "wf_interp_for_formula (w, I') \<phi>" "length I' = Suc n" "satisfies (w, I') \<phi>"
       unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    moreover then obtain I\<^sub>0 I where "I' = I\<^sub>0 # I" by (cases I') auto
    moreover with FExists(2) *(2) obtain p where "I\<^sub>0 = Inl p" "p < length w"
      by (auto simp: nth_Cons' split: sum.splits if_split_asm)
    ultimately have "x = enc (w, I)" "wf_interp_for_formula (w, I) (FExists \<phi>)" "length I = n"
      "length w > 0" "satisfies (w, I) (FExists \<phi>)" using FExists(2) unfolding x
      by (auto simp: map_tl nth_Cons' split: if_split_asm simp del: o_apply) (auto simp: \<pi>_def)
    thus "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FExists \<phi>)" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by (auto intro!: exI[of _ w] exI[of _ I])
  qed
next
  case (FEXISTS \<phi>)
  show ?case
  proof (intro equalityI subsetI)
    fix x assume "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FEXISTS \<phi>)"
    then obtain w I P where
      *: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FEXISTS \<phi>)"
       "length I = n" "length w > 0" "P \<subseteq> {0 .. length w - 1}" "satisfies (w, Inr P # I) \<phi>"
       unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    from *(4,5) have "\<forall>p \<in> P. p < length w" by (cases w) auto
    with *(2-4,6) FEXISTS(2) have "enc (w, Inr P # I) \<in> ?L (Suc n) \<phi>"
      by (intro subsetD[OF equalityD1[OF FEXISTS(1)], of "Suc n" "enc (w, Inr P # I)"])
       (auto simp: lang\<^sub>M\<^sub>2\<^sub>L_def nth_Cons' split: if_split_asm sum.splits
        intro!: exI[of _ w] exI[of _ "Inr P # I"])
    with *(1) show "x \<in> ?L n (FEXISTS \<phi>)"
      by (auto simp: map_index intro!: image_eqI[of _ "map \<pi>"] simp del: o_apply) (auto simp: \<pi>_def)
  next
    fix x assume "x \<in> ?L n (FEXISTS \<phi>)"
    then obtain x' where x: "x = map \<pi> x'" and x': "length x' > 0" and "x' \<in> ?L (Suc n) \<phi>" by (auto simp del: o_apply)
    with FEXISTS(2) have "x' \<in> lang\<^sub>M\<^sub>2\<^sub>L (Suc n) \<phi>"
      by (intro subsetD[OF equalityD2[OF FEXISTS(1)], of "Suc n" x'])
         (auto split: if_split_asm sum.splits)
    then obtain w I' where
      *: "x' = enc (w, I')" "wf_interp_for_formula (w, I') \<phi>" "length I' = Suc n" "satisfies (w, I') \<phi>"
       unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto
    moreover then obtain I\<^sub>0 I where "I' = I\<^sub>0 # I" by (cases I') auto
    moreover with FEXISTS(2) *(2) obtain P where "I\<^sub>0 = Inr P"
      by (auto simp: nth_Cons' split: sum.splits if_split_asm)
    moreover have "length w \<ge> 1" using x' *(1) by (cases w) auto
    ultimately have "x = enc (w, I)" "wf_interp_for_formula (w, I) (FEXISTS \<phi>)" "length I = n"
      "length w > 0" "satisfies (w, I) (FEXISTS \<phi>)" using FEXISTS(2) unfolding x
      by (auto simp add: map_tl nth_Cons' split: if_split_asm
        intro!: exI[of _ P] simp del: o_apply) (auto simp: \<pi>_def)
    thus "x \<in> lang\<^sub>M\<^sub>2\<^sub>L n (FEXISTS \<phi>)" unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by (auto intro!: exI[of _ w] exI[of _ I])
  qed
qed

lemma wf_rexp_of: "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of n \<phi>)"
  by (induct \<phi> arbitrary: n) (auto intro: wf_rexp_ENC simp: finite_FOV max_idx_vars)

lemma wf_rexp_of_alt: "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of_alt n \<phi>)"
  by (induct \<phi> arbitrary: n) (auto simp: wf_rexp_ENC finite_FOV max_idx_vars)

lemma wf_rexp_of': "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of' n \<phi>)"
  unfolding rexp_of'_def by (auto simp: wf_rexp_ENC wf_rexp_of_alt finite_FOV max_idx_vars)

lemma wf_rexp_of_alt': "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of_alt' n \<phi>)"
  by (induct \<phi> arbitrary: n) (auto simp: wf_rexp_ENC)

lemma wf_rexp_of'': "wf_formula n \<phi> \<Longrightarrow> wf n (rexp_of'' n \<phi>)"
  unfolding rexp_of''_def by (auto simp: wf_rexp_ENC wf_rexp_of_alt' finite_FOV max_idx_vars)

lemma ENC_Not: "ENC n (FOV (FNot \<phi>)) = ENC n (FOV \<phi>)"
  unfolding ENC_def by auto

lemma ENC_And:
  "wf_formula n (FAnd \<phi> \<psi>) \<Longrightarrow> lang n (ENC n (FOV (FAnd \<phi> \<psi>))) - {[]} \<subseteq> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>)) - {[]}"
proof
  fix x assume wf: "wf_formula n (FAnd \<phi> \<psi>)" and x: "x \<in> lang n (ENC n (FOV (FAnd \<phi> \<psi>))) - {[]}"
  hence wf1: "wf_formula n \<phi>" and wf2: "wf_formula n \<psi>" by auto
  from x obtain w I where wI: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FAnd \<phi> \<psi>)" "length I = n"
    using lang_ENC_formula[OF wf] by blast
  hence "wf_interp_for_formula (w, I) \<phi>" "wf_interp_for_formula (w, I) \<psi>"
    unfolding wf_interp_for_formula_FAnd by auto
  hence "x \<in> (lang n (ENC n (FOV \<phi>)) - {[]}) \<inter> (lang n (ENC n (FOV \<psi>)) - {[]})"
    unfolding lang_ENC_formula[OF wf1] lang_ENC_formula[OF wf2] using wI by auto
  thus "x \<in> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>)) - {[]}" by blast
qed
  
lemma ENC_Or:
  "wf_formula n (FOr \<phi> \<psi>) \<Longrightarrow> lang n (ENC n (FOV (FOr \<phi> \<psi>))) - {[]} \<subseteq> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>)) - {[]}"
proof
  fix x assume wf: "wf_formula n (FOr \<phi> \<psi>)" and x: "x \<in> lang n (ENC n (FOV (FOr \<phi> \<psi>))) - {[]}"
  hence wf1: "wf_formula n \<phi>" and wf2: "wf_formula n \<psi>" by auto
  from x obtain w I where wI: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FOr \<phi> \<psi>)" "length I = n"
    using lang_ENC_formula[OF wf] by blast
  hence "wf_interp_for_formula (w, I) \<phi>" "wf_interp_for_formula (w, I) \<psi>"
    unfolding wf_interp_for_formula_FOr by auto
  hence "x \<in> (lang n (ENC n (FOV \<phi>)) - {[]}) \<inter> (lang n (ENC n (FOV \<psi>)) - {[]})"
    unfolding lang_ENC_formula[OF wf1] lang_ENC_formula[OF wf2] using wI by auto
  thus "x \<in> lang n (ENC n (FOV \<phi>)) \<inter> lang n (ENC n (FOV \<psi>)) - {[]}" by blast
qed

lemma project_enc: "map \<pi> (enc (w, x # I)) = enc (w, I)"
  unfolding \<pi>_def by auto

lemma list_list_eqI:
  assumes "\<forall>(_, x) \<in> set xs. x \<noteq> []" "\<forall>(_, y) \<in> set ys. y \<noteq> []"
    "map (\<lambda>(_, x). hd x) xs = map (\<lambda>(_, x). hd x) ys" "map \<pi> xs = map \<pi> ys"
  shows "xs = ys"
proof -
  from assms(4) have "length xs = length ys" by (metis length_map)
  then show ?thesis using assms by (induct rule: list_induct2) (auto simp: \<pi>_def neq_Nil_conv)
qed

lemma project_enc_extend:
  assumes "map \<pi> x = enc (w, I)" "\<forall>(_, x) \<in> set x. x \<noteq> []"
  shows "x = enc (w, Inr (positions_in_row x 0) # I)"
proof -
  from arg_cong[OF assms(1), of "map fst"] have w: "w = map fst x" by (auto simp: \<pi>_def)
  show ?thesis
  proof (rule list_list_eqI[OF assms(2)], unfold project_enc)
    show "map (\<lambda>(_, x). hd x) x = map (\<lambda>(_, x). hd x) (enc (w, Inr (positions_in_row x 0) # I))"
      using assms(2) unfolding enc.simps map_index positions_in_row w
      by (intro nth_equalityI) (auto dest!: nth_mem simp: hd_conv_nth)
  qed (auto simp: assms(1))
qed

lemma ENC_Exists:
  "wf_formula n (FExists \<phi>) \<Longrightarrow> lang n (ENC n (FOV (FExists \<phi>))) - {[]} = map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]}"
proof (intro equalityI subsetI)
  fix x assume wf: "wf_formula n (FExists \<phi>)" and x: "x \<in> lang n (ENC n (FOV (FExists \<phi>))) - {[]}"
  hence wf1: "wf_formula (Suc n) \<phi>" by auto
  from x obtain w I where wI: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FExists \<phi>)" "length I = n"
    using lang_ENC_formula[OF wf] by blast
  with x have "w \<noteq> []" by (cases w) auto
  from wI(2) obtain p where "p < length w" "wf_interp_for_formula (w, Inl p # I) \<phi>"
    using wf_interp_for_formula_FExists[OF wf[folded wI(3)] \<open>w \<noteq> []\<close>] by auto
  with wI(3) have "x \<in> map \<pi> ` (lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]})"
    unfolding wI(1) lang_ENC_formula[OF wf1] project_enc[symmetric, of w I "Inl p"]
    by (intro imageI CollectI exI[of _ w] exI[of _ "Inl p # I"]) auto
  thus "x \<in> map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]}" by blast
next
  fix x assume wf: "wf_formula n (FExists \<phi>)" and "x \<in> map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]}"
  hence wf1: "wf_formula (Suc n) \<phi>" and "0 \<in> FOV \<phi>" and x: "x \<in> map \<pi> ` (lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]})" by auto
  from x obtain w I where wI: "x = map \<pi> (enc (w, I))" "wf_interp_for_formula (w, I) \<phi>" "length I = Suc n"
    using lang_ENC_formula[OF wf1] by auto
  with \<open>0 \<in> FOV \<phi>\<close> obtain p I' where I: "I = Inl p # I'" by (cases I) (fastforce split: sum.splits)+
  with wI have wtlI: "x = enc (w, I')" "length I' = n" unfolding \<pi>_def by auto
  with x have "w \<noteq> []" by (cases w) auto
  have "wf_interp_for_formula (w, I') (FExists \<phi>)"
    using wf_interp_for_formula_FExists[OF wf[folded wtlI(2)] \<open>w \<noteq> []\<close>]
          wf_interp_for_formula_any_Inl[OF wI(2)[unfolded I]] ..
  with wtlI show "x \<in> lang n (ENC n (FOV (FExists \<phi>))) - {[]}" unfolding lang_ENC_formula[OF wf] by blast
qed

lemma ENC_EXISTS:
  "wf_formula n (FEXISTS \<phi>) \<Longrightarrow> lang n (ENC n (FOV (FEXISTS \<phi>))) - {[]} = map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]}"
proof (intro equalityI subsetI)
  fix x assume wf: "wf_formula n (FEXISTS \<phi>)" and x: "x \<in> lang n (ENC n (FOV (FEXISTS \<phi>))) - {[]}"
  hence wf1: "wf_formula (Suc n) \<phi>" by auto
  from x obtain w I where wI: "x = enc (w, I)" "wf_interp_for_formula (w, I) (FEXISTS \<phi>)" "length I = n"
    using lang_ENC_formula[OF wf] by blast
  with x have "w \<noteq> []" by (cases w) auto
  from wI(2) obtain P where "\<forall>p \<in> P. p < length w" "wf_interp_for_formula (w, Inr P # I) \<phi>"
    using wf_interp_for_formula_FEXISTS[OF wf[folded wI(3)] \<open>w \<noteq> []\<close>] by auto
  with wI(3) have "x \<in> map \<pi> ` (lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]})"
    unfolding wI(1) lang_ENC_formula[OF wf1] project_enc[symmetric, of w I "Inr P"]
    by (intro imageI CollectI exI[of _ w] exI[of _ "Inr P # I"]) auto
  thus "x \<in> map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]}" by blast
next
  fix x assume wf: "wf_formula n (FEXISTS \<phi>)" and "x \<in> map \<pi> ` lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]}"
  hence wf1: "wf_formula (Suc n) \<phi>" and "0 \<in> SOV \<phi>" and x: "x \<in> map \<pi> ` (lang (Suc n) (ENC (Suc n) (FOV \<phi>)) - {[]})" by auto
  from x obtain w I where wI: "x = map \<pi> (enc (w, I))" "wf_interp_for_formula (w, I) \<phi>" "length I = Suc n"
    using lang_ENC_formula[OF wf1] by auto
  with \<open>0 \<in> SOV \<phi>\<close> obtain P I' where I: "I = Inr P # I'" by (cases I) (fastforce split: sum.splits)+
  with wI have wtlI: "x = enc (w, I')" "length I' = n" unfolding \<pi>_def by auto
  with x have "w \<noteq> []" by (cases w) auto
  have "wf_interp_for_formula (w, I') (FEXISTS \<phi>)"
    using wf_interp_for_formula_FEXISTS[OF wf[folded wtlI(2)] \<open>w \<noteq> []\<close>]
          wf_interp_for_formula_any_Inr[OF wI(2)[unfolded I]] ..
  with wtlI show "x \<in> lang n (ENC n (FOV (FEXISTS \<phi>))) - {[]}" unfolding lang_ENC_formula[OF wf] by blast
qed


lemma map_project_empty: "map \<pi> ` A - {[]} = map \<pi> ` (A - {[]})"
  by auto

lemma lang\<^sub>M\<^sub>2\<^sub>L_rexp_of_rexp_of':
  "wf_formula n \<phi> \<Longrightarrow> lang n (rexp_of n \<phi>) - {[]} = lang n (rexp_of' n \<phi>) - {[]}"
unfolding rexp_of'_def proof (induction \<phi> arbitrary: n)
  case (FNot \<phi>)
  hence "wf_formula n \<phi>" by simp
  with FNot.IH show ?case unfolding rexp_of.simps rexp_of_alt.simps lang.simps ENC_Not by blast
next
  case (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FAnd.IH(1)[OF wf1] FAnd.IH(2)[OF wf2] show ?case using ENC_And[OF FAnd.prems]
    unfolding rexp_of.simps rexp_of_alt.simps lang.simps rexp_of_list.simps by blast
next
  case (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FOr.IH(1)[OF wf1] FOr.IH(2)[OF wf2] show ?case using ENC_Or[OF FOr.prems]
    unfolding rexp_of.simps rexp_of_alt.simps lang.simps by blast
next
  case (FExists \<phi>)
  hence wf: "wf_formula (n + 1) \<phi>" by auto
  show ?case using ENC_Exists[OF FExists.prems]
    unfolding rexp_of.simps rexp_of_alt.simps lang.simps map_project_empty FExists.IH[OF wf] by auto
next
  case (FEXISTS \<phi>)
  hence wf: "wf_formula (n + 1) \<phi>" by auto
  show ?case using ENC_EXISTS[OF FEXISTS.prems]
    unfolding rexp_of.simps rexp_of_alt.simps lang.simps map_project_empty FEXISTS.IH[OF wf] by auto
qed auto

lemma Int_Diff_both: "A \<inter> B - C = (A - C) \<inter> (B - C)"
  by auto

lemma lang_ENC_split:
  assumes "finite X" "X = Y1 \<union> Y2" "n = 0 \<or> (\<forall>p \<in> X. p < n)"
  shows "lang n (ENC n X) = lang n (ENC n Y1) \<inter> lang n (ENC n Y2)"
  unfolding ENC_def lang_INTERSECT using assms lang_subset_lists[OF wf_rexp_valid_ENC, of n] by auto

lemma map_project_Int_ENC:
  assumes "0 \<notin> X" "X \<subseteq> {0 ..< n + 1}" "Z \<subseteq> lists ((set o \<sigma> \<Sigma>) (n + 1))"
  shows "map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X) - {[]}) =
    map \<pi> ` Z \<inter> lang n (ENC n ((\<lambda>x. x - 1) ` X)) - {[]}"
proof -
  let ?Y = "{0 ..< n + 1} - X"
  let ?fX = "(\<lambda>x. x - 1) ` X"
  let ?fY = "{0 ..< n} - (\<lambda>x. x - 1) ` X"
  from assms have *: "(\<lambda>x. x - 1) ` X \<subseteq> {0 ..< n}" by (cases n) auto
  show ?thesis unfolding Int_Diff lang_ENC[OF assms(2) subset_refl] lang_ENC[OF * subset_refl]
  proof (safe elim!: imageI)
    fix w I
    assume *: "length I = n + 1" "w \<noteq> []"
      "\<forall>i\<in>X. case I ! i of Inl x \<Rightarrow> True | Inr x \<Rightarrow> False"
      "\<forall>i\<in>?Y. case I ! i of Inl x \<Rightarrow> False | Inr x \<Rightarrow> True"
      "\<forall>a\<in>set w. a \<in> set \<Sigma>" "Ball (set I) (case_sum (\<lambda>p. p < length w) (\<lambda>P. \<forall>p\<in>P. p < length w))"
    then obtain p Is where "I = p # Is" by (cases I) auto
    then show "\<exists>w' I'.
      map \<pi> (enc (w, I)) = enc (w', I') \<and>
      length I' = n \<and> (0 < length w' \<and> (\<forall>a\<in>set w'. a \<in> set \<Sigma>) \<and>
      Ball (set I') (case_sum (\<lambda>p. p < length w') (\<lambda>P. \<forall>p\<in>P. p < length w'))) \<and>
      (\<forall>i\<in>?fX. case I' ! i of Inl x \<Rightarrow> True | Inr x \<Rightarrow> False) \<and>
      (\<forall>i\<in>?fY. case I' ! i of Inl x \<Rightarrow> False | Inr x \<Rightarrow> True)"
    proof (hypsubst, intro exI[of _ w] exI[of _ Is] conjI ballI project_enc)
      fix i assume "i \<in> ?fY"
      then show "case Is ! i of Inl x \<Rightarrow> False | Inr x \<Rightarrow> True"
        using *[unfolded \<open>I = p # Is\<close>] assms(1)
        by (cases "i = 0") (fastforce simp: nth_Cons' image_iff split: sum.splits if_splits)+ 
    qed (insert *[unfolded \<open>I = p # Is\<close>] assms(1), auto simp: nth_Cons' split: sum.splits if_splits)
  next
    fix x w I
    assume *: "w \<noteq> []" "x \<in> Z" "map \<pi> x = enc (w, I)"
      "\<forall>i\<in>?fX. case I ! i of Inl x \<Rightarrow> True | Inr x \<Rightarrow> False"
      "\<forall>i\<in>{0 ..< length I} - ?fX. case I ! i of Inl x \<Rightarrow> False | Inr x \<Rightarrow> True"
      "\<forall>a\<in>set w. a \<in> set \<Sigma>" "Ball (set I) (case_sum (\<lambda>p. p < length w) (\<lambda>P. \<forall>p\<in>P. p < length w))"
    moreover from assms(1) have "\<forall>x \<in> X. x > 0" "\<And>x y. x - Suc 0 = y - Suc 0 \<longleftrightarrow> 
      x = y \<or> (x = 0 \<and> y = Suc 0) \<or> (x = Suc 0 \<and> y = 0)"
      by (metis neq0_conv) (metis One_nat_def Suc_diff_1 diff_0_eq_0 diff_self_eq_0 neq0_conv)
    moreover from *(2) assms(3) have "x = enc (w, Inr (positions_in_row x 0) # I)"
      apply (intro project_enc_extend [OF *(3)])
      apply (simp only: \<sigma>_def)
      apply auto
      done
    moreover from arg_cong[OF *(3), of length] have "length w = length x" by simp
    ultimately show " map \<pi> x \<in> map \<pi> `
      (Z \<inter> {enc (w, I') |w I'. length I' = length I + 1 \<and> (0 < length w \<and> (\<forall>a\<in>set w. a \<in> set \<Sigma>) \<and>
         Ball (set I') (case_sum (\<lambda>p. p < length w) (\<lambda>P. \<forall>p\<in>P. p < length w))) \<and>
           (\<forall>i\<in>X. case I' ! i of Inl x \<Rightarrow> True | Inr x \<Rightarrow> False) \<and>
           (\<forall>i\<in>{0..<length I + 1} - X. case I' ! i of Inl x \<Rightarrow> False | Inr x \<Rightarrow> True)})"
      by (intro imageI CollectI conjI IntI exI[of _ w] exI[of _ "Inr (positions_in_row x 0) # I"])
        (auto simp: nth_Cons' positions_in_row elim!: bspec simp del: enc.simps)
  qed
qed

lemma map_project_ENC:
  assumes "X \<subseteq> {0 ..< n + 1}" "Z \<subseteq> lists ((set o \<sigma> \<Sigma>) (n + 1))"
  shows "map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) X) - {[]}) =
    (if 0 \<in> X
    then map \<pi> ` (Z \<inter> lang (n + 1) (ENC (n + 1) {0})) \<inter> lang n (ENC n ((\<lambda>x. x - 1) ` (X - {0}))) - {[]}
    else map \<pi> ` Z \<inter> lang n (ENC n ((\<lambda>x. x - 1) ` (X - {0}))) - {[]})"
    (is "?L = (if _ then ?R1 else ?R2)")
proof (split if_splits, intro conjI impI)
  assume 0: "0 \<notin> X"
  from assms have fin: "finite X" "finite ((\<lambda>x. x - 1) ` X)"
    by (auto elim: finite_subset intro!: finite_imageI[of "X"])
  from 0 show "?L = ?R2" using map_project_Int_ENC[OF 0 assms]
    unfolding lists_image[symmetric] \<pi>_\<sigma>
      Int_absorb1[OF lang_subset_lists[OF wf_rexp_ENC[OF fin(1)]], of "n + 1"]
      Int_absorb1[OF lang_subset_lists[OF wf_rexp_ENC[OF fin(2)]], of n]
    by auto
next
  assume "0 \<in> X"
  hence 0: "0 \<notin> X - {0}" and X: "X = {0} \<union> (X - {0})" by auto
  from assms have fin: "finite X"
    by (auto elim: finite_subset intro!: finite_imageI[of "X"])
  have "?L = map \<pi> ` ((Z \<inter> lang (n + 1) (ENC (n + 1) {0})) \<inter> lang (n + 1) (ENC (n + 1) (X - {0})) - {[]})"
    unfolding Int_assoc using assms by (subst lang_ENC_split[OF fin X, of "n + 1"]) auto
  also have "\<dots> = ?R1"
    using 0 assms by (elim map_project_Int_ENC) auto
  finally show "?L = ?R1" .
qed

abbreviation "\<LL> \<equiv> project.lang (set \<circ> \<sigma> \<Sigma>) \<pi>"

lemma lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'_rexp_of'':
  "wf_formula n \<phi> \<Longrightarrow> lang n (rexp_of' n \<phi>) - {[]} = lang n (rexp_of'' n \<phi>) - {[]}"
unfolding rexp_of'_def rexp_of''_def
proof (induction \<phi> arbitrary: n)
  case (FNot \<phi>)
  hence "wf_formula n \<phi>" by simp
  with FNot.IH show ?case unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps ENC_Not by blast
next
  case (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FAnd.IH(1)[OF wf1] FAnd.IH(2)[OF wf2] show ?case using ENC_And[OF FAnd.prems]
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps rexp_of_list.simps by blast
next
  case (FOr \<phi>\<^sub>1 \<phi>\<^sub>2)
  hence wf1: "wf_formula n \<phi>\<^sub>1" and wf2: "wf_formula n \<phi>\<^sub>2" by force+
  from FOr.IH(1)[OF wf1] FOr.IH(2)[OF wf2] show ?case using ENC_Or[OF FOr.prems]
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps rexp_of_list.simps by blast
next
  case (FExists \<phi>)
  hence wf: "wf_formula (n + 1) \<phi>" and 0: "0 \<in> FOV \<phi>" by auto
  then show ?case
    using ENC_Exists[OF FExists.prems] map_project_ENC[of "FOV \<phi>" n] max_idx_vars[of "n + 1" \<phi>]
      wf_rexp_of_alt'[OF wf] 0
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps Int_Diff_both
    unfolding map_project_empty FExists.IH[OF wf, unfolded lang.simps]
    by (intro trans[OF arg_cong2[of _ _ _ _ "(\<inter>)", OF map_project_ENC[OF _ lang_subset_lists] refl]])
      fastforce+
next
  case (FEXISTS \<phi>)
  hence wf: "wf_formula (n + 1) \<phi>" and 0: "0 \<notin> FOV \<phi>" by auto
  then show ?case
    using ENC_EXISTS[OF FEXISTS.prems] map_project_ENC[of "FOV \<phi>" n] max_idx_vars[of "n + 1" \<phi>]
      wf_rexp_of_alt'[OF wf] 0
    unfolding rexp_of_alt.simps rexp_of_alt'.simps lang.simps Int_Diff_both
    unfolding map_project_empty FEXISTS.IH[OF wf, unfolded lang.simps]
    by (intro trans[OF arg_cong2[of _ _ _ _ "(\<inter>)", OF map_project_ENC[OF _ lang_subset_lists] refl]])
      fastforce+
qed simp_all

theorem lang\<^sub>M\<^sub>2\<^sub>L_rexp_of': "wf_formula n \<phi> \<Longrightarrow> lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = lang n (rexp_of' n \<phi>) - {[]}"
  unfolding lang\<^sub>M\<^sub>2\<^sub>L_rexp_of_rexp_of'[symmetric] by (rule lang\<^sub>M\<^sub>2\<^sub>L_rexp_of)

theorem lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'': "wf_formula n \<phi> \<Longrightarrow> lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = lang n (rexp_of'' n \<phi>) - {[]}"
  unfolding lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'_rexp_of''[symmetric] by (rule lang\<^sub>M\<^sub>2\<^sub>L_rexp_of')

end

(*<*)
end
(*>*)
