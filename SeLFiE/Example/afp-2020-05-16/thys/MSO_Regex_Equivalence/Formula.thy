(* Author: Dmitriy Traytel *)

section \<open>Monadic Second-Order Logic Formulas\<close>

(*<*)
theory Formula
imports Pi_Regular_Operators List_More
begin
(*>*)

subsection \<open>Interpretations and Encodings\<close>

type_synonym 'a interp = "'a list \<times> (nat + nat set) list"

abbreviation "enc_atom_bool I n \<equiv> map (\<lambda>x. case x of Inl p \<Rightarrow> n = p | Inr P \<Rightarrow> n \<in> P) I"

abbreviation "enc_atom I n a \<equiv> (a, enc_atom_bool I n)"

subsection \<open>Syntax and Semantics of MSO\<close>

datatype 'a formula =
  FQ 'a nat
| FLess nat nat
| FIn nat nat
| FNot "'a formula"
| FOr "'a formula" "'a formula"
| FAnd "'a formula" "'a formula"
| FExists "'a formula"
| FEXISTS "'a formula"

primrec FOV :: "'a formula \<Rightarrow> nat set" where
  "FOV (FQ a m) = {m}"
| "FOV (FLess m1 m2) = {m1, m2}"
| "FOV (FIn m M) = {m}"
| "FOV (FNot \<phi>) = FOV \<phi>"
| "FOV (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = FOV \<phi>\<^sub>1 \<union> FOV \<phi>\<^sub>2"
| "FOV (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = FOV \<phi>\<^sub>1 \<union> FOV \<phi>\<^sub>2"
| "FOV (FExists \<phi>) = (\<lambda>x. x - 1) ` (FOV \<phi> - {0})"
| "FOV (FEXISTS \<phi>) = (\<lambda>x. x - 1) ` FOV \<phi>"

primrec SOV :: "'a formula \<Rightarrow> nat set" where
  "SOV (FQ a m) = {}"
| "SOV (FLess m1 m2) = {}"
| "SOV (FIn m M) = {M}"
| "SOV (FNot \<phi>) = SOV \<phi>"
| "SOV (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = SOV \<phi>\<^sub>1 \<union> SOV \<phi>\<^sub>2"
| "SOV (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = SOV \<phi>\<^sub>1 \<union> SOV \<phi>\<^sub>2"
| "SOV (FExists \<phi>) = (\<lambda>x. x - 1) ` SOV \<phi>"
| "SOV (FEXISTS \<phi>) = (\<lambda>x. x - 1) ` (SOV \<phi> - {0})"

definition "\<sigma> = (\<lambda>\<Sigma> n. concat (map (\<lambda>bs. map (\<lambda>a. (a, bs)) \<Sigma>) (List.n_lists n [True, False])))"
definition "\<pi> = (\<lambda>(a, bs). (a, tl bs))"
definition "\<epsilon> = (\<lambda>\<Sigma> (a::'a, bs). if a \<in> set \<Sigma> then [(a, True # bs), (a, False # bs)] else [])"

datatype 'a atom =
    Singleton 'a "bool list"
  | AQ nat 'a
  | Arbitrary_Except nat bool
  | Arbitrary_Except2 nat nat
derive linorder atom

fun wf_atom where
  "wf_atom \<Sigma> n (Singleton a bs) = (a \<in> set \<Sigma> \<and> length bs = n)"
| "wf_atom \<Sigma> n (AQ m a) = (a \<in> set \<Sigma> \<and> m < n)"
| "wf_atom \<Sigma> n (Arbitrary_Except m _) = (m < n)"
| "wf_atom \<Sigma> n (Arbitrary_Except2 m1 m2) = (m1 < n \<and> m2 < n)"

fun lookup where
  "lookup (Singleton a' bs') (a, bs) = (a = a' \<and> bs = bs')"
| "lookup (AQ m a') (a, bs) = (a = a' \<and> bs ! m)"
| "lookup (Arbitrary_Except m b) (_, bs) = (bs ! m = b)"
| "lookup (Arbitrary_Except2 m1 m2) (_, bs) = (bs ! m1 \<and> bs ! m2)"

lemma \<pi>_\<sigma>: "\<pi> ` (set o \<sigma> \<Sigma>) (n + 1) = (set o \<sigma> \<Sigma>) n"
  unfolding \<pi>_def \<sigma>_def set_map[symmetric] o_apply map_concat by auto

locale formula = embed2 "set o (\<sigma> \<Sigma>)" "wf_atom \<Sigma>" \<pi> lookup "\<epsilon> \<Sigma>" "case_prod Singleton"
for \<Sigma> :: "'a :: linorder list" +
assumes nonempty: "\<Sigma> \<noteq> []"
begin

abbreviation "\<Sigma>_product_lists n \<equiv>
   List.maps (\<lambda>bools. map (\<lambda>a. (a, bools)) \<Sigma>) (bool_product_lists n)"

(* Normal form: quantified variables are used in the body *)
primrec pre_wf_formula :: "nat \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "pre_wf_formula n (FQ a m) = (a \<in> set \<Sigma> \<and> m < n)"
| "pre_wf_formula n (FLess m1 m2) = (m1 < n \<and> m2 < n)"
| "pre_wf_formula n (FIn m M) = (m < n \<and> M < n)"
| "pre_wf_formula n (FNot \<phi>) = pre_wf_formula n \<phi>"
| "pre_wf_formula n (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = (pre_wf_formula n \<phi>\<^sub>1 \<and> pre_wf_formula n \<phi>\<^sub>2)"
| "pre_wf_formula n (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = (pre_wf_formula n \<phi>\<^sub>1 \<and> pre_wf_formula n \<phi>\<^sub>2)"
| "pre_wf_formula n (FExists \<phi>) = (pre_wf_formula (n + 1) \<phi> \<and> 0 \<in> FOV \<phi> \<and> 0 \<notin> SOV \<phi>)"
| "pre_wf_formula n (FEXISTS \<phi>) = (pre_wf_formula (n + 1) \<phi> \<and> 0 \<notin> FOV \<phi> \<and> 0 \<in> SOV \<phi>)"

abbreviation "closed \<equiv> pre_wf_formula 0"

definition [simp]: "wf_formula n \<phi> \<equiv> pre_wf_formula n \<phi> \<and> FOV \<phi> \<inter> SOV \<phi> = {}"

lemma max_idx_vars: "pre_wf_formula n \<phi> \<Longrightarrow> \<forall>p \<in> FOV \<phi> \<union> SOV \<phi>. p < n"
  by (induct \<phi> arbitrary: n)
   (auto split: if_split_asm, (metis Un_iff diff_Suc_less less_SucE less_imp_diff_less)+)

lemma finite_FOV: "finite (FOV \<phi>)"
  by (induct \<phi>) (auto split: if_split_asm)

subsection \<open>ENC\<close>

definition valid_ENC :: "nat \<Rightarrow> nat \<Rightarrow> ('a atom) rexp" where
  "valid_ENC n p = (if n = 0 then Full else
    TIMES [
      Star (Atom (Arbitrary_Except p False)),
      Atom (Arbitrary_Except p True),
      Star (Atom (Arbitrary_Except p False))])"

lemma wf_rexp_valid_ENC: "n = 0 \<or> p < n \<Longrightarrow> wf n (valid_ENC n p)"
  unfolding valid_ENC_def by auto

definition ENC :: "nat \<Rightarrow> nat set \<Rightarrow> ('a atom) rexp" where
  "ENC n V = flatten INTERSECT (valid_ENC n ` V)"

lemma wf_rexp_ENC: "\<lbrakk>finite V; n = 0 \<or> (\<forall>v \<in> V. v < n)\<rbrakk> \<Longrightarrow> wf n (ENC n V)"
  unfolding ENC_def
  by (intro iffD2[OF wf_flatten_INTERSECT]) (auto simp: wf_rexp_valid_ENC)

lemma enc_atom_\<sigma>_eq: "i < length w \<Longrightarrow>
 (length I = n \<and> p \<in> set \<Sigma>) \<longleftrightarrow> enc_atom I i p \<in> set (\<sigma> \<Sigma> n)"
  by (auto simp: \<sigma>_def set_n_lists intro!: exI[of _ "enc_atom_bool I i"] imageI)

lemmas enc_atom_\<sigma> = iffD1[OF enc_atom_\<sigma>_eq, OF _ conjI]

lemma enc_atom_bool_take_drop_True:
  "\<lbrakk>r < length I; case I ! r of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P\<rbrakk> \<Longrightarrow>
    enc_atom_bool I p = take r (enc_atom_bool I p) @ True # drop (Suc r) (enc_atom_bool I p)"
  by (auto intro: trans[OF id_take_nth_drop])

lemma enc_atom_bool_take_drop_True2:
  "\<lbrakk>r < length I; case I ! r of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P;
    s < length I; case I ! s of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P; r < s\<rbrakk> \<Longrightarrow>
    enc_atom_bool I p = take r (enc_atom_bool I p) @ True #
      take (s - Suc r) (drop (Suc r) (enc_atom_bool I p)) @ True #
      drop (Suc s) (enc_atom_bool I p)"
  using id_take_nth_drop[of r "enc_atom_bool I p"]
      id_take_nth_drop[of "s - r - 1" "drop (Suc r) (enc_atom_bool I p)"]
  by auto

lemma enc_atom_bool_take_drop_False:
  "\<lbrakk>r < length I; case I ! r of Inl p' \<Rightarrow> p \<noteq> p' | Inr P \<Rightarrow> p \<notin> P\<rbrakk> \<Longrightarrow>
    enc_atom_bool I p = take r (enc_atom_bool I p) @ False # drop (Suc r) (enc_atom_bool I p)"
  by (auto intro: trans[OF id_take_nth_drop] split: sum.splits)

lemma enc_atom_lang_AQ: "\<lbrakk>r < length I;
   case I ! r of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P; length I = n; a \<in> set \<Sigma>\<rbrakk> \<Longrightarrow>
  [enc_atom I p a] \<in> lang n (Atom (AQ r a))"
  unfolding lang.simps
  by (force intro!: enc_atom_bool_take_drop_True
    image_eqI[of _ _ "(\<lambda>J. take r J @ drop (r + 1) J) (enc_atom_bool I p)"]
    simp: \<sigma>_def set_n_lists)

lemma enc_atom_lang_Arbitrary_Except_True: "\<lbrakk>r < length I;
   case I ! r of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P; length I = n; a \<in> set \<Sigma>\<rbrakk> \<Longrightarrow>
  [enc_atom I p a] \<in> lang n (Atom (Arbitrary_Except r True))"
  unfolding lang.simps
  by (force intro!: enc_atom_bool_take_drop_True
    image_eqI[of _ _ "(\<lambda>J. take r J @ drop (r + 1) J) (enc_atom_bool I p)"]
    simp: \<sigma>_def set_n_lists)

lemma enc_atom_lang_Arbitrary_Except2:"\<lbrakk>r < length I; s < length I; 
  case I ! r of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P;
  case I ! s of Inl p' \<Rightarrow> p = p' | Inr P \<Rightarrow> p \<in> P; length I = n; a \<in> set \<Sigma>\<rbrakk> \<Longrightarrow>
  [enc_atom I p a] \<in> lang n (Atom (Arbitrary_Except2 r s))"
  unfolding lang.simps
  by (force intro!: enc_atom_bool_take_drop_True2
    simp: set_n_lists \<sigma>_def take_Cons' drop_Cons' numeral_eq_Suc)

lemma enc_atom_lang_Arbitrary_Except_False: "\<lbrakk>r < length I;
  case I ! r of Inl p' \<Rightarrow> p \<noteq> p' | Inr P \<Rightarrow> p \<notin> P; length I = n; a \<in> set \<Sigma>\<rbrakk> \<Longrightarrow>
  [enc_atom I p a] \<in> lang n (Atom (Arbitrary_Except r False))"
  unfolding lang.simps
  by (force intro!: enc_atom_bool_take_drop_False
    image_eqI[of _ _ "(\<lambda>J. take r J @ drop (r + 1) J) (enc_atom_bool I p)"]
    simp: set_n_lists \<sigma>_def split: sum.splits)

lemma AQ_D:
  assumes "v \<in> lang n (Atom (AQ m a))" "m < n" "a \<in> set \<Sigma>"
  shows "\<exists>x. v = [x] \<and> fst x = a \<and> snd x ! m"
  using assms by auto

lemma Arbitrary_ExceptD:
  assumes "v \<in> lang n (Atom (Arbitrary_Except r b))" "r < n"
  shows "\<exists>x. v = [x] \<and> snd x ! r = b"
  using assms by auto

lemma Arbitrary_Except2D:
  assumes "v \<in> lang n (Atom (Arbitrary_Except2 r s))" "r < n" "s < n"
  shows "\<exists>x. v = [x] \<and> snd x ! r \<and> snd x ! s"
  using assms by auto

lemma star_Arbitrary_ExceptD:
  "\<lbrakk>v \<in> star (lang n (Atom (Arbitrary_Except r b))); r < n; i < length v\<rbrakk> \<Longrightarrow>
    snd (v ! i) ! r = b"
proof (induct arbitrary: i rule: star_induct)
  case (append u v) thus ?case by (cases i) (auto dest: Arbitrary_ExceptD)
qed simp

end

end
