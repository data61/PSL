(* Title: Generat.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Generative probabilistic values\<close>

theory Generat imports 
  Misc_CryptHOL
begin

subsection \<open>Single-step generative\<close>

datatype (generat_pures: 'a, generat_outs: 'b, generat_conts: 'c) generat 
  = Pure (result: 'a)
  | IO ("output": 'b) (continuation: "'c")

datatype_compat generat

lemma IO_code_cong: "out = out' \<Longrightarrow> IO out c = IO out' c" by simp
setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm IO_code_cong})\<close>

lemma is_Pure_map_generat [simp]: "is_Pure (map_generat f g h x) = is_Pure x"
by(cases x) simp_all

lemma result_map_generat [simp]: "is_Pure x \<Longrightarrow> result (map_generat f g h x) = f (result x)"
by(cases x) simp_all

lemma output_map_generat [simp]: "\<not> is_Pure x \<Longrightarrow> output (map_generat f g h x) = g (output x)"
by(cases x) simp_all

lemma continuation_map_generat [simp]: "\<not> is_Pure x \<Longrightarrow> continuation (map_generat f g h x) = h (continuation x)"
by(cases x) simp_all

lemma [simp]:
  shows map_generat_eq_Pure:
  "map_generat f g h generat = Pure x \<longleftrightarrow> (\<exists>x'. generat = Pure x' \<and> x = f x')"
  and Pure_eq_map_generat:
  "Pure x = map_generat f g h generat \<longleftrightarrow> (\<exists>x'. generat = Pure x' \<and> x = f x')"
by(cases generat; auto; fail)+

lemma [simp]:
  shows map_generat_eq_IO:
  "map_generat f g h generat = IO out c \<longleftrightarrow> (\<exists>out' c'. generat = IO out' c' \<and> out = g out' \<and> c = h c')"
  and IO_eq_map_generat:
  "IO out c = map_generat f g h generat \<longleftrightarrow> (\<exists>out' c'. generat = IO out' c' \<and> out = g out' \<and> c = h c')"
by(cases generat; auto; fail)+

lemma is_PureE [cases pred]:
  assumes "is_Pure generat"
  obtains (Pure) x where "generat = Pure x"
using assms by(auto simp add: is_Pure_def)

lemma not_is_PureE:
  assumes "\<not> is_Pure generat"
  obtains (IO) out c where "generat = IO out c"
using assms by(cases generat) auto

lemma rel_generatI:
  "\<lbrakk> is_Pure x \<longleftrightarrow> is_Pure y;
     \<lbrakk> is_Pure x; is_Pure y \<rbrakk> \<Longrightarrow> A (result x) (result y);
     \<lbrakk> \<not> is_Pure x; \<not> is_Pure y \<rbrakk> \<Longrightarrow> Out (output x) (output y) \<and> R (continuation x) (continuation y) \<rbrakk>
  \<Longrightarrow> rel_generat A Out R x y"
by(cases x y rule: generat.exhaust[case_product generat.exhaust]) simp_all

lemma rel_generatD':
  "rel_generat A Out R x y
  \<Longrightarrow> (is_Pure x \<longleftrightarrow> is_Pure y) \<and> 
     (is_Pure x \<longrightarrow> is_Pure y \<longrightarrow> A (result x) (result y)) \<and> 
     (\<not> is_Pure x \<longrightarrow> \<not> is_Pure y \<longrightarrow> Out (output x) (output y) \<and> R (continuation x) (continuation y))"
by(cases x y rule: generat.exhaust[case_product generat.exhaust]) simp_all

lemma rel_generatD:
  assumes "rel_generat A Out R x y"
  shows rel_generat_is_PureD: "is_Pure x \<longleftrightarrow> is_Pure y"
  and rel_generat_resultD: "is_Pure x \<or> is_Pure y \<Longrightarrow> A (result x) (result y)"
  and rel_generat_outputD: "\<not> is_Pure x \<or> \<not> is_Pure y \<Longrightarrow> Out (output x) (output y)"
  and rel_generat_continuationD: "\<not> is_Pure x \<or> \<not> is_Pure y \<Longrightarrow> R (continuation x) (continuation y)"
using rel_generatD'[OF assms] by simp_all

lemma rel_generat_mono:
  "\<lbrakk> rel_generat A B C x y; \<And>x y. A x y \<Longrightarrow> A' x y; \<And>x y. B x y \<Longrightarrow> B' x y; \<And>x y. C x y \<Longrightarrow> C' x y \<rbrakk>
  \<Longrightarrow> rel_generat A' B' C' x y"
using generat.rel_mono[of A A' B B' C C'] by(auto simp add: le_fun_def)

lemma rel_generat_mono' [mono]:
  "\<lbrakk> \<And>x y. A x y \<longrightarrow> A' x y; \<And>x y. B x y \<longrightarrow> B' x y; \<And>x y. C x y \<longrightarrow> C' x y \<rbrakk>
  \<Longrightarrow> rel_generat A B C x y \<longrightarrow> rel_generat A' B' C' x y"
by(blast intro: rel_generat_mono)

lemma rel_generat_same:
  "rel_generat A B C r r \<longleftrightarrow> 
  (\<forall>x \<in> generat_pures r. A x x) \<and>
  (\<forall>out \<in> generat_outs r. B out out) \<and>
  (\<forall>c \<in>generat_conts r. C c c)"
by(cases r)(auto simp add: rel_fun_def)

lemma rel_generat_reflI:
  "\<lbrakk> \<And>y. y \<in> generat_pures x \<Longrightarrow> A y y; 
     \<And>out. out \<in> generat_outs x \<Longrightarrow> B out out;
     \<And>cont. cont \<in> generat_conts x \<Longrightarrow> C cont cont \<rbrakk>
  \<Longrightarrow> rel_generat A B C x x"
by(cases x) auto

lemma reflp_rel_generat [simp]: "reflp (rel_generat A B C) \<longleftrightarrow> reflp A \<and> reflp B \<and> reflp C"
by(auto 4 3 intro!: reflpI rel_generatI dest: reflpD reflpD[where x="Pure _"] reflpD[where x="IO _ _"])

lemma transp_rel_generatI:
  assumes "transp A" "transp B" "transp C"
  shows "transp (rel_generat A B C)"
by(rule transpI)(auto 6 5 dest: rel_generatD' intro!: rel_generatI intro: assms[THEN transpD] simp add: rel_fun_def)

lemma rel_generat_inf:
  "inf (rel_generat A B C) (rel_generat A' B' C') = rel_generat (inf A A') (inf B B') (inf C C')"
  (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by(auto elim!: generat.rel_cases simp add: rel_fun_def)
qed(auto elim: rel_generat_mono)

lemma rel_generat_Pure1: "rel_generat A B C (Pure x) = (\<lambda>r. \<exists>y. r = Pure y \<and> A x y)"
by(rule ext)(case_tac r, simp_all)

lemma rel_generat_IO1: "rel_generat A B C (IO out c) = (\<lambda>r. \<exists>out' c'. r = IO out' c' \<and> B out out' \<and> C c c')"
by(rule ext)(case_tac r, simp_all)

lemma not_is_Pure_conv: "\<not> is_Pure r \<longleftrightarrow> (\<exists>out c. r = IO out c)"
by(cases r) auto

lemma finite_generat_outs [simp]: "finite (generat_outs generat)"
by(cases generat) auto

lemma countable_generat_outs [simp]: "countable (generat_outs generat)"
by(simp add: countable_finite)

lemma case_map_generat:
  "case_generat pure io (map_generat a b d r) = 
   case_generat (pure \<circ> a) (\<lambda>out. io (b out) \<circ> d) r"
by(cases r) simp_all

lemma continuation_in_generat_conts:
  "\<not> is_Pure r \<Longrightarrow> continuation r \<in> generat_conts r"
by(cases r) auto


fun dest_IO :: "('a, 'out, 'c) generat \<Rightarrow> ('out \<times> 'c) option"
where
  "dest_IO (Pure _) = None"
| "dest_IO (IO out c) = Some (out, c)"

lemma dest_IO_eq_Some_iff [simp]: "dest_IO generat = Some (out, c) \<longleftrightarrow> generat = IO out c"
by(cases generat) simp_all

lemma dest_IO_eq_None_iff [simp]: "dest_IO generat = None \<longleftrightarrow> is_Pure generat"
by(cases generat) simp_all

lemma dest_IO_comp_Pure [simp]: "dest_IO \<circ> Pure = (\<lambda>_. None)"
by(simp add: fun_eq_iff)

lemma dom_dest_IO: "dom dest_IO = {x. \<not> is_Pure x}"
by(auto simp add: not_is_Pure_conv)


definition generat_lub :: "('a set \<Rightarrow> 'b) \<Rightarrow> ('out set \<Rightarrow> 'out') \<Rightarrow> ('cont set \<Rightarrow> 'cont') 
  \<Rightarrow> ('a, 'out, 'cont) generat set \<Rightarrow> ('b, 'out', 'cont') generat"
where
  "generat_lub lub1 lub2 lub3 A =
  (if \<exists>x\<in>A. is_Pure x then Pure (lub1 (result ` (A \<inter> {f. is_Pure f})))
   else IO (lub2 (output ` (A \<inter> {f. \<not> is_Pure f}))) (lub3 (continuation ` (A \<inter> {f. \<not> is_Pure f}))))"

lemma is_Pure_generat_lub [simp]:
  "is_Pure (generat_lub lub1 lub2 lub3 A) \<longleftrightarrow> (\<exists>x\<in>A. is_Pure x)"
by(simp add: generat_lub_def)

lemma result_generat_lub [simp]:
  "\<exists>x\<in>A. is_Pure x \<Longrightarrow> result (generat_lub lub1 lub2 lub3 A) = lub1 (result ` (A \<inter> {f. is_Pure f}))"
by(simp add: generat_lub_def)

lemma output_generat_lub: 
  "\<forall>x\<in>A. \<not> is_Pure x \<Longrightarrow> output (generat_lub lub1 lub2 lub3 A) = lub2 (output ` (A \<inter> {f. \<not> is_Pure f}))"
by(simp add: generat_lub_def)

lemma continuation_generat_lub:
  "\<forall>x\<in>A. \<not> is_Pure x \<Longrightarrow> continuation (generat_lub lub1 lub2 lub3 A) = lub3 (continuation ` (A \<inter> {f. \<not> is_Pure f}))"
by(simp add: generat_lub_def)

lemma generat_lub_map [simp]:
  "generat_lub lub1 lub2 lub3 (map_generat f g h ` A) = generat_lub (lub1 \<circ> (`) f) (lub2 \<circ> (`) g) (lub3 \<circ> (`) h) A"
by(auto 4 3 simp add: generat_lub_def intro: arg_cong[where f=lub1] arg_cong[where f=lub2] arg_cong[where f=lub3] rev_image_eqI del: ext intro!: ext)

lemma map_generat_lub [simp]:
  "map_generat f g h (generat_lub lub1 lub2 lub3 A) = generat_lub (f \<circ> lub1) (g \<circ> lub2) (h \<circ> lub3) A"
by(simp add: generat_lub_def o_def)


abbreviation generat_lub' :: "('cont set \<Rightarrow> 'cont') \<Rightarrow> ('a, 'out, 'cont) generat set \<Rightarrow> ('a, 'out, 'cont') generat"
where "generat_lub' \<equiv> generat_lub (\<lambda>A. THE x. x \<in> A) (\<lambda>A. THE x. x \<in> A)"

end
