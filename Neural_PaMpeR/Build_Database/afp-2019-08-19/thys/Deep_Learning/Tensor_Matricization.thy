(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Matricization\<close>

theory Tensor_Matricization
imports Tensor_Plus
Jordan_Normal_Form.Matrix Jordan_Normal_Form.DL_Missing_Sublist
begin

fun digit_decode :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
"digit_decode [] [] = 0" |
"digit_decode (d # ds) (i # is) = i + d * digit_decode ds is"

fun digit_encode :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"digit_encode [] a = []" |
"digit_encode (d # ds) a = a mod d # digit_encode ds (a div d)"

lemma digit_encode_decode[simp]:
assumes "is \<lhd> ds"
shows "digit_encode ds (digit_decode ds is) = is"
  using assms apply (induction rule:valid_index.induct)
  unfolding digit_decode.simps digit_encode.simps
  by simp_all

lemma digit_decode_encode[simp]:
shows "digit_decode ds (digit_encode ds a) = a mod (prod_list ds)"
by (induction ds arbitrary:a; simp add: Divides.mod_mult2_eq add.commute)

lemma digit_decode_encode_lt[simp]:
assumes "a < prod_list ds"
shows "digit_decode ds (digit_encode ds a) = a"
by (simp add: assms)

lemma digit_decode_lt:
assumes "is \<lhd> ds"
shows "digit_decode ds is < prod_list ds"
using assms proof (induction rule:valid_index.induct)
  case Nil
  then show ?case by simp
next
  case (Cons "is" ds i d)
  have "(i + d * digit_decode ds is) div (d * prod_list ds) = 0"
    using Cons.IH Cons.hyps(2) div_mult2_eq by force
  then show ?case unfolding digit_decode.simps prod_list.Cons
    by (metis (no_types) Cons.IH Cons.hyps(2) div_eq_0_iff mult_eq_0_iff not_less0)
qed

lemma digit_encode_valid_index:
assumes "a < prod_list ds"
shows "digit_encode ds a \<lhd> ds"
using assms proof (induction ds arbitrary:a)
  case Nil
  show ?case by (simp add: valid_index.Nil)
next
  case (Cons d ds a)
  then have "a < d * prod_list ds"
    by simp
  then have "a div d < prod_list ds"
    by (metis div_eq_0_iff div_mult2_eq mult_0_right not_less0)
  then have "digit_encode ds (a div d) \<lhd> ds"
    by (rule Cons)
  moreover have "d > 0"
    using \<open>a < d * prod_list ds\<close> by (cases "d = 0") simp_all
  then have "a mod d < d"
    by simp
  ultimately show ?case
    by (simp add: valid_index.Cons)
qed

lemma length_digit_encode:
shows "length (digit_encode ds a) = length ds"
  by (induction ds arbitrary:a; simp_all)

lemma digit_encode_0:
"prod_list ds dvd a \<Longrightarrow> digit_encode ds a = replicate (length ds) 0"
proof (induction ds arbitrary:a)
  case Nil
  then show ?case by simp
next
  case (Cons d ds a)
  then have "prod_list ds dvd (a div d)" unfolding prod_list.Cons
    by (metis dvd_0_right dvd_div_iff_mult dvd_mult_left mult.commute split_div)
  then show ?case unfolding digit_encode.simps length_Cons replicate_Suc prod_list.Cons using Cons
    using dvd_imp_mod_0 dvd_mult_left prod_list.Cons by force
qed
  
lemma valid_index_weave:
assumes "is1 \<lhd> (nths ds A)"
and     "is2 \<lhd> (nths ds (-A))"
shows "weave A is1 is2 \<lhd> ds"
and "nths (weave A is1 is2) A = is1"
and "nths (weave A is1 is2) (-A) = is2"
proof -
  have length_ds: "length is1 + length is2 = length ds"
    using valid_index_length[OF assms(1)] valid_index_length[OF assms(2)]
    length_weave  weave_complementary_nthss by metis
  have 1:"length is1 = card {i \<in> A. i < length is1 + length is2}" unfolding length_ds
    using length_nths' assms(1) valid_index_length by auto
  have 2:"length is2 = card {i \<in> -A. i < length is1 + length is2}" unfolding length_ds
    using length_nths'[of ds "-A"] assms(2) valid_index_length by auto
  show "nths (weave A is1 is2) A = is1" "nths (weave A is1 is2) (-A) = is2" using nths_weave[OF 1 2] by blast+
  then have "nths (weave A is1 is2) A \<lhd> (nths ds A)"
       "nths (weave A is1 is2) (-A) \<lhd> (nths ds (-A))" using assms by auto
  then show "weave A is1 is2 \<lhd> ds" using list_all2_nths valid_index_list_all2_iff by blast
qed

definition matricize :: "nat set \<Rightarrow> 'a tensor \<Rightarrow> 'a mat" where
"matricize rmodes T = mat
  (prod_list (nths (Tensor.dims T) rmodes))
  (prod_list (nths (Tensor.dims T) (-rmodes)))
  (\<lambda>(r, c). Tensor.lookup T (weave rmodes
    (digit_encode (nths (Tensor.dims T) rmodes) r)
    (digit_encode (nths (Tensor.dims T) (-rmodes)) c)
  ))
"

definition dematricize::"nat set \<Rightarrow> 'a mat \<Rightarrow> nat list \<Rightarrow> 'a tensor" where
"dematricize rmodes A ds  = tensor_from_lookup ds
  (\<lambda>is. A $$ (digit_decode (nths ds rmodes) (nths is rmodes),
              digit_decode (nths ds (-rmodes)) (nths is (-rmodes)))
 )
"

lemma dims_matricize:
"dim_row (matricize rmodes T) = prod_list (nths (Tensor.dims T) rmodes)"
"dim_col (matricize rmodes T) = prod_list (nths (Tensor.dims T) (-rmodes))"
  unfolding matricize_def using dim_row_mat by simp_all

lemma dims_dematricize: "Tensor.dims (dematricize rmodes A ds) = ds"
  by (simp add: dematricize_def dims_tensor_from_lookup)

lemma valid_index_nths:
assumes "is \<lhd> ds"
shows "nths is A \<lhd> nths ds A"
using assms proof (induction arbitrary:A rule:valid_index.induct)
  case Nil
  then show ?case using nths_nil valid_index.simps by blast
next
  case (Cons "is" ds i d)
  then have " nths is {j. Suc j \<in> A} \<lhd> nths ds {j. Suc j \<in> A}"
    by simp
  then show ?case unfolding nths_Cons
    by (cases "0\<in>A"; simp_all add: Cons.hyps(2) valid_index.Cons)
qed

lemma dematricize_matricize:
shows "dematricize rmodes (matricize rmodes T) (Tensor.dims T) = T"
proof (rule tensor_lookup_eqI)
  show 1:"Tensor.dims (dematricize rmodes (matricize rmodes T) (Tensor.dims T)) = Tensor.dims T"
    by (simp add: dematricize_def dims_tensor_from_lookup)
  fix "is" assume "is \<lhd> Tensor.dims (dematricize rmodes (matricize rmodes T) (Tensor.dims T))"
  then have "is \<lhd> Tensor.dims T" using 1 by auto
  let ?rds = "(nths (Tensor.dims T) rmodes)"
  let ?cds = "(nths (Tensor.dims T) (-rmodes))"
  have decode_r: "digit_decode ?rds (nths is rmodes) < prod_list ?rds"
    by (simp add: \<open>is \<lhd> Tensor.dims T\<close> valid_index_nths digit_decode_lt)
  have decode_c: "digit_decode ?cds (nths is (-rmodes)) < prod_list ?cds"
    by (simp add: \<open>is \<lhd> Tensor.dims T\<close> valid_index_nths digit_decode_lt)
  have "(matricize rmodes T) $$
     (digit_decode ?rds (nths is rmodes),
      digit_decode ?cds (nths is (- rmodes))) =
    Tensor.lookup T is"
    unfolding matricize_def
    by (simp add: decode_r decode_c \<open>is \<lhd> Tensor.dims T\<close> valid_index_nths)
  then show "Tensor.lookup (dematricize rmodes (matricize rmodes T) (Tensor.dims T)) is = Tensor.lookup T is"
    by (simp add: dematricize_def dims_tensor_from_lookup lookup_tensor_from_lookup[OF \<open>is \<lhd> Tensor.dims T\<close>])
qed

lemma matricize_dematricize:
assumes " dim_row A = prod_list (nths ds rmodes)"
and " dim_col A = prod_list (nths ds (-rmodes))"
shows "matricize rmodes (dematricize rmodes A ds) = A"
proof (rule eq_matI)
  show "dim_row (matricize rmodes (dematricize rmodes A ds)) = dim_row A"
    unfolding assms(1) dematricize_def dims_tensor_from_lookup matricize_def dim_row_mat by metis
  show "dim_col (matricize rmodes (dematricize rmodes A ds)) = dim_col A"
    unfolding assms(2) dematricize_def dims_tensor_from_lookup matricize_def dim_col_mat by metis
  fix r c assume "r < dim_row A" "c < dim_col A"
  have valid1:"digit_encode (nths ds rmodes) r \<lhd> nths ds rmodes" and
       valid2:"digit_encode (nths ds (- rmodes)) c \<lhd> nths ds (- rmodes)"
    using \<open>r < dim_row A\<close> assms(1) \<open>c < dim_col A\<close> assms(2) digit_encode_valid_index by auto
  have 0:"Tensor.lookup (dematricize rmodes A ds)
     (weave rmodes
       (digit_encode (nths (Tensor.dims (dematricize rmodes A ds)) rmodes) r)
       (digit_encode (nths (Tensor.dims (dematricize rmodes A ds)) (- rmodes)) c)
     ) =  A $$ (r, c)"
      unfolding dematricize_def unfolding dims_tensor_from_lookup
      unfolding lookup_tensor_from_lookup[OF valid_index_weave(1)[OF valid1 valid2]]
      using digit_decode_encode_lt[OF \<open>c < dim_col A\<close>[unfolded assms(2)]]
      digit_decode_encode_lt[OF \<open>r < dim_row A\<close>[unfolded assms(1)]]
      valid_index_weave(2)[OF valid1 valid2] valid_index_weave(3)[OF valid1 valid2]
      by presburger
  from \<open>r < dim_row A\<close> have r_le: "r < prod_list (nths (Tensor.dims (dematricize rmodes A ds)) rmodes)"
    by (metis \<open>dim_row (matricize rmodes (dematricize rmodes A ds)) = dim_row A\<close> matricize_def dim_row_mat(1))
  from \<open>c < dim_col A \<close>have c_le: "c < prod_list (nths (Tensor.dims (dematricize rmodes A ds)) (- rmodes))"
    by (metis \<open>dim_col (matricize rmodes (dematricize rmodes A ds)) = dim_col A\<close> matricize_def dim_col_mat(1))
  then show "(matricize rmodes (dematricize rmodes A ds)) $$ (r, c) = A $$ (r, c)"
    unfolding matricize_def using r_le c_le 0 by simp
qed

lemma matricize_add:
assumes "dims A = dims B"
shows "matricize I A + matricize I B = matricize I (A+B)"
proof (rule eq_matI)
  show "dim_row (matricize I A + matricize I B) = dim_row (matricize I (A + B))" by (simp add: assms dims_matricize(1))
  show "dim_col (matricize I A + matricize I B) = dim_col (matricize I (A + B))" by (simp add: assms dims_matricize(2))
  fix i j assume ij_le1:"i < dim_row (matricize I (A + B))" "j < dim_col (matricize I (A + B))"
  then have
    ij_le2:"i < prod_list (nths (Tensor.dims A) I)"  "j < prod_list (nths (Tensor.dims A) (-I))" and
    ij_le3:"i < prod_list (nths (Tensor.dims B) I)"  "j < prod_list (nths (Tensor.dims B) (-I))" and
    ij_le4:"i < prod_list (nths (Tensor.dims (A + B)) I)"  "j < prod_list (nths (Tensor.dims (A + B)) (-I))"
    by (simp_all add: assms dims_matricize)
  then have ij_le5:"i < dim_row (matricize I B)" "j < dim_col (matricize I B)"
    by (simp_all add: assms dims_matricize)
  show "(matricize I A + matricize I B) $$ (i, j) = matricize I (A + B) $$ (i, j)"
    unfolding index_add_mat(1)[OF ij_le5] unfolding matricize_def unfolding index_mat[OF ij_le2] index_mat[OF ij_le3] index_mat[OF ij_le4]
    using assms digit_encode_valid_index ij_le2(1) ij_le2(2) valid_index_weave(1) by auto
qed

lemma matricize_0:
shows "matricize I (tensor0 ds) = 0\<^sub>m (dim_row (matricize I (tensor0 ds))) (dim_col (matricize I (tensor0 ds)))"
proof (rule eq_matI)
  show "dim_row (matricize I (tensor0 ds)) = dim_row (0\<^sub>m (dim_row (matricize I (tensor0 ds))) (dim_col (matricize I (tensor0 ds))))"
    unfolding zero_mat_def dim_row_mat by (simp add: dims_matricize(1))
  show "dim_col (matricize I (tensor0 ds)) = dim_col (0\<^sub>m (dim_row (matricize I (tensor0 ds))) (dim_col (matricize I (tensor0 ds))))"
    unfolding zero_mat_def dim_row_mat by (simp add: dims_matricize(2))
  fix i j assume ij_le1: "i < dim_row (0\<^sub>m (dim_row (matricize I (tensor0 ds))) (dim_col (matricize I (tensor0 ds))))"
                 "j < dim_col (0\<^sub>m (dim_row (matricize I (tensor0 ds))) (dim_col (matricize I (tensor0 ds))))"
  then have ij_le2:"i < dim_row (matricize I (tensor0 ds))" "j < dim_col (matricize I (tensor0 ds))"
    unfolding zero_mat_def dim_row_mat by (simp_all add: dims_matricize)
  show "matricize I (tensor0 ds) $$ (i, j) = 0\<^sub>m (dim_row (matricize I (tensor0 ds))) (dim_col (matricize I (tensor0 ds))) $$ (i, j)"
    unfolding zero_mat_def  index_mat[OF ij_le2] unfolding matricize_def index_mat[OF ij_le2[unfolded dims_matricize]]
    by (simp, metis lookup_tensor0 digit_encode_valid_index dims_matricize(1) dims_matricize(2) dims_tensor0
    ij_le2(1) ij_le2(2) valid_index_weave(1))
qed

end
