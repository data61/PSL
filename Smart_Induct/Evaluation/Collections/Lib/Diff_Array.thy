section \<open>Arrays with in-place updates\<close>
theory Diff_Array imports
  Assoc_List
  Automatic_Refinement.Parametricity
  "HOL-Library.Code_Target_Numeral"
begin

datatype 'a array = Array "'a list"

subsection \<open>primitive operations\<close>

definition new_array :: "'a \<Rightarrow> nat \<Rightarrow> 'a array"
where "new_array a n = Array (replicate n a)"

primrec array_length :: "'a array \<Rightarrow> nat"
where "array_length (Array a) = length a"

primrec array_get :: "'a array \<Rightarrow> nat \<Rightarrow> 'a"
where "array_get (Array a) n = a ! n"

primrec array_set :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array"
where "array_set (Array A) n a = Array (A[n := a])"

definition array_of_list :: "'a list \<Rightarrow> 'a array"
where "array_of_list = Array"

  \<comment> \<open>Grows array by @{text inc} elements initialized to value @{text x}.\<close>
primrec array_grow :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array"
  where "array_grow (Array A) inc x = Array (A @ replicate inc x)"

  \<comment> \<open>Shrinks array to new size @{text sz}. Undefined if @{text "sz > array_length"}\<close>
primrec array_shrink :: "'a array \<Rightarrow> nat \<Rightarrow> 'a array"
  where "array_shrink (Array A) sz = (
  if (sz > length A) then
    undefined
  else
    Array (take sz A)
  )"

subsection \<open>Derived operations\<close>

text \<open>The following operations are total versions of
  \<open>array_get\<close> and \<open>array_set\<close>, which return a default
  value in case the index is out of bounds.
  They can be efficiently implemented in the target language by catching
  exceptions.
\<close>
definition "array_get_oo x a i \<equiv>
  if i<array_length a then array_get a i else x"
definition "array_set_oo f a i v \<equiv>
  if i<array_length a then array_set a i v else f ()"

primrec list_of_array :: "'a array \<Rightarrow> 'a list"
where "list_of_array (Array a) = a"

primrec assoc_list_of_array :: "'a array \<Rightarrow> (nat \<times> 'a) list"
where "assoc_list_of_array (Array a) = zip [0..<length a] a"

function assoc_list_of_array_code :: "'a array \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) list"
where [simp del]:
  "assoc_list_of_array_code a n =
  (if array_length a \<le> n then []
   else (n, array_get a n) # assoc_list_of_array_code a (n + 1))"
by pat_completeness auto
termination assoc_list_of_array_code
by(relation "measure (\<lambda>p. (array_length (fst p) - snd p))") auto

definition array_map :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b array"
where "array_map f a = array_of_list (map (\<lambda>(i, v). f i v) (assoc_list_of_array a))"

definition array_foldr :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b \<Rightarrow> 'b"
where "array_foldr f a b = foldr (\<lambda>(k, v). f k v) (assoc_list_of_array a) b"

definition array_foldl :: "(nat \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a array \<Rightarrow> 'b"
where "array_foldl f b a = foldl (\<lambda>b (k, v). f k b v) b (assoc_list_of_array a)"

subsection \<open>Lemmas\<close>

lemma array_length_new_array [simp]:
  "array_length (new_array a n) = n"
by(simp add: new_array_def)

lemma array_length_array_set [simp]:
  "array_length (array_set a i e) = array_length a"
by(cases a) simp

lemma array_get_new_array [simp]:
  "i < n \<Longrightarrow> array_get (new_array a n) i = a"
by(simp add: new_array_def)

lemma array_get_array_set_same [simp]:
  "n < array_length A \<Longrightarrow> array_get (array_set A n a) n = a"
by(cases A) simp

lemma array_get_array_set_other:
  "n \<noteq> n' \<Longrightarrow> array_get (array_set A n a) n' = array_get A n'"
by(cases A) simp

lemma list_of_array_grow [simp]:
  "list_of_array (array_grow a inc x) = list_of_array a @ replicate inc x"
by (cases a) (simp)

lemma array_grow_length [simp]:
  "array_length (array_grow a inc x) = array_length a + inc"
by (cases a)(simp add: array_of_list_def)

lemma array_grow_get [simp]:
  "i < array_length a \<Longrightarrow> array_get (array_grow a inc x) i = array_get a i"
  "\<lbrakk> i \<ge> array_length a;  i < array_length a + inc\<rbrakk> \<Longrightarrow> array_get (array_grow a inc x) i = x"
by (cases a, simp add: nth_append)+

lemma list_of_array_shrink [simp]:
  "\<lbrakk> s \<le> array_length a\<rbrakk> \<Longrightarrow> list_of_array (array_shrink a s) = take s (list_of_array a)"
by (cases a) simp

lemma array_shrink_get [simp]:
  "\<lbrakk> i < s; s \<le> array_length a \<rbrakk> \<Longrightarrow> array_get (array_shrink a s) i = array_get a i"
by (cases a) (simp)

lemma list_of_array_id [simp]: "list_of_array (array_of_list l) = l"
by (cases l)(simp_all add: array_of_list_def)

lemma map_of_assoc_list_of_array:
  "map_of (assoc_list_of_array a) k = (if k < array_length a then Some (array_get a k) else None)"
by(cases a, cases "k < array_length a")(force simp add: set_zip)+

lemma length_assoc_list_of_array [simp]:
  "length (assoc_list_of_array a) = array_length a"
by(cases a) simp

lemma distinct_assoc_list_of_array:
  "distinct (map fst (assoc_list_of_array a))"
by(cases a)(auto)

lemma array_length_array_map [simp]:
  "array_length (array_map f a) = array_length a"
by(simp add: array_map_def array_of_list_def)

lemma array_get_array_map [simp]:
  "i < array_length a \<Longrightarrow> array_get (array_map f a) i = f i (array_get a i)"
by(cases a)(simp add: array_map_def map_ran_conv_map array_of_list_def)

lemma array_foldr_foldr:
  "array_foldr (\<lambda>n. f) (Array a) b = foldr f a b"
by(simp add: array_foldr_def foldr_snd_zip)

lemma assoc_list_of_array_code_induct:
  assumes IH: "\<And>n. (n < array_length a \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
  shows "P n"
proof -
  have "a = a \<longrightarrow> P n"
    by(rule assoc_list_of_array_code.induct[where P="\<lambda>a' n. a = a' \<longrightarrow> P n"])(auto intro: IH)
  thus ?thesis by simp
qed

lemma assoc_list_of_array_code [code]:
  "assoc_list_of_array a = assoc_list_of_array_code a 0"
proof(cases a)
  case (Array A)
  { fix n
    have "zip [n..<length A] (drop n A) = assoc_list_of_array_code (Array A) n"
    proof(induct n taking: "Array A" rule: assoc_list_of_array_code_induct)
      case (1 n)
      show ?case
      proof(cases "n < array_length (Array A)")
        case False
        thus ?thesis by(simp add: assoc_list_of_array_code.simps)
      next
        case True
        hence "zip [Suc n..<length A] (drop (Suc n) A) = assoc_list_of_array_code (Array A) (Suc n)"
          by(rule 1)
        moreover from True have "n < length A" by simp
        moreover then obtain a A' where A: "drop n A = a # A'" by(cases "drop n A") auto
        moreover with \<open>n < length A\<close> have [simp]: "a = A ! n"
          by(subst append_take_drop_id[symmetric, where n=n])(simp add: nth_append min_def)
        moreover from A have "drop (Suc n) A = A'"
          by(induct A arbitrary: n)(simp_all add: drop_Cons split: nat.split_asm)
        ultimately show ?thesis by(subst upt_rec)(simp add: assoc_list_of_array_code.simps)
      qed
    qed }
  note this[of 0]
  with Array show ?thesis by simp
qed

lemma list_of_array_code [code]:
  "list_of_array a = array_foldr (\<lambda>n. Cons) a []"
by(cases a)(simp add: array_foldr_foldr foldr_Cons)

lemma array_foldr_cong [fundef_cong]:
  "\<lbrakk> a = a'; b = b';
    \<And>i b. i < array_length a \<Longrightarrow> f i (array_get a i) b = g i (array_get a i) b \<rbrakk>
  \<Longrightarrow> array_foldr f a b = array_foldr g a' b'"
by(cases a)(auto simp add: array_foldr_def set_zip intro!: foldr_cong)

lemma array_foldl_foldl:
  "array_foldl (\<lambda>n. f) b (Array a) = foldl f b a"
by(simp add: array_foldl_def foldl_snd_zip)

lemma array_map_conv_foldl_array_set:
  assumes len: "array_length A = array_length a"
  shows "array_map f a = foldl (\<lambda>A (k, v). array_set A k (f k v)) A (assoc_list_of_array a)"
proof(cases a)
  case (Array xs)
  obtain ys where [simp]: "A = Array ys" by(cases A)
  with Array len have "length xs \<le> length ys" by simp
  hence "foldr (\<lambda>x y. array_set y (fst x) (f (fst x) (snd x)))
               (rev (zip [0..<length xs] xs)) (Array ys) =
         Array (map (\<lambda>x. f (fst x) (snd x)) (zip [0..<length xs] xs) @ drop (length xs) ys)"
  proof(induct xs arbitrary: ys rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc x xs ys)
    from \<open>length (xs @ [x]) \<le> length ys\<close> have "length xs \<le> length ys" by simp
    hence "foldr (\<lambda>x y. array_set y (fst x) (f (fst x) (snd x)))
                 (rev (zip [0..<length xs] xs)) (Array ys) =
           Array (map (\<lambda>x. f (fst x) (snd x)) (zip [0..<length xs] xs) @ drop (length xs) ys)"
      by(rule snoc)
    moreover from \<open>length (xs @ [x]) \<le> length ys\<close>
    obtain y ys' where ys: "drop (length xs) ys = y # ys'"
      by(cases "drop (length xs) ys") auto
    moreover hence "drop (Suc (length xs)) ys = ys'" by(auto dest: drop_eq_ConsD)
    ultimately show ?case by(simp add: list_update_append)
  qed
  thus ?thesis using Array len
    by(simp add: array_map_def split_beta array_of_list_def foldl_conv_foldr)
qed

subsection \<open>Lemmas about empty arrays\<close>

lemma array_length_eq_0 [simp]:
  "array_length a = 0 \<longleftrightarrow> a = Array []"
by(cases a) simp

lemma new_array_0 [simp]: "new_array v 0 = Array []"
by(simp add: new_array_def)

lemma array_of_list_Nil [simp]:
  "array_of_list [] = Array []"
by(simp add: array_of_list_def)

lemma array_map_Nil [simp]:
  "array_map f (Array []) = Array []"
by(simp add: array_map_def)

lemma array_foldl_Nil [simp]:
  "array_foldl f b (Array []) = b"
by(simp add: array_foldl_def)

lemma array_foldr_Nil [simp]:
  "array_foldr f (Array []) b = b"
by(simp add: array_foldr_def)

lemma prod_foldl_conv:
  "(foldl f a xs, foldl g b xs) = foldl (\<lambda>(a, b) x. (f a x, g b x)) (a, b) xs"
by(induct xs arbitrary: a b) simp_all

lemma prod_array_foldl_conv:
  "(array_foldl f b a, array_foldl g c a) = array_foldl (\<lambda>h (b, c) v. (f h b v, g h c v)) (b, c) a"
by(cases a)(simp add: array_foldl_def foldl_map prod_foldl_conv split_def)

lemma array_foldl_array_foldr_comm:
  "comp_fun_commute (\<lambda>(h, v) b. f h b v) \<Longrightarrow> array_foldl f b a = array_foldr (\<lambda>h v b. f h b v) a b"
by(cases a)(simp add: array_foldl_def array_foldr_def split_def comp_fun_commute.foldr_conv_foldl)

lemma array_map_conv_array_foldl:
  "array_map f a = array_foldl (\<lambda>h a v. array_set a h (f h v)) a a"
proof(cases a)
  case (Array xs)
  define a where "a = xs"
  hence "length xs \<le> length a" by simp
  hence "foldl (\<lambda>a (k, v). array_set a k (f k v))
              (Array a) (zip [0..<length xs] xs)
         = Array (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ drop (length xs) a)"
  proof(induct xs rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc x xs)
    have "foldl (\<lambda>a (k, v). array_set a k (f k v)) (Array a) (zip [0..<length (xs @ [x])] (xs @ [x])) =
          array_set (foldl (\<lambda>a (k, v). array_set a k (f k v)) (Array a) (zip [0..<length xs] xs))
                    (length xs) (f (length xs) x)" by simp
    also from \<open>length (xs @ [x]) \<le> length a\<close> have "length xs \<le> length a" by simp
    hence "foldl (\<lambda>a (k, v). array_set a k (f k v)) (Array a) (zip [0..<length xs] xs) =
           Array (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ drop (length xs) a)" by(rule snoc)
    also note array_set.simps
    also have "(map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ drop (length xs) a) [length xs := f (length xs) x] =
              (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ (drop (length xs) a) [0 := f (length xs) x])"
      by(simp add: list_update_append)
    also from \<open>length (xs @ [x]) \<le> length a\<close>
    have "(drop (length xs) a)[0 := f (length xs) x] =
          f (length xs) x # drop (Suc (length xs)) a"
      by(simp add: upd_conv_take_nth_drop)
    also have "map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ f (length xs) x # drop (Suc (length xs)) a =
             (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ [f (length xs) x]) @ drop (Suc (length xs)) a" by simp
    also have "\<dots> = map (\<lambda>(k, v). f k v) (zip [0..<length (xs @ [x])] (xs @ [x])) @ drop (length (xs @ [x])) a"
      by(simp)
    finally show ?case .
  qed
  with a_def Array show ?thesis
    by(simp add: array_foldl_def array_map_def array_of_list_def)
qed

lemma array_foldl_new_array:
  "array_foldl f b (new_array a n) = foldl (\<lambda>b (k, v). f k b v) b (zip [0..<n] (replicate n a))"
  by(simp add: new_array_def array_foldl_def)

lemma array_list_of_set[simp]:
  "list_of_array (array_set a i x) = (list_of_array a) [i := x]"
  by (cases a) simp

lemma array_length_list: "array_length a = length (list_of_array a)"
  by (cases a) simp


subsection \<open>Parametricity lemmas\<close>

lemma rec_array_is_case[simp]: "rec_array = case_array"
  apply (intro ext)
  apply (auto split: array.split)
  done

definition array_rel_def_internal:
  "array_rel R \<equiv>
    {(Array xs, Array ys)|xs ys. (xs,ys) \<in> \<langle>R\<rangle>list_rel}"

lemma array_rel_def:
  "\<langle>R\<rangle>array_rel \<equiv> {(Array xs, Array ys)|xs ys. (xs,ys) \<in> \<langle>R\<rangle>list_rel}"
  unfolding array_rel_def_internal relAPP_def .

lemma array_relD:
  "(Array l, Array l') \<in> \<langle>R\<rangle>array_rel \<Longrightarrow> (l,l') \<in> \<langle>R\<rangle>list_rel"
  by (simp add: array_rel_def)

lemma array_rel_alt:
  "\<langle>R\<rangle>array_rel =
  { (Array l, l) | l. True }
  O \<langle>R\<rangle>list_rel
  O {(l,Array l) | l. True}"
  by (auto simp: array_rel_def)

lemma array_rel_sv[relator_props]:
  shows "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>array_rel)"
  unfolding array_rel_alt
  apply (intro relator_props )
  apply (auto intro: single_valuedI)
  done

lemma param_Array[param]:
  "(Array,Array) \<in> \<langle>R\<rangle> list_rel \<rightarrow> \<langle>R\<rangle> array_rel"
  apply (intro fun_relI)
  apply (simp add: array_rel_def)
  done

lemma param_rec_array[param]:
  "(rec_array,rec_array) \<in> (\<langle>Ra\<rangle>list_rel \<rightarrow> Rb) \<rightarrow> \<langle>Ra\<rangle>array_rel \<rightarrow> Rb"
  apply (intro fun_relI)
  apply (rename_tac f f' a a', case_tac a, case_tac a')
  apply (auto dest: fun_relD array_relD)
  done

lemma param_case_array[param]:
  "(case_array,case_array) \<in> (\<langle>Ra\<rangle>list_rel \<rightarrow> Rb) \<rightarrow> \<langle>Ra\<rangle>array_rel \<rightarrow> Rb"
  apply (clarsimp split: array.split)
  apply (drule array_relD)
  by parametricity

lemma param_case_array1':
  assumes "(a,a')\<in>\<langle>Ra\<rangle>array_rel"
  assumes "\<And>l l'. \<lbrakk> a=Array l; a'=Array l'; (l,l')\<in>\<langle>Ra\<rangle>list_rel \<rbrakk>
    \<Longrightarrow> (f l,f' l') \<in> Rb"
  shows "(case_array f a,case_array f' a') \<in> Rb"
  using assms
  apply (clarsimp split: array.split)
  apply (drule array_relD)
  apply parametricity
  by (rule refl)+

lemmas param_case_array2' = param_case_array1'[folded rec_array_is_case]

lemmas param_case_array' = param_case_array1' param_case_array2'

lemma param_array_length[param]:
    "(array_length,array_length) \<in> \<langle>Rb\<rangle>array_rel \<rightarrow> nat_rel"
  unfolding array_length_def
  by parametricity

lemma param_array_grow[param]:
  "(array_grow,array_grow) \<in> \<langle>R\<rangle>array_rel \<rightarrow> nat_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>array_rel"
   unfolding array_grow_def by parametricity

lemma array_rel_imp_same_length:
  "(a, a') \<in> \<langle>R\<rangle>array_rel \<Longrightarrow> array_length a = array_length a'"
  apply (cases a, cases a')
  apply (auto simp add: list_rel_imp_same_length dest!: array_relD)
  done

lemma param_array_get[param]:
  assumes I: "i<array_length a"
  assumes IR: "(i,i')\<in>nat_rel"
  assumes AR: "(a,a')\<in>\<langle>R\<rangle>array_rel"
  shows "(array_get a i, array_get a' i') \<in> R"
proof -
  obtain l l' where [simp]: "a = Array l" "a' = Array l'"
      by (cases a, cases a', simp_all)
  from AR have LR: "(l,l') \<in> \<langle>R\<rangle>list_rel" by (force dest!: array_relD)
  thus ?thesis using assms
    unfolding array_get_def
    apply (auto intro!: param_nth[param_fo] dest: list_rel_imp_same_length)
    done
qed

lemma param_array_set[param]:
  "(array_set,array_set)\<in>\<langle>R\<rangle>array_rel\<rightarrow>nat_rel\<rightarrow>R\<rightarrow>\<langle>R\<rangle>array_rel"
  unfolding array_set_def by parametricity

lemma param_array_of_list[param]:
  "(array_of_list, array_of_list) \<in> \<langle>R\<rangle> list_rel \<rightarrow> \<langle>R\<rangle> array_rel"
  unfolding array_of_list_def by parametricity

lemma param_array_shrink[param]:
  assumes N: "array_length a \<ge> n"
  assumes NR: "(n,n')\<in>nat_rel"
  assumes AR: "(a,a')\<in>\<langle>R\<rangle>array_rel"
  shows "(array_shrink a n, array_shrink a' n') \<in> \<langle>R\<rangle> array_rel"
proof-
  obtain l l' where [simp]: "a = Array l" "a' = Array l'"
      by (cases a, cases a', simp_all)
  from AR have LR: "(l,l') \<in> \<langle>R\<rangle>list_rel"
    by (auto dest: array_relD)
  with assms show ?thesis by (auto intro:
      param_Array[param_fo] param_take[param_fo]
      dest: array_rel_imp_same_length
    )
qed

lemma param_assoc_list_of_array[param]:
  "(assoc_list_of_array, assoc_list_of_array) \<in>
       \<langle>R\<rangle> array_rel \<rightarrow> \<langle>\<langle>nat_rel,R\<rangle>prod_rel\<rangle>list_rel"
  unfolding assoc_list_of_array_def[abs_def] by parametricity

lemma param_array_map[param]:
  "(array_map, array_map) \<in>
       (nat_rel \<rightarrow> Ra \<rightarrow> Rb) \<rightarrow> \<langle>Ra\<rangle>array_rel \<rightarrow> \<langle>Rb\<rangle>array_rel"
  unfolding array_map_def[abs_def] by parametricity

lemma param_array_foldr[param]:
  "(array_foldr, array_foldr) \<in>
       (nat_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> Rb) \<rightarrow> \<langle>Ra\<rangle>array_rel \<rightarrow> Rb \<rightarrow> Rb"
  unfolding array_foldr_def[abs_def] by parametricity

lemma param_array_foldl[param]:
  "(array_foldl, array_foldl) \<in>
       (nat_rel \<rightarrow> Rb \<rightarrow> Ra \<rightarrow> Rb) \<rightarrow> Rb \<rightarrow> \<langle>Ra\<rangle>array_rel \<rightarrow> Rb"
  unfolding array_foldl_def[abs_def] by parametricity

subsection \<open>Code Generator Setup\<close>

subsubsection \<open>Code-Numeral Preparation\<close>

definition [code del]: "new_array' v == new_array v o nat_of_integer"
definition [code del]: "array_length' == integer_of_nat o array_length"
definition [code del]: "array_get' a == array_get a o nat_of_integer"
definition [code del]: "array_set' a == array_set a o nat_of_integer"
definition [code del]: "array_grow' a == array_grow a o nat_of_integer"
definition [code del]: "array_shrink' a == array_shrink a o nat_of_integer"
definition [code del]:
  "array_get_oo' x a == array_get_oo x a o nat_of_integer"
definition [code del]:
  "array_set_oo' f a == array_set_oo f a o nat_of_integer"


lemma [code]:
  "new_array v == new_array' v o integer_of_nat"
  "array_length == nat_of_integer o array_length'"
  "array_get a == array_get' a o integer_of_nat"
  "array_set a == array_set' a o integer_of_nat"
  "array_grow a == array_grow' a o integer_of_nat"
  "array_shrink a == array_shrink' a o integer_of_nat"
  "array_get_oo x a == array_get_oo' x a o integer_of_nat"
  "array_set_oo f a == array_set_oo' f a o integer_of_nat"
  by (simp_all
    add: o_def
    add: new_array'_def array_length'_def array_get'_def array_set'_def
      array_grow'_def array_shrink'_def array_get_oo'_def array_set_oo'_def)

text \<open>Fallbacks\<close>
lemmas [code] = array_get_oo'_def[unfolded array_get_oo_def[abs_def]]
lemmas [code] = array_set_oo'_def[unfolded array_set_oo_def[abs_def]]

subsubsection \<open>Code generator setup for Haskell\<close>

code_printing type_constructor array \<rightharpoonup>
  (Haskell) "Array.ArrayType/ _"

code_reserved Haskell array_of_list

(*
code_printing code_module "Array" \<rightharpoonup>
  (Haskell) {*
--import qualified Data.Array.Diff as Arr;
import qualified Data.Array as Arr;
import Data.Array.IArray;
import Nat;

instance Ix Nat where {
    range (Nat a, Nat b) = map Nat (range (a, b));
    index (Nat a, Nat b) (Nat c) = index (a,b) c;
    inRange (Nat a, Nat b) (Nat c) = inRange (a, b) c;
    rangeSize (Nat a, Nat b) = rangeSize (a, b);
};

type ArrayType = Arr.DiffArray Nat;
--type ArrayType = Arr.Array Nat;

-- we need to start at 1 and not 0, because the empty array
-- is modelled by having s > e for (s,e) = bounds
-- and as we are in Nat, 0 is the smallest number

array_of_size :: Nat -> [e] -> ArrayType e;
array_of_size n = Arr.listArray (1, n);

new_array :: e -> Nat -> ArrayType e;
new_array a n = array_of_size n (repeat a);

array_length :: ArrayType e -> Nat;
array_length a = let (s, e) = bounds a in if s > e then 0 else e - s + 1;
-- the `if` is actually needed, because in Nat we have s > e --> e - s + 1 = 1

array_get :: ArrayType e -> Nat -> e;
array_get a i = a ! (i + 1);

array_set :: ArrayType e -> Nat -> e -> ArrayType e;
array_set a i e = a // [(i + 1, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = array_of_size (fromInteger (toInteger (length xs - 1))) xs;

array_grow :: ArrayType e -> Nat -> e -> ArrayType e;
array_grow a i x = let (s, e) = bounds a in Arr.listArray (s, e+i) (Arr.elems a ++ repeat x);

array_shrink :: ArrayType e -> Nat -> ArrayType e;
array_shrink a sz = if sz > array_length a then undefined else array_of_size sz (Arr.elems a);
*}
*)

(* TODO/FIXME: Using standard functional arrays here, as DiffArray seems 
  to be discontinued in Haskell! *)
code_printing code_module "Array" \<rightharpoonup>
  (Haskell) \<open>module Array where {

--import qualified Data.Array.Diff as Arr;
import qualified Data.Array as Arr;

type ArrayType = Arr.Array Integer;


array_of_size :: Integer -> [e] -> ArrayType e;
array_of_size n = Arr.listArray (0, n-1);

new_array :: e -> Integer -> ArrayType e;
new_array a n = array_of_size n (repeat a);

array_length :: ArrayType e -> Integer;
array_length a = let (s, e) = Arr.bounds a in e;

array_get :: ArrayType e -> Integer -> e;
array_get a i = a Arr.! i;

array_set :: ArrayType e -> Integer -> e -> ArrayType e;
array_set a i e = a Arr.// [(i, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = array_of_size (toInteger (length xs)) xs;

array_grow :: ArrayType e -> Integer -> e -> ArrayType e;
array_grow a i x = let (s, e) = Arr.bounds a in Arr.listArray (s, e+i) (Arr.elems a ++ repeat x);

array_shrink :: ArrayType e -> Integer -> ArrayType e;
array_shrink a sz = if sz > array_length a then undefined else array_of_size sz (Arr.elems a);
}\<close>




code_printing constant Array \<rightharpoonup> (Haskell) "Array.array'_of'_list"
code_printing constant new_array' \<rightharpoonup> (Haskell) "Array.new'_array"
code_printing constant array_length' \<rightharpoonup> (Haskell) "Array.array'_length"
code_printing constant array_get' \<rightharpoonup> (Haskell) "Array.array'_get"
code_printing constant array_set' \<rightharpoonup> (Haskell) "Array.array'_set"
code_printing constant array_of_list \<rightharpoonup> (Haskell) "Array.array'_of'_list"
code_printing constant array_grow' \<rightharpoonup> (Haskell) "Array.array'_grow"
code_printing constant array_shrink' \<rightharpoonup> (Haskell) "Array.array'_shrink"

subsubsection \<open>Code Generator Setup For SML\<close>

text \<open>
  We have the choice between single-threaded arrays, that raise an exception if an old version is accessed,
  and truly functional arrays, that update the array in place, but store undo-information to restore
  old versions.
\<close>

code_printing code_module "STArray" \<rightharpoonup>
  (SML)
\<open>
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x)
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x)
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;


\<close>

code_printing
  type_constructor array \<rightharpoonup> (SML) "_/ FArray.IsabelleMapping.ArrayType"
| constant Array \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_of'_list"
| constant new_array' \<rightharpoonup> (SML) "FArray.IsabelleMapping.new'_array"
| constant array_length' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_length"
| constant array_get' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_get"
| constant array_set' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_set"
| constant array_grow' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_grow"
| constant array_shrink' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_shrink"
| constant array_of_list \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_of'_list"
| constant array_get_oo' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_get'_oo"
| constant array_set_oo' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_set'_oo"


subsection \<open>Code Generator Setup for Scala\<close>
text \<open>
  We use a DiffArray-Implementation in Scala.
\<close>
code_printing code_module "DiffArray" \<rightharpoonup>
  (Scala) \<open>
object DiffArray {

  import scala.collection.mutable.ArraySeq

  protected abstract sealed class DiffArray_D[A]
  final case class Current[A] (a:ArraySeq[A]) extends DiffArray_D[A]
  final case class Upd[A] (i:Int, v:A, n:DiffArray_D[A]) extends DiffArray_D[A]

  object DiffArray_Realizer {
    def realize[A](a:DiffArray_D[A]) : ArraySeq[A] = a match {
      case Current(a) => ArraySeq.empty ++ a
      case Upd(j,v,n) => {val a = realize(n); a.update(j, v); a}
    }
  }

  class T[A] (var d:DiffArray_D[A]) {

    def realize () = { val a=DiffArray_Realizer.realize(d); d = Current(a); a }
    override def toString() = realize().toSeq.toString

    override def equals(obj:Any) =
      if (obj.isInstanceOf[T[A]]) obj.asInstanceOf[T[A]].realize().equals(realize())
      else false

  }


  def array_of_list[A](l : List[A]) : T[A] = new T(Current(ArraySeq.empty ++ l))
    def new_array[A](v:A, sz : BigInt) = new T[A](Current[A](ArraySeq.fill[A](sz.intValue)(v)))

    private def length[A](a:DiffArray_D[A]) : BigInt = a match {
    case Current(a) => a.length
    case Upd(_,_,n) => length(n)
  }

  def length[A](a : T[A]) : BigInt = length(a.d)

  private def sub[A](a:DiffArray_D[A], i:Int) : A = a match {
    case Current(a) => a (i)
    case Upd(j,v,n) => if (i==j) v else sub(n,i)
  }

  def get[A](a:T[A], i:BigInt) : A = sub(a.d,i.intValue)

  private def realize[A](a:DiffArray_D[A]) = DiffArray_Realizer.realize[A](a)

  def set[A](a:T[A], i:BigInt,v:A) : T[A] = a.d match {
    case Current(ad) => {
      val ii = i.intValue;
      a.d = Upd(ii,ad(ii),a.d);
      //ad.update(ii,v);
      ad(ii)=v
      new T[A](Current(ad))
    }
    case Upd(_,_,_) => set(new T[A](Current(realize(a.d))), i.intValue,v)
  }

  def grow[A](a:T[A], sz:BigInt, v:A) : T[A] = a.d match {
    case Current(ad) => {
      val adt = ArraySeq.fill[A](sz.intValue)(v)
      System.arraycopy(ad.array, 0, adt.array, 0, ad.length);
      new T[A](Current[A](adt))
    }
    case Upd (_,_,_) =>  {
      val adt = ArraySeq.fill[A](sz.intValue)(v)
      val ad = realize(a.d)
      System.arraycopy(ad.array, 0, adt.array, 0, ad.length);
      new T[A](Current[A](adt))
    }
  }

  def shrink[A](a:T[A], sz:BigInt) : T[A] =
    if (sz==0) {
      array_of_list(Nil)
    } else {
      a.d match {
        case Current(ad) => {
            val v=ad(0);
            val szz=sz.intValue
          val adt = ArraySeq.fill[A](szz)(v);
          System.arraycopy(ad.array, 0, adt.array, 0, szz);
          new T[A](Current[A](adt))
        }
        case Upd (_,_,_) =>  {
          val ad = realize(a.d);
            val szz=sz.intValue
            val v=ad(0);
          val adt = ArraySeq.fill[A](szz)(v);
          System.arraycopy(ad.array, 0, adt.array, 0, szz);
          new T[A](Current[A](adt))
        }
      }
    }

  def get_oo[A](d: => A, a:T[A], i:BigInt):A = try get(a,i) catch {
    case _:scala.IndexOutOfBoundsException => d
  }

  def set_oo[A](d: Unit => T[A], a:T[A], i:BigInt, v:A) : T[A] = try set(a,i,v) catch {
    case _:scala.IndexOutOfBoundsException => d ()
  }

}

/*
object Test {



  def assert (b : Boolean) : Unit = if (b) () else throw new java.lang.AssertionError("Assertion Failed")

  def eql[A] (a:DiffArray.T[A], b:List[A]) = assert (a.realize.corresponds(b)((x,y) => x.equals(y)))


  def tests1(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Another update
    val c = DiffArray.set(b,3,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)

    // Update of old version (forces realize)
    val d = DiffArray.set(b,2,8)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)
      eql(d,1::2::8::4::Nil)

    }

  def tests2(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Grow of current version
    val c = DiffArray.grow(b,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)

    // Grow of old version
    val d = DiffArray.grow(a,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)
      eql(d,1::2::3::4::9::9::Nil)

  }

  def tests3(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Shrink of current version
    val c = DiffArray.shrink(b,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)

    // Shrink of old version
    val d = DiffArray.shrink(a,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)
      eql(d,1::2::3::Nil)

  }

  def tests4(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update _oo (succeeds)
    val b = DiffArray.set_oo((_) => a,a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Update _oo (current version,fails)
    val c = DiffArray.set_oo((_) => a,b,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)

    // Update _oo (old version,fails)
    val d = DiffArray.set_oo((_) => b,a,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)
      eql(d,1::2::9::4::Nil)

  }

  def tests5(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Get_oo (current version, succeeds)
      assert (DiffArray.get_oo(0,b,2)==9)
    // Get_oo (current version, fails)
      assert (DiffArray.get_oo(0,b,5)==0)
    // Get_oo (old version, succeeds)
      assert (DiffArray.get_oo(0,a,2)==3)
    // Get_oo (old version, fails)
      assert (DiffArray.get_oo(0,a,5)==0)

  }




  def main(args: Array[String]): Unit = {
    tests1 ()
    tests2 ()
    tests3 ()
    tests4 ()
    tests5 ()


    Console.println("Tests passed")
  }

}*/

\<close>

code_printing
  type_constructor array \<rightharpoonup> (Scala) "DiffArray.T[_]"
| constant Array \<rightharpoonup> (Scala) "DiffArray.array'_of'_list"
| constant new_array' \<rightharpoonup> (Scala) "DiffArray.new'_array((_),(_).toInt)"
| constant array_length' \<rightharpoonup> (Scala) "DiffArray.length((_)).toInt"
| constant array_get' \<rightharpoonup> (Scala) "DiffArray.get((_),(_).toInt)"
| constant array_set' \<rightharpoonup> (Scala) "DiffArray.set((_),(_).toInt,(_))"
| constant array_grow' \<rightharpoonup> (Scala) "DiffArray.grow((_),(_).toInt,(_))"
| constant array_shrink' \<rightharpoonup> (Scala) "DiffArray.shrink((_),(_).toInt)"
| constant array_of_list \<rightharpoonup> (Scala) "DiffArray.array'_of'_list"
| constant array_get_oo' \<rightharpoonup> (Scala) "DiffArray.get'_oo((_),(_),(_).toInt)"
| constant array_set_oo' \<rightharpoonup> (Scala) "DiffArray.set'_oo((_),(_),(_).toInt,(_))"

context begin
(*private*) definition "test_diffarray_setup \<equiv> (Array,new_array',array_length',array_get', array_set', array_grow', array_shrink',array_of_list,array_get_oo',array_set_oo')"
export_code test_diffarray_setup checking Scala SML OCaml? Haskell?
end

end
