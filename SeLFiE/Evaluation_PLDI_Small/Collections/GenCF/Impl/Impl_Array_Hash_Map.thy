section \<open>\isaheader{Array Based Hash-Maps}\<close>
theory Impl_Array_Hash_Map imports 
  Automatic_Refinement.Automatic_Refinement
  "../../Iterator/Array_Iterator"
  "../Gen/Gen_Map"
  "../Intf/Intf_Hash"
  "../Intf/Intf_Map"
  "../../Lib/HashCode"
  "../../Lib/Code_Target_ICF"
  "../../Lib/Diff_Array"
  Impl_List_Map
begin


subsection \<open>Type definition and primitive operations\<close>

definition load_factor :: nat \<comment> \<open>in percent\<close>
  where "load_factor = 75"

datatype ('key, 'val) hashmap =
  HashMap "('key,'val) list_map array" "nat"

subsection \<open>Operations\<close>

definition new_hashmap_with :: "nat \<Rightarrow> ('k, 'v) hashmap"
where "\<And>size. new_hashmap_with size = 
    HashMap (new_array [] size) 0"

definition ahm_empty :: "nat \<Rightarrow> ('k, 'v) hashmap"
where "ahm_empty def_size \<equiv> new_hashmap_with def_size"

definition bucket_ok :: "'k bhc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('k\<times>'v) list \<Rightarrow> bool"
where "bucket_ok bhc len h kvs = (\<forall>k \<in> fst ` set kvs. bhc len k = h)"

definition ahm_invar_aux :: "'k bhc \<Rightarrow> nat \<Rightarrow> ('k\<times>'v) list array \<Rightarrow> bool"
where
  "ahm_invar_aux bhc n a \<longleftrightarrow>
  (\<forall>h. h < array_length a \<longrightarrow> bucket_ok bhc (array_length a) h 
      (array_get a h) \<and> list_map_invar (array_get a h)) \<and>
  array_foldl (\<lambda>_ n kvs. n + size kvs) 0 a = n \<and>
  array_length a > 1"

primrec ahm_invar :: "'k bhc \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> bool"
where "ahm_invar bhc (HashMap a n) = ahm_invar_aux bhc n a"

definition ahm_lookup_aux :: "'k eq \<Rightarrow> 'k bhc \<Rightarrow>
    'k \<Rightarrow> ('k, 'v) list_map array \<Rightarrow> 'v option"
where [simp]: "ahm_lookup_aux eq bhc k a  = list_map_lookup eq k (array_get a (bhc (array_length a) k))"

primrec ahm_lookup where
"ahm_lookup eq bhc k (HashMap a _) = ahm_lookup_aux eq bhc k a"

definition "ahm_\<alpha> bhc m \<equiv> \<lambda>k. ahm_lookup (=) bhc k m"

definition ahm_map_rel_def_internal: 
    "ahm_map_rel Rk Rv \<equiv> {(HashMap a n, HashMap a' n)| a a' n n'.
         (a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel \<and> (n,n') \<in> Id}"

lemma ahm_map_rel_def: "\<langle>Rk,Rv\<rangle> ahm_map_rel \<equiv> 
{(HashMap a n, HashMap a' n)| a a' n n'.
         (a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel \<and> (n,n') \<in> Id}"
    unfolding relAPP_def ahm_map_rel_def_internal .

definition ahm_map_rel'_def: 
  "ahm_map_rel' bhc \<equiv> br (ahm_\<alpha> bhc) (ahm_invar bhc)"

definition ahm_rel_def_internal: "ahm_rel bhc Rk Rv = 
    \<langle>Rk,Rv\<rangle> ahm_map_rel O ahm_map_rel' (abstract_bounded_hashcode Rk bhc)"
lemma ahm_rel_def: "\<langle>Rk, Rv\<rangle> ahm_rel bhc \<equiv>
     \<langle>Rk,Rv\<rangle> ahm_map_rel O ahm_map_rel' (abstract_bounded_hashcode Rk bhc)" 
    unfolding relAPP_def ahm_rel_def_internal .
lemmas [autoref_rel_intf] = REL_INTFI[of "ahm_rel bhc" i_map] for bhc

abbreviation "dflt_ahm_rel \<equiv> ahm_rel bounded_hashcode_nat"


primrec ahm_iteratei_aux :: "(('k\<times>'v) list array) \<Rightarrow> ('k\<times>'v, '\<sigma>) set_iterator"
where "ahm_iteratei_aux (Array xs) c f = foldli (concat xs) c f"

primrec ahm_iteratei :: "(('k, 'v) hashmap) \<Rightarrow> (('k\<times>'v), '\<sigma>) set_iterator"
where
  "ahm_iteratei (HashMap a n) = ahm_iteratei_aux a"

definition ahm_rehash_aux' :: "'k bhc \<Rightarrow> nat \<Rightarrow> 'k\<times>'v \<Rightarrow> 
    ('k\<times>'v) list array \<Rightarrow> ('k\<times>'v) list array"
where
  "ahm_rehash_aux' bhc n kv a =
   (let h = bhc n (fst kv)
    in array_set a h (kv # array_get a h))"

definition ahm_rehash_aux :: "'k bhc \<Rightarrow> ('k\<times>'v) list array \<Rightarrow> nat \<Rightarrow> 
    ('k\<times>'v) list array"
where
  "ahm_rehash_aux bhc a sz = ahm_iteratei_aux a (\<lambda>x. True) 
       (ahm_rehash_aux' bhc sz) (new_array [] sz)"

primrec ahm_rehash :: "'k bhc \<Rightarrow> ('k,'v) hashmap \<Rightarrow> nat \<Rightarrow> ('k,'v) hashmap"
where "ahm_rehash bhc (HashMap a n) sz = HashMap (ahm_rehash_aux bhc a sz) n"

primrec hm_grow :: "('k,'v) hashmap \<Rightarrow> nat"
where "hm_grow (HashMap a n) = 2 * array_length a + 3"

primrec ahm_filled :: "('k,'v) hashmap \<Rightarrow> bool"
where "ahm_filled (HashMap a n) = (array_length a * load_factor \<le> n * 100)"

primrec ahm_update_aux :: "'k eq \<Rightarrow> 'k bhc \<Rightarrow> ('k,'v) hashmap \<Rightarrow> 
    'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) hashmap"
where
  "ahm_update_aux eq bhc (HashMap a n) k v = 
  (let h = bhc (array_length a) k;
       m = array_get a h;
       insert = list_map_lookup eq k m = None
   in HashMap (array_set a h (list_map_update eq k v m)) 
       (if insert then n + 1 else n))"

definition ahm_update :: "'k eq \<Rightarrow> 'k bhc \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 
    ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where
  "ahm_update eq bhc k v hm = 
   (let hm' = ahm_update_aux eq bhc hm k v
    in (if ahm_filled hm' then ahm_rehash bhc hm' (hm_grow hm') else hm'))"

primrec ahm_delete :: "'k eq \<Rightarrow> 'k bhc \<Rightarrow> 'k \<Rightarrow> 
    ('k,'v) hashmap \<Rightarrow> ('k,'v) hashmap"
where
  "ahm_delete eq bhc k (HashMap a n) =
  (let h = bhc (array_length a) k;
       m = array_get a h;
       deleted = (list_map_lookup eq k m \<noteq> None)
   in HashMap (array_set a h (list_map_delete eq k m)) (if deleted then n - 1 else n))"

primrec ahm_isEmpty :: "('k,'v) hashmap \<Rightarrow> bool" where
  "ahm_isEmpty (HashMap _ n) = (n = 0)"

primrec ahm_isSng :: "('k,'v) hashmap \<Rightarrow> bool" where
  "ahm_isSng (HashMap _ n) = (n = 1)"

primrec ahm_size :: "('k,'v) hashmap \<Rightarrow> nat" where
  "ahm_size (HashMap _ n) = n"


lemma hm_grow_gt_1 [iff]:
  "Suc 0 < hm_grow hm"
by(cases hm)(simp)

lemma bucket_ok_Nil [simp]: "bucket_ok bhc len h [] = True"
by(simp add: bucket_ok_def)

lemma bucket_okD:
  "\<lbrakk> bucket_ok bhc len h xs; (k, v) \<in> set xs \<rbrakk>
  \<Longrightarrow> bhc len k = h"
by(auto simp add: bucket_ok_def)

lemma bucket_okI:
  "(\<And>k. k \<in> fst ` set kvs \<Longrightarrow> bhc len k = h) \<Longrightarrow> bucket_ok bhc len h kvs"
by(simp add: bucket_ok_def)


subsection \<open>Parametricity\<close>

lemma param_HashMap[param]: "(HashMap, HashMap) \<in> 
    \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Rk,Rv\<rangle>ahm_map_rel" 
    unfolding ahm_map_rel_def by force

lemma param_case_hashmap[param]: "(case_hashmap, case_hashmap) \<in>
    (\<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel \<rightarrow> nat_rel \<rightarrow> R) \<rightarrow> 
     \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow> R"
unfolding ahm_map_rel_def[abs_def]
by (force split: hashmap.split dest: fun_relD)

lemma rec_hashmap_is_case[simp]: "rec_hashmap = case_hashmap"
  by (intro ext, simp split: hashmap.split)



subsection \<open>@{term ahm_invar}\<close>

lemma ahm_invar_auxD:
  assumes "ahm_invar_aux bhc n a"
  shows "\<And>h. h < array_length a \<Longrightarrow> 
            bucket_ok bhc (array_length a) h (array_get a h)" and
        "\<And>h. h < array_length a \<Longrightarrow> 
            list_map_invar (array_get a h)" and
        "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a" and 
        "array_length a > 1"
using assms unfolding ahm_invar_aux_def by auto

lemma ahm_invar_auxE:
  assumes "ahm_invar_aux bhc n a"
  obtains "\<forall>h. h < array_length a \<longrightarrow> 
      bucket_ok bhc (array_length a) h (array_get a h) \<and> 
      list_map_invar (array_get a h)" and
  "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a" and 
  "array_length a > 1"
using assms unfolding ahm_invar_aux_def by blast

lemma ahm_invar_auxI:
  "\<lbrakk> \<And>h. h < array_length a \<Longrightarrow> 
         bucket_ok bhc (array_length a) h (array_get a h);
     \<And>h. h < array_length a \<Longrightarrow> list_map_invar (array_get a h);
     n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a; array_length a > 1 \<rbrakk>
  \<Longrightarrow> ahm_invar_aux bhc n a"
unfolding ahm_invar_aux_def by blast

lemma ahm_invar_distinct_fst_concatD:
  assumes inv: "ahm_invar_aux bhc n (Array xs)"
  shows "distinct (map fst (concat xs))"
proof -
  { fix h
    assume "h < length xs"
    with inv have "bucket_ok bhc (length xs) h (xs ! h)" and 
                  "list_map_invar (xs ! h)"
      by(simp_all add: ahm_invar_aux_def) }
  note no_junk = this

  show ?thesis unfolding map_concat
  proof(rule distinct_concat')
    have "distinct [x\<leftarrow>xs . x \<noteq> []]" unfolding distinct_conv_nth
    proof(intro allI ballI impI)
      fix i j
      assume "i < length [x\<leftarrow>xs . x \<noteq> []]" "j < length [x\<leftarrow>xs . x \<noteq> []]" "i \<noteq> j"
      from filter_nth_ex_nth[OF \<open>i < length [x\<leftarrow>xs . x \<noteq> []]\<close>]
      obtain i' where "i' \<ge> i" "i' < length xs" and ith: "[x\<leftarrow>xs . x \<noteq> []] ! i = xs ! i'" 
        and eqi: "[x\<leftarrow>take i' xs . x \<noteq> []] = take i [x\<leftarrow>xs . x \<noteq> []]" by blast
      from filter_nth_ex_nth[OF \<open>j < length [x\<leftarrow>xs . x \<noteq> []]\<close>]
      obtain j' where "j' \<ge> j" "j' < length xs" and jth: "[x\<leftarrow>xs . x \<noteq> []] ! j = xs ! j'"
        and eqj: "[x\<leftarrow>take j' xs . x \<noteq> []] = take j [x\<leftarrow>xs . x \<noteq> []]" by blast
      show "[x\<leftarrow>xs . x \<noteq> []] ! i \<noteq> [x\<leftarrow>xs . x \<noteq> []] ! j"
      proof
        assume "[x\<leftarrow>xs . x \<noteq> []] ! i = [x\<leftarrow>xs . x \<noteq> []] ! j"
        hence eq: "xs ! i' = xs ! j'" using ith jth by simp
        from \<open>i < length [x\<leftarrow>xs . x \<noteq> []]\<close>
        have "[x\<leftarrow>xs . x \<noteq> []] ! i \<in> set [x\<leftarrow>xs . x \<noteq> []]" by(rule nth_mem)
        with ith have "xs ! i' \<noteq> []" by simp
        then obtain kv where "kv \<in> set (xs ! i')" by(fastforce simp add: neq_Nil_conv)
        with no_junk[OF \<open>i' < length xs\<close>] have "bhc (length xs) (fst kv) = i'"
          by(simp add: bucket_ok_def)
        moreover from eq \<open>kv \<in> set (xs ! i')\<close> have "kv \<in> set (xs ! j')" by simp
        with no_junk[OF \<open>j' < length xs\<close>] have "bhc (length xs) (fst kv) = j'"
          by(simp add: bucket_ok_def)
        ultimately have [simp]: "i' = j'" by simp
        from \<open>i < length [x\<leftarrow>xs . x \<noteq> []]\<close> have "i = length (take i [x\<leftarrow>xs . x \<noteq> []])" by simp
        also from eqi eqj have "take i [x\<leftarrow>xs . x \<noteq> []] = take j [x\<leftarrow>xs . x \<noteq> []]" by simp
        finally show False using \<open>i \<noteq> j\<close> \<open>j < length [x\<leftarrow>xs . x \<noteq> []]\<close> by simp
      qed
    qed
    moreover have "inj_on (map fst) {x \<in> set xs. x \<noteq> []}"
    proof(rule inj_onI)
      fix x y
      assume "x \<in> {x \<in> set xs. x \<noteq> []}" "y \<in> {x \<in> set xs. x \<noteq> []}" "map fst x = map fst y"
      hence "x \<in> set xs" "y \<in> set xs" "x \<noteq> []" "y \<noteq> []" by auto
      from \<open>x \<in> set xs\<close> obtain i where "xs ! i = x" "i < length xs" unfolding set_conv_nth by fastforce
      from \<open>y \<in> set xs\<close> obtain j where "xs ! j = y" "j < length xs" unfolding set_conv_nth by fastforce
      from \<open>x \<noteq> []\<close> obtain k v x' where "x = (k, v) # x'" by(cases x) auto
      with no_junk[OF \<open>i < length xs\<close>] \<open>xs ! i = x\<close>
      have "bhc (length xs) k = i" by(auto simp add: bucket_ok_def)
      moreover from \<open>map fst x = map fst y\<close> \<open>x = (k, v) # x'\<close> obtain v' where "(k, v') \<in> set y" by fastforce
      with no_junk[OF \<open>j < length xs\<close>] \<open>xs ! j = y\<close>
      have "bhc (length xs) k = j" by(auto simp add: bucket_ok_def)
      ultimately have "i = j" by simp
      with \<open>xs ! i = x\<close> \<open>xs ! j = y\<close> show "x = y" by simp
    qed
    ultimately show "distinct [ys\<leftarrow>map (map fst) xs . ys \<noteq> []]"
      by(simp add: filter_map o_def distinct_map)
  next
    fix ys
    have A: "\<And>xs. distinct (map fst xs) = list_map_invar xs"
        by (simp add: list_map_invar_def)
    assume "ys \<in> set (map (map fst) xs)"
    thus "distinct ys"
        by(clarsimp simp add: set_conv_nth A) (erule no_junk(2))
  next
    fix ys zs
    assume "ys \<in> set (map (map fst) xs)" "zs \<in> set (map (map fst) xs)" "ys \<noteq> zs"
    then obtain ys' zs' where [simp]: "ys = map fst ys'" "zs = map fst zs'" 
      and "ys' \<in> set xs" "zs' \<in> set xs" by auto
    have "fst ` set ys' \<inter> fst ` set zs' = {}"
    proof(rule equals0I)
      fix k
      assume "k \<in> fst ` set ys' \<inter> fst ` set zs'"
      then obtain v v' where "(k, v) \<in> set ys'" "(k, v') \<in> set zs'" by(auto)
      from \<open>ys' \<in> set xs\<close> obtain i where "xs ! i = ys'" "i < length xs" unfolding set_conv_nth by fastforce
      with \<open>(k, v) \<in> set ys'\<close> have "bhc (length xs) k = i" by(auto dest: no_junk bucket_okD)
      moreover
      from \<open>zs' \<in> set xs\<close> obtain j where "xs ! j = zs'" "j < length xs" unfolding set_conv_nth by fastforce
      with \<open>(k, v') \<in> set zs'\<close> have "bhc (length xs) k = j" by(auto dest: no_junk bucket_okD)
      ultimately have "i = j" by simp
      with \<open>xs ! i = ys'\<close> \<open>xs ! j = zs'\<close> have "ys' = zs'" by simp
      with \<open>ys \<noteq> zs\<close> show False by simp
    qed
    thus "set ys \<inter> set zs = {}" by simp
  qed
qed

subsection \<open>@{term "ahm_\<alpha>"}\<close>

(* TODO: Move this *)
lemma list_map_lookup_is_map_of:
     "list_map_lookup (=) k l = map_of l k"
      using list_map_autoref_lookup_aux[where eq="(=)" and
           Rk=Id and Rv=Id] by force
definition "ahm_\<alpha>_aux bhc a \<equiv> 
    (\<lambda>k. ahm_lookup_aux (=) bhc k a)"
lemma ahm_\<alpha>_aux_def2: "ahm_\<alpha>_aux bhc a = (\<lambda>k. map_of (array_get a 
    (bhc (array_length a) k)) k)"
    unfolding ahm_\<alpha>_aux_def ahm_lookup_aux_def
    by (simp add: list_map_lookup_is_map_of)
lemma ahm_\<alpha>_def2: "ahm_\<alpha> bhc (HashMap a n) = ahm_\<alpha>_aux bhc a"
    unfolding ahm_\<alpha>_def ahm_\<alpha>_aux_def by simp

lemma finite_dom_ahm_\<alpha>_aux:
  assumes "is_bounded_hashcode Id (=) bhc" "ahm_invar_aux bhc n a"
  shows "finite (dom (ahm_\<alpha>_aux bhc a))"
proof -
  have "dom (ahm_\<alpha>_aux bhc a) \<subseteq> (\<Union>h \<in> range (bhc (array_length a) :: 'a \<Rightarrow> nat). dom (map_of (array_get a h)))" 
    unfolding ahm_\<alpha>_aux_def2
    by(force simp add: dom_map_of_conv_image_fst dest: map_of_SomeD)
  moreover have "finite \<dots>"
  proof(rule finite_UN_I)
    from \<open>ahm_invar_aux bhc n a\<close> have "array_length a > 1" by(simp add: ahm_invar_aux_def)
    hence "range (bhc (array_length a) :: 'a \<Rightarrow> nat) \<subseteq> {0..<array_length a}"
      using assms by force
    thus "finite (range (bhc (array_length a) :: 'a \<Rightarrow> nat))"
      by(rule finite_subset) simp
  qed(rule finite_dom_map_of)
  ultimately show ?thesis by(rule finite_subset)
qed

lemma ahm_\<alpha>_aux_new_array[simp]:
  assumes bhc: "is_bounded_hashcode Id (=) bhc" "1 < sz"
  shows "ahm_\<alpha>_aux bhc (new_array [] sz) k = None"
  using is_bounded_hashcodeD(3)[OF assms]
  unfolding ahm_\<alpha>_aux_def ahm_lookup_aux_def by simp

lemma ahm_\<alpha>_aux_conv_map_of_concat:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  assumes inv: "ahm_invar_aux bhc n (Array xs)"
  shows "ahm_\<alpha>_aux bhc (Array xs) = map_of (concat xs)"
proof
  fix k
  show "ahm_\<alpha>_aux bhc (Array xs) k = map_of (concat xs) k"
  proof(cases "map_of (concat xs) k")
    case None
    hence "k \<notin> fst ` set (concat xs)" by(simp add: map_of_eq_None_iff)
    hence "k \<notin> fst ` set (xs ! bhc (length xs) k)"
    proof(rule contrapos_nn)
      assume "k \<in> fst ` set (xs ! bhc (length xs) k)"
      then obtain v where "(k, v) \<in> set (xs ! bhc (length xs) k)" by auto
      moreover from inv have "bhc (length xs) k < length xs"
        using bhc by (force simp: ahm_invar_aux_def)
      ultimately show "k \<in> fst ` set (concat xs)"
        by (force intro: rev_image_eqI)
    qed
    thus ?thesis unfolding None ahm_\<alpha>_aux_def2
        by (simp add: map_of_eq_None_iff)
  next
    case (Some v)
    hence "(k, v) \<in> set (concat xs)" by(rule map_of_SomeD)
    then obtain ys where "ys \<in> set xs" "(k, v) \<in> set ys"
      unfolding set_concat by blast
    from \<open>ys \<in> set xs\<close> obtain i j where "i < length xs" "xs ! i = ys"
      unfolding set_conv_nth by auto
    with inv \<open>(k, v) \<in> set ys\<close>
    show ?thesis unfolding Some
      unfolding ahm_\<alpha>_aux_def2
      by(force dest: bucket_okD simp add: ahm_invar_aux_def list_map_invar_def)
  qed
qed

lemma ahm_invar_aux_card_dom_ahm_\<alpha>_auxD:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  assumes inv: "ahm_invar_aux bhc n a"
  shows "card (dom (ahm_\<alpha>_aux bhc a)) = n"
proof(cases a)
  case [simp]: (Array xs)
  from inv have "card (dom (ahm_\<alpha>_aux bhc (Array xs))) = card (dom (map_of (concat xs)))"
    by(simp add: ahm_\<alpha>_aux_conv_map_of_concat[OF bhc])
  also from inv have "distinct (map fst (concat xs))"
    by(simp add: ahm_invar_distinct_fst_concatD)
  hence "card (dom (map_of (concat xs))) = length (concat xs)"
    by(rule card_dom_map_of)
  also have "length (concat xs) = foldl (+) 0 (map length xs)"
    by (simp add: length_concat foldl_conv_fold add.commute fold_plus_sum_list_rev)
  also from inv
  have "\<dots> = n" unfolding foldl_map by(simp add: ahm_invar_aux_def array_foldl_foldl)
  finally show ?thesis by(simp)
qed

lemma finite_dom_ahm_\<alpha>:
  assumes "is_bounded_hashcode Id (=) bhc" "ahm_invar bhc hm"
  shows "finite (dom (ahm_\<alpha> bhc hm))"
  using assms by (cases hm, force intro: finite_dom_ahm_\<alpha>_aux 
      simp: ahm_\<alpha>_def2)


subsection \<open>@{term ahm_empty}\<close>

lemma ahm_invar_aux_new_array:
  assumes "n > 1"
  shows "ahm_invar_aux bhc 0 (new_array [] n)"
proof -
  have "foldl (\<lambda>b (k, v). b + length v) 0 (zip [0..<n] (replicate n [])) = 0"
    by(induct n)(simp_all add: replicate_Suc_conv_snoc del: replicate_Suc)
  with assms show ?thesis by(simp add: ahm_invar_aux_def array_foldl_new_array list_map_invar_def)
qed

lemma ahm_invar_new_hashmap_with:
  "n > 1 \<Longrightarrow> ahm_invar bhc (new_hashmap_with n)"
by(auto simp add: ahm_invar_def new_hashmap_with_def intro: ahm_invar_aux_new_array)

lemma ahm_\<alpha>_new_hashmap_with:
  assumes "is_bounded_hashcode Id (=) bhc" and "n > 1"
  shows "Map.empty = ahm_\<alpha> bhc (new_hashmap_with n)"
  unfolding new_hashmap_with_def ahm_\<alpha>_def
  using is_bounded_hashcodeD(3)[OF assms] by force

lemma ahm_empty_impl:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  assumes def_size: "def_size > 1"
  shows "(ahm_empty def_size, Map.empty) \<in> ahm_map_rel' bhc"
proof-
  from def_size and ahm_\<alpha>_new_hashmap_with[OF bhc def_size] and
       ahm_invar_new_hashmap_with[OF def_size]
  show ?thesis unfolding ahm_empty_def ahm_map_rel'_def br_def by force
qed

lemma param_ahm_empty[param]: 
  assumes def_size: "(def_size, def_size') \<in> nat_rel"
  shows "(ahm_empty def_size ,ahm_empty def_size') \<in> 
      \<langle>Rk,Rv\<rangle>ahm_map_rel"
unfolding ahm_empty_def[abs_def] new_hashmap_with_def[abs_def]
    new_array_def[abs_def]
using assms by parametricity

lemma autoref_ahm_empty[autoref_rules]:
  fixes Rk :: "('kc\<times>'ka) set"
  assumes bhc: "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  assumes def_size: "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('kc) def_size)"
  shows "(ahm_empty def_size, op_map_empty) \<in> \<langle>Rk, Rv\<rangle>ahm_rel bhc"
proof-
  from bhc have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel" 
    by (simp add: is_bounded_hashcodeD)
  with bhc have "is_bounded_hashcode Id (=) 
      (abstract_bounded_hashcode Rk bhc)" 
    unfolding autoref_tag_defs
    by blast
  thus ?thesis using assms 
    unfolding op_map_empty_def
    unfolding ahm_rel_def is_valid_def_hm_size_def autoref_tag_defs
    apply (intro relcompI)
    apply (rule param_ahm_empty[of def_size def_size], simp)
    apply (blast intro: ahm_empty_impl)
    done
qed


subsection \<open>@{term "ahm_lookup"}\<close>

lemma param_ahm_lookup[param]:
  assumes bhc: "is_bounded_hashcode Rk eq bhc"
  defines bhc'_def: "bhc' \<equiv> abstract_bounded_hashcode Rk bhc"
  assumes inv: "ahm_invar bhc' m'"
  assumes K: "(k,k') \<in> Rk"
  assumes M: "(m,m') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel"
  shows "(ahm_lookup eq bhc k m, ahm_lookup (=) bhc' k' m') \<in> 
             \<langle>Rv\<rangle>option_rel"
proof-
  from bhc have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel" by (simp add: is_bounded_hashcodeD)
  moreover from abstract_bhc_correct[OF bhc] 
      have bhc': "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel" unfolding bhc'_def .
  moreover from M obtain a a' n n' where 
      [simp]: "m = HashMap a n" and [simp]: "m' = HashMap a' n'" and
      A: "(a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel" and N: "(n,n') \<in> Id"
          by (cases m, cases m', unfold ahm_map_rel_def, auto)
  moreover from inv and array_rel_imp_same_length[OF A]
      have "array_length a > 1" by (simp add: ahm_invar_aux_def)
  with abstract_bhc_is_bhc[OF bhc]
      have "bhc' (array_length a) k' < array_length a"
      unfolding bhc'_def by blast
  with bhc'[param_fo, OF _ K] 
      have "bhc (array_length a) k < array_length a" by simp
  ultimately show ?thesis using K
      unfolding ahm_lookup_def[abs_def] rec_hashmap_is_case
      by (simp, parametricity)
qed


lemma ahm_lookup_impl:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  shows "(ahm_lookup (=) bhc, op_map_lookup) \<in> Id \<rightarrow> ahm_map_rel' bhc \<rightarrow> Id"
unfolding ahm_map_rel'_def br_def ahm_\<alpha>_def by force

lemma autoref_ahm_lookup[autoref_rules]:
  assumes 
    bhc[unfolded autoref_tag_defs]: "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  shows "(ahm_lookup eq bhc, op_map_lookup) 
    \<in> Rk \<rightarrow> \<langle>Rk,Rv\<rangle>ahm_rel bhc \<rightarrow> \<langle>Rv\<rangle>option_rel"
proof (intro fun_relI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix k k' a m'
  assume K: "(k,k') \<in> Rk"
  assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  from bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" 
    by blast

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast
  hence inv: "ahm_invar ?bhc' a'" 
      unfolding ahm_map_rel'_def br_def by simp
  
  from relcompI[OF param_ahm_lookup[OF bhc inv K M1]
                   ahm_lookup_impl[param_fo, OF bhc' _ M2]]
  show "(ahm_lookup eq bhc k a, op_map_lookup k' m') \<in> \<langle>Rv\<rangle>option_rel"
      by simp
qed


subsection \<open>@{term "ahm_iteratei"}\<close>

abbreviation "ahm_to_list \<equiv> it_to_list ahm_iteratei"

lemma param_ahm_iteratei_aux[param]:
  "(ahm_iteratei_aux,ahm_iteratei_aux) \<in> \<langle>\<langle>Ra\<rangle>list_rel\<rangle>array_rel \<rightarrow>
       (Rb \<rightarrow> bool_rel) \<rightarrow> (Ra \<rightarrow> Rb \<rightarrow> Rb) \<rightarrow> Rb \<rightarrow> Rb"
unfolding ahm_iteratei_aux_def[abs_def] by parametricity

lemma param_ahm_iteratei[param]:
  "(ahm_iteratei,ahm_iteratei) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow>
       (Rb \<rightarrow> bool_rel) \<rightarrow> (\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> Rb \<rightarrow> Rb) \<rightarrow> Rb \<rightarrow> Rb"
unfolding ahm_iteratei_def[abs_def] rec_hashmap_is_case by parametricity

lemma param_ahm_to_list[param]:
  "(ahm_to_list,ahm_to_list) \<in> 
       \<langle>Rk, Rv\<rangle>ahm_map_rel \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding it_to_list_def[abs_def] by parametricity

lemma ahm_to_list_distinct[simp,intro]:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  assumes inv: "ahm_invar bhc m"
  shows "distinct (ahm_to_list m)"
proof-
  obtain n a where [simp]: "m = HashMap a n" by (cases m)
  obtain l where [simp]: "a = Array l" by (cases a)
  from inv show "distinct (ahm_to_list m)" unfolding it_to_list_def
      by (force intro: distinct_mapI dest: ahm_invar_distinct_fst_concatD)
qed



lemma set_ahm_to_list:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  assumes ref: "(m,m') \<in> ahm_map_rel' bhc"
  shows "map_to_set m' = set (ahm_to_list m)"
proof-
  obtain n a where [simp]: "m = HashMap a n" by (cases m)
  obtain l where [simp]: "a = Array l" by (cases a)
  from ref have \<alpha>[simp]: "m' = ahm_\<alpha> bhc m" and 
      inv: "ahm_invar bhc m"
      unfolding ahm_map_rel'_def br_def by auto
  
  from inv have length: "length l > 1" 
      unfolding ahm_invar_def ahm_invar_aux_def by force
  from inv have buckets_ok: "\<And>h x. h < length l \<Longrightarrow> x \<in> set (l!h) \<Longrightarrow>
      bhc (length l) (fst x) = h"
      "\<And>h. h < length l \<Longrightarrow>  distinct (map fst (l!h))"
      by (simp_all add: ahm_invar_def ahm_invar_aux_def 
                        bucket_ok_def list_map_invar_def)

  show ?thesis unfolding it_to_list_def \<alpha> ahm_\<alpha>_def ahm_iteratei_def
      apply (simp add: list_map_lookup_is_map_of)
  proof (intro equalityI subsetI, goal_cases)
    case prems: (1 x)
    let ?m = "\<lambda>k. map_of (l ! bhc (length l) k) k"
    obtain k v where [simp]: "x = (k, v)" by (cases x)
    from prems have "set_to_map (map_to_set ?m) k = Some v"
      by (simp add: set_to_map_simp inj_on_fst_map_to_set)
    also note map_to_set_inverse
    finally have "map_of (l ! bhc (length l) k) k = Some v" .
    hence "(k,v) \<in> set (l ! bhc (length l) k)"
      by (simp add: map_of_SomeD)
    moreover have "bhc (length l) k < length l" using bhc length ..
    ultimately show ?case by force
  next
    case prems: (2 x)
    obtain k v where [simp]: "x = (k, v)" by (cases x)
    from prems obtain h where h_props: "(k,v) \<in> set (l!h)" "h < length l"
      by (force simp: set_conv_nth)
    moreover from h_props and buckets_ok
    have "bhc (length l) k = h" "distinct (map fst (l!h))" by auto
    ultimately have "map_of (l ! bhc (length l) k) k = Some v"
      by (force intro: map_of_is_SomeI)
    thus ?case by simp
  qed
qed

(* TODO: find out what the problem is here *)

lemma ahm_iteratei_aux_impl:
  assumes inv: "ahm_invar_aux bhc n a"
  and bhc: "is_bounded_hashcode Id (=) bhc"
  shows "map_iterator (ahm_iteratei_aux a) (ahm_\<alpha>_aux bhc a)"
proof (cases a, rule)
  fix xs assume [simp]: "a = Array xs"
  show "ahm_iteratei_aux a = foldli (concat xs)"
      by (intro ext, simp)
  from ahm_invar_distinct_fst_concatD and inv
      show "distinct (map fst (concat xs))" by simp
  from ahm_\<alpha>_aux_conv_map_of_concat and assms
      show "ahm_\<alpha>_aux bhc a = map_of (concat xs)" by simp
qed

lemma ahm_iteratei_impl:
  assumes inv: "ahm_invar bhc m"
  and bhc: "is_bounded_hashcode Id (=) bhc"
  shows "map_iterator (ahm_iteratei m) (ahm_\<alpha> bhc m)"
  by (insert assms, cases m, simp add: ahm_\<alpha>_def2,
          erule (1) ahm_iteratei_aux_impl)

lemma autoref_ahm_is_iterator[autoref_ga_rules]:
  (*assumes eq: "GEN_OP_tag ((eq,OP (=) ::: (Rk \<rightarrow> Rk \<rightarrow> bool_rel)) \<in> (Rk \<rightarrow> Rk \<rightarrow> bool_rel))"*)
  assumes bhc: "GEN_ALGO_tag (is_bounded_hashcode Rk eq bhc)"
  shows "is_map_to_list Rk Rv (ahm_rel bhc) ahm_to_list"
  unfolding is_map_to_list_def is_map_to_sorted_list_def
proof (intro allI impI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix a m' assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  from bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" 
    unfolding autoref_tag_defs
    apply (rule_tac abstract_bhc_is_bhc)
    by simp_all

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast
  hence inv: "ahm_invar ?bhc' a'" 
      unfolding ahm_map_rel'_def br_def by simp

  let ?l' = "ahm_to_list a'"
  from param_ahm_to_list[param_fo, OF M1]
      have "(ahm_to_list a, ?l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" .
  moreover from ahm_to_list_distinct[OF bhc' inv] 
      have "distinct (ahm_to_list a')" .
  moreover from set_ahm_to_list[OF bhc' M2]
      have "map_to_set m' = set (ahm_to_list a')" .
  ultimately show "\<exists>l'. (ahm_to_list a, l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<and>
                        RETURN l' \<le> it_to_sorted_list 
                            (key_rel (\<lambda>_ _. True)) (map_to_set m')"
      by (force simp: it_to_sorted_list_def key_rel_def[abs_def])
qed


lemma ahm_iteratei_aux_code[code]:
  "ahm_iteratei_aux a c f \<sigma> = idx_iteratei array_get array_length a c 
       (\<lambda>x. foldli x c f) \<sigma>"
proof(cases a)
  case [simp]: (Array xs)
  have "ahm_iteratei_aux a c f \<sigma> = foldli (concat xs) c f \<sigma>" by simp
  also have "\<dots> = foldli xs c (\<lambda>x. foldli x c f) \<sigma>" by (simp add: foldli_concat)
  also have "\<dots> = idx_iteratei (!) length xs c (\<lambda>x. foldli x c f) \<sigma>" 
      by (simp add: idx_iteratei_nth_length_conv_foldli)
  also have "\<dots> = idx_iteratei array_get array_length a c (\<lambda>x. foldli x c f) \<sigma>"
    by(simp add: idx_iteratei_array_get_Array_conv_nth)
  finally show ?thesis .
qed


subsection \<open>@{term "ahm_rehash"}\<close>

lemma array_length_ahm_rehash_aux':
  "array_length (ahm_rehash_aux' bhc n kv a) = array_length a"
by(simp add: ahm_rehash_aux'_def Let_def)

lemma ahm_rehash_aux'_preserves_ahm_invar_aux:
  assumes inv: "ahm_invar_aux bhc n a"
  and bhc: "is_bounded_hashcode Id (=) bhc"
  and fresh: "k \<notin> fst ` set (array_get a (bhc (array_length a) k))"
  shows "ahm_invar_aux bhc (Suc n) (ahm_rehash_aux' bhc (array_length a) (k, v) a)"
  (is "ahm_invar_aux bhc _ ?a")
proof(rule ahm_invar_auxI)
  note invD = ahm_invar_auxD[OF inv]
  let ?l = "array_length a"
  fix h
  assume "h < array_length ?a"
  hence hlen: "h < ?l" by(simp add: array_length_ahm_rehash_aux')
  from invD(1,2)[OF this] have bucket: "bucket_ok bhc ?l h (array_get a h)"
    and dist: "distinct (map fst (array_get a h))"
    by (simp_all add: list_map_invar_def)
  let ?h = "bhc (array_length a) k"
  from hlen bucket show "bucket_ok bhc (array_length ?a) h (array_get ?a h)"
    by(cases "h = ?h")(auto simp add: ahm_rehash_aux'_def Let_def array_length_ahm_rehash_aux' array_get_array_set_other dest: bucket_okD intro!: bucket_okI)
  from dist hlen fresh
  show "list_map_invar (array_get ?a h)"
    unfolding list_map_invar_def
    by(cases "h = ?h")(auto simp add: ahm_rehash_aux'_def Let_def array_get_array_set_other)
next
  let ?f = "\<lambda>n kvs. n + length kvs"
  { fix n :: nat and xs :: "('a \<times> 'b) list list"
    have "foldl ?f n xs = n + foldl ?f 0 xs"
      by(induct xs arbitrary:  rule: rev_induct) simp_all }
  note fold = this
  let ?h = "bhc (array_length a) k"

  obtain xs where a [simp]: "a = Array xs" by(cases a)
  from inv and bhc have [simp]: "bhc (length xs) k < length xs"
      by (force simp add: ahm_invar_aux_def)
  have xs: "xs = take ?h xs @ (xs ! ?h) # drop (Suc ?h) xs" by(simp add: Cons_nth_drop_Suc)
  from inv have "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a"
    by(auto elim: ahm_invar_auxE)
  hence "n = foldl ?f 0 (take ?h xs) + length (xs ! ?h) + foldl ?f 0 (drop (Suc ?h) xs)"
    by(simp add: array_foldl_foldl)(subst xs, simp, subst (1 2 3 4) fold, simp)
  thus "Suc n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 ?a"
    by(simp add: ahm_rehash_aux'_def Let_def array_foldl_foldl foldl_list_update)(subst (1 2 3 4) fold, simp)
next
  from inv have "1 < array_length a" by(auto elim: ahm_invar_auxE)
  thus "1 < array_length ?a" by(simp add: array_length_ahm_rehash_aux')
qed

(* TODO: Here be dragons *)


lemma ahm_rehash_aux_correct:
  fixes a :: "('k\<times>'v) list array"
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  and inv: "ahm_invar_aux bhc n a"
  and "sz > 1"
  shows "ahm_invar_aux bhc n (ahm_rehash_aux bhc a sz)" (is "?thesis1")
  and "ahm_\<alpha>_aux bhc (ahm_rehash_aux bhc a sz) = ahm_\<alpha>_aux bhc a" (is "?thesis2")
proof -
  let ?a = "ahm_rehash_aux bhc a sz"
  define I where "I it a' \<longleftrightarrow>
   ahm_invar_aux bhc (n - card it) a' 
 \<and> array_length a' = sz 
 \<and> (\<forall>k. if k \<in> it then 
      ahm_\<alpha>_aux bhc a' k = None 
      else ahm_\<alpha>_aux bhc a' k = ahm_\<alpha>_aux bhc a k)" for it a'

  note iterator_rule = map_iterator_no_cond_rule_P[
        OF ahm_iteratei_aux_impl[OF inv bhc], 
        of I "new_array [] sz" "ahm_rehash_aux' bhc sz" "I {}"]

  from inv have "I {} ?a" unfolding ahm_rehash_aux_def
  proof(intro iterator_rule)
    from ahm_invar_aux_card_dom_ahm_\<alpha>_auxD[OF bhc inv] 
        have "card (dom (ahm_\<alpha>_aux bhc a)) = n" .
    moreover from ahm_invar_aux_new_array[OF \<open>1 < sz\<close>]
        have "ahm_invar_aux bhc 0 (new_array ([]::('k\<times>'v) list) sz)" .
    moreover {
      fix k
      assume "k \<notin> dom (ahm_\<alpha>_aux bhc a)"
      hence "ahm_\<alpha>_aux bhc a k = None" by auto
      hence "ahm_\<alpha>_aux bhc (new_array [] sz) k = ahm_\<alpha>_aux bhc a k"
          using assms by simp
    }
    ultimately show "I (dom (ahm_\<alpha>_aux bhc a)) (new_array [] sz)"
        using assms by (simp add: I_def)
  next
    fix k :: 'k
      and v :: 'v
      and it a'
    assume "k \<in> it" "ahm_\<alpha>_aux bhc a k = Some v" 
      and it_sub: "it \<subseteq> dom (ahm_\<alpha>_aux bhc a)"
      and I: "I it a'"
    from I have inv': "ahm_invar_aux bhc (n - card it) a'" 
      and a'_eq_a: "\<And>k. k \<notin> it \<Longrightarrow> ahm_\<alpha>_aux bhc a' k = ahm_\<alpha>_aux bhc a k" 
      and a'_None: "\<And>k. k \<in> it \<Longrightarrow> ahm_\<alpha>_aux bhc a' k = None"
      and [simp]: "sz = array_length a'" 
      by (auto split: if_split_asm simp: I_def)
    from it_sub finite_dom_ahm_\<alpha>_aux[OF bhc inv] 
        have "finite it" by(rule finite_subset)
    moreover with \<open>k \<in> it\<close> have "card it > 0" by (auto simp add: card_gt_0_iff)
    moreover from finite_dom_ahm_\<alpha>_aux[OF bhc inv] it_sub
        have "card it \<le> card (dom (ahm_\<alpha>_aux bhc a))" by (rule card_mono)
    moreover have "\<dots> = n" using inv
        by(simp add: ahm_invar_aux_card_dom_ahm_\<alpha>_auxD[OF bhc])
    ultimately have "n - card (it - {k}) = (n - card it) + 1" 
        using \<open>k \<in> it\<close> by auto
    moreover from \<open>k \<in> it\<close> have "ahm_\<alpha>_aux bhc a' k = None" by (rule a'_None)
    hence "k \<notin> fst ` set (array_get a' (bhc (array_length a') k))"
        by (simp add: ahm_\<alpha>_aux_def2 map_of_eq_None_iff)
    ultimately have "ahm_invar_aux bhc (n - card (it - {k})) 
        (ahm_rehash_aux' bhc sz (k, v) a')"
        using ahm_rehash_aux'_preserves_ahm_invar_aux[OF inv' bhc] by simp
    moreover have "array_length (ahm_rehash_aux' bhc sz (k, v) a') = sz"
        by (simp add: array_length_ahm_rehash_aux')
    moreover {
      fix k'
      assume "k' \<in> it - {k}"
      with is_bounded_hashcodeD(3)[OF bhc \<open>1 < sz\<close>, of k'] a'_None[of k']
      have "ahm_\<alpha>_aux bhc (ahm_rehash_aux' bhc sz (k, v) a') k' = None"
          unfolding ahm_\<alpha>_aux_def2
          by (cases "bhc sz k = bhc sz k'") (simp_all add: 
                  array_get_array_set_other ahm_rehash_aux'_def Let_def)
    } moreover {
      fix k'
      assume "k' \<notin> it - {k}"
      with is_bounded_hashcodeD(3)[OF bhc \<open>1 < sz\<close>, of k]
           is_bounded_hashcodeD(3)[OF bhc \<open>1 < sz\<close>, of k'] 
           a'_eq_a[of k'] \<open>k \<in> it\<close>
      have "ahm_\<alpha>_aux bhc (ahm_rehash_aux' bhc sz (k, v) a') k' = 
                ahm_\<alpha>_aux bhc a k'"
          unfolding ahm_rehash_aux'_def Let_def 
          using \<open>ahm_\<alpha>_aux bhc a k = Some v\<close>
          unfolding ahm_\<alpha>_aux_def2
        by(cases "bhc sz k = bhc sz k'") (case_tac [!] "k' = k", 
            simp_all add: array_get_array_set_other)
    }
    ultimately show "I (it - {k}) (ahm_rehash_aux' bhc sz (k, v) a')"
        unfolding I_def by simp
  qed simp_all
  thus ?thesis1 ?thesis2 unfolding ahm_rehash_aux_def I_def by auto
qed

lemma ahm_rehash_correct:
  fixes hm :: "('k, 'v) hashmap"
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  and inv: "ahm_invar bhc hm"
  and "sz > 1"
  shows "ahm_invar bhc (ahm_rehash bhc hm sz)" 
        "ahm_\<alpha> bhc (ahm_rehash bhc hm sz) = ahm_\<alpha> bhc hm"
proof-
  obtain a n where [simp]: "hm = HashMap a n" by (cases hm)
  from inv have "ahm_invar_aux bhc n a" by simp
  from ahm_rehash_aux_correct[OF bhc this \<open>sz > 1\<close>]
      show "ahm_invar bhc (ahm_rehash bhc hm sz)" and
           "ahm_\<alpha> bhc (ahm_rehash bhc hm sz) = ahm_\<alpha> bhc hm"
      by (simp_all add: ahm_\<alpha>_def2)
qed

subsection \<open>@{term ahm_update}\<close>

lemma param_hm_grow[param]:
  "(hm_grow, hm_grow) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow> nat_rel"
unfolding hm_grow_def[abs_def] rec_hashmap_is_case by parametricity

lemma param_ahm_rehash_aux'[param]:
  assumes "is_bounded_hashcode Rk eq bhc"
  assumes "1 < n"
  assumes "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel"
  assumes "(n,n') \<in> nat_rel" and "n = array_length a"
  assumes "(kv,kv') \<in> \<langle>Rk,Rv\<rangle>prod_rel"
  assumes "(a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel"
  shows "(ahm_rehash_aux' bhc n kv a, ahm_rehash_aux' bhc' n' kv' a') \<in>
             \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel"
proof-
  from assms have "bhc n (fst kv) < array_length a" by force
  thus ?thesis unfolding ahm_rehash_aux'_def[abs_def] 
      rec_hashmap_is_case Let_def using assms by parametricity
qed

(* TODO: Move this *)
lemma param_new_array[param]: 
    "(new_array, new_array) \<in> R \<rightarrow> nat_rel \<rightarrow> \<langle>R\<rangle>array_rel"
unfolding new_array_def[abs_def] by parametricity

(* TODO: move *)
lemma param_foldli_induct:
  assumes l: "(l,l') \<in> \<langle>Ra\<rangle>list_rel"
  assumes c: "(c,c') \<in> Rb \<rightarrow> bool_rel"
  assumes \<sigma>: "(\<sigma>,\<sigma>') \<in> Rb"
  assumes P\<sigma>: "P \<sigma> \<sigma>'"
  assumes f: "\<And>a a' b b'. (a,a')\<in>Ra \<Longrightarrow> (b,b')\<in>Rb \<Longrightarrow> c b \<Longrightarrow> c' b' \<Longrightarrow> 
                           P b b' \<Longrightarrow> (f a b, f' a' b') \<in> Rb \<and> 
                          P (f a b) (f' a' b')"
  shows "(foldli l c f \<sigma>, foldli l' c' f' \<sigma>') \<in> Rb"
using c \<sigma> P\<sigma> f by (induction arbitrary: \<sigma> \<sigma>' rule: list_rel_induct[OF l],
                   auto dest!: fun_relD)

lemma param_foldli_induct_nocond:
  assumes l: "(l,l') \<in> \<langle>Ra\<rangle>list_rel"
  assumes \<sigma>: "(\<sigma>,\<sigma>') \<in> Rb"
  assumes P\<sigma>: "P \<sigma> \<sigma>'"
  assumes f: "\<And>a a' b b'. (a,a')\<in>Ra \<Longrightarrow> (b,b')\<in>Rb \<Longrightarrow> P b b' \<Longrightarrow> 
                  (f a b, f' a' b') \<in> Rb \<and> P (f a b) (f' a' b')"
  shows "(foldli l (\<lambda>_. True) f \<sigma>, foldli l' (\<lambda>_. True) f' \<sigma>') \<in> Rb"
  using assms by (blast intro: param_foldli_induct)

lemma param_ahm_rehash_aux[param]:
  assumes bhc: "is_bounded_hashcode Rk eq bhc"
  assumes bhc_rel: "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel"
  assumes A: "(a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel"
  assumes N: "(n,n') \<in> nat_rel" "1 < n"
  shows "(ahm_rehash_aux bhc a n, ahm_rehash_aux bhc' a' n') \<in> 
        \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel"
proof-
  obtain l l' where [simp]: "a = Array l" "a' = Array l'"
      by (cases a, cases a')
  from A have L: "(l,l') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>list_rel"
      unfolding array_rel_def by simp
  hence L': "(concat l, concat l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
      by parametricity
  let ?P = "\<lambda>a a'. n = array_length a"

  note induct_rule = param_foldli_induct_nocond[OF L', where P="?P"]

  show ?thesis unfolding ahm_rehash_aux_def
      by (simp, induction rule: induct_rule, insert N bhc bhc_rel,
          auto intro: param_new_array[param_fo] 
                      param_ahm_rehash_aux'[param_fo] 
          simp: array_length_ahm_rehash_aux')
qed

(* TODO: Parametricity fails to prove this. Why? *)
lemma param_ahm_rehash[param]:
  assumes bhc: "is_bounded_hashcode Rk eq bhc"
  assumes bhc_rel: "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel"
  assumes M: "(m,m') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel"
  assumes N: "(n,n') \<in> nat_rel" "1 < n"
  shows "(ahm_rehash bhc m n, ahm_rehash bhc' m' n') \<in>
             \<langle>Rk,Rv\<rangle>ahm_map_rel"
proof-
  obtain a a' k k' where [simp]: "m = HashMap a k" "m' = HashMap a' k'"
      by (cases m, cases m')
  hence K: "(k,k') \<in> nat_rel" and
        A: "(a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel"
      using M unfolding ahm_map_rel_def by simp_all
  show ?thesis unfolding ahm_rehash_def 
      by (simp, insert K A assms, parametricity)
qed

lemma param_load_factor[param]:
  "(load_factor, load_factor) \<in> nat_rel" 
  unfolding load_factor_def by simp

lemma param_ahm_filled[param]: 
    "(ahm_filled, ahm_filled) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow> bool_rel"
  unfolding ahm_filled_def[abs_def] rec_hashmap_is_case
  by parametricity

lemma param_ahm_update_aux[param]:
  assumes bhc: "is_bounded_hashcode Rk eq bhc"
  assumes bhc_rel: "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel"
  assumes inv: "ahm_invar bhc' m'"
  assumes K: "(k,k') \<in> Rk"
  assumes V: "(v,v') \<in> Rv"
  assumes M: "(m,m') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel"
  shows "(ahm_update_aux eq bhc m k v, 
          ahm_update_aux (=) bhc' m' k' v' ) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel"
proof-
  from bhc have eq[param]: "(eq, (=))\<in>Rk \<rightarrow> Rk \<rightarrow> bool_rel" by (simp add: is_bounded_hashcodeD)
  obtain a a' n n' where 
      [simp]: "m = HashMap a n" and [simp]: "m' = HashMap a' n'"
      by (cases m, cases m')
  from M have A: "(a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel" and 
              N: "(n,n') \<in> nat_rel"
      unfolding ahm_map_rel_def by simp_all

  from inv have "1 < array_length a'"
      unfolding ahm_invar_def ahm_invar_aux_def by force
  hence "1 < array_length a"
      by (simp add: array_rel_imp_same_length[OF A])
  with bhc have bhc_range: "bhc (array_length a) k < array_length a" by blast

  have option_compare: "\<And>a a'. (a,a') \<in> \<langle>Rv\<rangle>option_rel \<Longrightarrow>
                            (a = None,a' = None) \<in> bool_rel" by force
  have "(array_get a (bhc (array_length a) k),  
         array_get a' (bhc' (array_length a') k')) \<in> 
         \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
    using A K bhc_rel bhc_range by parametricity
  note cmp = option_compare[OF param_list_map_lookup[param_fo, OF eq K this]]
  
  show ?thesis apply simp
    unfolding ahm_update_aux_def Let_def rec_hashmap_is_case
    using assms A N bhc_range cmp by parametricity 
qed


lemma param_ahm_update[param]:
  assumes bhc: "is_bounded_hashcode Rk eq bhc"
  assumes bhc_rel: "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel"
  assumes inv: "ahm_invar bhc' m'"
  assumes K: "(k,k') \<in> Rk"
  assumes V: "(v,v') \<in> Rv"
  assumes M: "(m,m') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel"
  shows "(ahm_update eq bhc k v m, ahm_update (=) bhc' k' v' m') \<in> 
             \<langle>Rk,Rv\<rangle>ahm_map_rel"
proof-
  have "1 < hm_grow (ahm_update_aux eq bhc m k v)" by simp
  with assms show ?thesis unfolding ahm_update_def[abs_def] Let_def
      by parametricity
qed


(* TODO: Move *)
lemma length_list_map_update:
  "length (list_map_update (=) k v xs) =
    (if list_map_lookup (=) k xs = None then Suc (length xs) else length xs)"
        (is "?l_new = _")
proof (cases "list_map_lookup (=) k xs", simp_all)
  case None
    hence "k \<notin> dom (map_of xs)" by (force simp: list_map_lookup_is_map_of)
    hence "\<And>a. list_map_update_aux (=) k v xs a = (k,v) # rev xs @ a"
        by (induction xs, auto)
    thus "?l_new = Suc (length xs)" unfolding list_map_update_def by simp
next
  case (Some v')
    hence "(k,v') \<in> set xs" unfolding list_map_lookup_is_map_of
        by (rule map_of_SomeD)
    hence "\<And>a. length (list_map_update_aux (=) k v xs a) = 
        length xs + length a" by (induction xs, auto)
    thus "?l_new = length xs" unfolding list_map_update_def by simp
qed
  
lemma length_list_map_delete:
  "length (list_map_delete (=) k xs) =
    (if list_map_lookup (=) k xs = None then length xs else length xs - 1)"
        (is "?l_new = _")
proof (cases "list_map_lookup (=) k xs", simp_all)
  case None
    hence "k \<notin> dom (map_of xs)" by (force simp: list_map_lookup_is_map_of)
    hence "\<And>a. list_map_delete_aux (=) k xs a = rev xs @ a"
        by (induction xs, auto)
    thus "?l_new = length xs" unfolding list_map_delete_def by simp
next
  case (Some v')
    hence "(k,v') \<in> set xs" unfolding list_map_lookup_is_map_of
        by (rule map_of_SomeD)
    hence "\<And>a. k \<notin> fst`set a \<Longrightarrow> length (list_map_delete_aux (=) k xs a) = 
        length xs + length a - 1" by (induction xs, auto)
    thus "?l_new = length xs - Suc 0" unfolding list_map_delete_def by simp
qed
    


lemma ahm_update_impl:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  shows "(ahm_update (=) bhc, op_map_update) \<in> (Id::('k\<times>'k) set) \<rightarrow> 
              (Id::('v\<times>'v) set) \<rightarrow> ahm_map_rel' bhc \<rightarrow> ahm_map_rel' bhc"
proof (intro fun_relI, clarsimp)
  fix k::'k and v::'v and hm::"('k,'v) hashmap" and  m::"'k\<rightharpoonup>'v"
  assume "(hm,m) \<in> ahm_map_rel' bhc"
  hence \<alpha>: "m = ahm_\<alpha> bhc hm" and inv: "ahm_invar bhc hm"
      unfolding ahm_map_rel'_def br_def by simp_all
  obtain a n where [simp]: "hm = HashMap a n" by (cases hm)

  have K: "(k,k) \<in> Id" and V: "(v,v) \<in> Id" by simp_all

  from inv have [simp]: "1 < array_length a"
      unfolding ahm_invar_def ahm_invar_aux_def by simp
  hence bhc_range[simp]: "\<And>k. bhc (array_length a) k < array_length a"
      using bhc by blast

  let ?l = "array_length a"
  let ?h = "bhc (array_length a) k"
  let ?a' = "array_set a ?h (list_map_update (=) k v (array_get a ?h))"
  let ?n' = "if list_map_lookup (=) k (array_get a ?h) = None 
                 then n + 1 else n"

  let ?list = "array_get a (bhc ?l k)"
  let ?list' = "map_of ?list"
  have L: "(?list, ?list') \<in> br map_of list_map_invar"
      using inv unfolding ahm_invar_def ahm_invar_aux_def br_def by simp
  hence list: "list_map_invar ?list" by (simp_all add: br_def)
  let ?list_new = "list_map_update (=) k v ?list"
  let ?list_new' = "op_map_update k v (map_of (?list))"
  from list_map_autoref_update2[param_fo, OF K V L]
      have list_updated: "map_of ?list_new = ?list_new'" 
           "list_map_invar ?list_new" unfolding br_def by simp_all

  have "ahm_invar bhc (HashMap ?a' ?n')" unfolding ahm_invar.simps
  proof(rule ahm_invar_auxI)
    fix h
    assume "h < array_length ?a'"
    hence h_in_range: "h < array_length a" by simp
    with inv have bucket_ok: "bucket_ok bhc ?l h (array_get a h)"
        by(auto elim: ahm_invar_auxD)
    thus "bucket_ok bhc (array_length ?a') h (array_get ?a' h)"
      proof (cases "h = bhc (array_length a) k")
        case False 
          with bucket_ok show ?thesis
              by (intro bucket_okI, force simp add: 
                  array_get_array_set_other dest: bucket_okD)
      next
        case True
          show ?thesis
          proof (insert True, simp, intro bucket_okI, goal_cases)
            case prems: (1 k')
              show ?case
              proof (cases "k = k'")
                case False
                  from prems have "k' \<in> dom ?list_new'"
                      by (simp only: dom_map_of_conv_image_fst 
                          list_updated(1)[symmetric])
                  hence "k' \<in> fst`set ?list" using False
                      by (simp add: dom_map_of_conv_image_fst)
                  from imageE[OF this] obtain x where 
                      "fst x = k'" and "x \<in> set ?list" by force
                  then obtain v' where "(k',v') \<in> set ?list"
                       by (cases x, simp)
                  with bucket_okD[OF bucket_ok] and 
                      \<open>h = bhc (array_length a) k\<close>
                      show ?thesis by simp
             qed simp
          qed
      qed
    from \<open>h < array_length a\<close> inv have "list_map_invar (array_get a h)"
        by(auto dest: ahm_invar_auxD)
    with \<open>h < array_length a\<close>
    show "list_map_invar (array_get ?a' h)"
        by (cases "h = ?h", simp_all add: 
            list_updated array_get_array_set_other)
  next

    obtain xs where a [simp]: "a = Array xs" by(cases a)

    let ?f = "\<lambda>n kvs. n + length kvs"
    { fix n :: nat and xs :: "('k \<times> 'v) list list"
      have "foldl ?f n xs = n + foldl ?f 0 xs"
        by(induct xs arbitrary:  rule: rev_induct) simp_all }
    note fold = this

    from inv have [simp]: "bhc (length xs) k < length xs"
        using bhc_range by simp
    have xs: "xs = take ?h xs @ (xs ! ?h) # drop (Suc ?h) xs"
        by(simp add: Cons_nth_drop_Suc)
    from inv have "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a"
        by (force dest: ahm_invar_auxD)
    hence "n = foldl ?f 0 (take ?h xs) + length (xs ! ?h) + foldl ?f 0 (drop (Suc ?h) xs)"
      apply (simp add: array_foldl_foldl)
      apply (subst xs)
      apply simp
      apply (metis fold)
      done
    thus "?n' = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 ?a'"
      apply(simp add: ahm_rehash_aux'_def Let_def array_foldl_foldl foldl_list_update map_of_eq_None_iff)
      apply(subst (1 2 3 4 5 6 7 8) fold)
      apply(simp add: length_list_map_update)
      done
  next
    from inv have "1 < array_length a" by(auto elim: ahm_invar_auxE)
    thus "1 < array_length ?a'" by simp
  next
  qed

  moreover have "ahm_\<alpha> bhc (ahm_update_aux (=) bhc hm k v) = 
                     ahm_\<alpha> bhc hm(k \<mapsto> v)"
  proof
    fix k'
    show "ahm_\<alpha> bhc (ahm_update_aux (=) bhc hm k v) k' = (ahm_\<alpha> bhc hm(k \<mapsto> v)) k'"
    proof (cases "bhc ?l k = bhc ?l k'") 
      case False
        thus ?thesis by (force simp add: Let_def 
            ahm_\<alpha>_def array_get_array_set_other)
    next
      case True
        hence "bhc ?l k' = bhc ?l k" by simp
        thus ?thesis by (auto simp add: Let_def ahm_\<alpha>_def 
            list_map_lookup_is_map_of list_updated)
    qed
  qed

  ultimately have ref: "(ahm_update_aux (=) bhc hm k v, 
                    m(k \<mapsto> v)) \<in> ahm_map_rel' bhc" (is "(?hm',_)\<in>_")
  unfolding ahm_map_rel'_def br_def using \<alpha> by (auto simp: Let_def)

  show "(ahm_update (=) bhc k v hm, m(k \<mapsto> v))
            \<in> ahm_map_rel' bhc"
  proof (cases "ahm_filled ?hm'")
    case False
      with ref show ?thesis unfolding ahm_update_def
          by (simp del: ahm_update_aux.simps)
  next
    case True
      from ref have "(ahm_rehash bhc ?hm' (hm_grow ?hm'), m(k \<mapsto> v)) \<in> 
          ahm_map_rel' bhc" unfolding ahm_map_rel'_def br_def
          by (simp del: ahm_update_aux.simps 
                   add: ahm_rehash_correct[OF bhc])
      thus ?thesis unfolding ahm_update_def using True
          by (simp del: ahm_update_aux.simps add: Let_def)
  qed
qed

lemma autoref_ahm_update[autoref_rules]:
  assumes bhc[unfolded autoref_tag_defs]: 
    "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  shows "(ahm_update eq bhc, op_map_update) \<in> 
              Rk \<rightarrow> Rv \<rightarrow> \<langle>Rk,Rv\<rangle>ahm_rel bhc \<rightarrow> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
proof (intro fun_relI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix k k' v v' a m'
  assume K: "(k,k') \<in> Rk" and V: "(v,v') \<in> Rv"
  assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  (*from eq have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel" by simp*)
  with bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" by blast
  from abstract_bhc_correct[OF bhc] 
      have bhc_rel: "(bhc,?bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel" .

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast
  hence inv: "ahm_invar ?bhc' a'" 
      unfolding ahm_map_rel'_def br_def by simp


  from relcompI[OF param_ahm_update[OF bhc bhc_rel inv K V M1]
                   ahm_update_impl[param_fo, OF bhc' _ _ M2]]
  show "(ahm_update eq bhc k v a, op_map_update k' v' m') \<in> 
            \<langle>Rk,Rv\<rangle>ahm_rel bhc" unfolding ahm_rel_def by simp
qed

subsection \<open>@{term "ahm_delete"}\<close>

lemma param_ahm_delete[param]:
  (*assumes eq: "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel"*)
  assumes isbhc: "is_bounded_hashcode Rk eq bhc"
  assumes bhc: "(bhc,bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel"
  assumes inv: "ahm_invar bhc' m'"
  assumes K: "(k,k') \<in> Rk"
  assumes M: "(m,m') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel"
  shows
  "(ahm_delete eq bhc k m, ahm_delete (=) bhc' k' m') \<in> 
       \<langle>Rk,Rv\<rangle>ahm_map_rel"
proof-
  from isbhc have eq: "(eq,(=))\<in>Rk\<rightarrow>Rk\<rightarrow>bool_rel" by (simp add: is_bounded_hashcodeD)

  obtain a a' n n' where 
      [simp]: "m = HashMap a n" and [simp]: "m' = HashMap a' n'"
      by (cases m, cases m')
  from M have A: "(a,a') \<in> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel" and 
              N: "(n,n') \<in> nat_rel"
      unfolding ahm_map_rel_def by simp_all

  from inv have "1 < array_length a'"
      unfolding ahm_invar_def ahm_invar_aux_def by force
  hence "1 < array_length a"
      by (simp add: array_rel_imp_same_length[OF A])
  with isbhc have bhc_range: "bhc (array_length a) k < array_length a" by blast

  have option_compare: "\<And>a a'. (a,a') \<in> \<langle>Rv\<rangle>option_rel \<Longrightarrow>
                            (a = None,a' = None) \<in> bool_rel" by force
  have "(array_get a (bhc (array_length a) k),  
         array_get a' (bhc' (array_length a') k')) \<in> 
         \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
      using A K bhc bhc_range by parametricity
  note cmp = option_compare[OF param_list_map_lookup[param_fo, OF eq K this]]

  show ?thesis unfolding \<open>m = HashMap a n\<close> \<open>m' = HashMap a' n'\<close>
      by (simp only: ahm_delete.simps Let_def,
             insert eq isbhc bhc K A N bhc_range cmp, parametricity)
qed


lemma ahm_delete_impl:
  assumes bhc: "is_bounded_hashcode Id (=) bhc"
  shows "(ahm_delete (=) bhc, op_map_delete) \<in> (Id::('k\<times>'k) set) \<rightarrow> 
              ahm_map_rel' bhc \<rightarrow> ahm_map_rel' bhc"
proof (intro fun_relI, clarsimp)
  fix k::'k and hm::"('k,'v) hashmap" and  m::"'k\<rightharpoonup>'v"
  assume "(hm,m) \<in> ahm_map_rel' bhc"
  hence \<alpha>: "m = ahm_\<alpha> bhc hm" and inv: "ahm_invar bhc hm"
      unfolding ahm_map_rel'_def br_def by simp_all
  obtain a n where [simp]: "hm = HashMap a n" by (cases hm)

  have K: "(k,k) \<in> Id" by simp

  from inv have [simp]: "1 < array_length a"
      unfolding ahm_invar_def ahm_invar_aux_def by simp
  hence bhc_range[simp]: "\<And>k. bhc (array_length a) k < array_length a"
      using bhc by blast

  let ?l = "array_length a"
  let ?h = "bhc ?l k"
  let ?a' = "array_set a ?h (list_map_delete (=) k (array_get a ?h))"
  let ?n' = "if list_map_lookup (=) k (array_get a ?h) = None then n else n - 1"
  let ?list = "array_get a ?h" let ?list' = "map_of ?list"
  let ?list_new = "list_map_delete (=) k ?list"
  let ?list_new' = "?list' |` (-{k})"
  from inv have "(?list, ?list') \<in> br map_of list_map_invar"
      unfolding br_def ahm_invar_def ahm_invar_aux_def by simp
  from list_map_autoref_delete2[param_fo, OF K this]
      have list_updated: "map_of ?list_new = ?list_new'"
           "list_map_invar ?list_new" by (simp_all add: br_def)
  
  have [simp]: "array_length ?a' = ?l" by simp

  have "ahm_invar_aux bhc ?n' ?a'"
  proof(rule ahm_invar_auxI)
    fix h
    assume "h < array_length ?a'"
    hence h_in_range[simp]: "h < array_length a" by simp
    with inv have inv': "bucket_ok bhc ?l h (array_get a h)" "1 < ?l" 
        "list_map_invar (array_get a h)" by (auto elim: ahm_invar_auxE)

    show "bucket_ok bhc (array_length ?a') h (array_get ?a' h)"
      proof (cases "h = bhc ?l k")
        case False thus ?thesis using inv'
            by (simp add: array_get_array_set_other)
      next
        case True thus ?thesis
        proof (simp, intro bucket_okI, goal_cases)
          case prems: (1 k')
              show ?case
              proof (cases "k = k'")
                case False
                  from prems have "k' \<in> dom ?list_new'"
                      by (simp only: dom_map_of_conv_image_fst 
                          list_updated(1)[symmetric])
                  hence "k' \<in> fst`set ?list" using False
                      by (simp add: dom_map_of_conv_image_fst)
                  from imageE[OF this] obtain x where 
                      "fst x = k'" and "x \<in> set ?list" by force
                  then obtain v' where "(k',v') \<in> set ?list"
                       by (cases x, simp)
                  with bucket_okD[OF inv'(1)] and 
                      \<open>h = bhc (array_length a) k\<close>
                      show ?thesis by blast
             qed simp
        qed
      qed
    
    from inv'(3) \<open>h < array_length a\<close>
    show "list_map_invar (array_get ?a' h)"
        by (cases "h = ?h", simp_all add: 
            list_updated array_get_array_set_other)
  next
    obtain xs where a [simp]: "a = Array xs" by(cases a)

    let ?f = "\<lambda>n kvs. n + length (kvs::('k\<times>'v) list)"
    { fix n :: nat and xs :: "('k\<times>'v) list list"
      have "foldl ?f n xs = n + foldl ?f 0 xs"
        by(induct xs arbitrary:  rule: rev_induct) simp_all }
    note fold = this

    from bhc_range have [simp]: "bhc (length xs) k < length xs" by simp
    moreover
    have xs: "xs = take ?h xs @ (xs ! ?h) # drop (Suc ?h) xs" by(simp add: Cons_nth_drop_Suc)
    from inv have "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a"
      by(auto elim: ahm_invar_auxE)
    hence "n = foldl ?f 0 (take ?h xs) + length (xs ! ?h) + foldl ?f 0 (drop (Suc ?h) xs)"
      by(simp add: array_foldl_foldl)(subst xs, simp, subst (1 2 3 4) fold, simp)
    moreover have "\<And>v a b. list_map_lookup (=) k (xs ! ?h) = Some v
        \<Longrightarrow> a + (length (xs ! ?h) - 1) + b = a + length (xs ! ?h) + b - 1"
         by (cases "xs ! ?h", simp_all)
    ultimately show "?n' = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 ?a'"
      apply(simp add: array_foldl_foldl foldl_list_update map_of_eq_None_iff)
      apply(subst (1 2 3 4 5 6 7 8) fold)
apply (intro conjI impI)
      apply(auto simp add: length_list_map_delete)
      done
  next

    from inv show "1 < array_length ?a'" by(auto elim: ahm_invar_auxE)
  qed
  hence "ahm_invar bhc (HashMap ?a' ?n')" by simp

  moreover have "ahm_\<alpha>_aux bhc ?a' = ahm_\<alpha>_aux bhc a |` (- {k})"
  proof
    fix k' :: 'k
    show "ahm_\<alpha>_aux bhc ?a' k' = (ahm_\<alpha>_aux bhc a |` (- {k})) k'"
    proof (cases "bhc ?l k' = ?h")
      case False
        hence "k \<noteq> k'" by force
        thus ?thesis using False unfolding ahm_\<alpha>_aux_def 
            by (simp add: array_get_array_set_other 
                          list_map_lookup_is_map_of)
    next
      case True
        thus ?thesis unfolding ahm_\<alpha>_aux_def 
            by (simp add: list_map_lookup_is_map_of 
                       list_updated(1) restrict_map_def)
    qed
  qed 
  hence "ahm_\<alpha> bhc (HashMap ?a' ?n') = op_map_delete k m"
      unfolding op_map_delete_def by (simp add: ahm_\<alpha>_def2 \<alpha>)
  
  ultimately have "(HashMap ?a' ?n', op_map_delete k m) \<in> ahm_map_rel' bhc"
      unfolding ahm_map_rel'_def br_def by simp

  thus "(ahm_delete (=) bhc k hm, m |` (-{k})) \<in> ahm_map_rel' bhc"
      by (simp only: \<open>hm = HashMap a n\<close> ahm_delete.simps Let_def 
                 op_map_delete_def, force)
qed

lemma autoref_ahm_delete[autoref_rules]:
  assumes bhc[unfolded autoref_tag_defs]: 
    "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  shows "(ahm_delete eq bhc, op_map_delete) \<in> 
              Rk \<rightarrow> \<langle>Rk,Rv\<rangle>ahm_rel bhc \<rightarrow> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
proof (intro fun_relI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix k k' a m'
  assume K: "(k,k') \<in> Rk"
  assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  (*from bhc have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel" by (simp add: is_bounded_hashcodeD)*)
  with bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" by blast
  from abstract_bhc_correct[OF bhc] 
      have bhc_rel: "(bhc,?bhc') \<in> nat_rel \<rightarrow> Rk \<rightarrow> nat_rel" .

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast
  hence inv: "ahm_invar ?bhc' a'" 
      unfolding ahm_map_rel'_def br_def by simp

  from relcompI[OF param_ahm_delete[OF bhc bhc_rel inv K M1]
                   ahm_delete_impl[param_fo, OF bhc' _ M2]]
  show "(ahm_delete eq bhc k a, op_map_delete k' m') \<in> 
            \<langle>Rk,Rv\<rangle>ahm_rel bhc" unfolding ahm_rel_def by simp
qed


subsection \<open>Various simple operations\<close>

lemma param_ahm_isEmpty[param]: 
    "(ahm_isEmpty, ahm_isEmpty) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow> bool_rel"
unfolding ahm_isEmpty_def[abs_def] rec_hashmap_is_case
by parametricity

lemma param_ahm_isSng[param]: 
    "(ahm_isSng, ahm_isSng) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow> bool_rel"
unfolding ahm_isSng_def[abs_def] rec_hashmap_is_case
by parametricity

lemma param_ahm_size[param]: 
    "(ahm_size, ahm_size) \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel \<rightarrow> nat_rel"
unfolding ahm_size_def[abs_def] rec_hashmap_is_case
by parametricity


lemma ahm_isEmpty_impl:
  assumes "is_bounded_hashcode Id (=) bhc"
  shows "(ahm_isEmpty, op_map_isEmpty) \<in> ahm_map_rel' bhc \<rightarrow> bool_rel"
proof (intro fun_relI)
  fix hm m assume rel: "(hm,m) \<in> ahm_map_rel' bhc"
  obtain a n where [simp]: "hm = HashMap a n" by (cases hm)
  from rel have \<alpha>: "m = ahm_\<alpha>_aux bhc a" and inv: "ahm_invar_aux bhc n a"
      unfolding ahm_map_rel'_def br_def by (simp_all add: ahm_\<alpha>_def2)
  from ahm_invar_aux_card_dom_ahm_\<alpha>_auxD[OF assms inv,symmetric] and
       finite_dom_ahm_\<alpha>_aux[OF assms inv]
      show "(ahm_isEmpty hm, op_map_isEmpty m) \<in> bool_rel"
          unfolding ahm_isEmpty_def op_map_isEmpty_def
          by (simp add: \<alpha> card_eq_0_iff)
qed

lemma ahm_isSng_impl:
  assumes "is_bounded_hashcode Id (=) bhc"
  shows "(ahm_isSng, op_map_isSng) \<in> ahm_map_rel' bhc \<rightarrow> bool_rel"
proof (intro fun_relI)
  fix hm m assume rel: "(hm,m) \<in> ahm_map_rel' bhc"
  obtain a n where [simp]: "hm = HashMap a n" by (cases hm)
  from rel have \<alpha>: "m = ahm_\<alpha>_aux bhc a" and inv: "ahm_invar_aux bhc n a"
      unfolding ahm_map_rel'_def br_def by (simp_all add: ahm_\<alpha>_def2)
  note n_props[simp] = ahm_invar_aux_card_dom_ahm_\<alpha>_auxD[OF assms inv,symmetric]
  note finite_dom[simp] =  finite_dom_ahm_\<alpha>_aux[OF assms inv]
  show "(ahm_isSng hm, op_map_isSng m) \<in> bool_rel"
      by (force simp add: \<alpha>[symmetric] dom_eq_singleton_conv 
                dest!: card_eq_SucD)
qed

lemma ahm_size_impl:
  assumes "is_bounded_hashcode Id (=) bhc"
  shows "(ahm_size, op_map_size) \<in> ahm_map_rel' bhc \<rightarrow> nat_rel"
proof (intro fun_relI)
  fix hm m assume rel: "(hm,m) \<in> ahm_map_rel' bhc"
  obtain a n where [simp]: "hm = HashMap a n" by (cases hm)
  from rel have \<alpha>: "m = ahm_\<alpha>_aux bhc a" and inv: "ahm_invar_aux bhc n a"
      unfolding ahm_map_rel'_def br_def by (simp_all add: ahm_\<alpha>_def2)
  from ahm_invar_aux_card_dom_ahm_\<alpha>_auxD[OF assms inv,symmetric]
      show "(ahm_size hm, op_map_size m) \<in> nat_rel"
          unfolding ahm_isEmpty_def op_map_isEmpty_def
          by (simp add: \<alpha> card_eq_0_iff)
qed


lemma autoref_ahm_isEmpty[autoref_rules]:
  (*assumes eq: "GEN_OP eq (=) (Rk \<rightarrow> Rk \<rightarrow> bool_rel)"*)
  assumes bhc[unfolded autoref_tag_defs]: 
      "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  shows "(ahm_isEmpty, op_map_isEmpty) \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc \<rightarrow> bool_rel"
proof (intro fun_relI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix k k' a m'
  assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  (*from eq have "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel" by simp*)
  from bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" 
    by blast

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast

  from relcompI[OF param_ahm_isEmpty[param_fo, OF M1]
                   ahm_isEmpty_impl[param_fo, OF bhc' M2]]
  show "(ahm_isEmpty a, op_map_isEmpty m') \<in> bool_rel" by simp
qed

lemma autoref_ahm_isSng[autoref_rules]:
  assumes bhc[unfolded autoref_tag_defs]: 
      "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  shows "(ahm_isSng, op_map_isSng) \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc \<rightarrow> bool_rel"
proof (intro fun_relI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix k k' a m'
  assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  from bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" 
    by blast

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast

  from relcompI[OF param_ahm_isSng[param_fo, OF M1]
                   ahm_isSng_impl[param_fo, OF bhc' M2]]
  show "(ahm_isSng a, op_map_isSng m') \<in> bool_rel" by simp
qed

lemma autoref_ahm_size[autoref_rules]:
  assumes bhc[unfolded autoref_tag_defs]: 
      "SIDE_GEN_ALGO (is_bounded_hashcode Rk eq bhc)"
  shows "(ahm_size, op_map_size) \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc \<rightarrow> nat_rel"
proof (intro fun_relI)
  let ?bhc' = "abstract_bounded_hashcode Rk bhc"
  fix k k' a m'
  assume M: "(a,m') \<in> \<langle>Rk,Rv\<rangle>ahm_rel bhc"
  from bhc have bhc': "is_bounded_hashcode Id (=) ?bhc'" 
    by blast

  from M obtain a' where M1: "(a,a') \<in> \<langle>Rk,Rv\<rangle>ahm_map_rel" and
      M2: "(a',m') \<in> ahm_map_rel' ?bhc'" unfolding ahm_rel_def by blast

  from relcompI[OF param_ahm_size[param_fo, OF M1]
                   ahm_size_impl[param_fo, OF bhc' M2]]
  show "(ahm_size a, op_map_size m') \<in> nat_rel" by simp
qed

lemma ahm_map_rel_sv[relator_props]:
  assumes SK: "single_valued Rk" 
  assumes SV: "single_valued Rv"
  shows "single_valued (\<langle>Rk, Rv\<rangle>ahm_map_rel)"
proof -
  from SK SV have 1: "single_valued (\<langle>\<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>array_rel)"
    by (tagged_solver)

  thus ?thesis
    unfolding ahm_map_rel_def
    by (auto intro: single_valuedI dest: single_valuedD[OF 1])
qed

lemma ahm_rel_sv[relator_props]:
  "\<lbrakk>single_valued Rk; single_valued Rv\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rk,Rv\<rangle>ahm_rel bhc)"
  unfolding ahm_rel_def ahm_map_rel'_def
  by (tagged_solver (keep))

lemma rbt_map_rel_finite[relator_props]: 
  assumes A[simplified]: "GEN_ALGO_tag (is_bounded_hashcode Rk eq bhc)"
  shows "finite_map_rel (\<langle>Rk,Rv\<rangle>ahm_rel bhc)"
  unfolding ahm_rel_def finite_map_rel_def ahm_map_rel'_def br_def
  apply auto
  apply (case_tac y)
  apply (auto simp: ahm_\<alpha>_def2)
  thm finite_dom_ahm_\<alpha>_aux
  apply (rule finite_dom_ahm_\<alpha>_aux)
  apply (rule abstract_bhc_is_bhc)
  apply (rule A)
  apply assumption
  done

subsection \<open>Proper iterator proofs\<close>

lemma pi_ahm[icf_proper_iteratorI]: 
  "proper_it (ahm_iteratei m) (ahm_iteratei m)"
proof-
  obtain a n where [simp]: "m = HashMap a n" by (cases m)
  then obtain l where [simp]: "a = Array l" by (cases a)
  thus ?thesis
    unfolding proper_it_def list_map_iteratei_def
    by (simp add: ahm_iteratei_aux_def, blast)
qed

lemma pi'_ahm[icf_proper_iteratorI]: 
  "proper_it' ahm_iteratei ahm_iteratei"
  by (rule proper_it'I, rule pi_ahm)


(*
hide_const (open) HashMap bucket_ok ahm_invar ahm_\<alpha>
  ahm_rehash hm_grow ahm_filled
hide_type (open) hashmap
*)


lemmas autoref_ahm_rules = 
  autoref_ahm_empty 
  autoref_ahm_lookup 
  autoref_ahm_update
  autoref_ahm_delete
  autoref_ahm_isEmpty
  autoref_ahm_isSng
  autoref_ahm_size

lemmas autoref_ahm_rules_hashable[autoref_rules_raw]
  = autoref_ahm_rules[where Rk="Rk"] for Rk :: "(_\<times>_::hashable) set"


end
