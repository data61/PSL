(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Iteration of Subsets of Factors\<close>
theory Sublist_Iteration
imports 
  Polynomial_Factorization.Missing_Multiset
  Polynomial_Factorization.Missing_List
  "HOL-Library.IArray"
begin

paragraph \<open>Misc lemmas\<close>

lemma mem_snd_map: "(\<exists>x. (x, y) \<in> S) \<longleftrightarrow> y \<in> snd ` S" by force

lemma filter_upt: assumes "l \<le> m" "m < n" shows "filter ((\<le>) m) [l..<n] = [m..<n]"
proof(insert assms, induct n)
  case 0 then show ?case by auto
next
  case (Suc n) then show ?case by (cases "m = n", auto)
qed

lemma upt_append: "i < j \<Longrightarrow> j < k \<Longrightarrow> [i..<j]@[j..<k] = [i..<k]"
proof(induct k arbitrary: j)
  case 0 then show ?case by auto
next
  case (Suc k) then show ?case by (cases "j = k", auto)
qed

lemma IArray_sub[simp]: "(!!) as = (!) (IArray.list_of as)" by auto
declare IArray.sub_def[simp del]

text \<open>Following lemmas in this section are for @{const subseqs}\<close>

lemma subseqs_Cons[simp]: "subseqs (x#xs) = map (Cons x) (subseqs xs) @ subseqs xs"
  by (simp add: Let_def)

declare subseqs.simps(2) [simp del]

lemma singleton_mem_set_subseqs [simp]: "[x] \<in> set (subseqs xs) \<longleftrightarrow> x \<in> set xs" by (induct xs, auto)

lemma Cons_mem_set_subseqsD: "y#ys \<in> set (subseqs xs) \<Longrightarrow> y \<in> set xs" by (induct xs, auto)

lemma subseqs_subset: "ys \<in> set (subseqs xs) \<Longrightarrow> set ys \<subseteq> set xs"
  by (metis Pow_iff image_eqI subseqs_powset)

lemma Cons_mem_set_subseqs_Cons:
  "y#ys \<in> set (subseqs (x#xs)) \<longleftrightarrow> (y = x \<and> ys \<in> set (subseqs xs)) \<or> y#ys \<in> set (subseqs xs)"
  by auto

lemma sorted_subseqs_sorted:
  "sorted xs \<Longrightarrow> ys \<in> set (subseqs xs) \<Longrightarrow> sorted ys"
proof(induct xs arbitrary: ys)
  case Nil thus ?case by simp
next
  case Cons thus ?case using subseqs_subset by fastforce
qed


lemma subseqs_of_subseq: "ys \<in> set (subseqs xs) \<Longrightarrow> set (subseqs ys) \<subseteq> set (subseqs xs)"
proof(induct xs arbitrary: ys)
  case Nil then show ?case by auto
next
  case IHx: (Cons x xs)
  from IHx.prems show ?case
  proof(induct ys)
    case Nil then show ?case by auto
  next
    case IHy: (Cons y ys)
    from IHy.prems[unfolded subseqs_Cons]
    consider "y = x" "ys \<in> set (subseqs xs)" | "y # ys \<in> set (subseqs xs)" by auto
    then show ?case
    proof(cases)
      case 1 with IHx.hyps show ?thesis by auto
    next
      case 2 from IHx.hyps[OF this] show ?thesis by auto
    qed
  qed
qed

lemma mem_set_subseqs_append: "xs \<in> set (subseqs ys) \<Longrightarrow> xs \<in> set (subseqs (zs @ ys))"
  by (induct zs, auto)

lemma Cons_mem_set_subseqs_append:
  "x \<in> set ys \<Longrightarrow> xs \<in> set (subseqs zs) \<Longrightarrow> x#xs \<in> set (subseqs (ys@zs))"
proof(induct ys)
  case Nil then show ?case by auto
next
  case IH: (Cons y ys)
  then consider "x = y" | "x \<in> set ys" by auto
  then show ?case
  proof(cases)
    case 1 with IH show ?thesis by (auto intro: mem_set_subseqs_append)
  next
    case 2 from IH.hyps[OF this IH.prems(2)] show ?thesis by auto
  qed
qed

lemma Cons_mem_set_subseqs_sorted:
  "sorted xs \<Longrightarrow> y#ys \<in> set (subseqs xs) \<Longrightarrow> y#ys \<in> set (subseqs (filter (\<lambda>x. y \<le> x) xs))"
by (induct xs) (auto simp: Let_def)

lemma subseqs_map[simp]: "subseqs (map f xs) = map (map f) (subseqs xs)" by (induct xs, auto)

lemma subseqs_of_indices: "map (map (nth xs)) (subseqs [0..<length xs]) = subseqs xs"
proof (induct xs)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  from this[symmetric]
  have "subseqs xs = map (map ((!) (x#xs))) (subseqs [Suc 0..<Suc (length xs)])"
    by (fold map_Suc_upt, simp)
  then show ?case by (unfold length_Cons upt_conv_Cons[OF zero_less_Suc], simp)
qed


paragraph \<open>Specification\<close>

definition "subseq_of_length n xs ys \<equiv> ys \<in> set (subseqs xs) \<and> length ys = n"

lemma subseq_of_lengthI[intro]:
  assumes "ys \<in> set (subseqs xs)" "length ys = n"
  shows "subseq_of_length n xs ys"
by (insert assms, unfold subseq_of_length_def, auto)

lemma subseq_of_lengthD[dest]:
  assumes "subseq_of_length n xs ys"
  shows "ys \<in> set (subseqs xs)" "length ys = n"
  by (insert assms, unfold subseq_of_length_def, auto)

lemma subseq_of_length0[simp]: "subseq_of_length 0 xs ys \<longleftrightarrow> ys = []" by auto

lemma subseq_of_length_Nil[simp]: "subseq_of_length n [] ys \<longleftrightarrow> n = 0 \<and> ys = []"
  by (auto simp: subseq_of_length_def)

lemma subseq_of_length_Suc_upt:
  "subseq_of_length (Suc n) [0..<m] xs \<longleftrightarrow>
   (if n = 0 then length xs = Suc 0 \<and> hd xs < m
    else hd xs < hd (tl xs) \<and> subseq_of_length n [0..<m] (tl xs))" (is "?l \<longleftrightarrow> ?r")
proof(cases "n")
  case 0
  show ?thesis
  proof(intro iffI)
    assume l: "?l"
    with 0 have 1: "length xs = Suc 0" by auto
    then have xs: "xs = [hd xs]" by (metis length_0_conv length_Suc_conv list.sel(1))
    with l have "[hd xs] \<in> set (subseqs [0..<m])" by auto
    with 1 show "?r" by (unfold 0, auto)
  next
    assume ?r
    with 0 have 1: "length xs = Suc 0" and 2: "hd xs < m" by auto
    then have xs: "xs = [hd xs]" by (metis length_0_conv length_Suc_conv list.sel(1))
    from 2 show "?l" by (subst xs, auto simp: 0)
  qed
next
  case n: (Suc n')
  show ?thesis
  proof (intro iffI)
    assume "?l"
    with n have 1: "length xs = Suc (Suc n')" and 2: "xs \<in> set (subseqs [0..<m])" by auto
    from 1[unfolded length_Suc_conv]
    obtain x y ys where xs: "xs = x#y#ys" and n': "length ys = n'" by auto
    have "sorted xs" by(rule sorted_subseqs_sorted[OF _ 2], auto)
    from this[unfolded xs] have "x \<le> y" by auto
    moreover
      from 2 have "distinct xs" by (rule subseqs_distinctD, auto)
      from this[unfolded xs] have "x \<noteq> y" by auto
    ultimately have "x < y" by auto
    moreover
      from 2 have "y#ys \<in> set (subseqs [0..<m])" by (unfold xs, auto dest: Cons_in_subseqsD)
      with n n' have "subseq_of_length n [0..<m] (y#ys)" by auto
    ultimately show ?r by (auto simp: xs)
  next
    assume r: "?r"
    with n have len: "length xs = Suc (Suc n')"
     and *: "hd xs < hd (tl xs)" "tl xs \<in> set (subseqs [0..<m])" by auto
    from len[unfolded length_Suc_conv] obtain x y ys
    where xs: "xs = x#y#ys" and n': "length ys = n'" by auto
    with * have xy: "x < y" and yys: "y#ys \<in> set (subseqs [0..<m])" by auto
    from Cons_mem_set_subseqs_sorted[OF _ yys]
    have "y#ys \<in> set (subseqs (filter ((\<le>) y) [0..<m]))" by auto
    also from Cons_mem_set_subseqsD[OF yys] have ym: "y < m" by auto
      then have "filter ((\<le>) y) [0..<m] = [y..<m]" by (auto intro: filter_upt)
    finally have "y#ys \<in> set (subseqs [y..<m])" by auto
    with xy have "x#y#ys \<in> set (subseqs (x#[y..<m]))" by auto
    also from xy have "... \<subseteq> set (subseqs ([0..<y] @ [y..<m]))"
      by (intro subseqs_of_subseq Cons_mem_set_subseqs_append, auto intro: subseqs_refl)
    also from xy ym have "[0..<y] @ [y..<m] = [0..<m]" by (auto intro: upt_append)
    finally have "xs \<in> set (subseqs [0..<m])" by (unfold xs)
    with len[folded n] show ?l by auto
  qed
qed

lemma subseqs_of_length_of_indices:
  "{ ys. subseq_of_length n xs ys } = { map (nth xs) is | is. subseq_of_length n [0..<length xs] is }"
  by(unfold subseq_of_length_def, subst subseqs_of_indices[symmetric], auto)

lemma subseqs_of_length_Suc_Cons:
  "{ ys. subseq_of_length (Suc n) (x#xs) ys } =
   Cons x ` { ys. subseq_of_length n xs ys } \<union> { ys. subseq_of_length (Suc n) xs ys }"
  by (unfold subseq_of_length_def, auto)


datatype ('a,'b,'state)subseqs_impl = Sublists_Impl
  (create_subseqs: "'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('b \<times> 'a list)list \<times> 'state")
  (next_subseqs: "'state \<Rightarrow> ('b \<times> 'a list)list \<times> 'state")

locale subseqs_impl = 
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  and sl_impl :: "('a,'b,'state)subseqs_impl"
begin

definition S :: "'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('b \<times> 'a list)set" where
  "S base elements n = { (foldr f ys base, ys) | ys. subseq_of_length n elements ys }"

end

locale correct_subseqs_impl = subseqs_impl f sl_impl
  for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" 
  and sl_impl :: "('a,'b,'state)subseqs_impl" +
  fixes invariant :: "'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'state \<Rightarrow> bool" 
  assumes create_subseqs: "create_subseqs sl_impl base elements n = (out, state) \<Longrightarrow> invariant base elements n state \<and> set out = S base elements n" 
  and next_subseqs:
    "invariant base elements n state \<Longrightarrow> 
     next_subseqs sl_impl state = (out, state') \<Longrightarrow> 
     invariant base elements (Suc n) state' \<and> set out = S base elements (Suc n)"  


(* **** old implementation *********** *)
paragraph \<open>Basic Implementation\<close>
fun subseqs_i_n_main :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('b \<times> 'a list) list" where
  "subseqs_i_n_main f b xs i n = (if i = 0 then [(b,[])] else if i = n then [(foldr f xs b, xs)]
    else case xs of 
      (y # ys) \<Rightarrow> map (\<lambda> (c,zs) \<Rightarrow> (c,y # zs)) (subseqs_i_n_main f (f y b) ys (i - 1) (n - 1)) 
        @ subseqs_i_n_main f b ys i (n - 1))"
declare subseqs_i_n_main.simps[simp del]

definition subseqs_length :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('b \<times> 'a list) list" where
  "subseqs_length f b i xs = (
    let n = length xs in if i > n then [] else subseqs_i_n_main f b xs i n)"

lemma subseqs_length: assumes f_ac: "\<And> x y z. f x (f y z) = f y (f x z)" 
  shows "set (subseqs_length f a n xs) = 
  { (foldr f ys a, ys) | ys. ys \<in> set (subseqs xs) \<and> length ys = n}" 
proof -
  show ?thesis 
  proof (cases "length xs < n")
    case True
    thus ?thesis unfolding subseqs_length_def Let_def
      using length_subseqs[of xs] subseqs_length_simple_False by auto 
  next
    case False
    hence id: "(length xs < n) = False" and "n \<le> length xs" by auto
    from this(2) show ?thesis unfolding subseqs_length_def Let_def id if_False
    proof (induct xs arbitrary: n a rule: length_induct[rule_format])
      case (1 xs n a)
      note n = 1(2)
      note IH = 1(1)
      note simp[simp] = subseqs_i_n_main.simps[of f _ xs n]
      show ?case
      proof (cases "n = 0")
        case True
        thus ?thesis unfolding simp by simp
      next
        case False note 0 = this
        show ?thesis
        proof (cases "n = length xs")
          case True
          have "?thesis = ({(foldr f xs a, xs)} = (\<lambda> ys. (foldr f ys a, ys)) ` {ys. ys \<in> set (subseqs xs) \<and> length ys = length xs})" 
            unfolding simp using 0 True by auto
          from this[unfolded full_list_subseqs] show ?thesis by auto
        next
          case False
          with n have n: "n < length xs" by auto
          from 0 obtain m where m: "n = Suc m" by (cases n, auto)
          from n 0 obtain y ys where xs: "xs = y # ys" by (cases xs, auto)
          from n m xs have le: "m \<le> length ys" "n \<le> length ys" by auto
          from xs have lt: "length ys < length xs" by auto
          have sub: "set (subseqs_i_n_main f a xs n (length xs)) = 
            (\<lambda>(c, zs). (c, y # zs)) ` set (subseqs_i_n_main f (f y a) ys m (length ys)) \<union>
            set (subseqs_i_n_main f a ys n (length ys))" 
            unfolding simp using 0 False by (simp add: xs m)
          have fold: "\<And> ys. foldr f ys (f y a) = f y (foldr f ys a)" 
            by (induct_tac ys, auto simp: f_ac)
          show ?thesis unfolding sub IH[OF lt le(1)] IH[OF lt le(2)]
            unfolding m xs by (auto simp: Let_def fold)
        qed
      qed
    qed
  qed
qed

definition basic_subseqs_impl :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b, 'b \<times> 'a list \<times> nat)subseqs_impl" where
  "basic_subseqs_impl f = Sublists_Impl 
    (\<lambda> a xs n. (subseqs_length f a n xs, (a,xs,n)))
    (\<lambda> (a,xs,n). (subseqs_length f a (Suc n) xs, (a,xs,Suc n)))"
  
lemma basic_subseqs_impl: assumes f_ac: "\<And> x y z. f x (f y z) = f y (f x z)"
  shows "correct_subseqs_impl f (basic_subseqs_impl f) 
    (\<lambda> a xs n triple. (a,xs,n) = triple)"
  by (unfold_locales; unfold subseqs_impl.S_def basic_subseqs_impl_def subseq_of_length_def,
      insert subseqs_length[of f, OF f_ac], auto)

(******** new implementation ********)
paragraph \<open>Improved Implementation\<close>

datatype ('a,'b,'state) subseqs_foldr_impl = Sublists_Foldr_Impl
  (subseqs_foldr: "'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'b list \<times> 'state")
  (next_subseqs_foldr: "'state \<Rightarrow> 'b list \<times> 'state")

locale subseqs_foldr_impl =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  and impl :: "('a,'b,'state) subseqs_foldr_impl"
begin
definition S where "S base elements n \<equiv> { foldr f ys base | ys. subseq_of_length n elements ys }"
end

locale correct_subseqs_foldr_impl = subseqs_foldr_impl f impl
  for f and impl :: "('a,'b,'state) subseqs_foldr_impl" +
  fixes invariant :: "'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'state \<Rightarrow> bool"
  assumes subseqs_foldr:
    "subseqs_foldr impl base elements n = (out, state) \<Longrightarrow>
     invariant base elements n state \<and> set out = S base elements n" 
  and next_subseqs_foldr:
    "next_subseqs_foldr impl state = (out, state') \<Longrightarrow> invariant base elements n state \<Longrightarrow>
     invariant base elements (Suc n) state' \<and> set out = S base elements (Suc n)"

locale my_subseqs =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
begin

context fixes head :: "'a" and tail :: "'a iarray"
begin

fun next_subseqs1 and next_subseqs2
where "next_subseqs1 ret0 ret1 [] = (ret0, (head, tail, ret1))"
  |   "next_subseqs1 ret0 ret1 ((i,v)#prevs) = next_subseqs2 (f head v # ret0) ret1 prevs v [0..<i]"
  |   "next_subseqs2 ret0 ret1 prevs v [] = next_subseqs1 ret0 ret1 prevs"
  |   "next_subseqs2 ret0 ret1 prevs v (j#js) =
       (let v' = f (tail !! j) v in next_subseqs2 (v' # ret0) ((j,v') # ret1) prevs v js)"

definition "next_subseqs2_set v js \<equiv> { (j, f (tail !! j) v) | j. j \<in> set js }"

definition "out_subseqs2_set v js \<equiv> { f (tail !! j) v | j. j \<in> set js }"

definition "next_subseqs1_set prevs \<equiv> \<Union> { next_subseqs2_set v [0..<i] | v i. (i,v) \<in> set prevs }"

definition "out_subseqs1_set prevs \<equiv>
  (f head \<circ> snd) ` set prevs \<union> (\<Union> { out_subseqs2_set v [0..<i] | v i. (i,v) \<in> set prevs })"

fun next_subseqs1_spec where
  "next_subseqs1_spec out nexts prevs (out', (head',tail',nexts')) \<longleftrightarrow>
   set nexts' = set nexts \<union> next_subseqs1_set prevs \<and>
   set out' = set out \<union> out_subseqs1_set prevs"

fun next_subseqs2_spec where
  "next_subseqs2_spec out nexts prevs v js (out', (head',tail',nexts')) \<longleftrightarrow>
   set nexts' = set nexts \<union> next_subseqs1_set prevs \<union> next_subseqs2_set v js \<and>
   set out' = set out \<union> out_subseqs1_set prevs \<union> out_subseqs2_set v js"

lemma next_subseqs2_Cons:
  "next_subseqs2_set v (j#js) = insert (j, f (tail!!j) v) (next_subseqs2_set v js)"
  by (auto simp: next_subseqs2_set_def)

lemma out_subseqs2_Cons:
  "out_subseqs2_set v (j#js) = insert (f (tail!!j) v) (out_subseqs2_set v js)"
  by (auto simp: out_subseqs2_set_def)

lemma next_subseqs1_set_as_next_subseqs2_set:
  "next_subseqs1_set ((i,v) # prevs) = next_subseqs1_set prevs \<union> next_subseqs2_set v [0..<i]"
  by (auto simp: next_subseqs1_set_def)

lemma out_subseqs1_set_as_out_subseqs2_set:
  "out_subseqs1_set ((i,v) # prevs) =
   { f head v } \<union> out_subseqs1_set prevs \<union> out_subseqs2_set v [0..<i]"
  by (auto simp: out_subseqs1_set_def)

lemma next_subseqs1_spec:
  shows "\<And>out nexts. next_subseqs1_spec out nexts prevs (next_subseqs1 out nexts prevs)"
    and "\<And>out nexts. next_subseqs2_spec out nexts prevs v js (next_subseqs2 out nexts prevs v js)"
proof(induct rule: next_subseqs1_next_subseqs2.induct)
  case (1 ret0 ret1)
  then show ?case by (simp add: next_subseqs1_set_def out_subseqs1_set_def)
next
  case (2 ret0 ret1 i v prevs)
  show ?case
  proof(cases "next_subseqs1 out nexts ((i, v) # prevs)")
    case split: (fields out' head' tail' nexts')
    have "next_subseqs2_spec (f head v # out) nexts prevs v [0..<i] (out', (head',tail',nexts'))"
      by (fold split, unfold next_subseqs1.simps, rule 2)
    then show ?thesis
      apply (unfold next_subseqs2_spec.simps split)
      by (auto simp: next_subseqs1_set_as_next_subseqs2_set out_subseqs1_set_as_out_subseqs2_set)
  qed
next
  case (3 ret0 ret1 prevs v)
  show ?case
  proof (cases "next_subseqs1 out nexts prevs")
    case split: (fields out' head' tail' nexts')
    from 3[of out nexts] show ?thesis by(simp add: split next_subseqs2_set_def out_subseqs2_set_def)
  qed
next
  case (4 ret0 ret1 prevs v j js)
  define tj where "tj = tail !! j"
  define nexts'' where "nexts'' = (j, f tj v) # nexts"
  define out'' where "out'' = (f tj v) # out"
  let ?n = "next_subseqs2 out'' nexts'' prevs v js"
  show ?case
  proof (cases ?n)
    case split: (fields out' head' tail' nexts')
    show ?thesis
      apply (unfold next_subseqs2.simps Let_def)
      apply (fold tj_def)
      apply (fold out''_def nexts''_def)
      apply (unfold split next_subseqs2_spec.simps next_subseqs2_Cons out_subseqs2_Cons)
      using 4[OF refl, of out'' nexts'', unfolded split]
      apply (auto simp: tj_def nexts''_def out''_def)
      done
  qed
qed

end

fun next_subseqs where "next_subseqs (head,tail,prevs) = next_subseqs1 head tail [] [] prevs"

fun create_subseqs
where "create_subseqs base elements 0 = (
       if elements = [] then ([base],(undefined, IArray [], []))
       else let head = hd elements; tail = IArray (tl elements) in
         ([base], (head, tail, [(IArray.length tail, base)])))"
  |   "create_subseqs base elements (Suc n) =
       next_subseqs (snd (create_subseqs base elements n))"

definition impl where "impl = Sublists_Foldr_Impl create_subseqs next_subseqs"

sublocale subseqs_foldr_impl f impl .

definition set_prevs where "set_prevs base tail n \<equiv>
  { (i, foldr f (map ((!) tail) is) base) | i is.
   subseq_of_length n [0..<length tail] is \<and> i = (if n = 0 then length tail else hd is) }"

lemma snd_set_prevs:
  "snd ` (set_prevs base tail n) = (\<lambda>as. foldr f as base) ` { as. subseq_of_length n tail as }"
  by (subst subseqs_of_length_of_indices, auto simp: set_prevs_def image_Collect)


fun invariant where "invariant base elements n (head,tail,prevs) =
  (if elements = [] then prevs = []
   else head = hd elements \<and> tail = IArray (tl elements) \<and> set prevs = set_prevs base (tl elements) n)"


lemma next_subseq_preserve:
  assumes "next_subseqs (head,tail,prevs) = (out, (head',tail',prevs'))"
  shows "head' = head" "tail' = tail"
proof-
  define P :: "'b list \<times> _ \<times> _ \<times> (nat \<times> 'b) list \<Rightarrow> bool"
  where "P \<equiv> \<lambda> (out, (head',tail',prevs')). head' = head \<and> tail' = tail"
  { fix ret0 ret1 v js
    have *: "P (next_subseqs1 head tail ret0 ret1 prevs)"
     and  "P (next_subseqs2 head tail ret0 ret1 prevs v js)"
    by(induct rule: next_subseqs1_next_subseqs2.induct, simp add: P_def, auto simp: Let_def)
  }
  from this(1)[unfolded P_def, of "[]" "[]", folded next_subseqs.simps] assms
  show "head' = head" "tail' = tail" by auto
qed

lemma next_subseqs_spec:
  assumes nxt: "next_subseqs (head,tail,prevs) = (out, (head',tail',prevs'))"
  shows "set prevs' = { (j, f (tail !! j) v) | v i j. (i,v) \<in> set prevs \<and> j < i }" (is "?g1")
    and "set out = (f head \<circ> snd) ` set prevs \<union> snd ` set prevs'" (is "?g2")
proof-
  note next_subseqs1_spec(1)[of head tail Nil Nil prevs]
  note this[unfolded nxt[simplified]]
  note this[unfolded next_subseqs1_spec.simps]
  note this[unfolded next_subseqs1_set_def out_subseqs1_set_def]
  note * = this[unfolded next_subseqs2_set_def out_subseqs2_set_def]
  then show g1: ?g1 by auto
  also have "snd ` ... =  (\<Union> {{(f (tail !! j) v) | j. j < i} | v i. (i, v) \<in> set prevs})"
     by (unfold image_Collect, auto)
  finally have **: "snd ` set prevs' = ...".
  with conjunct2[OF *] show ?g2 by simp
qed

lemma next_subseq_prevs:
  assumes nxt: "next_subseqs (head,tail,prevs) = (out, (head',tail',prevs'))"
      and inv_prevs: "set prevs = set_prevs base (IArray.list_of tail) n"
  shows "set prevs' = set_prevs base (IArray.list_of tail) (Suc n)" (is "?l = ?r")
proof(intro equalityI subsetI)
  fix t
  assume r: "t \<in> ?r"
  from this[unfolded set_prevs_def] obtain iis
  where t: "t = (hd iis, foldr f (map ((!!) tail) iis) base)"
    and sl: "subseq_of_length (Suc n) [0..<IArray.length tail] iis" by auto
  from sl have "length iis > 0" by auto
  then obtain i "is" where iis: "iis = i#is" by (meson list.set_cases nth_mem)
  define v where "v = foldr f (map ((!!) tail) is) base"
  note sl[unfolded subseq_of_length_Suc_upt]
  note nxt = next_subseqs_spec[OF nxt]
  show "t \<in> ?l"
  proof(cases "n = 0")
    case True
    from sl[unfolded subseq_of_length_Suc_upt] t
    show ?thesis by (unfold nxt[unfolded inv_prevs] True set_prevs_def length_Suc_conv, auto)
  next
    case [simp]: False
    from sl[unfolded subseq_of_length_Suc_upt iis,simplified]
    have i: "i < hd is" and "is": "subseq_of_length n [0..<IArray.length tail] is" by auto
    then have *: "(hd is, v) \<in> set_prevs base (IArray.list_of tail) n"
      by (unfold set_prevs_def, auto intro!: exI[of _ "is"] simp: v_def)
    with i have "(i, f (tail !! i) v) \<in> {(j, f (tail !! j) v) | j. j < hd is}" by auto
    with t[unfolded iis] have "t \<in> ..." by (auto simp: v_def)
    with * show ?thesis by (unfold nxt[unfolded inv_prevs], auto)
  qed
next
  fix t
  assume l: "t \<in> ?l"
  from l[unfolded next_subseqs_spec(1)[OF nxt]]
  obtain j v i
  where t: "t = (j, f (tail!!j) v)"
    and j: "j < i"
    and iv: "(i,v) \<in> set prevs" by auto
  from iv[unfolded inv_prevs set_prevs_def, simplified]
  obtain "is"
  where v: "v = foldr f (map ((!!) tail) is) base"
    and "is": "subseq_of_length n [0..<IArray.length tail] is"
    and i: "if n = 0 then i = IArray.length tail else i = hd is" by auto
  from "is" j i have jis: "subseq_of_length (Suc n) [0..<IArray.length tail] (j#is)"
    by (unfold subseq_of_length_Suc_upt, auto)
  then show "t \<in> ?r" by (auto intro!: exI[of _ "j#is"] simp: set_prevs_def t v)
qed

lemma invariant_next_subseqs:
  assumes inv: "invariant base elements n state"
      and nxt: "next_subseqs state = (out, state')"
  shows "invariant base elements (Suc n) state'"
proof(cases "elements = []")
  case True with inv nxt show ?thesis by(cases state, auto)
next
  case False with inv nxt show ?thesis
  proof (cases state)
    case state: (fields head tail prevs)
    note inv = inv[unfolded state]
    show ?thesis
    proof (cases state')
      case state': (fields head' tail' prevs')
      note nxt = nxt[unfolded state state']
      note [simp] = next_subseq_preserve[OF nxt]
      from False inv
      have "set prevs = set_prevs base (IArray.list_of tail) n" by auto
      from False next_subseq_prevs[OF nxt this] inv
      show ?thesis by(auto simp: state')
    qed
  qed
qed

lemma out_next_subseqs:
  assumes inv: "invariant base elements n state"
      and nxt: "next_subseqs state = (out, state')"
  shows "set out = S base elements (Suc n)"
proof (cases state)
  case state: (fields head tail prevs)
  show ?thesis
  proof(cases "elements = []")
    case True
    with inv nxt show ?thesis by (auto simp: state S_def)
  next
    case elements: False
    show ?thesis
    proof(cases state')
      case state': (fields head' tail' prevs')
      from elements inv[unfolded state,simplified]
      have "head = hd elements"
       and "tail = IArray (tl elements)"
       and prevs: "set prevs = set_prevs base (tl elements) n" by auto
      with elements have elements2: "elements = head # IArray.list_of tail"  by auto
      let ?f = "\<lambda>as. (foldr f as base)"
      have "set out = ?f ` {ys. subseq_of_length (Suc n) elements ys}"
      proof-
        from invariant_next_subseqs[OF inv nxt, unfolded state' invariant.simps if_not_P[OF elements]]
        have tail': "tail' = IArray (tl elements)"
         and prevs': "set prevs' = set_prevs base (tl elements) (Suc n)" by auto
        note next_subseqs_spec(2)[OF nxt[unfolded state state'], unfolded this]
        note this[folded image_comp, unfolded snd_set_prevs]
        also note prevs
        also note snd_set_prevs
        also have "f head ` ?f ` { as. subseq_of_length n (tl elements) as } =
          ?f ` Cons head ` { as. subseq_of_length n (tl elements) as }" by (auto simp: image_def)
        also note image_Un[symmetric]
        also have
          "((#) head ` {as. subseq_of_length n (tl elements) as} \<union>
           {as. subseq_of_length (Suc n) (tl elements) as}) =
           {as. subseq_of_length (Suc n) elements as}"
        by (unfold subseqs_of_length_Suc_Cons elements2, auto)
        finally show ?thesis.
      qed
      then show ?thesis by (auto simp: S_def)
    qed
  qed
qed

lemma create_subseqs:
  "create_subseqs base elements n = (out, state) \<Longrightarrow>
   invariant base elements n state \<and> set out = S base elements n"
proof(induct n arbitrary: out state)
  case 0 then show ?case by (cases "elements", cases state, auto simp: S_def Let_def set_prevs_def)
next
  case (Suc n) show ?case
  proof (cases "create_subseqs base elements n")
    case 1: (fields out'' head tail prevs)
    show ?thesis
    proof (cases "next_subseqs (head, tail, prevs)")
      case (fields out' head' tail' prevs')
      note 2 = this[unfolded next_subseq_preserve[OF this]]
      from Suc(2)[unfolded create_subseqs.simps 1 snd_conv 2]
      have 3: "out' = out" "state = (head,tail,prevs')" by auto
      from Suc(1)[OF 1]
      have inv: "invariant base elements n (head, tail, prevs)" by auto
      from out_next_subseqs[OF inv 2] invariant_next_subseqs[OF inv 2]
      show ?thesis by (auto simp: 3)
    qed
  qed
qed

sublocale correct_subseqs_foldr_impl f impl invariant
  by (unfold_locales; auto simp: impl_def invariant_next_subseqs out_next_subseqs create_subseqs)

lemma impl_correct: "correct_subseqs_foldr_impl f impl invariant" ..
end

lemmas [code] =
  my_subseqs.next_subseqs.simps
  my_subseqs.next_subseqs1.simps
  my_subseqs.next_subseqs2.simps
  my_subseqs.create_subseqs.simps
  my_subseqs.impl_def

end
