(*  Title:      Containers/DList_Set.thy
    Author:     Andreas Lochbihler, KIT *)

theory DList_Set imports 
  Collection_Eq
  Equal
begin

section \<open>Sets implemented by distinct lists\<close>

subsection \<open>Operations on the raw type with parametrised equality\<close>

context equal_base begin

primrec list_member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
where
  "list_member []       y \<longleftrightarrow> False"
| "list_member (x # xs) y \<longleftrightarrow> equal x y \<or> list_member xs y"

primrec list_distinct :: "'a list \<Rightarrow> bool"
where 
  "list_distinct []       \<longleftrightarrow> True"
| "list_distinct (x # xs) \<longleftrightarrow> \<not> list_member xs x \<and> list_distinct xs"

definition list_insert :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_insert x xs = (if list_member xs x then xs else x # xs)"

primrec list_remove1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_remove1 x [] = []"
| "list_remove1 x (y # xs) = (if equal x y then xs else y # list_remove1 x xs)"

primrec list_remdups :: "'a list \<Rightarrow> 'a list" where
  "list_remdups [] = []"
| "list_remdups (x # xs) = (if list_member xs x then list_remdups xs else x # list_remdups xs)"

lemma list_member_filterD: "list_member (filter P xs) x \<Longrightarrow> list_member xs x"
by(induct xs)(auto split: if_split_asm)

lemma list_distinct_filter [simp]: "list_distinct xs \<Longrightarrow> list_distinct (filter P xs)"
by(induct xs)(auto dest: list_member_filterD)

lemma list_distinct_tl [simp]: "list_distinct xs \<Longrightarrow> list_distinct (tl xs)"
by(cases xs) simp_all

end

lemmas [code] =
  equal_base.list_member.simps
  equal_base.list_distinct.simps
  equal_base.list_insert_def
  equal_base.list_remove1.simps
  equal_base.list_remdups.simps

lemmas [simp] =
  equal_base.list_member.simps
  equal_base.list_distinct.simps
  equal_base.list_remove1.simps
  equal_base.list_remdups.simps

lemma list_member_conv_member [simp]: 
  "equal_base.list_member (=) = List.member"
proof(intro ext)
  fix xs and x :: 'a
  show "equal_base.list_member (=) xs x = List.member xs x"
    by(induct xs)(auto simp add: List.member_def)
qed

lemma list_distinct_conv_distinct [simp]:
  "equal_base.list_distinct (=) = List.distinct"
proof
  fix xs :: "'a list"
  show "equal_base.list_distinct (=) xs = distinct xs"
    by(induct xs)(auto simp add: List.member_def)
qed

lemma list_insert_conv_insert [simp]:
  "equal_base.list_insert (=) = List.insert"
unfolding equal_base.list_insert_def[abs_def] List.insert_def[abs_def]
by(simp add: List.member_def)

lemma list_remove1_conv_remove1 [simp]:
  "equal_base.list_remove1 (=) = List.remove1"
unfolding equal_base.list_remove1_def List.remove1_def ..

lemma list_remdups_conv_remdups [simp]:
  "equal_base.list_remdups (=) = List.remdups"
unfolding equal_base.list_remdups_def List.remdups_def list_member_conv_member List.member_def ..

context equal begin

lemma member_insert [simp]: "list_member (list_insert x xs) y \<longleftrightarrow> equal x y \<or> list_member xs y"
by(auto simp add: equal_eq List.member_def)

lemma member_remove1 [simp]:
  "\<not> equal x y \<Longrightarrow> list_member (list_remove1 x xs) y = list_member xs y"
by(simp add: equal_eq List.member_def)

lemma distinct_remove1:
  "list_distinct xs \<Longrightarrow> list_distinct (list_remove1 x xs)"
by(simp add: equal_eq)

lemma distinct_member_remove1 [simp]:
  "list_distinct xs \<Longrightarrow> list_member (list_remove1 x xs) = (list_member xs)(x := False)"
by(auto simp add: equal_eq List.member_def[abs_def] fun_eq_iff)

end


lemma ID_ceq: (* FIXME: Adapt Set_Impl to directly use above equal class! *)
  "ID CEQ('a :: ceq) = Some eq \<Longrightarrow> equal eq"
by(unfold_locales)(clarsimp simp add: ID_ceq)

subsection \<open>The type of distinct lists\<close>

typedef (overloaded) 'a :: ceq set_dlist =
  "{xs::'a list. equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None}"
  morphisms list_of_dlist Abs_dlist'
proof
  show "[] \<in> ?set_dlist" by(simp)
qed

definition Abs_dlist :: "'a :: ceq list \<Rightarrow> 'a set_dlist" 
where 
  "Abs_dlist xs = Abs_dlist' 
  (if equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None then xs 
   else equal_base.list_remdups ceq' xs)"

lemma Abs_dlist_inverse:
  fixes y :: "'a :: ceq list"
  assumes "y \<in> {xs. equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None}"
  shows "list_of_dlist (Abs_dlist y) = y"
using assms by(auto simp add: Abs_dlist_def Abs_dlist'_inverse)

lemma list_of_dlist_inverse: "Abs_dlist (list_of_dlist dxs) = dxs"
by(cases dxs)(simp add: Abs_dlist'_inverse Abs_dlist_def)

lemma type_definition_set_dlist':
  "type_definition list_of_dlist Abs_dlist
  {xs :: 'a :: ceq list. equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None}"
by(unfold_locales)(rule set_dlist.list_of_dlist Abs_dlist_inverse list_of_dlist_inverse)+

lemmas Abs_dlist_cases[cases type: set_dlist] = 
  type_definition.Abs_cases[OF type_definition_set_dlist'] 
  and Abs_dlist_induct[induct type: set_dlist] =
  type_definition.Abs_induct[OF type_definition_set_dlist'] and
  Abs_dlist_inject = type_definition.Abs_inject[OF type_definition_set_dlist']

setup_lifting type_definition_set_dlist'

subsection \<open>Operations\<close>

lift_definition empty :: "'a :: ceq set_dlist" is "[]"
by simp

lift_definition insert :: "'a :: ceq \<Rightarrow> 'a set_dlist \<Rightarrow> 'a set_dlist" is 
  "equal_base.list_insert ceq'"
by(simp add: equal_base.list_insert_def)

lift_definition remove :: "'a :: ceq \<Rightarrow> 'a set_dlist \<Rightarrow> 'a set_dlist" is 
  "equal_base.list_remove1 ceq'"
by(auto simp: equal.distinct_remove1 ID_ceq)

lift_definition filter :: "('a :: ceq \<Rightarrow> bool) \<Rightarrow> 'a set_dlist \<Rightarrow> 'a set_dlist" is List.filter
by(auto simp add: equal_base.list_distinct_filter)

text \<open>Derived operations:\<close>

lift_definition null :: "'a :: ceq set_dlist \<Rightarrow> bool" is List.null .

lift_definition member :: "'a :: ceq set_dlist \<Rightarrow> 'a \<Rightarrow> bool" is "equal_base.list_member ceq'" .

lift_definition length :: "'a :: ceq set_dlist \<Rightarrow> nat" is List.length .

lift_definition fold :: "('a :: ceq \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set_dlist \<Rightarrow> 'b \<Rightarrow> 'b" is List.fold .

lift_definition foldr :: "('a :: ceq \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set_dlist \<Rightarrow> 'b \<Rightarrow> 'b" is List.foldr .

lift_definition hd :: "'a :: ceq set_dlist \<Rightarrow> 'a" is "List.hd" .

lift_definition tl :: "'a :: ceq set_dlist \<Rightarrow> 'a set_dlist" is "List.tl"
by(auto simp add: equal_base.list_distinct_tl)

lift_definition dlist_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a :: ceq set_dlist \<Rightarrow> bool" is "list_all" .

lift_definition dlist_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a :: ceq set_dlist \<Rightarrow> bool" is "list_ex" .

definition union :: "'a :: ceq set_dlist \<Rightarrow> 'a set_dlist \<Rightarrow> 'a set_dlist" where
  "union = fold insert"

lift_definition product :: "'a :: ceq set_dlist \<Rightarrow> 'b :: ceq set_dlist \<Rightarrow> ('a \<times> 'b) set_dlist"
  is "\<lambda>xs ys. rev (concat (map (\<lambda>x. map (Pair x) ys) xs))"
proof -
  fix xs :: "'a list" and ys :: "'b list"
  assume *: "equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None"
    "equal_base.list_distinct ceq' ys \<or> ID CEQ('b) = None"
  let ?product = "concat (map (\<lambda>x. map (Pair x) ys) xs)"
  { assume neq: "ID CEQ('a) \<noteq> None" "ID CEQ('b) \<noteq> None"
    hence ceq': "ceq' = ((=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)" "ceq' = ((=) :: 'b \<Rightarrow> 'b \<Rightarrow> bool)"
      by(auto intro: equal.equal_eq[OF ID_ceq])
    with * neq have dist: "distinct xs" "distinct ys" by simp_all
    hence "distinct ?product"
      by(cases "ys = []")(auto simp add: distinct_map map_replicate_const intro!: inj_onI distinct_concat)
    hence "distinct (rev ?product)" by simp
    moreover have "ceq' = ((=) :: ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool)"
      using neq ceq' by (auto simp add: ceq_prod_def ID_Some fun_eq_iff list_all_eq_def)
    ultimately have "equal_base.list_distinct ceq' (rev ?product)" by simp }
  with * 
  show "equal_base.list_distinct ceq' (rev ?product) \<or> ID CEQ('a \<times> 'b) = None"
    by(fastforce simp add: ceq_prod_def ID_def split: option.split_asm)
qed

lift_definition Id_on :: "'a :: ceq set_dlist \<Rightarrow> ('a \<times> 'a) set_dlist"
 is "map (\<lambda>x. (x, x))"
proof -
  fix xs :: "'a list"
  assume ceq: "equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None"
  { 
    assume ceq: "ID CEQ('a \<times> 'a) \<noteq> None"
      and xs: "equal_base.list_distinct ceq' xs"
    from ceq have "ID CEQ('a) \<noteq> None"
      and "ceq' = ((=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)" 
      and "ceq' = ((=) :: ('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool)"
      by(auto simp add: equal.equal_eq[OF ID_ceq] ceq_prod_def ID_None ID_Some split: option.split_asm)
    hence "?thesis xs" using xs by(auto simp add: distinct_map intro: inj_onI) }
  thus "?thesis xs" using ceq by(auto dest: equal.equal_eq[OF ID_ceq] simp add: ceq_prod_def ID_None)
qed

subsection \<open>Properties\<close>

lemma member_empty [simp]: "member empty = (\<lambda>_. False)"
by transfer (simp add: fun_eq_iff)

lemma null_iff [simp]: "null xs \<longleftrightarrow> xs = empty"
by transfer(simp add: List.null_def)

lemma list_of_dlist_empty [simp]: "list_of_dlist DList_Set.empty = []"
by(rule empty.rep_eq)

lemma list_of_dlist_insert [simp]: "\<not> member dxs x \<Longrightarrow> list_of_dlist (insert x dxs) = x # list_of_dlist dxs"
by(cases dxs)(auto simp add: DList_Set.insert_def DList_Set.member_def Abs_dlist_inverse Abs_dlist_inject equal_base.list_insert_def List.member_def intro: Abs_dlist_inverse)

lemma list_of_dlist_eq_Nil_iff [simp]: "list_of_dlist dxs = [] \<longleftrightarrow> dxs = empty"
by(cases dxs)(auto simp add: Abs_dlist_inverse Abs_dlist_inject DList_Set.empty_def)

lemma fold_empty [simp]: "DList_Set.fold f empty b = b"
by(transfer) simp

lemma fold_insert [simp]: "\<not> member dxs x \<Longrightarrow> DList_Set.fold f (insert x dxs) b = DList_Set.fold f dxs (f x b)"
by(transfer)(simp add: equal_base.list_insert_def)

lemma no_memb_fold_insert:
  "\<not> member dxs x \<Longrightarrow> fold f (insert x dxs) b = fold f dxs (f x b)"
by(transfer)(simp add: equal_base.list_insert_def)

lemma set_fold_insert: "set (List.fold List.insert xs1 xs2) = set xs1 \<union> set xs2"
by(induct xs1 arbitrary: xs2) simp_all

lemma list_of_dlist_eq_singleton_conv:
  "list_of_dlist dxs = [x] \<longleftrightarrow> dxs = DList_Set.insert x DList_Set.empty"
by transfer(case_tac dxs, auto simp add: equal_base.list_insert_def)

lemma product_code [code abstract]:
  "list_of_dlist (product dxs1 dxs2) = fold (\<lambda>a. fold (\<lambda>c rest. (a, c) # rest) dxs2) dxs1 []"
proof -
  { fix xs ys and zs :: "('a \<times> 'b) list"
    have "rev (concat (map (\<lambda>x. map (Pair x) ys) xs)) @ zs = 
          List.fold (\<lambda>a. List.fold (\<lambda>c rest. (a, c) # rest) ys) xs zs"
    proof(induction xs arbitrary: zs)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      have "List.fold (\<lambda>c rest. (x, c) # rest) ys zs = rev (map (Pair x) ys) @ zs"
        by(induct ys arbitrary: zs) simp_all
      with Cons.IH[of "rev (map (Pair x) ys) @ zs"]
      show ?case by simp
    qed }
  from this[of "list_of_dlist dxs2" "list_of_dlist dxs1" "[]"]
  show ?thesis by(simp add: product.rep_eq fold.rep_eq)
qed

lemma set_list_of_dlist_Abs_dlist:
  "set (list_of_dlist (Abs_dlist xs)) = set xs"
by(clarsimp simp add: Abs_dlist_def Abs_dlist'_inverse)(subst Abs_dlist'_inverse, auto dest: equal.equal_eq[OF ID_ceq])

context assumes ID_ceq_neq_None: "ID CEQ('a :: ceq) \<noteq> None"
begin

lemma equal_ceq: "equal (ceq' :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
using ID_ceq_neq_None by(clarsimp)(rule ID_ceq)

(* workaround for the next theorem *)
declare Domainp_forall_transfer[where A = "pcr_set_dlist (=)", simplified set_dlist.domain_eq, transfer_rule]

lemma set_dlist_induct [case_names Nil insert, induct type: set_dlist]:
  fixes dxs :: "'a :: ceq set_dlist"
  assumes Nil: "P empty" and Cons: "\<And>a dxs. \<lbrakk> \<not> member dxs a; P dxs \<rbrakk> \<Longrightarrow> P (insert a dxs)"
  shows "P dxs"
using assms
proof transfer
  fix P :: "'a list \<Rightarrow> bool" and xs :: "'a list"
  assume NIL: "P []"
    and Insert: "\<And>xs. equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None
                 \<Longrightarrow> (\<And>x. \<lbrakk> \<not> equal_base.list_member ceq' xs x; P xs \<rbrakk> \<Longrightarrow> P (equal_base.list_insert ceq' x xs))"
    and Eq: "equal_base.list_distinct ceq' xs \<or> ID CEQ('a) = None"
  from Eq show "P xs"
  proof(induction xs)
    case Nil show ?case by(rule NIL)
  next
    case (Cons x xs) thus ?case using Insert[of xs x] equal.equal_eq[OF equal_ceq] ID_ceq_neq_None
      by(auto simp add: List.member_def simp del: not_None_eq)
  qed
qed

context includes lifting_syntax
begin

lemma fold_transfer2 [transfer_rule]:
  assumes "is_equality A"
  shows "((A ===> pcr_set_dlist (=) ===> pcr_set_dlist (=)) ===>
    (pcr_set_dlist (=) :: 'a list \<Rightarrow> 'a set_dlist \<Rightarrow> bool) ===> pcr_set_dlist (=) ===> pcr_set_dlist (=))
     List.fold DList_Set.fold"
unfolding Transfer.Rel_def set_dlist.pcr_cr_eq
proof(rule rel_funI)+
  fix f :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b list" and g and xs :: "'a list" and ys and b :: "'b list" and c
  assume fg: "(A ===> cr_set_dlist ===> cr_set_dlist) f g"
  assume "cr_set_dlist xs ys" "cr_set_dlist b c"
  thus "cr_set_dlist (List.fold f xs b) (DList_Set.fold g ys c)"
  proof(induct ys arbitrary: xs b c rule: set_dlist_induct)
    case Nil thus ?case by(simp add: cr_set_dlist_def)
  next
    case (insert y dxs)
    have "A y y" and "cr_set_dlist (list_of_dlist c) c"
      using assms by(simp_all add: cr_set_dlist_def is_equality_def)
    with fg have "cr_set_dlist (f y (list_of_dlist c)) (g y c)"
      by -(drule (1) rel_funD)+
    thus ?case using insert by(simp add: cr_set_dlist_def)
  qed
qed

end

lemma distinct_list_of_dlist:
  "distinct (list_of_dlist (dxs :: 'a set_dlist))"
using list_of_dlist[of dxs] equal.equal_eq[OF equal_ceq]
by(simp add: ID_ceq_neq_None)

lemma member_empty_empty: "(\<forall>x :: 'a. \<not> member dxs x) \<longleftrightarrow> dxs = empty"
by(transfer)(simp add: equal.equal_eq[OF equal_ceq] List.member_def)

lemma Collect_member: "Collect (member (dxs :: 'a set_dlist)) = set (list_of_dlist dxs)"
by(simp add: member_def equal.equal_eq[OF equal_ceq] List.member_def[abs_def])

lemma member_insert: "member (insert (x :: 'a) xs) = (member xs)(x := True)"
by(transfer)(simp add: fun_eq_iff List.member_def ID_ceq_neq_None equal.equal_eq[OF equal_ceq])

lemma member_remove:
  "member (remove (x :: 'a) xs) = (member xs)(x := False)"
by transfer (auto simp add: fun_eq_iff ID_ceq_neq_None equal.equal_eq[OF equal_ceq] List.member_def)

lemma member_union: "member (union (xs1 :: 'a set_dlist) xs2) x \<longleftrightarrow> member xs1 x \<or> member xs2 x"
unfolding union_def
by(transfer)(simp add: equal.equal_eq[OF equal_ceq] List.member_def set_fold_insert)

lemma member_fold_insert: "member (List.fold insert xs dxs) (x :: 'a) \<longleftrightarrow> member dxs x \<or> x \<in> set xs"
by transfer(auto simp add: ID_ceq_neq_None equal.equal_eq[OF equal_ceq] List.member_def set_fold_insert)

lemma card_eq_length [simp]:
  "card (Collect (member (dxs :: 'a set_dlist))) = length dxs"
by transfer(simp add: ID_ceq_neq_None equal.equal_eq[OF equal_ceq] List.member_def[abs_def] distinct_card)

lemma finite_member [simp]: 
  "finite (Collect (member (dxs :: 'a set_dlist)))"
by transfer(simp add: ID_ceq_neq_None equal.equal_eq[OF equal_ceq] List.member_def[abs_def])

lemma member_filter [simp]: "member (filter P xs) = (\<lambda>x :: 'a. member xs x \<and> P x)"
by transfer(simp add: ID_ceq_neq_None equal.equal_eq[OF equal_ceq] List.member_def[abs_def])

lemma dlist_all_conv_member: "dlist_all P dxs \<longleftrightarrow> (\<forall>x :: 'a. member dxs x \<longrightarrow> P x)"
by transfer(auto simp add: ID_ceq_neq_None equal.equal_eq[OF equal_ceq] list_all_iff List.member_def)

lemma dlist_ex_conv_member: "dlist_ex P dxs \<longleftrightarrow> (\<exists>x :: 'a. member dxs x \<and> P x)"
by transfer(auto simp add: ID_ceq_neq_None equal.equal_eq[OF equal_ceq] list_ex_iff List.member_def)

lemma member_Id_on: "member (Id_on dxs) = (\<lambda>(x :: 'a, y). x = y \<and> member dxs x)"
proof -
  have "ID CEQ('a \<times> 'a) = Some (=)"
    using equal.equal_eq[where ?'a='a, OF equal_ceq]
    by(auto simp add: ceq_prod_def list_all_eq_def ID_ceq_neq_None ID_Some fun_eq_iff split: option.split)
  thus ?thesis
    using equal.equal_eq[where ?'a='a, OF equal_ceq]
    by transfer(auto simp add: ID_ceq_neq_None List.member_def[abs_def] ID_Some intro!: ext split: option.split_asm)
qed

end

lemma product_member: 
  assumes "ID CEQ('a :: ceq) \<noteq> None" "ID CEQ('b :: ceq) \<noteq> None"
  shows "member (product dxs1 dxs2) = (\<lambda>(a :: 'a, b :: 'b). member dxs1 a \<and> member dxs2 b)"
proof -
  from assms have "ceq' = ((=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)" "ceq' = ((=) :: 'b \<Rightarrow> 'b \<Rightarrow> bool)"
    by(auto intro: equal.equal_eq[OF ID_ceq])
  moreover with assms have "ceq' = ((=) :: ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool)"
    by(auto simp add: ceq_prod_def list_all_eq_def ID_Some fun_eq_iff)
  ultimately show ?thesis by(transfer)(auto simp add: List.member_def[abs_def])
qed

hide_const (open) empty insert remove null member length fold foldr union filter hd tl dlist_all product Id_on

end
