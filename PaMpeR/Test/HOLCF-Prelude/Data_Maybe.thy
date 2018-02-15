section \<open>Data: Maybe\<close>

theory Data_Maybe
  imports
    Type_Classes
    Data_Function
    Data_List
    Data_Bool
begin

domain 'a Maybe = Nothing | Just (lazy "'a")

abbreviation maybe :: "'b \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a Maybe \<rightarrow> 'b" where
  "maybe \<equiv> Maybe_case"

fixrec isJust :: "'a Maybe \<rightarrow> tr" where
  "isJust\<cdot>(Just\<cdot>a) = TT" |
  "isJust\<cdot>Nothing = FF"

fixrec isNothing :: "'a Maybe \<rightarrow> tr" where
  "isNothing = neg oo isJust"

fixrec fromJust :: "'a Maybe \<rightarrow> 'a" where
  "fromJust\<cdot>(Just\<cdot>a) = a" |
  "fromJust\<cdot>Nothing = \<bottom>"

fixrec fromMaybe :: "'a \<rightarrow> 'a Maybe \<rightarrow> 'a" where
  "fromMaybe\<cdot>d\<cdot>Nothing = d" |
  "fromMaybe\<cdot>d\<cdot>(Just\<cdot>a) = a"

fixrec maybeToList :: "'a Maybe \<rightarrow> ['a]" where
  "maybeToList\<cdot>Nothing = []" |
  "maybeToList\<cdot>(Just\<cdot>a) = [a]"

fixrec listToMaybe :: "['a] \<rightarrow> 'a Maybe" where
  "listToMaybe\<cdot>[] = Nothing" |
  "listToMaybe\<cdot>(a:_) = Just\<cdot>a"

(* FIXME: The Prelude definition uses list comps, which are too advanced for our syntax *)
fixrec catMaybes :: "['a Maybe] \<rightarrow> ['a]" where
  "catMaybes = concatMap\<cdot>maybeToList"

fixrec mapMaybe :: "('a \<rightarrow> 'b Maybe) \<rightarrow> ['a] \<rightarrow> ['b]" where
  "mapMaybe\<cdot>f = catMaybes oo map\<cdot>f"

instantiation Maybe :: (Eq) Eq_strict
begin

definition
  "eq = maybe\<cdot>(maybe\<cdot>TT\<cdot>(\<Lambda> y. FF))\<cdot>(\<Lambda> x. maybe\<cdot>FF\<cdot>(\<Lambda> y. eq\<cdot>x\<cdot>y))"

instance proof
  fix x :: "'a Maybe"
  show "eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding eq_Maybe_def by (cases x) simp_all
  show "eq\<cdot>\<bottom>\<cdot>x = \<bottom>"
    unfolding eq_Maybe_def by simp
qed

end

lemma eq_Maybe_simps [simp]:
  "eq\<cdot>Nothing\<cdot>Nothing = TT"
  "eq\<cdot>Nothing\<cdot>(Just\<cdot>y) = FF"
  "eq\<cdot>(Just\<cdot>x)\<cdot>Nothing = FF"
  "eq\<cdot>(Just\<cdot>x)\<cdot>(Just\<cdot>y) = eq\<cdot>x\<cdot>y"
  unfolding eq_Maybe_def by simp_all

instance Maybe :: (Eq_sym) Eq_sym
proof
  fix x y :: "'a Maybe"
  show "eq\<cdot>x\<cdot>y = eq\<cdot>y\<cdot>x"
    by (cases x, simp, cases y, simp, simp, simp,
        cases y, simp, simp, simp add: eq_sym)
qed

instance Maybe :: (Eq_equiv) Eq_equiv
proof
  fix x y z :: "'a Maybe"
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    by (cases x, simp_all)
  assume "eq\<cdot>x\<cdot>y = TT" and "eq\<cdot>y\<cdot>z = TT" then show "eq\<cdot>x\<cdot>z = TT"
    by (cases x, simp, cases y, simp, cases z, simp, simp, simp, simp,
        cases y, simp, simp, cases z, simp, simp, simp, fast elim: eq_trans)
qed

instance Maybe :: (Eq_eq) Eq_eq
proof
  fix x y :: "'a Maybe"
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    by (cases x, simp_all)
  assume "eq\<cdot>x\<cdot>y = TT" then show "x = y"
    by (cases x, simp, cases y, simp, simp, simp,
        cases y, simp, simp, simp, fast)
qed

instantiation Maybe :: (Ord) Ord_strict
begin

definition
  "compare = maybe\<cdot>(maybe\<cdot>EQ\<cdot>(\<Lambda> y. LT))\<cdot>(\<Lambda> x. maybe\<cdot>GT\<cdot>(\<Lambda> y. compare\<cdot>x\<cdot>y))"

instance proof
  fix x :: "'a Maybe"
  show "compare\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding compare_Maybe_def by (cases x) simp_all
  show "compare\<cdot>\<bottom>\<cdot>x = \<bottom>"
    unfolding compare_Maybe_def by simp
qed

end

lemma compare_Maybe_simps [simp]:
  "compare\<cdot>Nothing\<cdot>Nothing = EQ"
  "compare\<cdot>Nothing\<cdot>(Just\<cdot>y) = LT"
  "compare\<cdot>(Just\<cdot>x)\<cdot>Nothing = GT"
  "compare\<cdot>(Just\<cdot>x)\<cdot>(Just\<cdot>y) = compare\<cdot>x\<cdot>y"
  unfolding compare_Maybe_def by simp_all

instance Maybe :: (Ord_linear) Ord_linear
proof
  fix x y z :: "'a Maybe"
  show "eq\<cdot>x\<cdot>y = is_EQ\<cdot>(compare\<cdot>x\<cdot>y)"
    by (cases x, simp, cases y, simp, simp, simp,
        cases y, simp, simp, simp add: eq_conv_compare)
  show "oppOrdering\<cdot>(compare\<cdot>x\<cdot>y) = compare\<cdot>y\<cdot>x"
    by (cases x, simp, (cases y, simp, simp, simp)+)
  show "compare\<cdot>x\<cdot>x \<sqsubseteq> EQ"
    by (cases x) simp_all
  { assume "compare\<cdot>x\<cdot>y = EQ" then show "x = y"
      by (cases x, simp, cases y, simp, simp, simp,
          cases y, simp, simp, simp) (erule compare_EQ_dest) }
  { assume "compare\<cdot>x\<cdot>y = LT" and "compare\<cdot>y\<cdot>z = LT" then show "compare\<cdot>x\<cdot>z = LT"
      apply (cases x, simp)
       apply (cases y, simp, simp)
       apply (cases z, simp, simp, simp)
      apply (cases y, simp, simp)
      apply (cases z, simp, simp)
      apply (auto elim: compare_LT_trans)
      done }
qed

lemma isJust_strict [simp]: "isJust\<cdot>\<bottom>  = \<bottom>" by (fixrec_simp)
lemma fromMaybe_strict [simp]: "fromMaybe\<cdot>x\<cdot>\<bottom>  = \<bottom>" by (fixrec_simp)
lemma maybeToList_strict [simp]: "maybeToList\<cdot>\<bottom>  = \<bottom>" by (fixrec_simp)

end