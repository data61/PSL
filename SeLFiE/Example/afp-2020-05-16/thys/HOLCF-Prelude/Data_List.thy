section \<open>Data: List\<close>

theory Data_List
  imports
    Type_Classes
    Data_Function
    Data_Bool
    Data_Tuple
    Data_Integer
    Numeral_Cpo
begin

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

subsection \<open>Datatype definition\<close>

domain 'a list ("[_]") =
  Nil ("[]") |
  Cons (lazy head :: 'a) (lazy tail :: "['a]") (infixr ":" 65)
(*FIXME: We need to standardize a mapping from Haskell fixities
(0 to 9) to Isabelle ones (between 50 and 100).*)


subsubsection \<open>Section syntax for @{const Cons}\<close>

syntax
  "_Cons_section" :: "'a \<rightarrow> ['a] \<rightarrow> ['a]" ("'(:')")
  "_Cons_section_left" :: "'a \<Rightarrow> ['a] \<rightarrow> ['a]" ("'(_:')")
translations
  "(x:)" == "(CONST Rep_cfun) (CONST Cons) x"

abbreviation Cons_section_right :: "['a] \<Rightarrow> 'a \<rightarrow> ['a]" ("'(:_')") where
  "(:xs) \<equiv> \<Lambda> x. x:xs"

syntax
  "_lazy_list" :: "args \<Rightarrow> ['a]" ("[(_)]")
translations
  "[x, xs]" == "x : [xs]"
  "[x]" == "x : []"

abbreviation null :: "['a] \<rightarrow> tr" where "null \<equiv> is_Nil"


subsection \<open>Haskell function definitions\<close>

instantiation list :: (Eq) Eq_strict
begin

fixrec eq_list :: "['a] \<rightarrow> ['a] \<rightarrow> tr" where
  "eq_list\<cdot>[]\<cdot>[] = TT" |
  "eq_list\<cdot>(x : xs)\<cdot>[] = FF" |
  "eq_list\<cdot>[]\<cdot>(y : ys) = FF" |
  "eq_list\<cdot>(x : xs)\<cdot>(y : ys) = (eq\<cdot>x\<cdot>y andalso eq_list\<cdot>xs\<cdot>ys)"

instance proof
  fix xs :: "['a]"
  show "eq\<cdot>xs\<cdot>\<bottom> = \<bottom>"
    by (cases xs, fixrec_simp+)
  show "eq\<cdot>\<bottom>\<cdot>xs = \<bottom>"
    by fixrec_simp
qed

end

instance list :: (Eq_sym) Eq_sym
proof
  fix xs ys :: "['a]"
  show "eq\<cdot>xs\<cdot>ys = eq\<cdot>ys\<cdot>xs"
  proof (induct xs arbitrary: ys)
    case Nil
    show ?case by (cases ys; simp)
  next
    case Cons
    then show ?case by (cases ys; simp add: eq_sym)
  qed simp_all
qed

instance list :: (Eq_equiv) Eq_equiv
proof
  fix xs ys zs :: "['a]"
  show "eq\<cdot>xs\<cdot>xs \<noteq> FF"
    by (induct xs, simp_all)
  assume "eq\<cdot>xs\<cdot>ys = TT" and "eq\<cdot>ys\<cdot>zs = TT" then show "eq\<cdot>xs\<cdot>zs = TT"
  proof (induct xs arbitrary: ys zs)
    case (Nil ys zs) then show ?case by (cases ys, simp_all)
  next
    case (Cons x xs ys zs)
    from Cons.prems show ?case
      by (cases ys; cases zs) (auto intro: eq_trans Cons.hyps)
  qed simp_all
qed

instance list :: (Eq_eq) Eq_eq
proof
  fix xs ys :: "['a]"
  show "eq\<cdot>xs\<cdot>xs \<noteq> FF"
    by (induct xs) simp_all
  assume "eq\<cdot>xs\<cdot>ys = TT" then show "xs = ys"
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by (cases ys) auto
  next
    case Cons
    then show ?case by (cases ys) auto
  qed auto
qed

instantiation list :: (Ord) Ord_strict
begin

fixrec compare_list :: "['a] \<rightarrow> ['a] \<rightarrow> Ordering" where
  "compare_list\<cdot>[]\<cdot>[] = EQ" |
  "compare_list\<cdot>(x : xs)\<cdot>[] = GT" |
  "compare_list\<cdot>[]\<cdot>(y : ys) = LT" |
  "compare_list\<cdot>(x : xs)\<cdot>(y : ys) =
    thenOrdering\<cdot>(compare\<cdot>x\<cdot>y)\<cdot>(compare_list\<cdot>xs\<cdot>ys)"

instance
  by standard (fixrec_simp, rename_tac x, case_tac x, fixrec_simp+)

end

instance list :: (Ord_linear) Ord_linear
proof
  fix xs ys zs :: "['a]"
  show "oppOrdering\<cdot>(compare\<cdot>xs\<cdot>ys) = compare\<cdot>ys\<cdot>xs"
  proof (induct xs arbitrary: ys)
    case Nil
    show ?case by (cases ys; simp)
  next
    case Cons
    then show ?case by (cases ys; simp add: oppOrdering_thenOrdering)
  qed simp_all
  show "xs = ys" if "compare\<cdot>xs\<cdot>ys = EQ"
    using that
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by (cases ys; simp)
  next
    case Cons
    then show ?case by (cases ys; auto elim: compare_EQ_dest)
  qed simp_all
  show "compare\<cdot>xs\<cdot>zs = LT" if "compare\<cdot>xs\<cdot>ys = LT" and "compare\<cdot>ys\<cdot>zs = LT"
    using that
  proof (induct xs arbitrary: ys zs)
    case Nil
    then show ?case by (cases ys; cases zs; simp)
  next
    case (Cons a xs)
    then show ?case
      by (cases ys; cases zs) (auto dest: compare_EQ_dest compare_LT_trans)
  qed simp_all
  show "eq\<cdot>xs\<cdot>ys = is_EQ\<cdot>(compare\<cdot>xs\<cdot>ys)"
  proof (induct xs arbitrary: ys)
    case Nil
    show ?case by (cases ys; simp)
  next
    case Cons
    then show ?case by (cases ys; simp add: eq_conv_compare)
  qed simp_all
  show "compare\<cdot>xs\<cdot>xs \<sqsubseteq> EQ"
    by (induct xs) simp_all
qed

fixrec zipWith :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ['a] \<rightarrow> ['b] \<rightarrow> ['c]" where
  "zipWith\<cdot>f\<cdot>(x : xs)\<cdot>(y : ys) = f\<cdot>x\<cdot>y : zipWith\<cdot>f\<cdot>xs\<cdot>ys" |
  "zipWith\<cdot>f\<cdot>(x : xs)\<cdot>[] = []" |
  "zipWith\<cdot>f\<cdot>[]\<cdot>ys = []"

definition zip :: "['a] \<rightarrow> ['b] \<rightarrow> [\<langle>'a, 'b\<rangle>]" where
  "zip = zipWith\<cdot>\<langle>,\<rangle>"

fixrec zipWith3 :: "('a \<rightarrow> 'b \<rightarrow> 'c \<rightarrow> 'd) \<rightarrow> ['a] \<rightarrow> ['b] \<rightarrow> ['c] \<rightarrow> ['d]" where
  "zipWith3\<cdot>f\<cdot>(x : xs)\<cdot>(y : ys)\<cdot>(z : zs) = f\<cdot>x\<cdot>y\<cdot>z : zipWith3\<cdot>f\<cdot>xs\<cdot>ys\<cdot>zs" |
  (unchecked) "zipWith3\<cdot>f\<cdot>xs\<cdot>ys\<cdot>zs = []"

definition zip3 :: "['a] \<rightarrow> ['b] \<rightarrow> ['c] \<rightarrow> [\<langle>'a, 'b, 'c\<rangle>]" where
  "zip3 = zipWith3\<cdot>\<langle>,,\<rangle>"

fixrec map :: "('a \<rightarrow> 'b) \<rightarrow> ['a] \<rightarrow> ['b]" where
  "map\<cdot>f\<cdot>[] = []" |
  "map\<cdot>f\<cdot>(x : xs) = f\<cdot>x : map\<cdot>f\<cdot>xs"

fixrec filter :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> ['a]" where
  "filter\<cdot>P\<cdot>[] = []" |
  "filter\<cdot>P\<cdot>(x : xs) =
    If (P\<cdot>x) then x : filter\<cdot>P\<cdot>xs else filter\<cdot>P\<cdot>xs"

fixrec repeat :: "'a \<rightarrow> ['a]" where
  [simp del]: "repeat\<cdot>x = x : repeat\<cdot>x"

fixrec takeWhile :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> ['a]" where
 "takeWhile\<cdot>p\<cdot>[]     =  []" |
 "takeWhile\<cdot>p\<cdot>(x:xs) = If p\<cdot>x then x : takeWhile\<cdot>p\<cdot>xs else  []"

fixrec dropWhile :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> ['a]" where
 "dropWhile\<cdot>p\<cdot>[]     =  []" |
 "dropWhile\<cdot>p\<cdot>(x:xs) = If p\<cdot>x then dropWhile\<cdot>p\<cdot>xs else (x:xs)"

fixrec span :: "('a -> tr) -> ['a] -> \<langle>['a],['a]\<rangle>" where
 "span\<cdot>p\<cdot>[]     = \<langle>[],[]\<rangle>" |
 "span\<cdot>p\<cdot>(x:xs) = If p\<cdot>x then (case span\<cdot>p\<cdot>xs of \<langle>ys, zs\<rangle> \<Rightarrow> \<langle>x:ys,zs\<rangle>) else \<langle>[], x:xs\<rangle>"

fixrec break :: "('a -> tr) -> ['a] -> \<langle>['a],['a]\<rangle>" where
 "break\<cdot>p = span\<cdot>(neg oo p)"

fixrec nth :: "['a] \<rightarrow> Integer \<rightarrow> 'a" where
  "nth\<cdot>[]\<cdot>n = \<bottom>" |
  nth_Cons [simp del]:
  "nth\<cdot>(x : xs)\<cdot>n = If eq\<cdot>n\<cdot>0 then x else nth\<cdot>xs\<cdot>(n - 1)"
(* bh: Perhaps we should rename this to 'index',
to match the standard Haskell function named 'genericIndex'. *)

abbreviation nth_syn :: "['a] \<Rightarrow> Integer \<Rightarrow> 'a" (infixl "!!" 100) where
  "xs !! n \<equiv> nth\<cdot>xs\<cdot>n"

definition partition :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> \<langle>['a], ['a]\<rangle>" where
  "partition = (\<Lambda> P xs. \<langle>filter\<cdot>P\<cdot>xs, filter\<cdot>(neg oo P)\<cdot>xs\<rangle>)"

fixrec iterate :: "('a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> ['a]" where
  "iterate\<cdot>f\<cdot>x = x : iterate\<cdot>f\<cdot>(f\<cdot>x)"

fixrec foldl ::  "('a -> 'b -> 'a) -> 'a -> ['b] -> 'a" where
  "foldl\<cdot>f\<cdot>z\<cdot>[]     = z" |
  "foldl\<cdot>f\<cdot>z\<cdot>(x:xs) = foldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>x)\<cdot>xs"

fixrec foldl1 ::  "('a -> 'a -> 'a) -> ['a] -> 'a" where
  "foldl1\<cdot>f\<cdot>[]     = \<bottom>" |
  "foldl1\<cdot>f\<cdot>(x:xs) = foldl\<cdot>f\<cdot>x\<cdot>xs"

fixrec foldr :: "('a \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> ['a] \<rightarrow> 'b" where
  "foldr\<cdot>f\<cdot>d\<cdot>[] = d" |
  "foldr\<cdot>f\<cdot>d\<cdot>(x : xs) = f\<cdot>x\<cdot>(foldr\<cdot>f\<cdot>d\<cdot>xs)"

fixrec foldr1 :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<rightarrow> ['a] \<rightarrow> 'a" where
  "foldr1\<cdot>f\<cdot>[] = \<bottom>" |
  "foldr1\<cdot>f\<cdot>[x] = x" |
  "foldr1\<cdot>f\<cdot>(x : (x':xs)) = f\<cdot>x\<cdot>(foldr1\<cdot>f\<cdot>(x':xs))"

fixrec elem :: "'a::Eq \<rightarrow> ['a] \<rightarrow> tr" where
  "elem\<cdot>x\<cdot>[] = FF" |
  "elem\<cdot>x\<cdot>(y : ys) = (eq\<cdot>y\<cdot>x orelse elem\<cdot>x\<cdot>ys)"

fixrec notElem :: "'a::Eq \<rightarrow> ['a] \<rightarrow> tr" where
  "notElem\<cdot>x\<cdot>[] = TT" |
  "notElem\<cdot>x\<cdot>(y : ys) = (neq\<cdot>y\<cdot>x andalso notElem\<cdot>x\<cdot>ys)"

fixrec append :: "['a] \<rightarrow> ['a] \<rightarrow> ['a]" where
  "append\<cdot>[]\<cdot>ys = ys" |
  "append\<cdot>(x : xs)\<cdot>ys = x : append\<cdot>xs\<cdot>ys"

abbreviation append_syn :: "['a] \<Rightarrow> ['a] \<Rightarrow> ['a]" (infixr "++" 65) where
  "xs ++ ys \<equiv> append\<cdot>xs\<cdot>ys"

definition concat :: "[['a]] \<rightarrow> ['a]" where
  "concat = foldr\<cdot>append\<cdot>[]"

definition concatMap :: "('a \<rightarrow> ['b]) \<rightarrow> ['a] \<rightarrow> ['b]" where
  "concatMap = (\<Lambda> f. concat oo map\<cdot>f)"

fixrec last :: "['a] -> 'a" where
  "last\<cdot>[x] = x" |
  "last\<cdot>(_:(x:xs)) = last\<cdot>(x:xs)"

fixrec init :: "['a] -> ['a]" where
  "init\<cdot>[x] = []" |
  "init\<cdot>(x:(y:xs)) = x:(init\<cdot>(y:xs))"

fixrec reverse :: "['a] -> ['a]" where
  [simp del]:"reverse = foldl\<cdot>(flip\<cdot>(:))\<cdot>[]"

fixrec the_and :: "[tr] \<rightarrow> tr" where
  "the_and = foldr\<cdot>trand\<cdot>TT"

fixrec the_or :: "[tr] \<rightarrow> tr" where
  "the_or = foldr\<cdot>tror\<cdot>FF"

fixrec all :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> tr" where
  "all\<cdot>P = the_and oo (map\<cdot>P)"

fixrec any :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> tr" where
  "any\<cdot>P = the_or oo (map\<cdot>P)"

fixrec tails :: "['a] \<rightarrow> [['a]]" where
  "tails\<cdot>[] = [[]]" |
  "tails\<cdot>(x : xs) = (x : xs) : tails\<cdot>xs"

fixrec inits :: "['a] \<rightarrow> [['a]]" where
  "inits\<cdot>[] = [[]]" |
  "inits\<cdot>(x : xs) = [[]] ++ map\<cdot>(x:)\<cdot>(inits\<cdot>xs)"

fixrec scanr :: "('a \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> ['a] \<rightarrow> ['b]"
where
  "scanr\<cdot>f\<cdot>q0\<cdot>[] = [q0]" |
  "scanr\<cdot>f\<cdot>q0\<cdot>(x : xs) = (
    let qs = scanr\<cdot>f\<cdot>q0\<cdot>xs in
    (case qs of
      [] \<Rightarrow> \<bottom>
    | q : qs' \<Rightarrow> f\<cdot>x\<cdot>q : qs))"

fixrec scanr1 :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<rightarrow> ['a] \<rightarrow> ['a]"
where
  "scanr1\<cdot>f\<cdot>[] = []" |
  "scanr1\<cdot>f\<cdot>(x : xs) =
    (case xs of
      [] \<Rightarrow> [x]
    | x' : xs' \<Rightarrow> (
      let qs = scanr1\<cdot>f\<cdot>xs in
      (case qs of
        [] \<Rightarrow> \<bottom>
      | q : qs' \<Rightarrow> f\<cdot>x\<cdot>q : qs)))"

fixrec scanl :: "('a \<rightarrow> 'b \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> ['b] \<rightarrow> ['a]" where
  "scanl\<cdot>f\<cdot>q\<cdot>ls = q : (case ls of
    [] \<Rightarrow> []
  | x : xs \<Rightarrow> scanl\<cdot>f\<cdot>(f\<cdot>q\<cdot>x)\<cdot>xs)"

definition scanl1 :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<rightarrow> ['a] \<rightarrow> ['a]" where
  "scanl1 = (\<Lambda> f ls. (case ls of
    [] \<Rightarrow> []
  | x : xs \<Rightarrow> scanl\<cdot>f\<cdot>x\<cdot>xs))"

subsubsection \<open>Arithmetic Sequences\<close>

fixrec upto :: "Integer \<rightarrow> Integer \<rightarrow> [Integer]" where
  [simp del]: "upto\<cdot>x\<cdot>y = If le\<cdot>x\<cdot>y then x : upto\<cdot>(x+1)\<cdot>y else []"

fixrec intsFrom :: "Integer \<rightarrow> [Integer]" where
  [simp del]: "intsFrom\<cdot>x = seq\<cdot>x\<cdot>(x : intsFrom\<cdot>(x+1))"

class Enum =
  fixes toEnum :: "Integer \<rightarrow> 'a"
    and fromEnum :: "'a \<rightarrow> Integer"
begin

definition succ :: "'a \<rightarrow> 'a" where
  "succ = toEnum oo (+1) oo fromEnum"

definition pred :: "'a \<rightarrow> 'a" where
  "pred = toEnum oo (-1) oo fromEnum"

definition enumFrom :: "'a \<rightarrow> ['a]" where
  "enumFrom = (\<Lambda> x. map\<cdot>toEnum\<cdot>(intsFrom\<cdot>(fromEnum\<cdot>x)))"

definition enumFromTo :: "'a \<rightarrow> 'a \<rightarrow> ['a]" where
  "enumFromTo = (\<Lambda> x y. map\<cdot>toEnum\<cdot>(upto\<cdot>(fromEnum\<cdot>x)\<cdot>(fromEnum\<cdot>y)))"

end

abbreviation enumFrom_To_syn :: "'a::Enum \<Rightarrow> 'a \<Rightarrow> ['a]" ("(1[_../_])") where
  "[m..n] \<equiv> enumFromTo\<cdot>m\<cdot>n"

abbreviation enumFrom_syn :: "'a::Enum \<Rightarrow> ['a]" ("(1[_..])") where
  "[n..] \<equiv> enumFrom\<cdot>n"

instantiation Integer :: Enum
begin
definition [simp]: "toEnum = ID"
definition [simp]: "fromEnum = ID"
instance ..
end

fixrec take :: "Integer \<rightarrow> ['a] \<rightarrow> ['a]" where
  [simp del]: "take\<cdot>n\<cdot>xs = If le\<cdot>n\<cdot>0 then [] else
    (case xs of [] \<Rightarrow> [] | y : ys \<Rightarrow> y : take\<cdot>(n - 1)\<cdot>ys)"

fixrec drop :: "Integer \<rightarrow> ['a] \<rightarrow> ['a]" where
  [simp del]: "drop\<cdot>n\<cdot>xs = If le\<cdot>n\<cdot>0 then xs else
    (case xs of [] \<Rightarrow> [] | y : ys \<Rightarrow> drop\<cdot>(n - 1)\<cdot>ys)"

fixrec isPrefixOf :: "['a::Eq] \<rightarrow> ['a] \<rightarrow> tr" where
  "isPrefixOf\<cdot>[]\<cdot>_ = TT" |
  "isPrefixOf\<cdot>(x:xs)\<cdot>[] = FF" |
  "isPrefixOf\<cdot>(x:xs)\<cdot>(y:ys) = (eq\<cdot>x\<cdot>y andalso isPrefixOf\<cdot>xs\<cdot>ys)"

fixrec isSuffixOf :: "['a::Eq] \<rightarrow> ['a] \<rightarrow> tr" where
  "isSuffixOf\<cdot>x\<cdot>y = isPrefixOf\<cdot>(reverse\<cdot>x)\<cdot>(reverse\<cdot>y)"

fixrec intersperse :: "'a \<rightarrow> ['a] \<rightarrow> ['a]" where
  "intersperse\<cdot>sep\<cdot>[] = []" |
  "intersperse\<cdot>sep\<cdot>[x] = [x]" |
  "intersperse\<cdot>sep\<cdot>(x:y:xs) = x:sep:intersperse\<cdot>sep\<cdot>(y:xs)"

fixrec intercalate :: "['a] \<rightarrow> [['a]] \<rightarrow> ['a]" where
  "intercalate\<cdot>xs\<cdot>xss = concat\<cdot>(intersperse\<cdot>xs\<cdot>xss)"

definition replicate :: "Integer \<rightarrow> 'a \<rightarrow> ['a]" where
  "replicate = (\<Lambda> n x. take\<cdot>n\<cdot>(repeat\<cdot>x))"

definition findIndices :: "('a \<rightarrow> tr) \<rightarrow> ['a] \<rightarrow> [Integer]" where
  "findIndices = (\<Lambda> P xs.
    map\<cdot>snd\<cdot>(filter\<cdot>(\<Lambda> \<langle>x, i\<rangle>. P\<cdot>x)\<cdot>(zip\<cdot>xs\<cdot>[0..])))"

fixrec length :: "['a] \<rightarrow> Integer" where
  "length\<cdot>[] = 0" |
  "length\<cdot>(x : xs) = length\<cdot>xs + 1"

fixrec delete :: "'a::Eq \<rightarrow> ['a] \<rightarrow> ['a]" where
  "delete\<cdot>x\<cdot>[] = []" |
  "delete\<cdot>x\<cdot>(y : ys) = If eq\<cdot>x\<cdot>y then ys else y : delete\<cdot>x\<cdot>ys"

fixrec diff :: "['a::Eq] \<rightarrow> ['a] \<rightarrow> ['a]" where
  "diff\<cdot>xs\<cdot>[] = xs" |
  "diff\<cdot>xs\<cdot>(y : ys) = diff\<cdot>(delete\<cdot>y\<cdot>xs)\<cdot>ys"

abbreviation diff_syn :: "['a::Eq] \<Rightarrow> ['a] \<Rightarrow> ['a]" (infixl "\\\\" 70) where
  "xs \\\\ ys \<equiv> diff\<cdot>xs\<cdot>ys"


subsection \<open>Logical predicates on lists\<close>

inductive finite_list :: "['a] \<Rightarrow> bool" where
  Nil [intro!, simp]: "finite_list []" |
  Cons [intro!, simp]: "\<And>x xs. finite_list xs \<Longrightarrow> finite_list (x : xs)"

inductive_cases finite_listE [elim!]: "finite_list (x : xs)"

lemma finite_list_upwards:
  assumes "finite_list xs" and "xs \<sqsubseteq> ys"
  shows "finite_list ys"
using assms
proof (induct xs arbitrary: ys)
  case Nil
  then have "ys = []" by (cases ys) simp+
  then show ?case by auto
next
  case (Cons x xs)
  from \<open>x : xs \<sqsubseteq> ys\<close> obtain y ys' where "ys = y : ys'" by (cases ys) auto
  with \<open>x : xs \<sqsubseteq> ys\<close> have "xs \<sqsubseteq> ys'" by auto
  then have "finite_list ys'" by (rule Cons.hyps)
  with \<open>ys = _\<close> show ?case by auto
qed

lemma adm_finite_list [simp]: "adm finite_list"
  by (metis finite_list_upwards adm_upward)

lemma bot_not_finite_list [simp]:
  "finite_list \<bottom> = False"
  by (rule, cases rule: finite_list.cases) auto

inductive listmem :: "'a \<Rightarrow> ['a] \<Rightarrow> bool" where
  "listmem x (x : xs)" |
  "listmem x xs \<Longrightarrow> listmem x (y : xs)"

lemma listmem_simps [simp]:
  shows "\<not> listmem x \<bottom>" and "\<not> listmem x []"
  and "listmem x (y : ys) \<longleftrightarrow> x = y \<or> listmem x ys"
  by (auto elim: listmem.cases intro: listmem.intros)

definition set :: "['a] \<Rightarrow> 'a set" where
  "set xs = {x. listmem x xs}"

lemma set_simps [simp]:
  shows "set \<bottom> = {}" and "set [] = {}"
  and "set (x : xs) = insert x (set xs)"
  unfolding set_def by auto

inductive distinct :: "['a] \<Rightarrow> bool" where
  Nil [intro!, simp]: "distinct []" |
  Cons [intro!, simp]: "\<And>x xs. distinct xs \<Longrightarrow> x \<notin> set xs \<Longrightarrow> distinct (x : xs)"


subsection \<open>Properties\<close>

lemma map_strict [simp]:
  "map\<cdot>P\<cdot>\<bottom> = \<bottom>"
  by (fixrec_simp)

lemma map_ID [simp]:
  "map\<cdot>ID\<cdot>xs = xs"
  by (induct xs) simp_all

lemma enumFrom_intsFrom_conv [simp]:
  "enumFrom = intsFrom"
  by (intro cfun_eqI) (simp add: enumFrom_def)

lemma enumFromTo_upto_conv [simp]:
  "enumFromTo = upto"
  by (intro cfun_eqI) (simp add: enumFromTo_def)

lemma zipWith_strict [simp]:
  "zipWith\<cdot>f\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "zipWith\<cdot>f\<cdot>(x : xs)\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp+

lemma zip_simps [simp]:
  "zip\<cdot>(x : xs)\<cdot>(y : ys) = \<langle>x, y\<rangle> : zip\<cdot>xs\<cdot>ys"
  "zip\<cdot>(x : xs)\<cdot>[] = []"
  "zip\<cdot>(x : xs)\<cdot>\<bottom> = \<bottom>"
  "zip\<cdot>[]\<cdot>ys = []"
  "zip\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  unfolding zip_def by simp_all

lemma zip_Nil2 [simp]:
  "xs \<noteq> \<bottom> \<Longrightarrow> zip\<cdot>xs\<cdot>[] = []"
  by (cases xs) simp_all

lemma nth_strict [simp]:
  "nth\<cdot>\<bottom>\<cdot>n = \<bottom>"
  "nth\<cdot>xs\<cdot>\<bottom> = \<bottom>"
  by (fixrec_simp) (cases xs, fixrec_simp+)

lemma upto_strict [simp]:
  "upto\<cdot>\<bottom>\<cdot>y = \<bottom>"
  "upto\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp+

lemma upto_simps [simp]:
  "n < m \<Longrightarrow> upto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n) = []"
  "m \<le> n \<Longrightarrow> upto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n) = MkI\<cdot>m : [MkI\<cdot>m+1..MkI\<cdot>n]"
  by (subst upto.simps, simp)+

lemma filter_strict [simp]:
  "filter\<cdot>P\<cdot>\<bottom> = \<bottom>"
  by (fixrec_simp)

lemma nth_Cons_simp [simp]:
  "eq\<cdot>n\<cdot>0 = TT \<Longrightarrow> nth\<cdot>(x : xs)\<cdot>n = x"
  "eq\<cdot>n\<cdot>0 = FF \<Longrightarrow> nth\<cdot>(x : xs)\<cdot>n = nth\<cdot>xs\<cdot>(n - 1)"
  by (subst nth.simps, simp)+

lemma nth_Cons_split:
   "P (nth\<cdot>(x : xs)\<cdot>n) = ((eq\<cdot>n\<cdot>0 = FF \<longrightarrow> P (nth\<cdot>(x : xs)\<cdot>n)) \<and>
                              (eq\<cdot>n\<cdot>0 = TT \<longrightarrow> P (nth\<cdot>(x : xs)\<cdot>n)) \<and>
                              (n = \<bottom> \<longrightarrow> P (nth\<cdot>(x : xs)\<cdot>n)))"
(*   "!!x. P (test x) = (~ (\<exists>a b. x = (a, b) & ~ P (test (a, b))))" *)
apply (cases n, simp)
apply (cases "n = 0", simp_all add: zero_Integer_def)
done



lemma nth_Cons_numeral [simp]:
  "(x : xs) !! 0 = x"
  "(x : xs) !! 1 = xs !! 0"
  "(x : xs) !! numeral (Num.Bit0 k) = xs !! numeral (Num.BitM k)"
  "(x : xs) !! numeral (Num.Bit1 k) = xs !! numeral (Num.Bit0 k)"
  by (simp_all add: nth_Cons numeral_Integer_eq
    zero_Integer_def one_Integer_def)

lemma take_strict [simp]:
  "take\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  by (fixrec_simp)

lemma take_strict_2 [simp]:
  "le\<cdot>1\<cdot>i = TT \<Longrightarrow> take\<cdot>i\<cdot>\<bottom> = \<bottom>"
  by (subst take.simps, cases "le\<cdot>i\<cdot>0") (auto dest: le_trans)

lemma drop_strict [simp]:
  "drop\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  by (fixrec_simp)

lemma isPrefixOf_strict [simp]:
  "isPrefixOf\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  "isPrefixOf\<cdot>(x:xs)\<cdot>\<bottom> = \<bottom>"
  by (fixrec_simp)+

lemma last_strict[simp]:
  "last\<cdot>\<bottom>= \<bottom>"
  "last\<cdot>(x:\<bottom>) = \<bottom>"
  by (fixrec_simp+)

lemma last_nil [simp]:
  "last\<cdot>[] = \<bottom>"
  by (fixrec_simp)

lemma last_spine_strict: "\<not> finite_list xs \<Longrightarrow> last\<cdot>xs = \<bottom>"
proof (induct xs)
  case (Cons a xs)
  then show ?case by (cases xs) auto
qed auto

lemma init_strict [simp]:
  "init\<cdot>\<bottom>= \<bottom>"
  "init\<cdot>(x:\<bottom>) = \<bottom>"
  by (fixrec_simp+)

lemma init_nil [simp]:
  "init\<cdot>[] = \<bottom>"
  by (fixrec_simp)

lemma strict_foldr_strict2 [simp]:
  "(\<And>x. f\<cdot>x\<cdot>\<bottom> = \<bottom>) \<Longrightarrow> foldr\<cdot>f\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  by (induct xs, auto) fixrec_simp

lemma foldr_strict [simp]:
  "foldr\<cdot>f\<cdot>d\<cdot>\<bottom> = \<bottom>"
  "foldr\<cdot>f\<cdot>\<bottom>\<cdot>[] = \<bottom>"
  "foldr\<cdot>\<bottom>\<cdot>d\<cdot>(x : xs) = \<bottom>"
  by fixrec_simp+

lemma foldr_Cons_Nil [simp]:
  "foldr\<cdot>(:)\<cdot>[]\<cdot>xs = xs"
  by (induct xs) simp+

lemma append_strict1 [simp]:
  "\<bottom> ++ ys = \<bottom>"
  by fixrec_simp

lemma foldr_append [simp]:
  "foldr\<cdot>f\<cdot>a\<cdot>(xs ++ ys) = foldr\<cdot>f\<cdot>(foldr\<cdot>f\<cdot>a\<cdot>ys)\<cdot>xs"
  by (induct xs) simp+

lemma foldl_strict [simp]:
  "foldl\<cdot>f\<cdot>d\<cdot>\<bottom> = \<bottom>"
  "foldl\<cdot>f\<cdot>\<bottom>\<cdot>[] = \<bottom>"
  by fixrec_simp+

lemma foldr1_strict [simp]:
  "foldr1\<cdot>f\<cdot>\<bottom>= \<bottom>"
  "foldr1\<cdot>f\<cdot>(x:\<bottom>)= \<bottom>"
  by fixrec_simp+

lemma foldl1_strict [simp]:
  "foldl1\<cdot>f\<cdot>\<bottom>= \<bottom>"
  by fixrec_simp

lemma foldl_spine_strict:
  "\<not> finite_list xs \<Longrightarrow> foldl\<cdot>f\<cdot>x\<cdot>xs = \<bottom>"
  by (induct xs arbitrary: x) auto

lemma foldl_assoc_foldr:
  assumes "finite_list xs"
    and assoc: "\<And>x y z. f\<cdot>(f\<cdot>x\<cdot>y)\<cdot>z = f\<cdot>x\<cdot>(f\<cdot>y\<cdot>z)"
    and neutr1: "\<And>x. f\<cdot>z\<cdot>x = x"
    and neutr2: "\<And>x. f\<cdot>x\<cdot>z = x"
  shows "foldl\<cdot>f\<cdot>z\<cdot>xs = foldr\<cdot>f\<cdot>z\<cdot>xs"
  using \<open>finite_list xs\<close>
proof (induct xs)
  case (Cons x xs)
  from \<open>finite_list xs\<close> have step: "\<And>y. f\<cdot>y\<cdot>(foldl\<cdot>f\<cdot>z\<cdot>xs) = foldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>y)\<cdot>xs"
  proof (induct xs)
    case (Cons x xs y)
    have "f\<cdot>y\<cdot>(foldl\<cdot>f\<cdot>z\<cdot>(x : xs)) = f\<cdot>y\<cdot>(foldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>x)\<cdot>xs)" by auto
    also have "... = f\<cdot>y\<cdot>(f\<cdot>x\<cdot>(foldl\<cdot>f\<cdot>z\<cdot>xs))" by (simp only: Cons.hyps)
    also have "... = f\<cdot>(f\<cdot>y\<cdot>x)\<cdot>(foldl\<cdot>f\<cdot>z\<cdot>xs)" by (simp only: assoc)
    also have "... = foldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>(f\<cdot>y\<cdot>x))\<cdot>xs" by (simp only: Cons.hyps)
    also have "... = foldl\<cdot>f\<cdot>(f\<cdot>(f\<cdot>z\<cdot>y)\<cdot>x)\<cdot>xs" by (simp only: assoc)
    also have "... = foldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>y)\<cdot>(x : xs)" by auto
    finally show ?case.
  qed (simp add: neutr1 neutr2)

  have "foldl\<cdot>f\<cdot>z\<cdot>(x : xs) = foldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>x)\<cdot>xs" by auto
  also have "... = f\<cdot>x\<cdot>(foldl\<cdot>f\<cdot>z\<cdot>xs)" by (simp only: step)
  also have "... = f\<cdot>x\<cdot>(foldr\<cdot>f\<cdot>z\<cdot>xs)" by (simp only: Cons.hyps)
  also have "... = (foldr\<cdot>f\<cdot>z\<cdot>(x:xs))" by auto
  finally show ?case .
qed auto

lemma elem_strict [simp]:
  "elem\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma notElem_strict [simp]:
  "notElem\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma list_eq_nil[simp]:
  "eq\<cdot>l\<cdot>[] = TT \<longleftrightarrow> l = []"
  "eq\<cdot>[]\<cdot>l = TT \<longleftrightarrow> l = []"
  by (cases l, auto)+

lemma take_Nil [simp]:
  "n \<noteq> \<bottom> \<Longrightarrow> take\<cdot>n\<cdot>[] = []"
  by (subst take.simps) (cases "le\<cdot>n\<cdot>0"; simp)

lemma take_0 [simp]:
  "take\<cdot>0\<cdot>xs = []"
  "take\<cdot>(MkI\<cdot>0)\<cdot>xs = []"
  by (subst take.simps, simp add: zero_Integer_def)+

lemma take_Cons [simp]:
  "le\<cdot>1\<cdot>i = TT \<Longrightarrow> take\<cdot>i\<cdot>(x:xs) = x : take\<cdot>(i - 1)\<cdot>xs"
  by (subst take.simps, cases "le\<cdot>i\<cdot>0") (auto dest: le_trans)

lemma take_MkI_Cons [simp]:
  "0 < n \<Longrightarrow> take\<cdot>(MkI\<cdot>n)\<cdot>(x : xs) = x : take\<cdot>(MkI\<cdot>(n - 1))\<cdot>xs"
  by (subst take.simps) (simp add: zero_Integer_def one_Integer_def)

lemma take_numeral_Cons [simp]:
  "take\<cdot>1\<cdot>(x : xs) = [x]"
  "take\<cdot>(numeral (Num.Bit0 k))\<cdot>(x : xs) = x : take\<cdot>(numeral (Num.BitM k))\<cdot>xs"
  "take\<cdot>(numeral (Num.Bit1 k))\<cdot>(x : xs) = x : take\<cdot>(numeral (Num.Bit0 k))\<cdot>xs"
  by (subst take.simps,
      simp add: zero_Integer_def one_Integer_def numeral_Integer_eq)+

lemma drop_0 [simp]:
  "drop\<cdot>0\<cdot>xs = xs"
  "drop\<cdot>(MkI\<cdot>0)\<cdot>xs = xs"
  by (subst drop.simps, simp add: zero_Integer_def)+

lemma drop_pos [simp]:
  "le\<cdot>n\<cdot>0 = FF \<Longrightarrow> drop\<cdot>n\<cdot>xs = (case xs of [] \<Rightarrow> [] | y : ys \<Rightarrow> drop\<cdot>(n - 1)\<cdot>ys)"
  by (subst drop.simps, simp)

lemma drop_numeral_Cons [simp]:
  "drop\<cdot>1\<cdot>(x : xs) = xs"
  "drop\<cdot>(numeral (Num.Bit0 k))\<cdot>(x : xs) = drop\<cdot>(numeral (Num.BitM k))\<cdot>xs"
  "drop\<cdot>(numeral (Num.Bit1 k))\<cdot>(x : xs) = drop\<cdot>(numeral (Num.Bit0 k))\<cdot>xs"
  by (subst drop.simps,
      simp add: zero_Integer_def one_Integer_def numeral_Integer_eq)+

lemma take_drop_append:
  "take\<cdot>(MkI\<cdot>i)\<cdot>xs ++ drop\<cdot>(MkI\<cdot>i)\<cdot>xs = xs"
proof (cases i)
  case (nonneg n)
  then show ?thesis
  proof (induct n arbitrary : i xs)
    case (Suc n)
    thus ?case
      apply (subst drop.simps)
      apply (subst take.simps)
      apply (cases xs)
        apply (auto simp add: zero_Integer_def one_Integer_def )
      done
  qed simp
next
  case (neg nat)
  then show ?thesis
    apply (subst drop.simps)
    apply (subst take.simps)
    apply (auto simp add: zero_Integer_def one_Integer_def )
    done
qed

lemma take_intsFrom_enumFrom [simp]:
  "take\<cdot>(MkI\<cdot>n)\<cdot>[MkI\<cdot>i..] = [MkI\<cdot>i..MkI\<cdot>(n+i) - 1]"
proof (cases n)
  fix m
  assume "n = int m"
  then show ?thesis
  proof (induct m arbitrary: n i)
    case 0 then show ?case by (simp add: one_Integer_def)
  next
    case (Suc m)
    then have "n - 1 = int m" by simp
    from Suc(1) [OF this]
    have "take\<cdot>(MkI\<cdot>(n - 1))\<cdot>[MkI\<cdot>(i+1)..] = [MkI\<cdot>(i+1)..MkI\<cdot>(n - 1 + (i+1)) - 1]" .
    moreover have "(n - 1) + (i+1) - 1 = n + i - 1" by arith
    ultimately have IH: "take\<cdot>(MkI\<cdot>(n - 1))\<cdot>[MkI\<cdot>(i+1)..] = [MkI\<cdot>(i+1)..MkI\<cdot>(n+i) - 1]" by simp
    from Suc(2) have gt: "n > 0" by simp
    moreover have "[MkI\<cdot>i..] = MkI\<cdot>i : [MkI\<cdot>i + 1..]" by (simp, subst intsFrom.simps) simp
    ultimately
    have *: "take\<cdot>(MkI\<cdot>n)\<cdot>[MkI\<cdot>i..] = MkI\<cdot>i : take\<cdot>(MkI\<cdot>(n - 1))\<cdot>[MkI\<cdot>(i+1)..]"
      by (simp add: one_Integer_def)
    show ?case unfolding IH * using gt by (simp add: one_Integer_def)
  qed
next
  fix m
  assume "n = - int m"
  then have "n \<le> 0" by simp
  then show ?thesis
    by (subst take.simps) (simp add: zero_Integer_def one_Integer_def)
qed

lemma drop_intsFrom_enumFrom [simp]:
  assumes "n \<ge> 0"
  shows "drop\<cdot>(MkI\<cdot>n)\<cdot>[MkI\<cdot>i..] = [MkI\<cdot>(n+i)..]"
proof-
  from assms obtain n' where "n = int n'" by (cases n, auto)
  then show ?thesis
    apply(induct n' arbitrary: n i )
     apply simp
    apply (subst intsFrom.simps[unfolded enumFrom_intsFrom_conv[symmetric]])
    apply (subst drop.simps)
    apply (auto simp add: zero_Integer_def one_Integer_def)
    apply (rule cfun_arg_cong)
    apply (rule cfun_arg_cong)
    apply arith
    done
qed

lemma last_append_singleton:
  "finite_list xs \<Longrightarrow> last\<cdot>(xs ++ [x]) = x"
proof (induct xs rule:finite_list.induct)
  case (Cons x xs)
  then show ?case by (cases xs) auto
qed auto

lemma init_append_singleton:
  "finite_list xs \<Longrightarrow> init\<cdot>(xs ++ [x]) = xs"
proof (induct xs rule:finite_list.induct)
  case (Cons x xs)
  then show ?case by (cases xs) auto
qed auto

lemma append_Nil2 [simp]:
  "xs ++ [] = xs"
  by (induct xs) simp_all

lemma append_assoc [simp]:
  "(xs ++ ys) ++ zs = xs ++ ys ++ zs"
  by (induct xs) simp_all

lemma concat_simps [simp]:
  "concat\<cdot>[] = []"
  "concat\<cdot>(xs : xss) = xs ++ concat\<cdot>xss"
  "concat\<cdot>\<bottom> = \<bottom>"
  unfolding concat_def by simp_all

lemma concatMap_simps [simp]:
  "concatMap\<cdot>f\<cdot>[] = []"
  "concatMap\<cdot>f\<cdot>(x : xs) = f\<cdot>x ++ concatMap\<cdot>f\<cdot>xs"
  "concatMap\<cdot>f\<cdot>\<bottom> = \<bottom>"
  unfolding concatMap_def by simp_all

lemma filter_append [simp]:
  "filter\<cdot>P\<cdot>(xs ++ ys) = filter\<cdot>P\<cdot>xs ++ filter\<cdot>P\<cdot>ys"
proof (induct xs)
  case (Cons x xs) then show ?case by (cases "P\<cdot>x") (auto simp: If_and_if)
qed simp_all

lemma elem_append [simp]:
  "elem\<cdot>x\<cdot>(xs ++ ys) = (elem\<cdot>x\<cdot>xs orelse elem\<cdot>x\<cdot>ys)"
    by (induct xs) auto

lemma filter_filter [simp]:
  "filter\<cdot>P\<cdot>(filter\<cdot>Q\<cdot>xs) = filter\<cdot>(\<Lambda> x. Q\<cdot>x andalso P\<cdot>x)\<cdot>xs"
  by (induct xs) (auto simp: If2_def [symmetric] split: split_If2)

lemma filter_const_TT [simp]:
  "filter\<cdot>(\<Lambda> _. TT)\<cdot>xs = xs"
  by (induct xs) simp_all

lemma tails_strict [simp]:
  "tails\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma inits_strict [simp]:
  "inits\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma the_and_strict [simp]:
  "the_and\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma the_or_strict [simp]:
  "the_or\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma all_strict [simp]:
  "all\<cdot>P\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma any_strict [simp]:
  "any\<cdot>P\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma tails_neq_Nil [simp]:
  "tails\<cdot>xs \<noteq> []"
  by (cases xs) simp_all

lemma inits_neq_Nil [simp]:
  "inits\<cdot>xs \<noteq> []"
  by (cases xs) simp_all

lemma Nil_neq_tails [simp]:
  "[] \<noteq> tails\<cdot>xs"
  by (cases xs) simp_all

lemma Nil_neq_inits [simp]:
  "[] \<noteq> inits\<cdot>xs"
  by (cases xs) simp_all

lemma finite_list_not_bottom [simp]:
  assumes "finite_list xs" shows "xs \<noteq> \<bottom>"
  using assms by (cases) simp_all

lemma head_append [simp]:
  "head\<cdot>(xs ++ ys) = If null\<cdot>xs then head\<cdot>ys else head\<cdot>xs"
  by (cases xs) simp_all

lemma filter_cong:
  "\<forall>x\<in>set xs. p\<cdot>x = q\<cdot>x \<Longrightarrow> filter\<cdot>p\<cdot>xs = filter\<cdot>q\<cdot>xs"
proof (induct arbitrary: xs rule: filter.induct)
  case (3 x)
  then show ?case by (cases xs) auto
qed simp_all

lemma filter_TT [simp]:
  assumes "\<forall>x\<in>set xs. P\<cdot>x = TT"
  shows "filter\<cdot>P\<cdot>xs = xs"
  by (rule filter_cong [of xs P "\<Lambda> _. TT", simplified, OF assms])

lemma filter_FF [simp]:
  assumes "finite_list xs"
    and "\<forall>x\<in>set xs. P\<cdot>x = FF"
  shows "filter\<cdot>P\<cdot>xs = []"
  using assms by (induct xs) simp_all

lemma map_cong:
  "\<forall>x\<in>set xs. p\<cdot>x = q\<cdot>x \<Longrightarrow> map\<cdot>p\<cdot>xs = map\<cdot>q\<cdot>xs"
proof (induct arbitrary: xs rule: map.induct)
  case (3 x)
  then show ?case by (cases xs) auto
qed simp_all

lemma finite_list_upto:
  "finite_list (upto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n))" (is "?P m n")
proof (cases "n - m")
  fix d
  assume "n - m = int d"
  then show "?P m n"
  proof (induct d arbitrary: m n)
    case (Suc d)
    then have "n - (m + 1) = int d" and le: "m \<le> n" by simp_all
    from Suc(1) [OF this(1)] have IH: "?P (m+1) n" .
    then show ?case using le by (simp add: one_Integer_def)
  qed (simp add: one_Integer_def)
next
  fix d
  assume "n - m = - int d"
  then have "n \<le> m" by auto
  moreover
  { assume "n = m" then have "?P m n" by (simp add: one_Integer_def) }
  moreover
  { assume "n < m" then have "?P m n" by (simp add: one_Integer_def) }
  ultimately show ?thesis by arith
qed

lemma filter_commute:
  assumes "\<forall>x\<in>set xs. (Q\<cdot>x andalso P\<cdot>x) = (P\<cdot>x andalso Q\<cdot>x)"
  shows "filter\<cdot>P\<cdot>(filter\<cdot>Q\<cdot>xs) = filter\<cdot>Q\<cdot>(filter\<cdot>P\<cdot>xs)"
  using filter_cong [of xs "\<Lambda> x. Q\<cdot>x andalso P\<cdot>x" "\<Lambda> x. P\<cdot>x andalso Q\<cdot>x"]
    and assms by simp

lemma upto_append_intsFrom [simp]:
  assumes "m \<le> n"
  shows "upto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n) ++ intsFrom\<cdot>(MkI\<cdot>n+1) = intsFrom\<cdot>(MkI\<cdot>m)"
    (is "?u m n ++ _ = ?i m")
proof (cases "n - m")
  case (nonneg i)
  with assms show ?thesis
  proof (induct i arbitrary: m n)
    case (Suc i)
    then have "m + 1 \<le> n" and "n - (m + 1) = int i" by simp_all
    from Suc(1) [OF this]
    have IH: "?u (m+1) n ++ ?i (n+1) = ?i (m+1)" by (simp add: one_Integer_def)
    from \<open>m + 1 \<le> n\<close> have "m \<le> n" by simp
    then have "?u m n ++ ?i (n+1) = (MkI\<cdot>m : ?u (m+1) n) ++ ?i (n+1)"
      by (simp add: one_Integer_def)
    also have "\<dots> = MkI\<cdot>m : ?i (m+1)" by (simp add: IH)
    finally show ?case by (subst (2) intsFrom.simps) (simp add: one_Integer_def)
  qed (subst (2) intsFrom.simps, simp add: one_Integer_def)
next
  case (neg i)
  then have "n < m" by simp
  with assms show ?thesis by simp
qed

lemma set_upto [simp]:
  "set (upto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n)) = {MkI\<cdot>i | i. m \<le> i \<and> i \<le> n}"
  (is "set (?u m n) = ?R m n")
proof (cases "n - m")
  case (nonneg i)
  then show ?thesis
  proof (induct i arbitrary: m n)
    case (Suc i)
    then have *: "n - (m + 1) = int i" by simp
    from Suc(1) [OF *] have IH: "set (?u (m+1) n) = ?R (m+1) n" .
    from * have "m \<le> n" by simp
    then have "set (?u m n) = set (MkI\<cdot>m : ?u (m+1) n)" by (simp add: one_Integer_def)
    also have "\<dots> = insert (MkI\<cdot>m) (?R (m+1) n)" by (simp add: IH)
    also have "\<dots> = ?R m n" using \<open>m \<le> n\<close> by auto
    finally show ?case .
  qed (force simp: one_Integer_def)
qed simp

lemma Nil_append_iff [iff]:
  "xs ++ ys = [] \<longleftrightarrow> xs = [] \<and> ys = []"
  by (induct xs) simp_all

text \<open>This version of definedness rule for Nil is made necessary by
the reorient simproc.\<close>

lemma bottom_neq_Nil [simp]: "\<bottom> \<noteq> []"
  by simp

text \<open>Simproc to rewrite @{term "Nil = x"} to @{term "x = Nil"}.\<close>

setup \<open>
  Reorient_Proc.add
    (fn Const(@{const_name Nil}, _) => true | _ => false)
\<close>

simproc_setup reorient_Nil ("Nil = x") = Reorient_Proc.proc


lemma set_append [simp]:
  assumes "finite_list xs"
  shows "set (xs ++ ys) = set xs \<union> set ys"
  using assms by (induct) simp_all

lemma distinct_Cons [simp]:
  "distinct (x : xs) \<longleftrightarrow> distinct xs \<and> x \<notin> set xs"
  (is "?l = ?r")
proof
  assume ?l then show ?r by (cases) simp_all
next
  assume ?r then show ?l by auto
qed

lemma finite_list_append [iff]:
  "finite_list (xs ++ ys) \<longleftrightarrow> finite_list xs \<and> finite_list ys"
  (is "?l = ?r")
proof
  presume "finite_list xs" and "finite_list ys"
  then show ?l by (induct) simp_all
next
  assume "?l" then show "?r"
  proof (induct "xs ++ ys" arbitrary: xs ys)
    case (Cons x xs)
    then show ?case by (cases xs) auto
  qed simp
qed simp_all

lemma distinct_append [simp]:
  assumes "finite_list (xs ++ ys)"
  shows "distinct (xs ++ ys) \<longleftrightarrow> distinct xs \<and> distinct ys \<and> set xs \<inter> set ys = {}"
    (is "?P xs ys")
  using assms
proof (induct "xs ++ ys" arbitrary: xs ys)
  case (Cons z zs)
  show ?case
  proof (cases xs)
    note Cons' = Cons
    case (Cons u us)
    with Cons' have "finite_list us"
      and [simp]: "zs = us ++ ys" "?P us ys" by simp_all
    then show ?thesis by (auto simp: Cons)
  qed (insert Cons, simp_all)
qed simp

lemma finite_set [simp]:
  assumes "distinct xs"
  shows "finite (set xs)"
  using assms by induct auto

lemma distinct_card:
  assumes "distinct xs"
  shows "MkI\<cdot>(int (card (set xs))) = length\<cdot>xs"
  using assms
  by (induct)
     (simp_all add: zero_Integer_def plus_MkI_MkI [symmetric] one_Integer_def ac_simps)

lemma set_delete [simp]:
  fixes xs :: "['a::Eq_eq]"
  assumes "distinct xs"
    and "\<forall>x\<in>set xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>"
  shows "set (delete\<cdot>a\<cdot>xs) = set xs - {a}"
  using assms
proof induct
  case (Cons x xs)
  then show ?case by (cases "eq\<cdot>a\<cdot>x", force+)
qed simp

lemma distinct_delete [simp]:
  fixes xs :: "['a::Eq_eq]"
  assumes "distinct xs"
    and "\<forall>x\<in>set xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>"
  shows "distinct (delete\<cdot>a\<cdot>xs)"
  using assms
proof induct
  case (Cons x xs)
  then show ?case by (cases "eq\<cdot>a\<cdot>x", force+)
qed simp

lemma set_diff [simp]:
  fixes xs ys :: "['a::Eq_eq]"
  assumes "distinct ys" and "distinct xs"
    and "\<forall>a\<in>set ys. \<forall>x\<in>set xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>"
  shows "set (xs \\\\ ys) = set xs - set ys"
  using assms
proof (induct arbitrary: xs)
  case Nil then show ?case by (induct xs rule: distinct.induct) simp_all
next
  case (Cons y ys)
  let ?xs = "delete\<cdot>y\<cdot>xs"
  from Cons have *: "\<forall>x\<in>set xs. eq\<cdot>y\<cdot>x \<noteq> \<bottom>" by simp
  from set_delete [OF \<open>distinct xs\<close> this]
  have **: "set ?xs = set xs - {y}" .
  with Cons have "\<forall>a\<in>set ys. \<forall>x\<in>set ?xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>" by simp
  moreover from * and \<open>distinct xs\<close> have "distinct ?xs" by simp
  ultimately have "set (?xs \\\\ ys) = set ?xs - set ys"
    using Cons by blast
  then show ?case by (force simp: **)
qed

lemma distinct_delete_filter:
  fixes xs :: "['a::Eq_eq]"
  assumes "distinct xs"
    and "\<forall>x\<in>set xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>"
  shows "delete\<cdot>a\<cdot>xs = filter\<cdot>(\<Lambda> x. neq\<cdot>a\<cdot>x)\<cdot>xs"
  using assms
proof (induct)
  case (Cons x xs)
  then have IH: "delete\<cdot>a\<cdot>xs = filter\<cdot>(\<Lambda> x. neq\<cdot>a\<cdot>x)\<cdot>xs" by simp
  show ?case
  proof (cases "eq\<cdot>a\<cdot>x")
    case TT
    have "\<forall>x\<in>set xs. (\<Lambda> x. neq\<cdot>a\<cdot>x)\<cdot>x = (\<Lambda> _. TT)\<cdot>x"
    proof
      fix y
      assume "y \<in> set xs"
      with Cons(3, 4) have "x \<noteq> y" and "eq\<cdot>a\<cdot>y \<noteq> \<bottom>" by auto
      with TT have "eq\<cdot>a\<cdot>y = FF" by (metis (no_types) eqD(1) trE)
      then show "(\<Lambda> x. neq\<cdot>a\<cdot>x)\<cdot>y = (\<Lambda> _. TT)\<cdot>y" by simp
    qed
    from filter_cong [OF this] and TT
    show ?thesis by simp
  qed (simp_all add: IH)
qed simp

lemma distinct_diff_filter:
  fixes xs ys :: "['a::Eq_eq]"
  assumes "finite_list ys"
    and "distinct xs"
    and "\<forall>a\<in>set ys. \<forall>x\<in>set xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>"
  shows "xs \\\\ ys = filter\<cdot>(\<Lambda> x. neg\<cdot>(elem\<cdot>x\<cdot>ys))\<cdot>xs"
  using assms
proof (induct arbitrary: xs)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  let ?xs = "delete\<cdot>y\<cdot>xs"
  from Cons have *: "\<forall>x\<in>set xs. eq\<cdot>y\<cdot>x \<noteq> \<bottom>" by simp
  from set_delete [OF \<open>distinct xs\<close> this]
  have "set ?xs = set xs - {y}" .
  with Cons have "\<forall>a\<in>set ys. \<forall>x\<in>set ?xs. eq\<cdot>a\<cdot>x \<noteq> \<bottom>" by simp
  moreover from * and \<open>distinct xs\<close> have "distinct ?xs" by simp
  ultimately have "?xs \\\\ ys = filter\<cdot>(\<Lambda> x. neg\<cdot>(elem\<cdot>x\<cdot>ys))\<cdot>?xs"
    using Cons by blast
  then show ?case
    using \<open>distinct xs\<close> and *
    by (simp add: distinct_delete_filter)
qed

lemma distinct_upto [intro, simp]:
  "distinct [MkI\<cdot>m..MkI\<cdot>n]"
proof (cases "n - m")
  case (nonneg i)
  then show ?thesis
  proof (induct i arbitrary: m)
    case (Suc i)
    then have "n - (m + 1) = int i" and "m \<le> n" by simp_all
    with Suc have "distinct [MkI\<cdot>(m+1)..MkI\<cdot>n]" by force
    with \<open>m \<le> n\<close> show ?case by (simp add: one_Integer_def)
  qed (simp add: one_Integer_def)
qed simp

lemma set_intsFrom [simp]:
  "set (intsFrom\<cdot>(MkI\<cdot>m)) = {MkI\<cdot>n | n. m \<le> n}"
  (is "set (?i m) = ?I")
proof
  show "set (?i m) \<subseteq> ?I"
  proof
    fix n
    assume "n \<in> set (?i m)"
    then have "listmem n (?i m)" by (simp add: set_def)
    then show "n \<in> ?I"
    proof (induct n "(?i m)" arbitrary: m)
      fix x xs m
      assume "x : xs = ?i m"
      then have "x : xs = MkI\<cdot>m : ?i (m+1)"
        by (subst (asm) intsFrom.simps) (simp add: one_Integer_def)
      then have [simp]: "x = MkI\<cdot>m" "xs = ?i (m+1)" by simp_all
      show "x \<in> {MkI\<cdot>n | n. m \<le> n}" by simp
    next
      fix x xs y m
      assume IH: "listmem x xs"
        "\<And>m. xs = ?i m \<Longrightarrow> x \<in> {MkI\<cdot>n | n. m \<le> n}"
        "y : xs = ?i m"
      then have "y : xs = MkI\<cdot>m : ?i (m+1)"
        by (subst (asm) (2) intsFrom.simps) (simp add: one_Integer_def)
      then have [simp]: "y = MkI\<cdot>m" "xs = ?i (m+1)" by simp_all
      from IH (2) [of "m+1"] have "x \<in> {MkI\<cdot>n | n. m+1 \<le> n}" by (simp add: one_Integer_def)
      then show "x \<in> {MkI\<cdot>n | n. m \<le> n}" by force
    qed
  qed
next
  show "?I \<subseteq> set (?i m)"
  proof
    fix x
    assume "x \<in> ?I"
    then obtain n where [simp]: "x = MkI\<cdot>n" and "m \<le> n" by blast
    from upto_append_intsFrom [OF this(2), symmetric]
    have *: "set (?i m) = set (upto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n)) \<union> set (?i (n+1))"
      using finite_list_upto [of m n] by (simp add: one_Integer_def)
    show "x \<in> set (?i m)" using \<open>m \<le> n\<close> by (auto simp: * one_Integer_def)
  qed
qed

lemma If_eq_bottom_iff [simp]: (* FIXME: move *)
  "(If b then x else y = \<bottom>) \<longleftrightarrow> b = \<bottom> \<or> b = TT \<and> x = \<bottom> \<or> b = FF \<and> y = \<bottom>"
  by (induct b) simp_all

lemma upto_eq_bottom_iff [simp]:
  "upto\<cdot>m\<cdot>n = \<bottom> \<longleftrightarrow> m = \<bottom> \<or> n = \<bottom>"
  by (subst upto.simps, simp)

lemma seq_eq_bottom_iff [simp]: (* FIXME: move *)
  "seq\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (simp add: seq_conv_if)

lemma intsFrom_eq_bottom_iff [simp]:
  "intsFrom\<cdot>m = \<bottom> \<longleftrightarrow> m = \<bottom>"
  by (subst intsFrom.simps, simp)

lemma intsFrom_split:
  assumes "m \<ge> n"
  shows "[MkI\<cdot>n..] = [MkI\<cdot>n .. MkI\<cdot>(m - 1)] ++ [MkI\<cdot>m..]"
proof-
  from assms have ge: "m - n \<ge> 0" by arith
  have "[MkI\<cdot>n..] = (take\<cdot>(MkI\<cdot>(m - n)) \<cdot> [MkI\<cdot>n..]) ++ (drop\<cdot>(MkI\<cdot>(m - n)) \<cdot> [MkI\<cdot>n..])"
    by (subst take_drop_append, rule)
  also have "... = [MkI\<cdot>n.. MkI\<cdot>(m - 1)] ++ [MkI\<cdot>m..]"
    by (subst drop_intsFrom_enumFrom[OF ge], auto simp add:take_intsFrom_enumFrom[simplified] one_Integer_def)
  finally show ?thesis .
qed

lemma filter_fast_forward:
  assumes "n+1 \<le> n'"
    and  "\<forall>k . n < k \<longrightarrow> k < n' \<longrightarrow> \<not> P k"
  shows "filter\<cdot>(\<Lambda> (MkI\<cdot>i) . Def (P i))\<cdot>[MkI\<cdot>(n+1)..] = filter\<cdot>(\<Lambda> (MkI\<cdot>i) . Def (P i))\<cdot>[MkI\<cdot>n'..]"
proof-
  from assms(1)
  have"[MkI\<cdot>(n+1)..] = [MkI\<cdot>(n+1).. MkI\<cdot>(n'- 1)] ++ [MkI\<cdot>n'..]" (is "_ = ?l1 ++ ?l2")
    by (subst intsFrom_split[of "n+1" n'], auto)
  moreover
  have "filter\<cdot>(\<Lambda> (MkI\<cdot>i) . Def (P i))\<cdot>[MkI\<cdot>(n+1).. MkI\<cdot>(n'- 1)] = []"
    apply (rule filter_FF)
     apply (simp, rule finite_list_upto)
    using assms(2)
    apply auto
    done
  ultimately
  show ?thesis by simp
qed

lemma null_eq_TT_iff [simp]:
  "null\<cdot>xs = TT \<longleftrightarrow> xs = []"
  by (cases xs) simp_all

lemma null_set_empty_conv:
  "xs \<noteq> \<bottom> \<Longrightarrow> null\<cdot>xs = TT \<longleftrightarrow> set xs = {}"
  by (cases xs) simp_all

lemma elem_TT [simp]:
  fixes x :: "'a::Eq_eq" shows "elem\<cdot>x\<cdot>xs = TT \<Longrightarrow> x \<in> set xs"
  apply (induct arbitrary: xs rule: elem.induct, simp_all)
  apply (rename_tac xs, case_tac xs, simp_all)
  apply (rename_tac a list, case_tac "eq\<cdot>a\<cdot>x", force+)
  done

lemma elem_FF [simp]:
  fixes x :: "'a::Eq_equiv" shows "elem\<cdot>x\<cdot>xs = FF \<Longrightarrow> x \<notin> set xs"
  by (induct arbitrary: xs rule: elem.induct, simp_all)
     (rename_tac xs, case_tac xs, simp_all, force)

lemma length_strict [simp]:
  "length\<cdot>\<bottom> = \<bottom>"
  by (fixrec_simp)

lemma repeat_neq_bottom [simp]:
  "repeat\<cdot>x \<noteq> \<bottom>"
  by (subst repeat.simps) simp

lemma list_case_repeat [simp]:
  "list_case\<cdot>a\<cdot>f\<cdot>(repeat\<cdot>x) = f\<cdot>x\<cdot>(repeat\<cdot>x)"
  by (subst repeat.simps) simp

lemma length_append [simp]:
  "length\<cdot>(xs ++ ys) = length\<cdot>xs + length\<cdot>ys"
  by (induct xs) (simp_all add: ac_simps)

lemma replicate_strict [simp]:
  "replicate\<cdot>\<bottom>\<cdot>x = \<bottom>"
  by (simp add: replicate_def)

lemma replicate_0 [simp]:
  "replicate\<cdot>0\<cdot>x = []"
  "replicate\<cdot>(MkI\<cdot>0)\<cdot>xs = []"
  by (simp add: replicate_def)+

lemma Integer_add_0 [simp]: "MkI\<cdot>0 + n = n"
  by (cases n) simp_all

lemma replicate_MkI_plus_1 [simp]:
  "0 \<le> n \<Longrightarrow> replicate\<cdot>(MkI\<cdot>(n+1))\<cdot>x = x : replicate\<cdot>(MkI\<cdot>n)\<cdot>x"
  "0 \<le> n \<Longrightarrow> replicate\<cdot>(MkI\<cdot>(1+n))\<cdot>x = x : replicate\<cdot>(MkI\<cdot>n)\<cdot>x"
  by (simp add: replicate_def, subst take.simps, simp add: one_Integer_def zero_Integer_def)+

lemma replicate_append_plus_conv:
  assumes "0 \<le> m" and "0 \<le> n"
  shows "replicate\<cdot>(MkI\<cdot>m)\<cdot>x ++ replicate\<cdot>(MkI\<cdot>n)\<cdot>x
    = replicate\<cdot>(MkI\<cdot>m + MkI\<cdot>n)\<cdot>x"
proof (cases m)
  case (nonneg i)
  with assms show ?thesis
  proof (induct i arbitrary: m)
    case (Suc i)
    then have ge: "int i + n \<ge> 0" by force
    have "replicate\<cdot>(MkI\<cdot>m)\<cdot>x ++ replicate\<cdot>(MkI\<cdot>n)\<cdot>x = x : (replicate\<cdot>(MkI\<cdot>(int i))\<cdot>x ++ replicate\<cdot>(MkI\<cdot>n)\<cdot>x)" by (simp add: Suc)
    also have "\<dots> = x : replicate\<cdot>(MkI\<cdot>(int i) + MkI\<cdot>n)\<cdot>x" using Suc by simp
    finally show ?case using ge by (simp add: Suc ac_simps)
  qed simp
next
  case (neg i)
  with assms show ?thesis by simp
qed

lemma replicate_MkI_1 [simp]:
  "replicate\<cdot>(MkI\<cdot>1)\<cdot>x = x : []"
  by (simp add: replicate_def, subst take.simps, simp add: zero_Integer_def one_Integer_def)

lemma length_replicate [simp]:
  assumes "0 \<le> n"
  shows "length\<cdot>(replicate\<cdot>(MkI\<cdot>n)\<cdot>x) = MkI\<cdot>n"
proof (cases n)
  case (nonneg i)
  with assms show ?thesis
    by (induct i arbitrary: n)
       (simp_all add: replicate_append_plus_conv zero_Integer_def one_Integer_def)
next
  case (neg i)
  with assms show ?thesis by (simp add: replicate_def)
qed

lemma map_oo [simp]:
  "map\<cdot>f\<cdot>(map\<cdot>g\<cdot>xs) = map\<cdot>(f oo g)\<cdot>xs"
  by (induct xs) simp_all

lemma nth_Cons_MkI [simp]:
  "0 < i \<Longrightarrow> (a : xs) !! (MkI\<cdot>i) = xs !! (MkI\<cdot>(i - 1))"
  unfolding nth_Cons
  by (cases i, simp add: zero_Integer_def one_Integer_def) (case_tac n, simp_all)

lemma map_plus_intsFrom:
  "map\<cdot>(+ MkI\<cdot>n)\<cdot>(intsFrom\<cdot>(MkI\<cdot>m)) = intsFrom\<cdot>(MkI\<cdot>(m+n))" (is "?l = ?r")
proof (rule list.take_lemma)
  fix i show "list_take i\<cdot>?l = list_take i\<cdot>?r"
  proof (induct i arbitrary: m)
    case (Suc i) then show ?case
      by (subst (1 2) intsFrom.simps) (simp add: ac_simps one_Integer_def)
  qed simp
qed

lemma plus_eq_MkI_conv:
  "l + n = MkI\<cdot>m \<longleftrightarrow> (\<exists>l' n'. l = MkI\<cdot>l' \<and> n = MkI\<cdot>n' \<and> m = l' + n')"
  by (cases l, simp) (cases n, auto)

lemma length_ge_0:
  "length\<cdot>xs = MkI\<cdot>n \<Longrightarrow> n \<ge> 0"
  by (induct xs arbitrary: n) (auto simp: one_Integer_def plus_eq_MkI_conv)

lemma length_0_conv [simp]:
  "length\<cdot>xs = MkI\<cdot>0 \<longleftrightarrow> xs = []"
  apply (cases xs)
    apply (simp_all add: one_Integer_def)
  apply (case_tac "length\<cdot>list")
   apply (auto dest: length_ge_0)
  done

lemma length_ge_1 [simp]:
  "length\<cdot>xs = MkI\<cdot>(1 + int n)
    \<longleftrightarrow> (\<exists>u us. xs = u : us \<and> length\<cdot>us = MkI\<cdot>(int n))"
  (is "?l = ?r")
proof
  assume ?r then show ?l by (auto simp: one_Integer_def)
next
  assume 1: ?l
  then obtain u us where [simp]: "xs = u : us" by (cases xs) auto
  from 1 have 2: "1 + length\<cdot>us = MkI\<cdot>(1 + int n)" by (simp add: ac_simps)
  then have "length\<cdot>us \<noteq> \<bottom>" by (cases "length\<cdot>us") simp_all
  moreover from 2 have "length\<cdot>us + 1 = MkI\<cdot>(int n) + 1" by (simp add: one_Integer_def ac_simps)
  ultimately have "length\<cdot>us = MkI\<cdot>(int n)"
    by (cases "length\<cdot>us") (simp_all add: one_Integer_def)
  then show ?r by simp
qed

lemma finite_list_length_conv:
  "finite_list xs \<longleftrightarrow> (\<exists>n. length\<cdot>xs = MkI\<cdot>(int n))" (is "?l = ?r")
proof
  assume "?l" then show "?r"
    by (induct, auto simp: one_Integer_def) presburger
next
  assume "?r"
  then obtain n where "length\<cdot>xs = MkI\<cdot>(int n)" by blast
  then show "?l" by (induct n arbitrary: xs) auto
qed

lemma nth_append:
  assumes "length\<cdot>xs = MkI\<cdot>n" and "n \<le> m"
  shows "(xs ++ ys) !! MkI\<cdot>m = ys !! MkI\<cdot>(m - n)"
  using assms
proof (induct xs arbitrary: n m)
  case (Cons x xs)
  then have ge: "n \<ge> 0" by (blast intro: length_ge_0)
  from Cons(2)
  have len: "length\<cdot>xs = MkI\<cdot>(n - 1)"
    by (auto simp: plus_eq_MkI_conv one_Integer_def)
  from Cons(3) have le: "n - 1 \<le> m - 1" by simp
  { assume "m < 0"
    with ge have ?case using Cons(3) by simp }
  moreover
  { assume "m = 0"
    with Cons(3) and ge have "n = 0" by simp
    with Cons(2) have ?case
      by (auto dest: length_ge_0 simp: one_Integer_def plus_eq_MkI_conv) }
  moreover
  { assume "m > 0"
    then have ?case
      by (auto simp: Cons(1) [OF len le] zero_Integer_def one_Integer_def) }
  ultimately show ?case by arith
qed (simp_all add: zero_Integer_def)

lemma replicate_nth [simp]:
  assumes "0 \<le> n"
  shows "(replicate\<cdot>(MkI\<cdot>n)\<cdot>x ++ xs) !! MkI\<cdot>n = xs !! MkI\<cdot>0"
  using nth_append [OF length_replicate [OF assms], of n]
    by simp

lemma map2_zip:
  "map\<cdot>(\<Lambda>\<langle>x, y\<rangle>. \<langle>x, f\<cdot>y\<rangle>)\<cdot>(zip\<cdot>xs\<cdot>ys) = zip\<cdot>xs\<cdot>(map\<cdot>f\<cdot>ys)"
  by (induct xs arbitrary: ys) (simp_all, case_tac ys, simp_all)

lemma map2_filter:
  "map\<cdot>(\<Lambda>\<langle>x, y\<rangle>. \<langle>x, f\<cdot>y\<rangle>)\<cdot>(filter\<cdot>(\<Lambda>\<langle>x, y\<rangle>. P\<cdot>x)\<cdot>xs)
    = filter\<cdot>(\<Lambda>\<langle>x, y\<rangle>. P\<cdot>x)\<cdot>(map\<cdot>(\<Lambda>\<langle>x, y\<rangle>. \<langle>x, f\<cdot>y\<rangle>)\<cdot>xs)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs, case_tac x, simp, simp)
  apply (rename_tac a b, case_tac "P\<cdot>a", auto)
done

lemma map_map_snd:
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> map\<cdot>f\<cdot>(map\<cdot>snd\<cdot>xs)
    = map\<cdot>snd\<cdot>(map\<cdot>(\<Lambda>\<langle>x, y\<rangle>. \<langle>x, f\<cdot>y\<rangle>)\<cdot>xs)"
  by (induct xs, simp_all, rename_tac a b, case_tac a, simp_all)

lemma findIndices_Cons [simp]:
  "findIndices\<cdot>P\<cdot>(a : xs) =
    If P\<cdot>a then 0 : map\<cdot>(+1)\<cdot>(findIndices\<cdot>P\<cdot>xs)
    else map\<cdot>(+1)\<cdot>(findIndices\<cdot>P\<cdot>xs)"
  by (auto simp: findIndices_def, subst intsFrom.simps, cases "P\<cdot>a")
     (simp_all
       del: map_oo
       add: map_oo [symmetric] map_map_snd one_Integer_def zero_Integer_def
       map_plus_intsFrom [of 1 0, simplified, symmetric]
       map2_zip [of "(+ MkI\<cdot>1)", simplified]
       map2_filter [of "(+ MkI\<cdot>1)", simplified])

lemma filter_alt_def:
  fixes xs :: "['a]"
  shows "filter\<cdot>P\<cdot>xs = map\<cdot>(nth\<cdot>xs)\<cdot>(findIndices\<cdot>P\<cdot>xs)"
proof -
  {
    fix f g :: "Integer \<rightarrow> 'a"
      and P :: "'a \<rightarrow> tr"
      and i xs
    assume "\<forall>j\<ge>i. f\<cdot>(MkI\<cdot>j) = g\<cdot>(MkI\<cdot>j)"
    then have "map\<cdot>f\<cdot>(map\<cdot>snd\<cdot>(filter\<cdot>(\<Lambda>\<langle>x, i\<rangle>. P\<cdot>x)\<cdot>(zip\<cdot>xs\<cdot>[MkI\<cdot>i..])))
      = map\<cdot>g\<cdot>(map\<cdot>snd\<cdot>(filter\<cdot>(\<Lambda>\<langle>x, i\<rangle>. P\<cdot>x)\<cdot>(zip\<cdot>xs\<cdot>[MkI\<cdot>i..])))"
      by (induct xs arbitrary: i, simp_all, subst (1 2) intsFrom.simps)
        (rename_tac a b c, case_tac "P\<cdot>a", simp_all add: one_Integer_def)
  } note 1 = this
  {
    fix a and ys :: "['a]"
    have "\<forall>i\<ge>0. nth\<cdot>ys\<cdot>(MkI\<cdot>i) = (nth\<cdot>(a : ys) oo (+1))\<cdot>(MkI\<cdot>i)"
      by (auto simp: one_Integer_def zero_Integer_def)
  } note 2 = this
  {
    fix a P and ys xs :: "['a]"
    have "map\<cdot>(nth\<cdot>(a : ys) oo (+1))\<cdot>(findIndices\<cdot>P\<cdot>xs)
      = map\<cdot>(nth\<cdot>ys)\<cdot>(findIndices\<cdot>P\<cdot>xs)"
      by (simp add: findIndices_def 1 [OF 2, simplified, of ys P xs a] zero_Integer_def)
  } note 3 = this
  show ?thesis
    by (induct xs, simp_all, simp add: findIndices_def, simp add: findIndices_def)
       (rename_tac a b, case_tac "P\<cdot>a", simp add: findIndices_def, simp_all add: 3)
qed

abbreviation cfun_image :: "('a \<rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set" (infixr "`\<cdot>" 90) where
  "f `\<cdot> A \<equiv> Rep_cfun f ` A"

lemma set_map:
  "set (map\<cdot>f\<cdot>xs) = f `\<cdot> set xs" (is "?l = ?r")
proof
  { fix a assume "listmem a xs" then have "listmem (f\<cdot>a) (map\<cdot>f\<cdot>xs)"
      by (induct) simp_all }
  then show "?r \<subseteq> ?l" by (auto simp: set_def)
next
  { fix a assume "listmem a (map\<cdot>f\<cdot>xs)"
    then have "\<exists>b. a = f\<cdot>b \<and> listmem b xs"
    by (induct a "map\<cdot>f\<cdot>xs" arbitrary: xs)
       (rename_tac xsa, case_tac xsa, auto)+ }
  then show "?l \<subseteq> ?r" unfolding set_def by auto
qed


subsection \<open>@{const reverse} and @{const reverse} induction\<close>

text \<open>Alternative simplification rules for @{const reverse} (easier
to use for equational reasoning):\<close>
lemma reverse_Nil [simp]:
  "reverse\<cdot>[] = []"
  by (simp add: reverse.simps)

lemma reverse_singleton [simp]:
  "reverse\<cdot>[x] = [x]"
  by (simp add: reverse.simps)

lemma reverse_strict [simp]:
  "reverse\<cdot>\<bottom> = \<bottom>"
  by (simp add: reverse.simps)

lemma foldl_flip_Cons_append:
  "foldl\<cdot>(flip\<cdot>(:))\<cdot>ys\<cdot>xs = foldl\<cdot>(flip\<cdot>(:))\<cdot>[]\<cdot>xs ++ ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs)
  show ?case by simp (metis (no_types) Cons append.simps append_assoc)
qed simp+

lemma reverse_Cons [simp]:
  "reverse\<cdot>(x:xs) = reverse\<cdot>xs ++ [x]"
  by (simp add: reverse.simps)
     (subst foldl_flip_Cons_append, rule refl)

lemma reverse_append_below:
  "reverse\<cdot>(xs ++ ys) \<sqsubseteq> reverse\<cdot>ys ++ reverse\<cdot>xs"
  apply (induction xs)
     apply (simp del: append_assoc add: append_assoc [symmetric])+
  apply (blast intro: monofun_cfun append_assoc)
  done

lemma reverse_reverse_below:
  "reverse\<cdot>(reverse\<cdot>xs) \<sqsubseteq> xs"
proof (induction xs)
  case (Cons x xs)
  have "reverse\<cdot>(reverse\<cdot>(x:xs)) = reverse\<cdot>(reverse\<cdot>xs ++ [x])" by simp
  also have "\<dots> \<sqsubseteq> reverse\<cdot>[x] ++ reverse\<cdot>(reverse\<cdot>xs)" by (rule reverse_append_below)
  also have "\<dots> = x : reverse\<cdot>(reverse\<cdot>xs)" by simp
  also have "\<dots> \<sqsubseteq> x : xs" by (simp add: Cons)
  finally show ?case .
qed simp+

lemma reverse_append [simp]:
  assumes "finite_list xs"
  shows "reverse\<cdot>(xs ++ ys) = reverse\<cdot>ys ++ reverse\<cdot>xs"
  using assms by (induct xs) simp+

lemma reverse_spine_strict:
  "\<not> finite_list xs \<Longrightarrow> reverse\<cdot>xs = \<bottom>"
  by (auto simp add: reverse.simps foldl_spine_strict)

lemma reverse_finite [simp]:
  assumes "finite_list xs" shows "finite_list (reverse\<cdot>xs)"
  using assms by (induct xs) simp+

lemma reverse_reverse [simp]:
  assumes "finite_list xs" shows "reverse\<cdot>(reverse\<cdot>xs) = xs"
  using assms by (induct xs) simp+

lemma reverse_induct [consumes 1, case_names Nil snoc]:
  "\<lbrakk>finite_list xs; P []; \<And>x xs . finite_list xs \<Longrightarrow> P xs \<Longrightarrow> P (xs ++ [x])\<rbrakk> \<Longrightarrow> P xs"
  apply (subst reverse_reverse [symmetric])
   apply assumption
  apply (rule finite_list.induct[where x = "reverse\<cdot>xs"])
    apply simp+
  done

lemma length_plus_not_0:
  "le\<cdot>1\<cdot>n = TT \<Longrightarrow> le\<cdot>(length\<cdot>xs + n)\<cdot>0 = TT \<Longrightarrow> False"
proof (induct xs arbitrary: n)
  case Nil then show ?case
    by auto (metis Ord_linear_class.le_trans dist_eq_tr(3) le_Integer_numeral_simps(3))
next
  case (Cons x xs)
  from Cons(1) [of "n + 1"] show ?case
    using Cons(2-) by (auto simp: ac_simps dest: le_plus_1)
qed simp+

lemma take_length_plus_1:
  "length\<cdot>xs \<noteq> \<bottom> \<Longrightarrow> take\<cdot>(length\<cdot>xs + 1)\<cdot>(y:ys) = y : take\<cdot>(length\<cdot>xs)\<cdot>ys"
  by (subst take.simps, cases "le\<cdot>(length\<cdot>xs + 1)\<cdot>0")
     (auto, metis (no_types) length_plus_not_0 le_Integer_numeral_simps(4))

lemma le_length_plus:
  "length\<cdot>xs \<noteq> \<bottom> \<Longrightarrow> n \<noteq> \<bottom> \<Longrightarrow> le\<cdot>n\<cdot>(length\<cdot>xs + n) = TT"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  then have "le\<cdot>(n + 1)\<cdot>(length\<cdot>xs + (n + 1)) = TT" by simp
  moreover have "le\<cdot>n\<cdot>(n + 1) = TT" using \<open>n \<noteq> \<bottom>\<close> by (metis le_plus_1 le_refl_Integer)
  ultimately have "le\<cdot>n\<cdot>(length\<cdot>xs + (n + 1)) = TT" by (blast dest: le_trans)
  then show ?case by (simp add: ac_simps)
qed simp+

lemma eq_take_length_isPrefixOf:
  "eq\<cdot>xs\<cdot>(take\<cdot>(length\<cdot>xs)\<cdot>ys) \<sqsubseteq> isPrefixOf\<cdot>xs\<cdot>ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs)
  note IH = this
  show ?case
  proof (cases "length\<cdot>xs = \<bottom>")
    case True then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases ys)
      case bottom
      then show ?thesis using False
        using le_length_plus [of xs 1] by simp
    next
      case Nil then show ?thesis using False by simp
    next
      case (Cons z zs)
      then show ?thesis
        using False and IH [of zs]
        by (simp add: take_length_plus_1 monofun_cfun_arg)
    qed
  qed
qed simp+

end
