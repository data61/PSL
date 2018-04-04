theory HLint
  imports
    "../HOLCF_Prelude"
    "../List_Comprehension"
begin

section \<open>HLint\<close>

text \<open>
  The tool \texttt{hlint} analyses Haskell code and, based on a data base of
  rewrite rules, suggests stylistic improvements to it. We verify
  a number of these rules using our implementation of the Haskell standard
  library.
\<close>

(* -- I/O *)
(*  putStrLn (show x) ==> print x *)
(*  mapM_ putChar ==> putStr *)
(*  hGetChar stdin ==> getChar *)
(*  hGetLine stdin ==> getLine *)
(*  hGetContents stdin ==> getContents *)
(*  hPutChar stdout ==> putChar *)
(*  hPutStr stdout ==> putStr *)
(*  hPutStrLn stdout ==> putStrLn *)
(*  hPrint stdout ==> print *)
(*  hWaitForInput a 0 ==> hReady a *)
(*  hPutStrLn a (show b) ==> hPrint a b *)
(*  hIsEOF stdin ==> isEOF *)
(* -- EXIT *)
(*  exitWith ExitSuccess ==> exitSuccess *)

subsection \<open>Ord\<close>

(*  not (a == b) ==> a /= b where note = "incorrect if either value is NaN" *)
(*  not (a /= b) ==> a == b where note = "incorrect if either value is NaN" *)
(*  not (a >  b) ==> a <= b where note = "incorrect if either value is NaN" *)
(*  not (a >= b) ==> a <  b where note = "incorrect if either value is NaN" *)
(*  not (a <  b) ==> a >= b where note = "incorrect if either value is NaN" *)
(*  not (a <= b) ==> a >  b where note = "incorrect if either value is NaN" *)

(*  compare x y /= GT ==> x <= y *)
(*  compare x y == LT ==> x < y *)
(*  compare x y /= LT ==> x >= y *)
(*  compare x y == GT ==> x > y *)

text \<open>@{verbatim \<open>x == a || x == b || x == c ==> x `elem` [a,b,c]\<close> } \<close>
lemma "(eq\<cdot>(x::'a::Eq_sym)\<cdot>a orelse eq\<cdot>x\<cdot>b orelse eq\<cdot>x\<cdot>c) = elem\<cdot>x\<cdot>[a, b, c]"
  by (auto simp add: eq_sym)

text \<open>@{verbatim \<open> x /= a && x /= b && x /= c ==> x `notElem` [a,b,c]\<close> } \<close>
lemma "(neq\<cdot>(x::'a::Eq_sym)\<cdot>a andalso neq\<cdot>x\<cdot>b andalso neq\<cdot>x\<cdot>c) = notElem\<cdot>x\<cdot>[a, b, c]"
  by (auto simp add: eq_sym)

    (*  compare (f x) (f y) ==> Data.Ord.comparing f x y -- not that great *)
    (*  on compare f ==> Data.Ord.comparing f -- not that great *)
    (* -- READ/SHOW *)
    (*  showsPrec 0 x "" ==> show x *)
    (*  readsPrec 0 ==> reads *)
    (*  showsPrec 0 ==> shows *)
    (*  showIntAtBase 16 intToDigit ==> showHex *)
    (*  showIntAtBase 8 intToDigit ==> showOct *)

subsection \<open>List\<close>

text \<open>@{verbatim \<open> concat (map f x) ==> concatMap f x\<close> } \<close>
lemma "concat\<cdot>(map\<cdot>f\<cdot>x) = concatMap\<cdot>f\<cdot>x"
  by (auto simp add: concatMap_def)

text \<open>@{verbatim \<open> concat [a, b] ==> a ++ b\<close> } \<close>
lemma "concat\<cdot>[a, b] = a ++ b"
  by auto

text \<open>@{verbatim \<open> map f (map g x) ==> map (f . g) x\<close> } \<close>
lemma "map\<cdot>f\<cdot>(map\<cdot>g\<cdot>x) = map\<cdot>(f oo g)\<cdot>x"
  by auto

text \<open>@{verbatim \<open> x !! 0 ==> head x\<close> } \<close>
lemma "x !! 0 = head\<cdot>x"
  by (cases x) auto

text \<open>@{verbatim \<open> take n (repeat x) ==> replicate n x\<close> } \<close>
lemma "take\<cdot>n\<cdot>(repeat\<cdot>x) = replicate\<cdot>n\<cdot>x"
  by (simp add: replicate_def)

text \<open>@{verbatim \<open>lemma "head\<cdot>(reverse\<cdot>x) = last\<cdot>x" \<close> } \<close>
lemma "head\<cdot>(reverse\<cdot>x) = last\<cdot>x"
proof (cases "finite_list x")
  case True then show ?thesis
    by (induct x rule: reverse_induct) (auto simp add: last_append_singleton)
next
  case False then show ?thesis
    by (simp add: last_spine_strict reverse_spine_strict)
qed

text \<open>@{verbatim \<open> head (drop n x) ==> x !! n where note = "if the index is non-negative"\<close> } \<close>
lemma
  assumes "le\<cdot>0\<cdot>n \<noteq> FF"
  shows "head\<cdot>(drop\<cdot>n\<cdot>x) = x !! n"
proof (cases "le\<cdot>0\<cdot>n")
  assume "le\<cdot>0\<cdot>n = FF" with assms show ?thesis..
next
  assume "le\<cdot>0\<cdot>n = TT"
  then show ?thesis
  proof (induction arbitrary: x rule: nonneg_Integer_induct)
    case 0
    show ?case by (cases x) auto
  next
    case (step i x)
    from step.hyps have [simp]:"le\<cdot>i\<cdot>0 = FF" by (cases i, auto simp add: one_Integer_def zero_Integer_def)
    from step.hyps have [simp]:"eq\<cdot>i\<cdot>0 = FF" by (cases i, auto simp add: one_Integer_def zero_Integer_def)
    show ?case
      using step.IH  by (cases x)auto
  qed
qed simp

text \<open>@{verbatim \<open> reverse (tail (reverse x)) ==> init x\<close> } \<close>
lemma "reverse\<cdot>(tail\<cdot>(reverse\<cdot>x)) \<sqsubseteq> init\<cdot>x"
proof (cases "finite_list x")
  case True
  then show ?thesis
    by (induct x rule: reverse_induct) (auto simp add: init_append_singleton)
next
  case False
  then show ?thesis
    by (auto simp add: reverse_spine_strict)
qed

text \<open>@{verbatim \<open> take (length x - 1) x ==> init x\<close> } \<close>
lemma
  assumes "x \<noteq> []"
  shows "take\<cdot>(length\<cdot>x - 1)\<cdot>x \<sqsubseteq> init\<cdot>x"
  using assms
proof (induct x)
  case (Cons y ys)
  show ?case
  proof (cases ys)
    note IH = Cons
    case (Cons z zs)
    show ?thesis
      using IH
      by (cases "length\<cdot>zs")
         (auto simp: Cons one_Integer_def dest: length_ge_0)
  qed (auto simp: one_Integer_def)
qed auto

text \<open>@{verbatim \<open> foldr (++) [] ==> concat\<close> } \<close>
lemma foldr_append_concat:"foldr\<cdot>append\<cdot>[] = concat"
proof (rule cfun_eqI)
  fix xs :: "[['a]]"
  show "foldr\<cdot>append\<cdot>[]\<cdot>xs = concat\<cdot>xs"
    by (induct xs) auto
qed

text \<open>@{verbatim \<open> foldl (++) [] ==> concat\<close> } \<close>
lemma "foldl\<cdot>append\<cdot>[] \<sqsubseteq> concat"
proof (rule cfun_belowI)
  fix xs :: "[['a]]"
  show "foldl\<cdot>append\<cdot>[]\<cdot>xs \<sqsubseteq> concat\<cdot>xs"
    by (cases "finite_list xs")
       (auto simp add: foldr_append_concat foldl_assoc_foldr foldl_spine_strict)
qed

text \<open>@{verbatim \<open> span (not . p) ==> break p\<close> } \<close>
lemma "span\<cdot>(neg oo p) = break\<cdot>p"
  by simp

text \<open>@{verbatim \<open> break (not . p) ==> span p\<close> } \<close>
lemma "break\<cdot>(neg oo p) = span\<cdot>p"
  by (unfold break.simps) (subst assoc_oo, simp)

(*  concatMap (++ "\n") ==> unlines *)

text \<open>@{verbatim \<open> or (map p x) ==> any p x\<close> } \<close>
lemma "the_or\<cdot>(map\<cdot>p\<cdot>x) = any\<cdot>p\<cdot>x"
  by simp

text \<open>@{verbatim \<open> and (map p x) ==> all p x\<close> } \<close>
lemma "the_and\<cdot>(map\<cdot>p\<cdot>x) = all\<cdot>p\<cdot>x"
  by simp

text \<open>@{verbatim \<open> zipWith (,) ==> zip\<close> } \<close>
lemma "zipWith\<cdot>\<langle>,\<rangle> = zip"
  by (simp add: zip_def)

text \<open>@{verbatim \<open> zipWith3 (,,) ==> zip3\<close> } \<close>
lemma "zipWith3\<cdot>\<langle>,,\<rangle> = zip3"
  by (simp add: zip3_def)

text \<open>@{verbatim \<open> length x == 0 ==> null x where note = "increases laziness"\<close> } \<close>
lemma "eq\<cdot>(length\<cdot>x)\<cdot>0 \<sqsubseteq> null\<cdot>x"
proof (cases x)
  case (Cons y ys)
  then show ?thesis
    by (cases "length\<cdot>ys")
       (auto dest: length_ge_0 simp: zero_Integer_def one_Integer_def)
qed simp+

text \<open>@{verbatim \<open> length x /= 0 ==> not (null x)\<close> } \<close>
lemma "neq\<cdot>(length\<cdot>x)\<cdot>0 \<sqsubseteq> neg\<cdot>(null\<cdot>x)"
proof (cases x)
  case (Cons y ys)
  then show ?thesis
    by (cases "length\<cdot>ys")
       (auto dest: length_ge_0 simp: zero_Integer_def one_Integer_def)
qed simp+

(*  (\x -> [x]) ==> (:[]) *)

text \<open>@{verbatim \<open> map (uncurry f) (zip x y) ==> zipWith f x y\<close> } \<close>
lemma "map\<cdot>(uncurry\<cdot>f)\<cdot>(zip\<cdot>x\<cdot>y) = zipWith\<cdot>f\<cdot>x\<cdot>y"
proof (induct x arbitrary: y)
  case (Cons x xs y) then show ?case by (cases y) auto
qed auto

text \<open>@{verbatim \<open> map f (zip x y) ==> zipWith (curry f) x y where _ = isVar f\<close> } \<close>
lemma "map\<cdot>f\<cdot>(zip\<cdot>x\<cdot>y) = zipWith\<cdot>(curry\<cdot>f)\<cdot>x\<cdot>y"
proof(induct x arbitrary: y)
  case (Cons x xs y) then show ?case by (cases y) auto
qed auto

text \<open>@{verbatim \<open> not (elem x y) ==> notElem x y\<close> } \<close>
lemma "neg\<cdot>(elem\<cdot>x\<cdot>y) = notElem\<cdot>x\<cdot>y"
  by (induct y) auto

text \<open>@{verbatim \<open> foldr f z (map g x) ==> foldr (f . g) z x\<close> } \<close>
lemma "foldr\<cdot>f\<cdot>z\<cdot>(map\<cdot>g\<cdot>x) = foldr\<cdot>(f oo g)\<cdot>z\<cdot>x"
  by (induct x) auto

(*  x ++ concatMap (' ':) y ==> unwords (x:y) *)
(*  intercalate " " ==> unwords *)
(*  concat (intersperse x y) ==> intercalate x y where _ = notEq x " " *)
(*  concat (intersperse " " x) ==> unwords x *)
text \<open>@{verbatim \<open> null (filter f x) ==> not (any f x)\<close> } \<close>
lemma "null\<cdot>(filter\<cdot>f\<cdot>x) = neg\<cdot>(any\<cdot>f\<cdot>x)"
proof (induct x)
  case (Cons x xs)
  then show ?case by (cases "f\<cdot>x") auto
qed auto

text \<open>@{verbatim \<open> filter f x == [] ==> not (any f x)\<close> } \<close>
lemma "eq\<cdot>(filter\<cdot>f\<cdot>x)\<cdot>[] = neg\<cdot>(any\<cdot>f\<cdot>x)"
proof (induct x)
  case (Cons x xs)
  then show ?case by (cases "f\<cdot>x") auto
qed auto

text \<open>@{verbatim \<open> filter f x /= [] ==> any f x\<close> } \<close>
lemma "neq\<cdot>(filter\<cdot>f\<cdot>x)\<cdot>[] = any\<cdot>f\<cdot>x"
proof (induct x)
  case (Cons x xs)
  then show ?case by (cases "f\<cdot>x") auto
qed auto

text \<open>@{verbatim \<open> any (== a) ==> elem a\<close> } \<close>
lemma "any\<cdot>(\<Lambda> z. eq\<cdot>z\<cdot>a) = elem\<cdot>a"
proof (rule cfun_eqI)
  fix xs
  show "any\<cdot>(\<Lambda> z. eq\<cdot>z\<cdot>a)\<cdot>xs = elem\<cdot>a\<cdot>xs"
    by (induct xs) auto
qed

text \<open>@{verbatim \<open> any ((==) a) ==> elem a\<close> } \<close>
lemma "any\<cdot>(eq\<cdot>(a::'a::Eq_sym)) = elem\<cdot>a"
proof (rule cfun_eqI)
  fix xs
  show "any\<cdot>(eq\<cdot>a)\<cdot>xs = elem\<cdot>a\<cdot>xs"
    by (induct xs) (auto simp: eq_sym)
qed

text \<open>@{verbatim \<open>any (a ==) ==> elem a\<close> } \<close>
lemma "any\<cdot>(\<Lambda> z. eq\<cdot>(a::'a::Eq_sym)\<cdot>z) = elem\<cdot>a"
proof (rule cfun_eqI)
  fix xs
  show "any\<cdot>(\<Lambda> z. eq\<cdot>a\<cdot>z)\<cdot>xs = elem\<cdot>a\<cdot>xs"
    by (induct xs) (auto simp: eq_sym)
qed

text \<open>@{verbatim \<open> all (/= a) ==> notElem a\<close> } \<close>
lemma "all\<cdot>(\<Lambda> z. neq\<cdot>z\<cdot>(a::'a::Eq_sym)) = notElem\<cdot>a"
proof (rule cfun_eqI)
  fix xs
  show "all\<cdot>(\<Lambda> z. neq\<cdot>z\<cdot>a)\<cdot>xs = notElem\<cdot>a\<cdot>xs"
    by (induct xs) auto
qed

text \<open>@{verbatim \<open> all (a /=) ==> notElem a\<close> } \<close>
lemma "all\<cdot>(\<Lambda> z. neq\<cdot>(a::'a::Eq_sym)\<cdot>z) = notElem\<cdot>a"
proof (rule cfun_eqI)
  fix xs
  show "all\<cdot>(\<Lambda> z. neq\<cdot>a\<cdot>z)\<cdot>xs = notElem\<cdot>a\<cdot>xs"
    by (induct xs) (auto simp: eq_sym)
qed

(* findIndex ((==) a) ==> elemIndex a *)
(* findIndex (a ==) ==> elemIndex a *)
(* findIndex (== a) ==> elemIndex a *)
(* findIndices ((==) a) ==> elemIndices a *)
(* findIndices (a ==) ==> elemIndices a *)
(* findIndices (== a) ==> elemIndices a *)
(* lookup b (zip l [0..]) ==> elemIndex b l *)

subsection \<open>Folds\<close>

(*  foldr  (>>) (return ()) ==> sequence_ *)

text \<open>@{verbatim \<open> foldr  (&&) True ==> and\<close> } \<close>
lemma "foldr\<cdot>trand\<cdot>TT = the_and"
  by (subst the_and.simps, rule)

text \<open>@{verbatim \<open> foldl  (&&) True ==> and\<close> } \<close>
lemma foldl_to_and:"foldl\<cdot>trand\<cdot>TT \<sqsubseteq> the_and"
proof (rule cfun_belowI)
  fix xs
  show "foldl\<cdot>trand\<cdot>TT\<cdot>xs \<sqsubseteq> the_and\<cdot>xs"
    by (cases "finite_list xs") (auto simp: foldl_assoc_foldr foldl_spine_strict)
qed

text \<open>@{verbatim \<open> foldr1 (&&)  ==> and\<close> } \<close>
lemma "foldr1\<cdot>trand \<sqsubseteq> the_and"
proof (rule cfun_belowI)
  fix xs
  show "foldr1\<cdot>trand\<cdot>xs \<sqsubseteq> the_and\<cdot>xs"
  proof (induct xs)
    case (Cons y ys)
    then show ?case by (cases ys) (auto elim: monofun_cfun_arg)
  qed simp+
qed

text \<open>@{verbatim \<open> foldl1 (&&)  ==> and\<close> } \<close>
lemma "foldl1\<cdot>trand \<sqsubseteq> the_and"
proof (rule cfun_belowI)
  fix x
  have "foldl1\<cdot>trand\<cdot>x \<sqsubseteq> foldl\<cdot>trand\<cdot>TT\<cdot>x"
    by (cases x, auto)
  also have "... \<sqsubseteq> the_and\<cdot>x"
    by (rule monofun_cfun_fun[OF foldl_to_and])
  finally show "foldl1\<cdot>trand\<cdot>x \<sqsubseteq> the_and\<cdot>x" .
qed

text \<open>@{verbatim \<open> foldr  (||) False ==> or\<close> } \<close>
lemma "foldr\<cdot>tror\<cdot>FF = the_or"
  by (subst the_or.simps, rule)

text \<open>@{verbatim \<open> foldl  (||) False ==> or\<close> } \<close>
lemma foldl_to_or: "foldl\<cdot>tror\<cdot>FF \<sqsubseteq> the_or"
proof (rule cfun_belowI)
  fix xs
  show "foldl\<cdot>tror\<cdot>FF\<cdot>xs \<sqsubseteq> the_or\<cdot>xs"
    by (cases "finite_list xs") (auto simp: foldl_assoc_foldr foldl_spine_strict)
qed

text \<open>@{verbatim \<open> foldr1 (||)  ==> or\<close> } \<close>
lemma "foldr1\<cdot>tror \<sqsubseteq> the_or"
proof (rule cfun_belowI)
  fix xs
  show "foldr1\<cdot>tror\<cdot>xs \<sqsubseteq> the_or\<cdot>xs"
  proof (induct xs)
    case (Cons y ys)
    then show ?case by (cases ys) (auto elim: monofun_cfun_arg)
  qed simp+
qed

text \<open>@{verbatim \<open> foldl1 (||)  ==> or\<close> } \<close>
lemma "foldl1\<cdot>tror \<sqsubseteq> the_or"
proof(rule cfun_belowI)
  fix x
  have "foldl1\<cdot>tror\<cdot>x \<sqsubseteq> foldl\<cdot>tror\<cdot>FF\<cdot>x"
    by (cases x, auto)
  also have "... \<sqsubseteq> the_or\<cdot>x"
    by (rule monofun_cfun_fun[OF foldl_to_or])
  finally show "foldl1\<cdot>tror\<cdot>x \<sqsubseteq> the_or\<cdot>x" .
qed

(*  foldl  (+) 0 ==> sum *)
(*  foldr  (+) 0 ==> sum *)
(*  foldl1 (+)   ==> sum *)
(*  foldr1 (+)   ==> sum *)
(*  foldl  ( * ) 1 ==> product *)
(*  foldr  ( * ) 1 ==> product *)
(*  foldl1 ( * )   ==> product *)
(*  foldr1 ( * )   ==> product *)
(*  foldl1 max   ==> maximum *)
(*  foldr1 max   ==> maximum *)
(*  foldl1 min   ==> minimum *)
(*  foldr1 min   ==> minimum *)
(*  foldr mplus mzero ==> msum *)

subsection \<open>Function\<close>
text \<open>@{verbatim \<open> (\x -> x) ==> id\<close> } \<close>
lemma "(\<Lambda> x. x) = ID"
  by (metis ID_def)

text \<open>@{verbatim \<open> (\x y -> x) ==> const\<close> } \<close>
lemma "(\<Lambda> x y. x) = const"
  by (intro cfun_eqI) simp

text \<open>@{verbatim \<open>(\(x,y) -> y) ==> fst where _ = notIn x y\<close> } \<close>
lemma "(\<Lambda> \<langle>x, y\<rangle>. x) = fst"
proof (rule cfun_eqI)
  fix p
  show "(case p of \<langle>x, y\<rangle> \<Rightarrow> x) = fst \<cdot> p"
  proof (cases p)
    case bottom then show ?thesis by simp
  next
    case Tuple2 then show ?thesis by simp
  qed
qed

text \<open>@{verbatim \<open>(\(x,y) -> y) ==> snd where _ = notIn x y\<close> } \<close>
lemma "(\<Lambda> \<langle>x, y\<rangle>. y) = snd"
proof (rule cfun_eqI)
  fix p
  show "(case p of \<langle>x, y\<rangle> \<Rightarrow> y) = snd \<cdot> p"
  proof (cases p)
    case bottom then show ?thesis by simp
  next
    case Tuple2 then show ?thesis by simp
  qed
qed

text \<open>@{verbatim \<open> (\x y-> f (x,y)) ==> curry f where _ = notIn [x,y] f\<close> } \<close>
lemma "(\<Lambda> x y. f\<cdot>\<langle>x, y\<rangle>) = curry\<cdot>f"
  by (auto intro!: cfun_eqI)

text \<open>@{verbatim \<open> (\(x,y) -> f x y) ==> uncurry f where _ = notIn [x,y] f\<close> } \<close>
lemma "(\<Lambda> \<langle>x, y\<rangle>. f\<cdot>x\<cdot>y) \<sqsubseteq> uncurry\<cdot>f"
  by (rule cfun_belowI, rename_tac x, case_tac x, auto)

(*  (($) . f) ==> f *)
(*  (f $) ==> f *)

text \<open>@{verbatim \<open> (\x -> y) ==> const y where _ = isAtom y && notIn x y\<close> } \<close>
lemma "(\<Lambda> x. y) = const\<cdot>y"
  by (intro cfun_eqI) simp

(*  flip f x y ==> f y x where _ = isApp original *)
lemma "flip\<cdot>f\<cdot>x\<cdot>y = f\<cdot>y\<cdot>x" by simp

(*  (\a b -> o (f a) (f b)) ==> o `Data.Function.on` f *)
(* -- CHAR *)
(*  a >= 'a' && a <= 'z' ==> isAsciiLower a *)
(*  a >= 'A' && a <= 'Z' ==> isAsciiUpper a *)
(*  a >= '0' && a <= '9' ==> isDigit a *)
(*  a >= '0' && a <= '7' ==> isOctDigit a *)
(*  not (isControl a) ==> isPrint a *)
(*  isLower a || isUpper a ==> isAlpha a *)
(*  isAlpha a || isDigit a ==> isAlphaNum a *)

subsection \<open>Bool\<close>

text \<open>@{verbatim \<open> a == True ==> a\<close> } \<close>
lemma eq_true:"eq\<cdot>x\<cdot>TT = x"
  by (cases x, auto)

text \<open>@{verbatim \<open> a == False ==> not a\<close> } \<close>
lemma eq_false:"eq\<cdot>x\<cdot>FF = neg\<cdot>x"
  by (cases x, auto)

text \<open>@{verbatim \<open> (if a then x else x) ==> x where note = "reduces strictness"\<close> } \<close>
lemma if_equal:"(If a then x else x) \<sqsubseteq> x"
  by (cases a, auto)

text \<open>@{verbatim \<open> (if a then True else False) ==> a\<close> } \<close>
lemma "(If a then TT else FF) = a"
  by (cases a, auto)

text \<open>@{verbatim \<open> (if a then False else True) ==> not a\<close> } \<close>
lemma "(If a then FF else TT) = neg\<cdot>a"
  by (cases a, auto)

text \<open>@{verbatim \<open> (if a then t else (if b then t else f)) ==> if a || b then t else f\<close> } \<close>
lemma "(If a then t else (If b then t else f)) = (If a orelse b then t else f)"
  by (cases a, auto)

text \<open>@{verbatim \<open> (if a then (if b then t else f) else f) ==> if a && b then t else f\<close> } \<close>
lemma "(If a then (If b then t else f) else f) = (If a andalso b then t else f)"
  by (cases a, auto)

text \<open>@{verbatim \<open> (if x then True else y) ==> x || y where _ = notEq y False\<close> } \<close>
lemma "(If x then TT else y) = (x orelse y)"
  by (cases x, auto)

text \<open>@{verbatim \<open> (if x then y else False) ==> x && y where _ = notEq y True\<close> } \<close>
lemma "(If x then y else FF) = (x andalso y)"
  by (cases x, auto)

(*  case a of {True -> t; False -> f} ==> if a then t else f *)
(*  case a of {False -> f; True -> t} ==> if a then t else f *)
(*  case a of {True -> t; _ -> f} ==> if a then t else f *)
(*  case a of {False -> f; _ -> t} ==> if a then t else f *)
text \<open>@{verbatim \<open> (if c then (True, x) else (False, x)) ==> (c, x) where note = "reduces strictness"\<close> } \<close>
lemma "(If c then \<langle>TT, x\<rangle> else \<langle>FF, x\<rangle>) \<sqsubseteq> \<langle>c, x\<rangle>"
  by (cases c, auto)

text \<open>@{verbatim \<open> (if c then (False, x) else (True, x)) ==> (not c, x) where note = "reduces strictness"\<close> } \<close>
lemma "(If c then \<langle>FF, x\<rangle> else \<langle>TT, x\<rangle>) \<sqsubseteq> \<langle>neg\<cdot>c, x\<rangle>"
  by (cases c, auto)

text \<open>@{verbatim \<open> or [x,y]  ==> x || y\<close> } \<close>
lemma "the_or\<cdot>[x, y] = (x orelse y)"
  by (fixrec_simp)

text \<open>@{verbatim \<open> or [x,y,z]  ==> x || y || z\<close> } \<close>
lemma "the_or\<cdot>[x, y, z] = (x orelse y orelse z)"
  by (fixrec_simp)

text \<open>@{verbatim \<open> and [x,y]  ==> x && y\<close> } \<close>
lemma "the_and\<cdot>[x, y] = (x andalso y)"
  by (fixrec_simp)

text \<open>@{verbatim \<open> and [x,y,z]  ==> x && y && z\<close> } \<close>
lemma "the_and\<cdot>[x, y, z] = (x andalso y andalso z)"
  by (fixrec_simp)

subsection \<open>Arrow\<close>

(*  id *** g ==> second g *)
(*  f *** id ==> first f *)
(*  zip (map f x) (map g x) ==> map (f Control.Arrow.&&& g) x *)
(*  (\(x,y) -> (f x, g y)) ==> f Control.Arrow.*** g where _ = notIn [x,y] [f,g] *)
(*  (\x -> (f x, g x)) ==> f Control.Arrow.&&& g where _ = notIn x [f,g] *)
(*  (\(x,y) -> (f x,y)) ==> Control.Arrow.first f where _ = notIn [x,y] f *)
(*  (\(x,y) -> (x,f y)) ==> Control.Arrow.second f where _ = notIn [x,y] f *)
(*  (f (fst x), g (snd x)) ==> (f Control.Arrow.*** g) x *)

text \<open>@{verbatim \<open> (fst x, snd x) ==>  x\<close> } \<close>
lemma "x \<sqsubseteq> \<langle>fst\<cdot>x, snd\<cdot>x\<rangle>"
  by (cases x, auto)

(* -- FUNCTOR *)
(*  fmap f (fmap g x) ==> fmap (f . g) x *)
(*  fmap id ==> id *)
(* -- MONAD *)
(*  return a >>= f ==> f a *)
(*  m >>= return ==> m *)
(*  m >>= return . f ==> Control.Monad.liftM f m -- cannot be fmap, because is in Functor not Monad *)
(*  (if x then y else return ()) ==> Control.Monad.when x $ _noParen_ y where _ = not (isAtom y) *)
(*  (if x then y else return ()) ==> Control.Monad.when x y where _ = isAtom y *)
(*  (if x then return () else y) ==> Control.Monad.unless x $ _noParen_ y where _ = not (isAtom y) *)
(*  (if x then return () else y) ==> Control.Monad.unless x y where _ = isAtom y *)
(*  sequence (map f x) ==> mapM f x *)
(*  sequence_ (map f x) ==> mapM_ f x *)
(*  flip mapM ==> Control.Monad.forM *)
(*  flip mapM_ ==> Control.Monad.forM_ *)
(*  flip forM ==> mapM *)
(*  flip forM_ ==> mapM_ *)
(*  when (not x) ==> unless x *)
(*  x >>= id ==> Control.Monad.join x *)
(*  liftM f (liftM g x) ==> liftM (f . g) x *)
(*  a >> return () ==> void a *)
(*  fmap (const ()) ==> void *)
(*  flip (>=>) ==> (<=<) *)
(*  flip (<=<) ==> (>=>) *)
(*  (\x -> f x >>= g) ==> f Control.Monad.>=> g where _ = notIn x [f,g] *)
(*  (\x -> f =<< g x) ==> f Control.Monad.<=< g where _ = notIn x [f,g] *)
(*  a >> forever a ==> forever a *)
(*  liftM2 id ==> ap *)
(* -- MONAD LIST *)
(*  liftM unzip (mapM f x) ==> Control.Monad.mapAndUnzipM f x *)
(*  sequence (zipWith f x y) ==> Control.Monad.zipWithM f x y *)
(*  sequence_ (zipWith f x y) ==> Control.Monad.zipWithM_ f x y *)
(*  sequence (replicate n x) ==> Control.Monad.replicateM n x *)
(*  sequence_ (replicate n x) ==> Control.Monad.replicateM_ n x *)
(*  mapM f (map g x) ==> mapM (f . g) x *)
(*  mapM_ f (map g x) ==> mapM_ (f . g) x *)
(* -- APPLICATIVE / TRAVERSABLE *)
(*  flip traverse ==> for *)
(*  flip for ==> traverse *)
(*  flip traverse_ ==> for_ *)
(*  flip for_ ==> traverse_ *)
(*  foldr ( *>) (pure ()) ==> sequenceA_ *)
(*  foldr (<|>) empty ==> asum *)
(*  liftA2 (flip ($)) ==> (<**>) *)
(*  Just <$> a <|> pure Nothing ==> optional a *)
(* -- LIST COMP *)
(*  (if b then [x] else []) ==> [x | b] *)
(*  [x | x <- y] ==> y where _ = isVar x *)
(* -- SEQ *)

subsection \<open>Seq\<close>

text \<open>@{verbatim \<open> x `seq` x ==> x\<close> } \<close>
lemma "seq\<cdot>x\<cdot>x = x" by (simp add: seq_def)

(*  id $! x ==> x *)
(*  x `seq` y ==> y where _ = isWHNF x *)
(*  f $! x ==> f x where _ = isWHNF x *)
(*  evaluate x ==> return x where _ = isWHNF x *)
(* -- MAYBE *)
(*  maybe x id ==> Data.Maybe.fromMaybe x *)
(*  maybe False (const True) ==> Data.Maybe.isJust *)
(*  maybe True (const False) ==> Data.Maybe.isNothing *)
(*  not (isNothing x) ==> isJust x *)
(*  not (isJust x) ==> isNothing x *)
(*  maybe [] (:[]) ==> maybeToList *)
(*  catMaybes (map f x) ==> mapMaybe f x *)
(*  (case x of Nothing -> y; Just a -> a)  ==> fromMaybe y x *)
(*  (if isNothing x then y else f (fromJust x)) ==> maybe y f x *)
(*  (if isJust x then f (fromJust x) else y) ==> maybe y f x *)
(*  maybe Nothing (Just . f) ==> fmap f *)
(*  map fromJust . filter isJust  ==>  Data.Maybe.catMaybes *)
(*  x == Nothing  ==>  isNothing x *)
(*  Nothing == x  ==>  isNothing x *)
(*  x /= Nothing  ==>  Data.Maybe.isJust x *)
(*  Nothing /= x  ==>  Data.Maybe.isJust x *)
(*  concatMap (maybeToList . f) ==> Data.Maybe.mapMaybe f *)
(*  concatMap maybeToList ==> catMaybes *)
(*  maybe n Just x ==> Control.Monad.mplus x n *)
(*  (case x of Just a -> a; Nothing -> y)  ==> fromMaybe y x *)
(*  (if isNothing x then y else fromJust x) ==> fromMaybe y x *)
(*  (if isJust x then fromJust x else y) ==> fromMaybe y x *)
(*  isJust x && (fromJust x == y) ==> x == Just y *)
(*  mapMaybe f (map g x) ==> mapMaybe (f . g) x *)
(*  fromMaybe a (fmap f x) ==> maybe a f x *)
(*  [x | Just x <- a] ==> Data.Maybe.catMaybes a *)
(* -- EITHER *)
(*  [a | Left a <- a] ==> lefts a *)
(*  [a | Right a <- a] ==> rights a *)
(* -- INFIX *)
(*  X.elem x y ==> x `X.elem` y where _ = not (isInfixApp original) && not (isParen result) *)
(*  X.notElem x y ==> x `X.notElem` y where _ = not (isInfixApp original) && not (isParen result) *)
(*  X.isInfixOf x y ==> x `X.isInfixOf` y where _ = not (isInfixApp original) && not (isParen result) *)
(*  X.isSuffixOf x y ==> x `X.isSuffixOf` y where _ = not (isInfixApp original) && not (isParen result) *)
(*  X.isPrefixOf x y ==> x `X.isPrefixOf` y where _ = not (isInfixApp original) && not (isParen result) *)
(*  X.union x y ==> x `X.union` y where _ = not (isInfixApp original) && not (isParen result) *)
(*  X.intersect x y ==> x `X.intersect` y where _ = not (isInfixApp original) && not (isParen result) *)
(* -- MATHS *)
(*  fromIntegral x ==> x where _ = isLitInt x *)
(*  fromInteger x ==> x where _ = isLitInt x *)
(*  x + negate y ==> x - y *)
(*  0 - x ==> negate x *)
(*  log y / log x ==> logBase x y *)
(*  x ** 0.5 ==> sqrt x *)
(*  sin x / cos x ==> tan x *)
(*  sinh x / cosh x ==> tanh x *)
(*  n `rem` 2 == 0 ==> even n *)
(*  n `rem` 2 /= 0 ==> odd n *)
(*  not (even x) ==> odd x *)
(*  not (odd x) ==> even x *)
(*  x ** 0.5 ==> sqrt x *)
(*  x ^^ y ==> x ** y where _ = isLitInt y *)
(*  x ^ 0 ==> 1 *)
(*  round (x - 0.5) ==> floor x *)
(* -- CONCURRENT *)
(*  mapM_ (writeChan a) ==> writeList2Chan a *)
(* -- EXCEPTION *)
(*  Prelude.catch ==> Control.Exception.catch where note = "Prelude.catch does not catch most exceptions" *)
(*  flip Control.Exception.catch ==> handle *)
(*  flip handle ==> Control.Exception.catch *)
(*  flip (catchJust p) ==> handleJust p *)
(*  flip (handleJust p) ==> catchJust p *)
(*  Control.Exception.bracket b (const a) (const t) ==> Control.Exception.bracket_ b a t *)
(*  Control.Exception.bracket (openFile x y) hClose ==> withFile x y *)
(*  Control.Exception.bracket (openBinaryFile x y) hClose ==> withBinaryFile x y *)
(*  throw (ErrorCall a) ==> error a *)
(*  a `seq` return a ==> Control.Exception.evaluate a *)
(*  toException NonTermination ==> nonTermination *)
(*  toException NestedAtomically ==> nestedAtomically *)
(* -- WEAK POINTERS *)
(*  mkWeak a a b ==> mkWeakPtr a b *)
(*  mkWeak a (a, b) c ==> mkWeakPair a b c *)

subsection \<open>Evaluate\<close>

text \<open>@{verbatim \<open> True && x ==> x\<close> } \<close>
lemma "(TT andalso x) = x" by auto

text \<open>@{verbatim \<open> False && x ==> False\<close> } \<close>
lemma "(FF andalso x) = FF" by auto

text \<open>@{verbatim \<open> True || x ==> True\<close> } \<close>
lemma "(TT orelse x) = TT" by auto

text \<open>@{verbatim \<open> False || x ==> x\<close> } \<close>
lemma "(FF orelse x) = x" by auto

text \<open>@{verbatim \<open> not True ==> False\<close> } \<close>
lemma "neg\<cdot>TT = FF" by auto

text \<open>@{verbatim \<open> not False ==> True\<close> } \<close>
lemma "neg\<cdot>FF = TT" by auto

(*  Nothing >>= k ==> Nothing *)
(*  either f g (Left x) ==> f x *)
(*  either f g (Right y) ==> g y *)
text \<open>@{verbatim \<open> fst (x,y) ==> x\<close> } \<close>
lemma "fst\<cdot>\<langle>x, y\<rangle> = x" by auto

text \<open>@{verbatim \<open> snd (x,y) ==> y\<close> } \<close>
lemma "snd\<cdot>\<langle>x, y\<rangle> = y" by auto

text \<open>@{verbatim \<open> f (fst p) (snd p) ==> uncurry f p\<close> } \<close>
lemma "f\<cdot>(fst\<cdot>p)\<cdot>(snd\<cdot>p) = uncurry\<cdot>f\<cdot>p"
  by (cases p, auto)

text \<open>@{verbatim \<open> init [x] ==> []\<close> } \<close>
lemma "init\<cdot>[x] = []" by auto

text \<open>@{verbatim \<open> null [] ==> True\<close> } \<close>
lemma "null\<cdot>[] = TT" by auto

text \<open>@{verbatim \<open> length [] ==> 0\<close> } \<close>
lemma "length\<cdot>[] = 0" by auto

text \<open>@{verbatim \<open> foldl f z [] ==> z\<close> } \<close>
lemma "foldl\<cdot>f\<cdot>z\<cdot>[] = z" by simp

text \<open>@{verbatim \<open> foldr f z [] ==> z\<close> } \<close>
lemma "foldr\<cdot>f\<cdot>z\<cdot>[] = z" by auto

text \<open>@{verbatim \<open> foldr1 f [x] ==> x\<close> } \<close>
lemma "foldr1\<cdot>f\<cdot>[x] = x" by simp

text \<open>@{verbatim \<open> scanr f z [] ==> [z]\<close> } \<close>
lemma "scanr\<cdot>f\<cdot>z\<cdot>[] = [z]" by simp

text \<open>@{verbatim \<open> scanr1 f [] ==> []\<close> } \<close>
lemma "scanr1\<cdot>f\<cdot>[] = []" by simp

text \<open>@{verbatim \<open> scanr1 f [x] ==> [x]\<close> } \<close>
lemma "scanr1\<cdot>f\<cdot>[x] = [x]" by simp

text \<open>@{verbatim \<open> take n [] ==> []\<close> } \<close>
lemma "take\<cdot>n\<cdot>[] \<sqsubseteq> []" by (cases n, auto)

text \<open>@{verbatim \<open> drop n [] ==> []\<close> } \<close>
lemma "drop\<cdot>n\<cdot>[] \<sqsubseteq> []"
  by (subst drop.simps) (auto simp: if_equal)

text \<open>@{verbatim \<open> takeWhile p [] ==> []\<close> } \<close>
lemma "takeWhile\<cdot>p\<cdot>[] = []" by (fixrec_simp)

text \<open>@{verbatim \<open> dropWhile p [] ==> []\<close> } \<close>
lemma "dropWhile\<cdot>p\<cdot>[] = []" by (fixrec_simp)

text \<open>@{verbatim \<open> span p [] ==> ([],[])\<close> } \<close>
lemma "span\<cdot>p\<cdot>[] = \<langle>[], []\<rangle>" by (fixrec_simp)

(*  lines "" ==> [] *)
(*  unwords [] ==> "" *)
(*  x - 0 ==> x *)
(*  x * 1 ==> x *)
(*  x / 1 ==> x *)
text \<open>@{verbatim \<open> concat [a] ==> a\<close> } \<close>
lemma "concat\<cdot>[a] = a" by auto

text \<open>@{verbatim \<open> concat [] ==> []\<close> } \<close>
lemma "concat\<cdot>[] = []" by auto

text \<open>@{verbatim \<open> zip [] [] ==> []\<close> } \<close>
lemma "zip\<cdot>[]\<cdot>[] = []" by auto

text \<open>@{verbatim \<open> id x ==> x\<close> } \<close>
lemma "ID\<cdot>x = x" by auto

text \<open>@{verbatim \<open> const x y ==> x\<close> } \<close>
lemma "const\<cdot>x\<cdot>y = x" by simp

subsection \<open>Complex hints\<close>

text \<open>@{verbatim \<open> take (length t) s == t ==> t `Data.List.isPrefixOf` s\<close> } \<close>
lemma
  fixes t :: "['a::Eq_sym]"
  shows "eq\<cdot>(take\<cdot>(length\<cdot>t)\<cdot>s)\<cdot>t \<sqsubseteq> isPrefixOf\<cdot>t\<cdot>s"
  by (subst eq_sym) (rule eq_take_length_isPrefixOf)

text \<open>@{verbatim \<open> (take i s == t) ==> _eval_ ((i >= length t) && (t `Data.List.isPrefixOf` s))\<close> } \<close>
text \<open>The hint is not true in general, as the following two lemmas show:\<close>
lemma
  assumes "t = []" and "s = x : xs" and "i = 1"
  shows "\<not> (eq\<cdot>(take\<cdot>i\<cdot>s)\<cdot>t \<sqsubseteq> (le\<cdot>(length\<cdot>t)\<cdot>i andalso isPrefixOf\<cdot>t\<cdot>s))"
  using assms by simp

lemma
  assumes "le\<cdot>0\<cdot>i = TT" and "le\<cdot>i\<cdot>0 = FF"
    and "s = \<bottom>" and "t = []"
  shows "\<not> ((le\<cdot>(length\<cdot>t)\<cdot>i andalso isPrefixOf\<cdot>t\<cdot>s) \<sqsubseteq> eq\<cdot>(take\<cdot>i\<cdot>s)\<cdot>t)"
  using assms by (subst take.simps) simp

(* -- clever hint, but not actually a good idea *)
(*  (do a <- f; g a) ==> f >>= g *)
(*  a $$$$ b $$$$ c ==> a . b $$$$$ c *)

(* not (a == b) ==> a /= b *)
lemma "neg\<cdot>(eq\<cdot>a\<cdot>b) = neq\<cdot>a\<cdot>b" by auto

text \<open>@{verbatim \<open>not (a /= b) ==> a == b\<close> } \<close>
lemma "neg\<cdot>(neq\<cdot>a\<cdot>b) = eq\<cdot>a\<cdot>b" by auto

text \<open>@{verbatim \<open>map id ==> id\<close> } \<close>
lemma map_id:"map\<cdot>ID = ID" by (auto simp add: cfun_eq_iff)

text \<open>@{verbatim \<open>x == [] ==> null x\<close> } \<close>
lemma "eq\<cdot>x\<cdot>[] = null\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>any id ==> or\<close> } \<close>
lemma "any\<cdot>ID = the_or" by (auto simp add:map_id)

text \<open>@{verbatim \<open>all id ==> and\<close> } \<close>
lemma "all\<cdot>ID = the_and" by (auto simp add:map_id)

text \<open>@{verbatim \<open>(if x then False else y) ==> (not x && y)\<close> } \<close>
lemma "(If x then FF else y) = (neg\<cdot>x andalso y)" by (cases x, auto)

text \<open>@{verbatim \<open>(if x then y else True) ==> (not x || y)\<close> } \<close>
lemma "(If x then y else TT) = (neg\<cdot>x orelse y)" by (cases x, auto)

text \<open>@{verbatim \<open>not (not x) ==> x\<close> } \<close>
lemma "neg\<cdot>(neg\<cdot>x) = x" by auto

text \<open>@{verbatim \<open>(if c then f x else f y) ==> f (if c then x else y)\<close> } \<close>
lemma "(If c then f\<cdot>x else f\<cdot>y) \<sqsubseteq> f\<cdot>(If c then x else y)" by (cases c, auto)

text \<open>@{verbatim \<open>(\ x -> [x]) ==> (: [])\<close> } \<close>
lemma "(\<Lambda> x. [x]) = (\<Lambda> z. z : [])" by auto

text \<open>@{verbatim \<open>True == a ==> a\<close> } \<close>
lemma "eq\<cdot>TT\<cdot>a = a" by (cases a, auto)

text \<open>@{verbatim \<open>False == a ==> not a\<close> } \<close>
lemma "eq\<cdot>FF\<cdot>a = neg\<cdot>a" by (cases a, auto)

text \<open>@{verbatim \<open>a /= True ==> not a\<close> } \<close>
lemma "neq\<cdot>a\<cdot>TT = neg\<cdot>a" by (cases a, auto)

text \<open>@{verbatim \<open>a /= False ==> a\<close> } \<close>
lemma "neq\<cdot>a\<cdot>FF = a" by (cases a, auto)

text \<open>@{verbatim \<open>True /= a ==> not a\<close> } \<close>
lemma "neq\<cdot>TT\<cdot>a = neg\<cdot>a" by (cases a, auto)

text \<open>@{verbatim \<open>False /= a ==> a\<close> } \<close>
lemma "neq\<cdot>FF\<cdot>a = a" by (cases a, auto)

text \<open>@{verbatim \<open>not (isNothing x) ==> isJust x\<close> } \<close>
lemma "neg\<cdot>(isNothing\<cdot>x) = isJust\<cdot>x" by auto

text \<open>@{verbatim \<open>not (isJust x) ==> isNothing x\<close> } \<close>
lemma "neg\<cdot>(isJust\<cdot>x) = isNothing\<cdot>x" by auto

text \<open>@{verbatim \<open>x == Nothing ==> isNothing x\<close> } \<close>
lemma "eq\<cdot>x\<cdot>Nothing = isNothing\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>Nothing == x ==> isNothing x\<close> } \<close>
lemma "eq\<cdot>Nothing\<cdot>x = isNothing\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>x /= Nothing ==> Data.Maybe.isJust x\<close> } \<close>
lemma "neq\<cdot>x\<cdot>Nothing = isJust\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>Nothing /= x ==> Data.Maybe.isJust x\<close> } \<close>
lemma "neq\<cdot>Nothing\<cdot>x = isJust\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>(if isNothing x then y else fromJust x) ==> fromMaybe y x\<close> } \<close>
lemma "(If isNothing\<cdot>x then y else fromJust\<cdot>x) = fromMaybe\<cdot>y\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>(if isJust x then fromJust x else y) ==> fromMaybe y x\<close> } \<close>
lemma "(If isJust\<cdot>x then fromJust\<cdot>x else y) = fromMaybe\<cdot>y\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>(isJust x && (fromJust x == y)) ==> x == Just y\<close> } \<close>
lemma "(isJust\<cdot>x andalso (eq\<cdot>(fromJust\<cdot>x)\<cdot>y)) = eq\<cdot>x\<cdot>(Just\<cdot>y)" by (cases x, auto)

text \<open>@{verbatim \<open>elem True ==> or\<close> } \<close>
lemma "elem\<cdot>TT = the_or"
proof (rule cfun_eqI)
  fix xs
  show "elem\<cdot>TT\<cdot>xs = the_or\<cdot>xs"
    by (induct xs) (auto simp: eq_true)
qed

text \<open>@{verbatim \<open>notElem False ==> and\<close> } \<close>
lemma "notElem\<cdot>FF = the_and"
proof (rule cfun_eqI)
  fix xs
  show "notElem\<cdot>FF\<cdot>xs = the_and\<cdot>xs"
    by (induct xs) (auto simp: eq_false)
qed

text \<open>@{verbatim \<open>all ((/=) a) ==> notElem a\<close> } \<close>
lemma "all\<cdot>(neq\<cdot>(a::'a::Eq_sym)) = notElem\<cdot>a"
proof (rule cfun_eqI)
  fix xs
  show "all\<cdot>(neq\<cdot>a)\<cdot>xs = notElem\<cdot>a\<cdot>xs"
    by (induct xs) (auto simp: eq_sym)
qed

text \<open>@{verbatim \<open>maybe x id ==> Data.Maybe.fromMaybe x\<close> } \<close>
lemma "maybe\<cdot>x\<cdot>ID = fromMaybe\<cdot>x"
proof (rule cfun_eqI)
  fix xs
  show "maybe\<cdot>x\<cdot>ID\<cdot>xs = fromMaybe\<cdot>x\<cdot>xs"
    by (cases xs) auto
qed

text \<open>@{verbatim \<open>maybe False (const True) ==> Data.Maybe.isJust\<close> } \<close>
lemma "maybe\<cdot>FF\<cdot>(const\<cdot>TT) = isJust"
proof (rule cfun_eqI)
  fix x :: "'a Maybe"
  show "maybe\<cdot>FF\<cdot>(const\<cdot>TT)\<cdot>x = isJust\<cdot>x"
    by (cases x) simp+
qed

text \<open>@{verbatim \<open>maybe True (const False) ==> Data.Maybe.isNothing\<close> } \<close>
lemma "maybe\<cdot>TT\<cdot>(const\<cdot>FF) = isNothing"
proof (rule cfun_eqI)
  fix x :: "'a Maybe"
  show "maybe\<cdot>TT\<cdot>(const\<cdot>FF)\<cdot>x = isNothing\<cdot>x"
    by (cases x) simp+
qed

text \<open>@{verbatim \<open>maybe [] (: []) ==> maybeToList\<close> } \<close>
lemma "maybe\<cdot>[]\<cdot>(\<Lambda> z. z : []) = maybeToList"
proof (rule cfun_eqI)
  fix x :: "'a Maybe"
  show "maybe\<cdot>[]\<cdot>(\<Lambda> z. z : [])\<cdot>x = maybeToList\<cdot>x"
    by (cases x) simp+
qed

text \<open>@{verbatim \<open>catMaybes (map f x) ==> mapMaybe f x\<close> } \<close>
lemma "catMaybes\<cdot>(map\<cdot>f\<cdot>x) = mapMaybe\<cdot>f\<cdot>x" by auto

text \<open>@{verbatim \<open>(if isNothing x then y else f (fromJust x)) ==> maybe y f x\<close> } \<close>
lemma "(If isNothing\<cdot>x then y else f\<cdot>(fromJust\<cdot>x)) = maybe\<cdot>y\<cdot>f\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>(if isJust x then f (fromJust x) else y) ==> maybe y f x\<close> } \<close>
lemma "(If isJust\<cdot>x then f\<cdot>(fromJust\<cdot>x) else y) = maybe\<cdot>y\<cdot>f\<cdot>x" by (cases x, auto)

text \<open>@{verbatim \<open>(map fromJust . filter isJust) ==> Data.Maybe.catMaybes\<close> } \<close>
lemma "(map\<cdot>fromJust oo filter\<cdot>isJust) = catMaybes"
proof (rule cfun_eqI)
  fix xs :: "['a Maybe]"
  show "(map\<cdot>fromJust oo filter\<cdot>isJust)\<cdot>xs = catMaybes\<cdot>xs"
  proof (induct xs)
    case (Cons y ys)
    then show ?case by (cases y) simp+
  qed simp+
qed

text \<open>@{verbatim \<open>concatMap (maybeToList . f) ==> Data.Maybe.mapMaybe f\<close> } \<close>
lemma "concatMap\<cdot>(maybeToList oo f) = mapMaybe\<cdot>f"
proof (rule cfun_eqI)
  fix xs
  show "concatMap\<cdot>(maybeToList oo f)\<cdot>xs = mapMaybe\<cdot>f\<cdot>xs"
    by (induct xs) auto
qed

text \<open>@{verbatim \<open>concatMap maybeToList ==> catMaybes\<close> } \<close>
lemma "concatMap\<cdot>maybeToList = catMaybes" by auto

text \<open>@{verbatim \<open>mapMaybe f (map g x) ==> mapMaybe (f . g) x\<close> } \<close>
lemma "mapMaybe\<cdot>f\<cdot>(map\<cdot>g\<cdot>x) = mapMaybe\<cdot>(f oo g)\<cdot>x" by auto

text \<open>@{verbatim \<open>(($) . f) ==> f\<close> } \<close>
lemma "(dollar oo f) = f" by (auto simp add:cfun_eq_iff)

text \<open>@{verbatim \<open>(f $) ==> f\<close> } \<close>
lemma "(\<Lambda> z. dollar\<cdot>f\<cdot>z) = f" by (auto simp add:cfun_eq_iff)

text \<open>@{verbatim \<open>(\ a b -> g (f a) (f b)) ==> g `Data.Function.on` f\<close> } \<close>
lemma "(\<Lambda> a b. g\<cdot>(f\<cdot>a)\<cdot>(f\<cdot>b)) = on\<cdot>g\<cdot>f" by (auto simp add:cfun_eq_iff)

text \<open>@{verbatim \<open>id $! x ==> x\<close> } \<close>
lemma "dollarBang\<cdot>ID\<cdot>x = x" by (auto simp add:seq_def)

text \<open>@{verbatim \<open>[x | x <- y] ==> y\<close> } \<close>
lemma "[x | x <- y] = y" by (induct y, auto)

text \<open>@{verbatim \<open>isPrefixOf (reverse x) (reverse y) ==> isSuffixOf x y\<close> } \<close>
lemma "isPrefixOf\<cdot>(reverse\<cdot>x)\<cdot>(reverse\<cdot>y) = isSuffixOf\<cdot>x\<cdot>y" by auto

text \<open>@{verbatim \<open>concat (intersperse x y) ==> intercalate x y\<close> } \<close>
lemma "concat\<cdot>(intersperse\<cdot>x\<cdot>y) = intercalate\<cdot>x\<cdot>y" by auto

text \<open>@{verbatim \<open>x `seq` y ==> y\<close> } \<close>
lemma
  assumes "x \<noteq> \<bottom>" shows "seq\<cdot>x\<cdot>y = y"
  using assms by (simp add: seq_def)

text \<open>@{verbatim \<open>f $! x ==> f x\<close> } \<close>
lemma assumes "x \<noteq> \<bottom>" shows "dollarBang\<cdot>f\<cdot>x = f\<cdot>x"
  using assms by (simp add: seq_def)

text \<open>@{verbatim \<open>maybe (f x) (f . g) ==> (f . maybe x g)\<close> } \<close>
lemma "maybe\<cdot>(f\<cdot>x)\<cdot>(f oo g) \<sqsubseteq> (f oo maybe\<cdot>x\<cdot>g)"
proof (rule cfun_belowI)
  fix y
  show "maybe\<cdot>(f\<cdot>x)\<cdot>(f oo g)\<cdot>y \<sqsubseteq> (f oo maybe\<cdot>x\<cdot>g)\<cdot>y"
    by (cases y) auto
qed

end