theory Test_Embed_Simple
imports
  Lazy_Case.Lazy_Case
  "../Preproc/Embed"
  "../Preproc/Eval_Instances"
begin

lemma "\<langle>\<lambda>y x. map x y\<rangle> = \<Lambda> \<Lambda> (Const (Name ''List_list_map'') $ Bound 0 $ Bound 1)" ..

definition id where "id x \<equiv> x"

embed id' is id .
print_theorems

fun app where
"app [] xs = xs" |
"app (y # ys) xs = y # app ys xs"

embed app' is app .
print_theorems

declassify "(@)"
embed app'' is List_append .
thm app''

fun rev where
"rev ys [] = ys" |
"rev ys (x # xs) = rev (x # ys) xs"

embed rev' is rev .
print_theorems

declassify butlast
print_theorems

(* FIXME butlast' uses guarded recursion with if ... doesn't work just yet
embed butlast' is List_butlast .*)

datatype foo = A | B | C
derive evaluate foo

datatype 'a bippy = X 'a 'a | Y 'a 'a
derive evaluate bippy

fun bip where
"bip (X a b) = a" |
"bip (Y c d) = c"

embed bip' is bip .
print_theorems

fun mapp where
"mapp [] = (\<lambda>_. [])" |
"mapp (x # xs) = (\<lambda>f. f x # mapp xs f)"

definition map_suc where "map_suc xs = mapp xs Suc"

embed mapp' is map_suc .
thm mapp'

fun odd and even :: "nat \<Rightarrow> bool" where
"odd 0 \<longleftrightarrow> id False" |
"odd (Suc n) \<longleftrightarrow> id (even n)" |
"even 0 \<longleftrightarrow> id (id True)" |
"even (Suc n) \<longleftrightarrow> odd n"

embed odd_even is id odd even .
thm odd_even

end
