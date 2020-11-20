structure DFS =
struct

fun fst (a, b) = a;

fun snd (a, b) = b;

fun nexts [] n = []
  | nexts (e :: es) n =
    (if (fst e = n) then (snd e :: nexts es n) else nexts es n);

fun append [] ys = ys
  | append (x :: xs) ys = (x :: append xs ys);

fun member [] y = false
  | member (x :: xs) y = ((x = y) orelse member xs y);

fun dfs g [] ys = ys
  | dfs g (x :: xs) ys =
    (if member ys x then dfs g xs ys
      else dfs g (append (nexts g x) xs) (x :: ys));

fun dfs2 g [] ys = ys
  | dfs2 g (x :: xs) ys =
    (if member ys x then dfs2 g xs ys
      else dfs2 g xs (dfs2 g (nexts g x) (x :: ys)));

val dfs = (fn x => dfs x);

val dfs2 = (fn x => dfs2 x);

end;
